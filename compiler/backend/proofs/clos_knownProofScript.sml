open preamble
open closPropsTheory clos_knownTheory closSemTheory
open clos_knownPropsTheory
open bagTheory

val _ = new_theory "clos_knownProof";

val value_CASES = TypeBase.nchotomy_of ``:closSem$v``
val v_case_eq =
    prove_case_eq_thm{case_def = TypeBase.case_def_of ``:closSem$v``,
                      nchotomy = value_CASES}

val ref_CASES = TypeBase.nchotomy_of ``:α closSem$ref``

val va_case_eq =
    prove_case_eq_thm{case_def = TypeBase.case_def_of ``:val_approx``,
                      nchotomy = TypeBase.nchotomy_of ``:val_approx``}
val result_ty = ``:(α,β)semanticPrimitives$result``
val result_CASES = TypeBase.nchotomy_of result_ty
val result_case_eq =
    prove_case_eq_thm{case_def = TypeBase.case_def_of result_ty,
                      nchotomy = result_CASES}
val error_ty = ``:α semanticPrimitives$error_result``
val error_CASES = TypeBase.nchotomy_of error_ty
val error_case_eq =
    prove_case_eq_thm{case_def = TypeBase.case_def_of error_ty,
                      nchotomy = error_CASES}

(* TODO: MOVE candidates *)
fun sel_ihpc f = first_x_assum (first_assum o mp_then (Pos f) mp_tac)
fun resolve_selected f th = first_assum (mp_then (Pos f) mp_tac th)

fun patresolve p f th = Q.PAT_ASSUM p (mp_then (Pos f) mp_tac th)

(* repeated resolution, requiring that all preconditions get removed *)
fun nailIHx k =
  first_x_assum
    (REPEAT_GTCL
       (fn ttcl => fn th => first_assum (mp_then (Pos hd) ttcl th))
       (k o assert (not o is_imp o #2 o strip_forall o concl)) o
     assert (is_imp o #2 o strip_forall o concl))

infix >~
fun (f >~ g) th = f th >> g

(* unused *)
(* val evaluate_list_members_individually = Q.store_thm( *)
(*   "evaluate_list_members_individually", *)
(*   `∀es env (s0:'a closSem$state) vs s. *)
(*      closSem$evaluate (es, env, s0) = (Rval vs, s) ⇒ *)
(*      ∀n. n < LENGTH es ⇒ *)
(*          ∃(s0':'a closSem$state) s'. *)
(*            evaluate([EL n es], env, s0') = (Rval [EL n vs], s')`, *)
(*   Induct >> simp[] >> Cases_on `es` >> fs[] *)
(*   >- (rpt strip_tac >> rename1 `evaluate ([exp], env, _)` >> *)
(*       `∃v. vs = [v]` by metis_tac[evaluate_SING] >> rw[] >> metis_tac[]) >> *)
(*   dsimp[evaluate_def, pair_case_eq, result_case_eq] >> *)
(*   rpt strip_tac >> reverse (Cases_on `n` >> fs[]) >- metis_tac[] >> *)
(*   imp_res_tac evaluate_SING >> rw[] >> metis_tac[]); *)

(* TODO: MOVE-HOL candidate; unused here *)
val union_idem = Q.store_thm(
  "union_idem[simp]",
  `∀spt. union spt spt = spt`,
  Induct >> simp[union_def]);

(* simple properties of constants from clos_known: i.e., merge and known *)
val known_op_changed_globals = Q.store_thm(
  "known_op_changed_globals",
  `∀opn as g0 a g.
     known_op opn as g0 = (a,g) ⇒
     ∀i. i ∈ domain g ∧ (i ∈ domain g0 ⇒ lookup i g ≠ lookup i g0) ⇒
         i ∈ SET_OF_BAG (op_gbag opn)`,
  rpt gen_tac >> Cases_on `opn` >>
  simp[known_op_def, case_eq_thms, op_gbag_def, pair_case_eq, va_case_eq,
       bool_case_eq] >> rw[] >>
  fs[bool_case_eq, lookup_insert]);

val known_changed_globals = Q.store_thm(
  "known_changed_globals",
  `∀es as g0 alist g.
     known es as g0 = (alist, g) ⇒
     ∀i. i ∈ domain g ∧ (i ∈ domain g0 ⇒ lookup i g ≠ lookup i g0) ⇒
         i ∈ SET_OF_BAG (elist_globals es)`,
  ho_match_mp_tac known_ind >> simp[known_def] >> rpt strip_tac >>
  rpt (pairarg_tac >> fs[]) >> rveq >> fs[]
  >- (map_every rename1 [`known [exp1] as g0 = (al,g')`,`i ∈ domain g`] >>
      Cases_on `i ∈ domain g'` >> fs[] >>
      Cases_on `i ∈ domain g0` >> fs[] >>
      Cases_on `lookup i g' = lookup i g0` >> fs[])
  >- (map_every rename1 [
        `known [exp1] as g0 = (al1,g1)`,
        `known [exp2] as g1 = (al2,g2)`,
        `known [exp3] as g2 = (al3,g3)`] >>
      Cases_on `i ∈ domain g2` >> fs[] >>
      Cases_on `i ∈ domain g1` >> fs[] >>
      Cases_on `i ∈ domain g0` >> fs[] >>
      Cases_on `lookup i g1 = lookup i g0` >> fs[] >>
      Cases_on `lookup i g2 = lookup i g1` >> fs[])
  >- (rename1 `known exps as g0 = (al1,g1)` >>
      Cases_on `i ∈ domain g1` >> fs[] >>
      Cases_on `i ∈ domain g0` >> fs[] >>
      Cases_on `lookup i g1 = lookup i g0` >> fs[])
  >- (rename1 `known _ _  g0 = (al1,g1)` >>
      Cases_on `i ∈ domain g1` >> fs[] >>
      Cases_on `i ∈ domain g0` >> fs[] >>
      Cases_on `lookup i g1 = lookup i g0` >> fs[])
  >- (rename1 `known _ _  g0 = (_,g1)` >>
      rename1 `known_op opn` >>
      Cases_on `i ∈ domain g1` >> fs[]
      >- (Cases_on `i ∈ domain g0` >> fs[] >>
          Cases_on `lookup i g1 = lookup i g0` >> fs[] >>
          resolve_selected hd known_op_changed_globals >> simp[]) >>
      resolve_selected hd known_op_changed_globals >> simp[])
  >- (rename1 `known _ _ g0 = (_, g1)` >>
      Cases_on `i ∈ domain g1` >> fs[] >>
      Cases_on `lookup i g1 = lookup i g0` >> fs[] >>
      Cases_on `lookup i g = lookup i g1` >> fs[]));

val subspt_better_definedg = Q.store_thm(
  "subspt_better_definedg",
  `subspt sp1 sp3 ∧ better_definedg sp1 sp2 ∧ better_definedg sp2 sp3 ⇒
   subspt sp1 sp2`,
  simp[subspt_def, better_definedg_def] >> rpt strip_tac >>
  spose_not_then assume_tac >>
  `k ∈ domain sp2 ∧ k ∈ domain sp3` by metis_tac [] >>
  `∃v1 v2 v3. lookup k sp1 = SOME v1 ∧ lookup k sp2 = SOME v2 ∧
              lookup k sp3 = SOME v3` by metis_tac[domain_lookup] >>
  `v3 = v1` by metis_tac[SOME_11] >> rveq >>
  `v1 ◁ v2 ∧ v2 ◁ v1` by metis_tac[THE_DEF] >>
  metis_tac[subapprox_antisym])

val subspt_known_elist_globals = Q.store_thm(
  "subspt_known_elist_globals",
  `∀es1 as1 g0 al1 g1 es2 as2 al2 g2.
     known es1 as1 g0 = (al1, g1) ∧ known es2 as2 g1 = (al2, g2) ∧
     subspt g0 g2 ∧ BAG_DISJOINT (elist_globals es1) (elist_globals es2) ⇒
     subspt g0 g1 ∧ subspt g1 g2`,
  rpt gen_tac >> strip_tac >>
  `subspt g0 g1` by metis_tac[known_better_definedg, subspt_better_definedg] >>
  simp[] >> fs[subspt_def] >>
  rpt (gen_tac ORELSE disch_then strip_assume_tac) >>
  `better_definedg g1 g2` by metis_tac[known_better_definedg] >>
  `k ∈ domain g2` by fs[better_definedg_def] >> simp[] >>
  spose_not_then strip_assume_tac >>
  `k ∈ SET_OF_BAG (elist_globals es2)` by metis_tac[known_changed_globals] >>
  Cases_on `k ∈ domain g0` >- metis_tac[] >>
  `k ∈ SET_OF_BAG (elist_globals es1)` by metis_tac[known_changed_globals] >>
  fs[BAG_DISJOINT, DISJOINT_DEF, EXTENSION] >> metis_tac[])

val subspt_known_op_elist_globals = Q.store_thm(
  "subspt_known_op_elist_globals",
  `∀es as1 g0 al1 g1 opn as2 g2 a.
      known es as1 g0 = (al1,g1) ∧ known_op opn as2 g1 = (a,g2) ∧ subspt g0 g2 ∧
      BAG_DISJOINT (op_gbag opn) (elist_globals es) ⇒
      subspt g0 g1 ∧ subspt g1 g2`,
  rpt gen_tac >> strip_tac >>
  `subspt g0 g1`
    by metis_tac[known_better_definedg, subspt_better_definedg,
                 known_op_better_definedg] >> simp[] >>
  fs[subspt_def] >> rpt (gen_tac ORELSE disch_then strip_assume_tac) >>
  `better_definedg g1 g2` by metis_tac[known_op_better_definedg] >>
  `k ∈ domain g2` by fs[better_definedg_def] >> simp[] >>
  spose_not_then strip_assume_tac >>
  `k ∈ SET_OF_BAG (op_gbag opn)` by metis_tac[known_op_changed_globals] >>
  Cases_on `k ∈ domain g0` >- metis_tac[] >>
  `k ∈ SET_OF_BAG (elist_globals es)` by metis_tac[known_changed_globals] >>
  fs[BAG_DISJOINT, DISJOINT_DEF, EXTENSION] >> metis_tac[])

val FINITE_BAG_FOLDR = Q.store_thm(
  "FINITE_BAG_FOLDR",
  `∀l f a.
     FINITE_BAG a ∧ (∀e a. FINITE_BAG a ∧ MEM e l ⇒ FINITE_BAG (f e a)) ⇒
     FINITE_BAG (FOLDR f a l)`,
  Induct >> simp[]);

val FINITE_set_globals = Q.store_thm(
  "FINITE_set_globals[simp]",
  `(∀e. FINITE_BAG (set_globals e)) ∧ ∀es. FINITE_BAG (elist_globals es)`,
  ho_match_mp_tac set_globals_ind >> simp[] >> rpt strip_tac >>
  rename1 `op_gbag opn` >> Cases_on `opn` >> simp[op_gbag_def]);

val state_globals_approx_def = Define`
  state_globals_approx s g ⇔
    ∀k v.
      get_global k s.globals = SOME (SOME v) ⇒
      ∃a. lookup k g = SOME a ∧ val_approx_val a v
`;

val state_approx_better_definedg = Q.store_thm(
  "state_approx_better_definedg",
  `better_definedg g1 g2 ∧ state_globals_approx s g1 ⇒
   state_globals_approx s g2`,
  csimp[better_definedg_def, state_globals_approx_def, domain_lookup,
        PULL_EXISTS] >>
  metis_tac[val_approx_better_approx]);

val mapped_globals_def = Define`
  mapped_globals (s:'a closSem$state) =
    { i | ∃v. get_global i s.globals = SOME (SOME v) }
`;

val mapped_globals_refupdate = Q.store_thm(
  "mapped_globals_refupdate[simp]",
  `mapped_globals (s with refs updated_by f) = mapped_globals s`,
  simp[mapped_globals_def]);

val mapped_globals_ffiupdate = Q.store_thm(
  "mapped_globals_ffiupdate[simp]",
  `mapped_globals (s with ffi updated_by v) = mapped_globals s`,
  simp[mapped_globals_def]);

val mapped_globals_clockupdate = Q.store_thm(
  "mapped_globals_clockupdate[simp]",
  `mapped_globals (s with clock updated_by f) = mapped_globals s`,
  simp[mapped_globals_def]);

val mapped_globals_dec_clock = Q.store_thm(
  "mapped_globals_dec_clock[simp]",
  `mapped_globals (dec_clock n s) = mapped_globals s`,
  simp[mapped_globals_def, dec_clock_def])

val evaluate_t = ``closSem$evaluate``
val fixeqs = let
  fun c t =
    let
      val r = rhs t
      val (f, _) = strip_comb r
    in
      if same_const evaluate_t f then REWR_CONV EQ_SYM_EQ
      else NO_CONV
    end t
in
  RULE_ASSUM_TAC (CONV_RULE (TRY_CONV c))
end

val state_globals_approx_clock_fupd = Q.store_thm(
  "state_globals_approx_clock_fupd[simp]",
  `state_globals_approx (s with clock updated_by f) g ⇔
   state_globals_approx s g`,
  simp[state_globals_approx_def]);

val state_globals_approx_dec_clock = Q.store_thm(
  "state_globals_approx_dec_clock[simp]",
  `state_globals_approx (dec_clock n s) g ⇔ state_globals_approx s g`,
  simp[dec_clock_def]);

val state_globals_approx_refsfupd = Q.store_thm(
  "state_globals_approx_refsfupd[simp]",
  `state_globals_approx (s with refs updated_by f) g ⇔
   state_globals_approx s g`,
  simp[state_globals_approx_def]);

val state_globals_approx_ffifupd = Q.store_thm(
  "state_globals_approx_ffifupd[simp]",
  `state_globals_approx (s with ffi updated_by f) g ⇔
   state_globals_approx s g`,
  simp[state_globals_approx_def]);

val value_ind =
  TypeBase.induction_of ``:closSem$v``
   |> Q.SPECL [`P`, `EVERY P`]
   |> SIMP_RULE (srw_ss()) []
   |> UNDISCH |> CONJUNCT1 |> DISCH_ALL |> Q.GEN `P`


val mglobals_extend_def = Define`
  mglobals_extend s1 mgs s2 ⇔
     mapped_globals s2 ⊆ mapped_globals s1 ∪ mgs ∧
     ∀k v. get_global k s2.globals = SOME (SOME v) ∧ k ∉ mgs ⇒
           get_global k s1.globals = SOME (SOME v)`

val mglobals_extend_refl = Q.store_thm(
  "mglobals_extend_refl[simp]",
  `mglobals_extend s gs s`,
  simp[mglobals_extend_def]);

val mglobals_extend_trans = Q.store_thm(
  "mglobals_extend_trans",
  `mglobals_extend s0 g1 s1 ∧ mglobals_extend s1 g2 s2 ⇒
   mglobals_extend s0 (g1 ∪ g2) s2`,
  simp[mglobals_extend_def, SUBSET_DEF] >> metis_tac[]);

val mglobals_extend_SUBSET = Q.store_thm(
  "mglobals_extend_SUBSET",
  `mglobals_extend s0 g1 s ∧ g1 ⊆ g2 ⇒ mglobals_extend s0 g2 s`,
  simp[mglobals_extend_def, SUBSET_DEF] >> metis_tac[]);

val mglobals_extend_refupdate = Q.store_thm(
  "mglobals_extend_refupdate[simp]",
  `(mglobals_extend s0 gs (s with refs updated_by f) ⇔
      mglobals_extend s0 gs s) ∧
   (mglobals_extend (s0 with refs updated_by f) gs s ⇔
      mglobals_extend s0 gs s)`,
  simp[mglobals_extend_def]);

val mglobals_extend_ffiupdate = Q.store_thm(
  "mglobals_extend_ffiupdate[simp]",
  `(mglobals_extend s0 gs (s with ffi updated_by f) ⇔
      mglobals_extend s0 gs s) ∧
   (mglobals_extend (s0 with ffi updated_by f) gs s  ⇔
      mglobals_extend s0 gs s)`,
  simp[mglobals_extend_def]);

val mglobals_extend_clockupdate = Q.store_thm(
  "mglobals_extend_clockupdate[simp]",
  `(mglobals_extend s0 gs (s with clock updated_by f) ⇔
      mglobals_extend s0 gs s) ∧
   (mglobals_extend (s0 with clock updated_by f) gs s ⇔
      mglobals_extend s0 gs s)`,
  simp[mglobals_extend_def]);

val mglobals_extend_decclock = Q.store_thm(
  "mglobals_extend_decclock[simp]",
  `(mglobals_extend (dec_clock n s0) gs s ⇔ mglobals_extend s0 gs s) ∧
   (mglobals_extend s0 gs (dec_clock n s) ⇔ mglobals_extend s0 gs s)`,
  simp[dec_clock_def]);

val do_app_ssgc = Q.store_thm(
  "do_app_ssgc",
  `∀opn args s0 res.
     do_app opn args s0 = res ⇒
     EVERY vsgc_free args ∧ ssgc_free s0 ⇒
     (∀v s. res = Rval(v,s) ⇒
            vsgc_free v ∧ ssgc_free s ∧
            mglobals_extend s0 (SET_OF_BAG (op_gbag opn)) s) ∧
     (∀v. res = Rerr (Rraise v) ⇒ vsgc_free v)`,
  Cases_on `opn` >>
  simp[do_app_def, case_eq_thms, op_gbag_def, PULL_EXISTS, bool_case_eq,
       pair_case_eq]
  >- ((* GetGlobal *)
      simp[get_global_def, ssgc_free_def] >> metis_tac[MEM_EL])
  >- ((* SetGlobal *)
      simp[ssgc_free_def, mglobals_extend_def, mapped_globals_def] >>
      rpt strip_tac
      >- metis_tac[]
      >- metis_tac[]
      >- (fs[MEM_LUPDATE] >> metis_tac[MEM_EL])
      >- (dsimp[SUBSET_DEF, get_global_def,
                EL_LUPDATE, bool_case_eq] >> metis_tac[])
      >- (fs[get_global_def, EL_LUPDATE]))
  >- (dsimp[ssgc_free_def, mglobals_extend_def, mapped_globals_def, SUBSET_DEF,
            get_global_def, EL_APPEND_EQN, bool_case_eq] >>
      reverse (rpt strip_tac)
      >- (rename1 `ii < LENGTH (ss:α closSem$state).globals` >>
          Cases_on `ii < LENGTH ss.globals` >> simp[] >>
          Cases_on `ii - LENGTH ss.globals = 0`
          >- (pop_assum SUBST_ALL_TAC >> simp[]) >> simp[])
      >- (rename1 `nn < LENGTH (ss:α closSem$state).globals` >>
          Cases_on `nn < LENGTH ss.globals` >> simp[] >>
          Cases_on `nn < LENGTH ss.globals + 1` >> simp[] >>
          `nn - LENGTH ss.globals = 0` by simp[] >> simp[]) >>
      metis_tac[])
  >- (
    dsimp [] >>
    rw [] >>
    irule EVERY_TAKE >>
    simp []
    >- intLib.ARITH_TAC >>
    irule EVERY_DROP >>
    simp []
    >- intLib.ARITH_TAC)
  >- (simp[PULL_FORALL] >> metis_tac[EVERY_MEM, MEM_EL])
  >- (simp[ssgc_free_def] >>
      rpt (disch_then strip_assume_tac ORELSE gen_tac) >> rpt conj_tac
      >- first_assum MATCH_ACCEPT_TAC >> fs[] >>
      simp[FLOOKUP_UPDATE, bool_case_eq] >> metis_tac[])
  >- (simp[ssgc_free_def] >>
      rpt (disch_then strip_assume_tac ORELSE gen_tac) >> rpt conj_tac
      >- first_assum MATCH_ACCEPT_TAC >> fs[] >>
      dsimp[FLOOKUP_UPDATE, bool_case_eq, EVERY_REPLICATE] >> metis_tac[])
  >- (simp[ssgc_free_def] >>
      rpt (disch_then strip_assume_tac ORELSE gen_tac) >> rpt conj_tac
      >- first_assum MATCH_ACCEPT_TAC >> fs[] >>
      dsimp[FLOOKUP_UPDATE, bool_case_eq, EVERY_REPLICATE] >> metis_tac[])
  >- (dsimp[ssgc_free_def,FLOOKUP_UPDATE,bool_case_eq] \\ rw[] \\ metis_tac[])
  >- (simp[PULL_FORALL] >> rpt gen_tac >> rename1 `v_to_list v = SOME vs` >>
      map_every qid_spec_tac [`vs`, `v`] >> ho_match_mp_tac value_ind >>
      simp[v_to_list_def] >> Cases >>
      simp[v_to_list_def] >>
      rename1 `closSem$Block _ (v1::vs)` >> Cases_on `vs` >>
      simp[v_to_list_def] >>
      rename1 `closSem$Block _ (v1::v2::vs)` >> Cases_on `vs` >>
      simp[v_to_list_def, case_eq_thms, PULL_EXISTS, PULL_FORALL])
  >- (dsimp[ssgc_free_def, FLOOKUP_UPDATE, bool_case_eq] >> metis_tac[])
  >- (dsimp[ssgc_free_def] >>
      metis_tac[MEM_EL, EVERY_MEM, integerTheory.INT_INJ,
                integerTheory.INT_OF_NUM, integerTheory.INT_LT])
  >- (dsimp[ssgc_free_def, FLOOKUP_UPDATE, bool_case_eq] >>
      rpt strip_tac
      >- metis_tac[]
      >- (irule IMP_EVERY_LUPDATE >> simp[] >> metis_tac[])
      >- metis_tac[])
  >- (dsimp[ssgc_free_def, FLOOKUP_UPDATE, bool_case_eq] >> metis_tac[])
  >> dsimp[]);

val EVERY_lookup_vars = Q.store_thm(
  "EVERY_lookup_vars",
  `∀vs env env'. EVERY P env ∧ lookup_vars vs env = SOME env' ⇒ EVERY P env'`,
  Induct >> simp[lookup_vars_def, case_eq_thms, PULL_EXISTS] >>
  metis_tac[MEM_EL, EVERY_MEM]);

val lem = Q.prove(
  `(∀a es env (s0:α closSem$state) res s.
      a = (es,env,s0) ∧ evaluate(es,env,s0) = (res,s) ⇒
      mapped_globals s0 ⊆ mapped_globals s) ∧
   (∀lopt f args (s0:α closSem$state) res s.
      evaluate_app lopt f args s0 = (res, s) ⇒
      mapped_globals s0 ⊆ mapped_globals s)`,
  ho_match_mp_tac evaluate_ind >> rw[evaluate_def]
  >- fs[evaluate_def]
  >- (fs[pair_case_eq, result_case_eq] >> rveq >> fs[] >>
      metis_tac[SUBSET_TRANS])
  >- fs[evaluate_def, bool_case_eq]
  >- (fs[pair_case_eq, result_case_eq, bool_case_eq] >> rveq >> fixeqs >>
      fs[] >> metis_tac[SUBSET_TRANS])
  >- (fs[pair_case_eq, result_case_eq] >> rveq >> fs[] >>
      metis_tac[SUBSET_TRANS])
  >- fs[result_case_eq, pair_case_eq]
  >- (fs[result_case_eq, pair_case_eq, error_case_eq] >> rveq >> fs[] >>
      metis_tac[SUBSET_TRANS])
  >- (fs[pair_case_eq, result_case_eq] >> rveq >> fs[] >>
      rename1 `closSem$do_app opn` >> Cases_on `opn` >>
      fs[do_app_def, case_eq_thms, bool_case_eq, pair_case_eq] >> rw[] >>
      fs[]
      >- (rename1 `closSem$evaluate(_,_,s0) = (_, s1)` >>
          irule SUBSET_TRANS >> qexists_tac `mapped_globals s1` >> simp[] >>
          simp[mapped_globals_def] >>
          fs[SUBSET_DEF, PULL_EXISTS, get_global_def,
             EL_LUPDATE, bool_case_eq] >> metis_tac[])
      >- (simp[mapped_globals_def, SUBSET_DEF, get_global_def,
               EL_APPEND_EQN, bool_case_eq] >> rpt strip_tac >>
          simp[]))
  >- fs[evaluate_def, bool_case_eq, case_eq_thms]
  >- (fs[case_eq_thms, PULL_EXISTS] >> rveq >> fs[])
  >- (fs[pair_case_eq, result_case_eq] >> rveq >> fs[] >>
      metis_tac[SUBSET_TRANS])
  >- (fs[pair_case_eq, result_case_eq, case_eq_thms, bool_case_eq] >> rveq >> fixeqs >>
      fs[] >> metis_tac[SUBSET_TRANS])
  >- (fs[case_eq_thms, bool_case_eq, pair_case_eq] >> rveq >> fs[] >>
      metis_tac[SUBSET_TRANS]));

val mapped_globals_grow = save_thm(
  "mapped_globals_grow",
  lem |> CONJUNCT1 |> SIMP_RULE bool_ss [])

fun say0 pfx s g = (print (pfx ^ ": " ^ s ^ "\n"); ALL_TAC g)
val say = say0 "ssgc_evaluate0"

val ssgc_evaluate0 = Q.prove(
  `(∀a es env (s0:α closSem$state) res s.
      ssgc_free s0 ∧ EVERY vsgc_free env ∧
      EVERY esgc_free es ∧ a = (es,env,s0) ∧
      evaluate a = (res,s) ⇒
      ssgc_free s ∧ rsgc_free res ∧
      mglobals_extend s0 (SET_OF_BAG (elist_globals es)) s) ∧
   (∀lopt f args (s0:α closSem$state) res s.
      ssgc_free s0 ∧ vsgc_free f ∧ EVERY vsgc_free args ∧
      evaluate_app lopt f args s0 = (res, s) ⇒
      ssgc_free s ∧ rsgc_free res ∧ mglobals_extend s0 ∅ s)`,
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >> simp[]
  >- (* nil *) simp[evaluate_def]
  >- ((* cons *) say "cons" >> rpt gen_tac >> strip_tac >>
      simp[evaluate_def, pair_case_eq, result_case_eq,
           PULL_EXISTS] >>
      rename1 `evaluate([e1], env, s0)` >>
      rpt gen_tac >> strip_tac >> rveq >> fs[]
      >- (imp_res_tac evaluate_SING >> rveq >> fs[SET_OF_BAG_UNION] >>
          metis_tac[mglobals_extend_trans])
      >- (fs[SET_OF_BAG_UNION] >> metis_tac[mglobals_extend_trans])
      >- (fs[SET_OF_BAG_UNION] >>
          metis_tac[mglobals_extend_SUBSET, SUBSET_UNION]))
  >- ((* var *) say "var" >> simp[evaluate_def] >> rw[] >> rw[] >>
      metis_tac[EVERY_MEM, MEM_EL])
  >- ((* If *) say "if" >> rpt gen_tac >> strip_tac >>
      simp[evaluate_def, pair_case_eq, result_case_eq,
           bool_case_eq] >>
      rpt gen_tac >> reverse strip_tac >> rveq >> fixeqs >>
      fs[SET_OF_BAG_UNION]
      >- metis_tac[mglobals_extend_SUBSET, SUBSET_UNION, UNION_ASSOC,
                   UNION_COMM]
      >- metis_tac[mglobals_extend_SUBSET, SUBSET_UNION, UNION_ASSOC,
                   UNION_COMM] >>
      rename1 `evaluate ([gd], env, s0) = (Rval vs, s1)` >>
      rename1 `mglobals_extend s0 set1 s1` >>
      rename1 `mglobals_extend s1 set2 s` >>
      `mglobals_extend s0 (set1 ∪ set2) s` by metis_tac[mglobals_extend_trans]>>
      metis_tac[mglobals_extend_SUBSET, SUBSET_UNION, UNION_ASSOC, UNION_COMM])
  >- ((* let *) say "let" >> rpt gen_tac >> strip_tac >>
      simp[evaluate_def, pair_case_eq, result_case_eq] >>
      rpt gen_tac >> strip_tac >> rveq >> fs[SUBSET_DEF, SET_OF_BAG_UNION] >>
      metis_tac[mglobals_extend_trans, UNION_COMM, SUBSET_UNION,
                mglobals_extend_SUBSET])
  >- ((* raise *) say "raise" >> rpt gen_tac >> strip_tac >>
      simp[evaluate_def, pair_case_eq, result_case_eq] >>
      rpt gen_tac >> strip_tac >> rveq >> fs[SUBSET_DEF, SET_OF_BAG_UNION] >>
      metis_tac[evaluate_SING, HD, EVERY_DEF])
  >- ((* handle *) say "handle" >> rpt gen_tac >> strip_tac >>
      simp[evaluate_def, pair_case_eq, result_case_eq,
           error_case_eq] >>
      rpt gen_tac >> strip_tac >> rveq >> fs[SUBSET_DEF, SET_OF_BAG_UNION] >>
      metis_tac[mglobals_extend_SUBSET, SUBSET_UNION, mglobals_extend_trans])
  >- ((* op *) say "op" >> rpt gen_tac >> strip_tac >>
      simp[evaluate_def, pair_case_eq, result_case_eq] >>
      rpt gen_tac >> strip_tac >> rveq >> fs[]
      >- (IMP_RES_THEN mp_tac do_app_ssgc >> simp[EVERY_REVERSE] >>
          fs[SET_OF_BAG_UNION] >>
          metis_tac[mglobals_extend_trans, UNION_COMM])
      >- (IMP_RES_THEN mp_tac do_app_ssgc >> simp[EVERY_REVERSE] >>
          rename1 `Rerr err` >> Cases_on `err` >> simp[] >>
          fs[SET_OF_BAG_UNION] >>
          metis_tac[SUBSET_UNION, mglobals_extend_SUBSET])
      >- (fs[SET_OF_BAG_UNION] >>
          metis_tac[SUBSET_UNION, mglobals_extend_SUBSET]))
  >- ((* Fn *) say "fn" >>
      simp[evaluate_def, case_eq_thms, bool_case_eq] >> rpt gen_tac >>
      strip_tac >> rveq >> fs[] >> metis_tac[EVERY_lookup_vars])
  >- ((* Letrec *) say "letrec" >>
      simp[evaluate_def, bool_case_eq, case_eq_thms] >>
      rpt (gen_tac ORELSE disch_then strip_assume_tac) >> rveq >>
      fs[EVERY_GENLIST] >>
      imp_res_tac EVERY_lookup_vars >> fs[] >>
      metis_tac[mglobals_extend_SUBSET, SUBSET_UNION])
  >- ((* App *) say "app" >>
      rpt gen_tac >> strip_tac >>
      simp[evaluate_def, bool_case_eq, pair_case_eq,
           result_case_eq] >>
      rpt (gen_tac ORELSE disch_then strip_assume_tac) >> rveq >> fs[]
      >- (imp_res_tac evaluate_SING >> rveq >>
          fs[SET_OF_BAG_UNION] >>
          metis_tac[mglobals_extend_trans, UNION_COMM, UNION_EMPTY])
      >- (fs[SET_OF_BAG_UNION] >> metis_tac[mglobals_extend_trans, UNION_COMM])
      >- (fs[SET_OF_BAG_UNION] >>
          metis_tac[mglobals_extend_SUBSET, SUBSET_UNION]))
  >- ((* Tick *)
      say "tick" >> simp[evaluate_def, bool_case_eq] >>
      rpt (gen_tac ORELSE disch_then strip_assume_tac) >> rveq >> fixeqs >>
      fs[])
  >- ((* Call *)
      say "call" >> rpt gen_tac >> strip_tac >>
      simp[evaluate_def, pair_case_eq, result_case_eq, case_eq_thms,
           bool_case_eq] >>
      rpt (gen_tac ORELSE disch_then strip_assume_tac) >> rveq >> fixeqs >>
      fs[] >> fs[find_code_def, case_eq_thms, pair_case_eq] >> rveq >>
      rename1 `FLOOKUP _.code _ = SOME (_, fbody)` >>
      `set_globals fbody = {||}` suffices_by
        (strip_tac >> fs[] >> imp_res_tac set_globals_empty_esgc_free >>
         fs[] >> metis_tac[mglobals_extend_trans, UNION_EMPTY]) >>
      fs[ssgc_free_def] >> metis_tac[])
  >- ((* evaluate_app *)
      say "evaluate_app" >> rpt gen_tac >> strip_tac >>
      simp[evaluate_def, case_eq_thms, bool_case_eq, pair_case_eq] >>
      rpt (gen_tac ORELSE disch_then strip_assume_tac) >> rveq >> fixeqs >>
      fs[]
      >- (fs[dest_closure_def, case_eq_thms, bool_case_eq] >> rveq >>
          fs[] >> pairarg_tac >> fs[bool_case_eq])
      >- (fs[dest_closure_def, case_eq_thms, bool_case_eq] >> rveq >>
          fs[EVERY_REVERSE, EVERY_DROP, EVERY_TAKE]
          >- (imp_res_tac set_globals_empty_esgc_free >> fs[] >>
              metis_tac[mglobals_extend_trans, UNION_EMPTY]) >>
          pairarg_tac >>
          fs[elglobals_EQ_EMPTY, bool_case_eq] >> rveq >>
          fs[EVERY_DROP, EVERY_TAKE, EVERY_REVERSE, EVERY_GENLIST,
             elglobals_EQ_EMPTY, MEM_MAP, PULL_EXISTS] >>
          rename1 `EL ii fns = (_, fbody)` >>
          `ii < LENGTH fns` by simp[] >>
          `set_globals fbody = {||}` by metis_tac[MEM_EL,SND] >>
          imp_res_tac set_globals_empty_esgc_free >> fs[] >>
          metis_tac[mglobals_extend_trans, UNION_EMPTY])
      >- (fs[dest_closure_def, case_eq_thms, bool_case_eq] >> rveq >>
          fs[EVERY_TAKE, EVERY_REVERSE, EVERY_DROP]
          >- (imp_res_tac set_globals_empty_esgc_free >> fs[]) >>
          pairarg_tac >>
          fs[elglobals_EQ_EMPTY, bool_case_eq] >> rveq >>
          fs[EVERY_DROP, EVERY_TAKE, EVERY_REVERSE, EVERY_GENLIST,
             elglobals_EQ_EMPTY, MEM_MAP, PULL_EXISTS] >>
          rename1 `EL ii fns = (_, fbody)` >>
          `ii < LENGTH fns` by simp[] >>
          `set_globals fbody = {||}` by metis_tac[MEM_EL,SND] >>
          imp_res_tac set_globals_empty_esgc_free >> fs[])
      >- (fs[dest_closure_def, case_eq_thms, bool_case_eq] >> rveq >>
          fs[EVERY_TAKE, EVERY_REVERSE, EVERY_DROP]
          >- (imp_res_tac set_globals_empty_esgc_free >> fs[]) >>
          pairarg_tac >>
          fs[elglobals_EQ_EMPTY, bool_case_eq] >> rveq >>
          fs[EVERY_DROP, EVERY_TAKE, EVERY_REVERSE, EVERY_GENLIST,
             elglobals_EQ_EMPTY, MEM_MAP, PULL_EXISTS] >>
          rename1 `EL ii fns = (_, fbody)` >>
          `ii < LENGTH fns` by simp[] >>
          `set_globals fbody = {||}` by metis_tac[MEM_EL,SND] >>
          imp_res_tac set_globals_empty_esgc_free >> fs[])))

val ssgc_evaluate = save_thm(
  "ssgc_evaluate",
  ssgc_evaluate0 |> CONJUNCT1 |> SIMP_RULE bool_ss []);

val known_preserves_setGlobals = Q.store_thm(
  "known_preserves_setGlobals",
  `∀es as g0 all g.
      known es as g0 = (all,g) ⇒
      elist_globals (MAP FST all) = elist_globals es`,
  ho_match_mp_tac known_ind >> simp[known_def] >> rpt strip_tac >>
  rpt (pairarg_tac >> fs[]) >> rw[] >> fs[] >> imp_res_tac known_sing_EQ_E >>
  rw[] >> fs[] >> rw[] >> simp[elist_globals_FOLDR]
  >- (rename [`isGlobal opn`] >> Cases_on `opn` >> fs[isGlobal_def] >>
      rename [`gO_destApx a`] >> Cases_on `a` >>
      fs[gO_destApx_def, op_gbag_def, elist_globals_FOLDR] >>
      fs[known_op_def, bool_case_eq, case_eq_thms, NULL_EQ] >> rw[op_gbag_def]) >>
  irule FOLDR_CONG >> simp[] >>
  simp[LIST_EQ_REWRITE, EL_MAP] >>
  rpt strip_tac >> pairarg_tac >>
  simp[]>> rw[] >>
  qmatch_abbrev_tac `set_globals (FST (HD (FST (known [X] ENV G0)))) =
                     set_globals X` >>
  rename1 `EL x fns = (nn,X)` >> `MEM (nn,X) fns` by metis_tac[MEM_EL] >>
  res_tac >> rfs[] >>
  `∃X' APX g'. known [X] ENV G0 = ([(X',APX)], g')` by metis_tac[known_sing] >>
  fs[])

val mglobals_extend_EMPTY_state_globals_approx = Q.store_thm(
  "mglobals_extend_EMPTY_state_globals_approx",
  `mglobals_extend s1 ∅ s2 ∧ mapped_globals s1 ⊆ mapped_globals s2 ⇒
   (state_globals_approx s1 g ⇔ state_globals_approx s2 g)`,
  simp[mglobals_extend_def, state_globals_approx_def, EXTENSION, SUBSET_DEF,
       mapped_globals_def] >>
  metis_tac[]);

val known_preserves_esgc_free = Q.store_thm(
  "known_preserves_esgc_free",
  `∀es as g0 all g.
     known es as g0 = (all,g) ∧ EVERY esgc_free es ⇒
     EVERY (esgc_free o FST) all`,
  ho_match_mp_tac known_ind >> simp[known_def] >> rpt strip_tac >>
  rpt (pairarg_tac >> fs[]) >> rw[] >> fs[] >> imp_res_tac known_sing_EQ_E >>
  rw[] >> fs[] >> rw[ALL_EL_MAP]
  >- (every_case_tac >> simp[] >> fs[EVERY_MEM, MEM_MAP, PULL_EXISTS])
  >- (imp_res_tac known_preserves_setGlobals >> fs[])
  >- (fs[elglobals_EQ_EMPTY, MEM_MAP, PULL_EXISTS] >> rpt strip_tac >>
      pairarg_tac >> rw[] >> fs[FORALL_PROD] >>
      qmatch_abbrev_tac
        `set_globals (FST (HD (FST (known [X] ENV g00)))) = _` >>
      rename1 `MEM (nn, X) fns` >>
      rpt (first_x_assum (qspecl_then [`nn`, `X`] mp_tac)) >> simp[] >>
      `∃X' APX gg. known [X] ENV g00 = ([(X',APX)], gg)`
        by metis_tac[known_sing] >> simp[] >>
      imp_res_tac known_preserves_setGlobals >> fs[]))

val ssgc_free_preserved_SING = Q.store_thm(
  "ssgc_free_preserved_SING",
  `known [e1] as g0 = ([(e1',a)], g) ∧ esgc_free e1 ∧ ssgc_free s0 ∧
   EVERY vsgc_free env ∧ evaluate([e1'],env,s0) = (res,s) ⇒ ssgc_free s`,
  rpt strip_tac >>
  `EVERY esgc_free [e1]` by simp[] >>
  `EVERY (esgc_free o FST) [(e1',a)]`
     by metis_tac[known_preserves_esgc_free] >>
  `EVERY esgc_free [e1']` by fs[] >>
  metis_tac[ssgc_evaluate]);

val known_op_correct_approx = Q.store_thm(
  "known_op_correct_approx",
  `known_op opn args g0 = (a,g) ∧ LIST_REL val_approx_val args vs ∧
   subspt g g' ∧
   state_globals_approx s0 g' ∧
   do_app opn vs s0 = Rval (v, s) ⇒
   state_globals_approx s g' ∧ val_approx_val a v`,
  Cases_on `opn` >>
  simp[known_op_def, do_app_def, case_eq_thms, va_case_eq, bool_case_eq,
       pair_case_eq] >>
  rpt strip_tac >> rveq >> fs[]
  >- (fs[state_globals_approx_def] >> res_tac >>
      fs[subspt_def] >> metis_tac[SOME_11, domain_lookup])
  >- (fs[state_globals_approx_def, get_global_def, EL_LUPDATE,
         lookup_insert, bool_case_eq] >> rw[] >> simp[] >>
      fs[subspt_def])
  >- (fs[state_globals_approx_def, get_global_def, EL_LUPDATE,
         bool_case_eq, lookup_insert] >> rw[] >> fs[subspt_def] >>
      metis_tac[val_approx_val_merge_I])
  >- (fs[state_globals_approx_def, get_global_def, EL_APPEND_EQN,
         bool_case_eq] >> rw[]
      >- metis_tac[]
      >- (rename1 `nn - LENGTH (ss:'a closSem$state).globals` >>
          `nn - LENGTH ss.globals = 0` by simp[] >>
          pop_assum (fn th => fs[th])))
  >- (rveq >> fs[LIST_REL_EL_EQN]));

val LENGTH_clos_gen = Q.prove(`
  ∀ls x c.
  LENGTH (clos_gen x c ls) = LENGTH ls`,
  Induct>>fs[FORALL_PROD,clos_gen_def])

val clos_gen_eq = Q.prove(`
  ∀n c fns.
  clos_gen n c fns =
  GENLIST (λi. Clos (2* (i+c) +n ) (FST (EL i fns))) (LENGTH fns)`,
  Induct_on`fns`>>fs[FORALL_PROD,clos_gen_def,GENLIST_CONS]>>rw[]>>
  simp[o_DEF,ADD1])

val letrec_case_eq = Q.prove(`
  (case loc of
    NONE => REPLICATE (LENGTH fns) Other
  | SOME n => clos_gen n 0 fns) =
  GENLIST (case loc of NONE => K Other | SOME n => λi. Clos (n+ 2*i) (FST (EL i fns))) (LENGTH fns)`,
  Cases_on`loc`>>fs[clos_gen_eq,REPLICATE_GENLIST])

val say = say0 "known_correct_approx"
val known_correct_approx = Q.store_thm(
  "known_correct_approx",
  `∀es as g0 all g env s0 s result g'.
     known es as g0 = (all,g) ∧ BAG_ALL_DISTINCT (elist_globals es) ∧
     LIST_REL val_approx_val as env ∧ subspt g0 g ∧ subspt g g' ∧
     state_globals_approx s0 g' ∧ ssgc_free s0 ∧ EVERY vsgc_free env ∧
     EVERY esgc_free es ∧ evaluate(MAP FST all, env, s0) = (result, s)
    ⇒
     state_globals_approx s g' ∧
     ∀vs. result = Rval vs ⇒ LIST_REL val_approx_val (MAP SND all) vs`,
  ho_match_mp_tac known_ind >> simp[known_def] >>
  rpt conj_tac >> rpt (gen_tac ORELSE disch_then strip_assume_tac)
  >- (* nil *) (say "nil" >> fs[evaluate_def] >> rw[])
  >- (say "cons" >> rpt (pairarg_tac >> fs[]) >> rveq >>
      rename1 `known [exp1] as g0` >>
      `∃exp1' a1 g1. known [exp1] as g0 = ([(exp1',a1)], g1)`
         by metis_tac[known_sing] >> fs[] >> rveq >> fs[] >>
      rename1 `known [exp1] EA g0 = ([(exp1',a1)], g1)` >>
      rename1 `known (exp2::erest) EA g1 = (al2,g)` >>
      `LENGTH al2 = LENGTH (exp2::erest)` by metis_tac[known_LENGTH, FST] >>
      fs[] >>
      `∃exp2' a2 arest. al2 = (exp2',a2)::arest`
        by (Cases_on `al2` >> fs[] >> metis_tac[pair_CASES]) >> rveq >>
      patresolve `known [_] _ _ = _` hd subspt_known_elist_globals >> simp[] >>
      disch_then (resolve_selected hd) >>
      fs[BAG_ALL_DISTINCT_BAG_UNION] >> strip_tac >>
      fs[evaluate_def, pair_case_eq, result_case_eq] >> rveq
      >- (rename1 `evaluate ([exp1'], env, s0) = (Rval v1, s1)` >>
          first_x_assum (Q.PAT_ASSUM `closSem$evaluate([_],_,_) = _` o
                         mp_then (Pos last) mp_tac) >>
          simp[] >>
          disch_then (resolve_selected last) >> simp[] >>
          impl_keep_tac >- metis_tac[subspt_trans] >> strip_tac >>
          simp[] >> rveq >> fs[] >> sel_ihpc last >> simp[] >>
          metis_tac[ssgc_free_preserved_SING])
      >- (simp[] >>
          first_x_assum (Q.PAT_ASSUM `closSem$evaluate ([_],_,_) = _` o
                         mp_then (Pos last) mp_tac) >>
          simp[] >>
          disch_then (resolve_selected last) >> simp[] >>
          impl_tac >- metis_tac[subspt_trans] >> rw[] >>
          sel_ihpc last >> simp[] >> disch_then irule >> simp[]>>
          metis_tac[ssgc_free_preserved_SING])
      >- (simp[] >> sel_ihpc last >> simp[] >> metis_tac[subspt_trans]))
  >- ((* Var *) say "var" >>
      fs[any_el_ALT, evaluate_def, bool_case_eq] >>
      fs[LIST_REL_EL_EQN])
  >- ((* If *) say "if" >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[BAG_ALL_DISTINCT_BAG_UNION] >>
      rename1 `known [ge] as g0 = (_, g1)` >>
      `∃ge' apx1. known [ge] as g0 = ([(ge',apx1)], g1)`
         by metis_tac[known_sing, PAIR_EQ] >>
      rename1 `known [tb] as g1 = (_, g2)` >>
      `∃tb' apx2. known [tb] as g1 = ([(tb',apx2)], g2)`
         by metis_tac[known_sing, PAIR_EQ] >>
      rename1 `known [eb] as g2 = (_, g3)` >>
      `∃eb' apx3. known [eb] as g2 = ([(eb',apx3)], g3)`
         by metis_tac[known_sing, PAIR_EQ] >> fs[] >> rveq >> fs[] >> rveq >>
      `subspt g0 g1 ∧ subspt g1 g2 ∧ subspt g2 g3`
         by (`∃al01. known [ge;tb] as g0 = (al01,g2)` by simp[known_def] >>
             first_assum (mp_then (Pos hd) mp_tac subspt_known_elist_globals) >>
             simp[] >>
             disch_then (first_assum o mp_then (Pos hd) mp_tac) >>
             simp[] >> strip_tac >>
             qpat_x_assum `known [_] _ g0 = (_,g1)`
               (mp_then (Pos hd) mp_tac subspt_known_elist_globals) >>
             simp[] >> disch_then (first_assum o mp_then (Pos hd) mp_tac) >>
             simp[]) >>
      reverse
        (fs[evaluate_def, pair_case_eq, result_case_eq,
            bool_case_eq]) >> rveq >> fixeqs >> simp[]
      >- (first_x_assum (first_assum o mp_then (Pos last) mp_tac) >> simp[] >>
          metis_tac[subspt_trans])
      >- (sel_ihpc last >> simp[] >> metis_tac[subspt_trans]) >>
      (* two cases from here on *)
      rename1 `evaluate ([ge'], env, s0) = (Rval gvs, s1)` >>
      first_x_assum
        (Q.PAT_ASSUM `evaluate ([ge'], _, _) = _` o mp_then (Pos last) mp_tac) >>
      simp[] >> disch_then (resolve_selected last) >> simp[] >>
      (impl_keep_tac >- metis_tac[subspt_trans]) >>
      strip_tac >> rveq >> fs[] >> rveq >> sel_ihpc last >> simp[] >>
      disch_then (resolve_selected (el 2)) >> simp[] >>
      impl_tac
      >- metis_tac[ssgc_free_preserved_SING]
      >- metis_tac[val_approx_val_merge_I]
      >- (conj_tac >- metis_tac[subspt_trans] >>
          irule (GEN_ALL ssgc_free_preserved_SING) >> metis_tac[])
      >- metis_tac[val_approx_val_merge_I])
  >- ((* let *) say "let" >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
      fs[evaluate_def, case_eq_thms, pair_case_eq, result_case_eq] >>
      rveq >> sel_ihpc last >> simp[] >> disch_then (resolve_selected last) >>
      simp[] >> fs[BAG_ALL_DISTINCT_BAG_UNION] >>
      map_every rename1 [`known [bod] _ g1 = (_, g)`,
                           `known _ _ g0 = (_, g1)`] >>
      patresolve `known [_] _ _ = _` (el 2) subspt_known_elist_globals >>
      simp[] >> disch_then (resolve_selected hd) >> simp[] >>
      (impl_tac >- fs[BAG_DISJOINT, DISJOINT_SYM]) >> strip_tac >> simp[] >>
      (impl_tac >- metis_tac[subspt_trans]) >> strip_tac >> simp[] >>
      imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rveq >>
      sel_ihpc last >> simp[EVERY2_APPEND_suff] >>
      disch_then (resolve_selected (el 2)) >> simp[] >> reverse impl_tac
      >- rw[] >> resolve_selected hd ssgc_evaluate >> simp[] >>
      disch_then (resolve_selected last) >> simp[] >>
      imp_res_tac known_preserves_esgc_free >> simp[ALL_EL_MAP])
  >- ((* raise *) say "raise" >>
      pairarg_tac >> fs[] >> imp_res_tac known_sing_EQ_E >> fs[] >> rveq >>
      fs[evaluate_def, pair_case_eq, result_case_eq] >> rveq >>
      simp[] >> metis_tac[])
  >- ((* tick *) say "tick" >>
      pairarg_tac >> fs[] >> imp_res_tac known_sing_EQ_E >> fs[] >> rveq >>
      fs[evaluate_def, pair_case_eq, result_case_eq,
         bool_case_eq] >> rveq >> simp[] >>
      fixeqs >> first_x_assum irule >> simp[] >>
      metis_tac[state_globals_approx_dec_clock, ssgc_free_dec_clock])
  >- ((* handle *) say "handle" >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
      map_every rename1 [`known _ (_ :: _) g1 = (_, g)`,
                           `known _ _ g0 = (_, g1)`] >>
      patresolve `known _ (_ :: _) _ = _` (el 2) subspt_known_elist_globals >>
      simp[] >> disch_then (resolve_selected hd) >> simp[] >>
      fs[BAG_ALL_DISTINCT_BAG_UNION] >> strip_tac >>
      fs[evaluate_def, pair_case_eq, result_case_eq,
         error_case_eq] >> rveq >> fs[] >>
      imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rveq
      >- (sel_ihpc last >> simp[] >> disch_then (resolve_selected last) >>
          simp[] >> reverse impl_keep_tac
          >- metis_tac[val_approx_val_merge_I] >>
          metis_tac[subspt_trans])
      >- (first_x_assum (Q.PAT_ASSUM `closSem$evaluate _ = (Rerr _, _)` o
                         mp_then (Pos last) mp_tac) >>
          simp[] >> disch_then (resolve_selected last) >> simp[] >>
          impl_keep_tac >- metis_tac[subspt_trans] >>
          strip_tac >> sel_ihpc last >> simp[PULL_EXISTS] >>
          disch_then (resolve_selected (el 2)) >> simp[] >> reverse impl_tac
          >- metis_tac[val_approx_val_merge_I] >>
          conj_tac >- metis_tac[ssgc_free_preserved_SING] >>
          resolve_selected hd ssgc_evaluate >>
          disch_then (resolve_selected last) >> simp[] >> reverse impl_tac
          >- simp[] >>
          imp_res_tac known_preserves_esgc_free >> fs[])
      >- (sel_ihpc last >> simp[] >> metis_tac[subspt_trans]))
  >- ((* call *) say "call" >> pairarg_tac >> fs[] >> rveq >> fs[] >>
      fs[evaluate_def, pair_case_eq, result_case_eq, case_eq_thms,
         bool_case_eq] >>
      rveq >> fs[] >> sel_ihpc last >> simp[] >> fixeqs >>
      disch_then (resolve_selected last) >> simp[] >>
      reverse (rpt strip_tac)
      >- (rveq >> imp_res_tac evaluate_SING >> simp[]) >>
      map_every rename1 [
        `evaluate([body],args,dec_clock (ticks+1) s1) = (result,s)`,
        `evaluate(MAP FST alist,env,s0) = (Rval vs, s1)`] >>
      `ssgc_free s1 ∧ EVERY vsgc_free vs`
         by (resolve_selected hd ssgc_evaluate >> simp[] >>
             disch_then (resolve_selected last) >> simp[] >>
             reverse impl_tac >- simp[] >>
             imp_res_tac known_preserves_esgc_free >> simp[ALL_EL_MAP]) >>
      `set_globals body = {||}`
         by (Q.UNDISCH_THEN `ssgc_free s1` mp_tac >>
             simp[ssgc_free_def] >> fs[find_code_def, case_eq_thms, pair_case_eq] >>
             metis_tac[])  >>
      `mapped_globals s1 ⊆ mapped_globals s`
         by metis_tac[mapped_globals_grow, mapped_globals_dec_clock] >>
      `mglobals_extend s1 {} s`
         by (qspecl_then [`[body]`, `args`, `dec_clock (ticks+1) s1`, `result`, `s`]
                         mp_tac ssgc_evaluate >> simp[] >>
             fs[find_code_def, case_eq_thms, pair_case_eq] >> rveq >>
             simp[set_globals_empty_esgc_free]) >>
      metis_tac[mglobals_extend_EMPTY_state_globals_approx])
  >- ((* op *) say "op" >> rpt (pairarg_tac >> fs[]) >> rveq >>
      fs[BAG_ALL_DISTINCT_BAG_UNION] >>
      resolve_selected hd subspt_known_op_elist_globals >> simp[] >>
      disch_then (resolve_selected hd) >> simp[] >> strip_tac >>
      rename[`known_op opn`] >> Cases_on `isGlobal opn` >> fs[] >| [
        rename[`gO_destApx apx`] >> Cases_on `gO_destApx apx` >| [
          fs[evaluate_def, do_app_def] >> rveq >> simp[] >> Cases_on `apx` >>
          fs[gO_destApx_def, bool_case_eq, NULL_EQ],
          fs[evaluate_def, do_app_def] >> rveq >> simp[] >> Cases_on `apx` >>
          fs[gO_destApx_def, bool_case_eq, NULL_EQ],
          ALL_TAC
        ],
        ALL_TAC
      ] >>
      fs[evaluate_def, pair_case_eq, result_case_eq] >> rveq >>
      fs[] >> sel_ihpc last >> simp[] >> disch_then (resolve_selected last) >>
      simp[] >> (impl_keep_tac >- metis_tac[subspt_trans]) >>
      simp[] >> strip_tac >>
      metis_tac[known_op_correct_approx, LIST_REL_REVERSE_EQ])
  >- (say "app" >> rpt (pairarg_tac >> fs[]) >> rveq >>
      imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rveq >>
      patresolve `known [_] _ _ = _` (el 2) subspt_known_elist_globals >>
      simp[] >> fs[BAG_ALL_DISTINCT_BAG_UNION] >>
      disch_then (resolve_selected hd) >> simp[] >> impl_tac
      >- fs[BAG_DISJOINT, DISJOINT_SYM] >> strip_tac >>
      fs[evaluate_def, bool_case_eq, pair_case_eq,
         result_case_eq] >> rveq >> fs[]
      >- (rename1 `evaluate(MAP FST args, env, s0) = (Rval argvs, s1)` >>
          rename1 `known exps apxs g0 = (args, g1)` >>
          rename1 `state_globals_approx s0 g'` >>
          `subspt g1 g'` by metis_tac[subspt_trans] >>
          nailIHx strip_assume_tac >> fs[] >>
          sel_ihpc last >> simp[] >> disch_then (resolve_selected (el 2)) >>
          simp[] >> resolve_selected hd ssgc_evaluate >> simp[] >>
          disch_then (resolve_selected last) >> simp[] >>
          impl_keep_tac
          >- (imp_res_tac known_preserves_esgc_free >> fs[ALL_EL_MAP]) >>
          simp[] >> rpt (disch_then strip_assume_tac) >> rveq >> fs[] >>
          rename1 `evaluate_app _ fval argvs s2 = (result, s)` >>
          reverse conj_tac
          >- (Cases_on `result` >> simp[] >>
              imp_res_tac evaluate_app_length_imp >>
              rename1 `LENGTH aa = 1` >> Cases_on `aa` >> fs[LENGTH_NIL]) >>
          rename1 `evaluate([fexp],env,s1) = (Rval[fval],s2)` >>
          qspecl_then [`[fexp]`, `env`, `s1`, `Rval [fval]`, `s2`]
                      mp_tac ssgc_evaluate >> simp[] >>
          impl_tac
          >- (IMP_RES_THEN mp_tac known_preserves_esgc_free >> simp[]) >>
          strip_tac >>
          qpat_x_assum `evaluate_app _ _ _ _ = _`
             (fn th =>
                 (mp_tac o PART_MATCH (last o strip_conj o #1 o dest_imp)
                                      (CONJUNCT2 ssgc_evaluate0) o concl) th >>
                 assume_tac th) >> simp[] >>
          strip_tac >>
          `mapped_globals s2 ⊆ mapped_globals s` suffices_by
            metis_tac[mglobals_extend_EMPTY_state_globals_approx] >>
          metis_tac[lem])
      >- (rename1 `evaluate(MAP FST args, env, s0) = (Rval argvs, s1)` >>
          rename1 `known exps apxs g0 = (args, g1)` >>
          rename1 `state_globals_approx s0 g'` >>
          `subspt g1 g'` by metis_tac[subspt_trans] >>
          nailIHx strip_assume_tac >> fs[] >> sel_ihpc last >> simp[] >>
          disch_then irule >>
          qspecl_then [`MAP FST args`, `env`, `s0`, `Rval argvs`, `s1`]
                      mp_tac ssgc_evaluate >> simp[] >>
          impl_tac
          >- (simp[ALL_EL_MAP] >> metis_tac[known_preserves_esgc_free]) >>
          simp[])
      >- (sel_ihpc last >> simp[] >> metis_tac[subspt_trans]))
  >- (say "fn" >> rpt (pairarg_tac >> fs[]) >> rveq >>
      imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rveq >>
      fs[evaluate_def, bool_case_eq, case_eq_thms] >> rveq >> fs[] >> every_case_tac >>
      simp[])
  >- (say "letrec" >> rpt (pairarg_tac >> fs[]) >> imp_res_tac known_sing_EQ_E>>
      rveq >> fs[] >> rveq >>
      fs[evaluate_def, bool_case_eq,clos_gen_eq]
      >- (fixeqs >>
          qmatch_assum_abbrev_tac
            `closSem$evaluate([_], GENLIST (_ (MAP ff _)) _ ++ _, _) = _` >>
          rename1
            `closSem$evaluate([body'],
                              GENLIST (Recclosure lopt [] env (MAP ff fns))
                                      (LENGTH fns) ++ env,
                              s0) = (result, s)` >>
          first_x_assum (qspecl_then [
            `GENLIST (Recclosure lopt [] env (MAP ff fns)) (LENGTH fns) ++ env`,
            `s0`] mp_tac) >> simp[] >>
          imp_res_tac LIST_REL_LENGTH >>
          simp[LIST_REL_EL_EQN, EL_GENLIST, EL_APPEND_EQN, EVERY_MEM,
               MEM_GENLIST, PULL_EXISTS] >>
          disch_then match_mp_tac
          >- (rpt conj_tac >> simp[]
              >- (Cases_on`lopt`>>fs[LENGTH_REPLICATE,LENGTH_clos_gen])
              >- (qx_gen_tac `i` >> reverse (Cases_on `i < LENGTH fns`) >>
                  Cases_on`lopt`>> simp[LENGTH_REPLICATE,LENGTH_clos_gen]>>
                  fs[LIST_REL_EL_EQN] >>
                  simp[Abbr`ff`,EL_REPLICATE,EL_MAP] >>
                  pairarg_tac >> simp[])
              >- (fs[elglobals_EQ_EMPTY, MEM_MAP, PULL_EXISTS, FORALL_PROD] >>
                  simp[Abbr`ff`] >> rpt strip_tac >>
                  qmatch_abbrev_tac `
                    set_globals (FST (HD (FST (known [_] ENV g0)))) = {||}` >>
                  rename1 `MEM (nargs, fbody) fns` >>
                  `set_globals fbody = {||}` by metis_tac[] >>
                  Cases_on `known [fbody] ENV g0` >> simp[] >>
                  imp_res_tac known_sing_EQ_E >> fs[] >> rveq >>
                  first_x_assum (mp_tac o MATCH_MP known_preserves_setGlobals)>>
                  simp[])))))

val kca_sing_sga =
    known_correct_approx
      |> Q.SPECL [`[e]`, `as`, `g0`, `[(e',a)]`, `g`]
      |> SIMP_RULE (srw_ss()) [PULL_FORALL]
      |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT1 |> DISCH_ALL

val ssgc_free_preserved_SING' = Q.store_thm(
  "ssgc_free_preserved_SING'",
  `esgc_free e1 ∧ ssgc_free s0 ∧
   EVERY vsgc_free env ∧ evaluate([e1],env,s0) = (res,s) ⇒ ssgc_free s`,
  rpt strip_tac >>
  `EVERY esgc_free [e1]` by simp[] >>
  metis_tac[ssgc_evaluate]);

val say = say0 "known_correct";

val exp_rel_def = Define`
  exp_rel as g' e1 e2 ⇔
    ∃g0 g apx. subspt g g' ∧ known [e1] as g0 = ([(e2,apx)], g)
`;
val _ = temp_overload_on ("kerel", ``clos_knownProof$exp_rel``)

val val_rel_def = tDefine "val_rel" `
  (val_rel g (Number i) v ⇔ v = Number i) ∧
  (val_rel g (Word64 w) v ⇔ v = Word64 w) ∧
  (val_rel g (Block n vs) v ⇔
     ∃vs'. v = Block n vs' ∧ LIST_REL (val_rel g) vs vs') ∧
  (val_rel g (ByteVector ws) v ⇔ v = ByteVector ws) ∧
  (val_rel g (RefPtr n) v ⇔ v = RefPtr n) ∧
  (val_rel g (Closure lopt vs1 env1 n bod1) v ⇔
     every_Fn_vs_NONE [bod1] ∧
     ∃vs2 env2 bod2 eapx.
       LIST_REL (val_rel g) vs1 vs2 ∧ LIST_REL (val_rel g) env1 env2 ∧
       LIST_REL val_approx_val eapx env2 ∧
       kerel (REPLICATE n Other ++ eapx) g bod1 bod2 ∧
       v = Closure lopt vs2 env2 n bod2) ∧
  (val_rel g (Recclosure lopt vs1 env1 fns1 i) v ⇔
     EVERY (λ(n,e). every_Fn_vs_NONE [e]) fns1 ∧
     let gfn = case lopt of
                 | NONE => K Other
                 | SOME n => (λi. Clos (n + 2*i) (FST (EL i fns1))) in
     let clos = GENLIST gfn (LENGTH fns1)
     in
       ∃vs2 env2 fns2 eapx.
         LIST_REL (val_rel g) vs1 vs2 ∧ LIST_REL (val_rel g) env1 env2 ∧
         LIST_REL val_approx_val eapx env2 ∧
         LIST_REL (λ(n1,e1) (n2,e2).
                     n1 = n2 ∧
                     kerel (REPLICATE n1 Other ++ clos ++ eapx) g e1 e2)
                  fns1 fns2 ∧
         v = Recclosure lopt vs2 env2 fns2 i)
` (WF_REL_TAC `measure (v_size o FST o SND)` >> simp[v_size_def] >>
   rpt strip_tac >> imp_res_tac v_size_lemma >> simp[])
val val_rel_ind = theorem "val_rel_ind"
val val_rel_def = save_thm(
  "val_rel_def[simp]",
  SIMP_RULE (bool_ss ++ ETA_ss) [] val_rel_def)

val _ = temp_overload_on ("kvrel", ``clos_knownProof$val_rel``)

(* necessary kvrel *)
val kvrel_vsgc_free = Q.store_thm(
  "kvrel_vsgc_free",
  `∀g v1 v2. kvrel g v1 v2 ⇒ (vsgc_free v1 ⇔ vsgc_free v2)`,
  ho_match_mp_tac val_rel_ind >> simp[] >> rpt strip_tac
  >- (fs[EVERY_MEM, LIST_REL_EL_EQN] >> metis_tac[MEM_EL])
  >- (fs[EVERY_MEM, LIST_REL_EL_EQN] >>
      fs[exp_rel_def] >> imp_res_tac known_preserves_setGlobals >>
      fs[] >> metis_tac[MEM_EL])
  >- (fs[EVERY_MEM, LIST_REL_EL_EQN, elglobals_EQ_EMPTY, MEM_MAP, PULL_EXISTS,
         FORALL_PROD]>>
      EQ_TAC >> rpt strip_tac
      >- (imp_res_tac (MEM_EL |> SPEC_ALL |> EQ_IMP_RULE |> #1 |> GSYM) >>
          rename1 `m < LENGTH fns2` >>
          Cases_on `EL m fns1` >> fs[] >>
          first_x_assum (qspec_then `m` mp_tac) >> simp[] >>
          rw[exp_rel_def] >>
          imp_res_tac known_preserves_setGlobals >> fs[] >>
          metis_tac[MEM_EL])
      >- metis_tac[MEM_EL]
      >- metis_tac[MEM_EL]
      >- (imp_res_tac (MEM_EL |> SPEC_ALL |> EQ_IMP_RULE |> #1 |> GSYM) >>
          rename1 `m < LENGTH fns1` >>
          Cases_on `EL m fns2` >> fs[] >>
          first_x_assum (qspec_then `m` mp_tac) >> simp[] >>
          rw[exp_rel_def] >>
          imp_res_tac known_preserves_setGlobals >> fs[] >>
          metis_tac[MEM_EL])
      >- metis_tac[MEM_EL]
      >- metis_tac[MEM_EL]))

val kvrel_Boolv = Q.store_thm(
  "kvrel_Boolv[simp]",
  `(kvrel g (Boolv b) v ⇔ v = Boolv b) ∧
   (kvrel g v (Boolv b) ⇔ v = Boolv b)`,
  simp[closSemTheory.Boolv_def] >> Cases_on `v` >> simp[] >> metis_tac[]);

val kvrel_Unit = Q.store_thm(
  "kvrel_Unit[simp]",
  `(kvrel g Unit v ⇔ v = Unit) ∧ (kvrel g v Unit ⇔ v = Unit)`,
  simp[Unit_def] >> Cases_on `v` >> simp[] >> metis_tac[])

val kvrel_EVERY_vsgc_free = Q.store_thm(
  "kvrel_EVERY_vsgc_free",
  `∀vs1 vs2.
     LIST_REL (kvrel g) vs1 vs2 ⇒
     (EVERY vsgc_free vs1 ⇔ EVERY vsgc_free vs2)`,
  Induct_on `LIST_REL` >> simp[] >> metis_tac[kvrel_vsgc_free]);

(* necessary kvrel *)
val kvrel_val_approx = Q.store_thm(
  "kvrel_val_approx",
  `∀g v1 v2.
     kvrel g v1 v2 ⇒ ∀a. val_approx_val a v1 ⇔ val_approx_val a v2`,
  ho_match_mp_tac val_rel_ind >> rw[]
  >- (Cases_on `a` >> simp[] >> fs[LIST_REL_EL_EQN] >> metis_tac[MEM_EL])
  >- (Cases_on `a` >> simp[] >> fs[LIST_REL_EL_EQN] >> metis_tac[LENGTH_NIL])
  >- (Cases_on `a` >> fs[LIST_REL_EL_EQN] >> rename1 `lopt = SOME _` >>
      Cases_on `lopt` >> simp[] >> rename1 `EL j` >>
      rename1 `j < LENGTH fns2` >> Cases_on `j < LENGTH fns2` >> simp[] >>
      rename1 `vvs = []` >> reverse (Cases_on `vvs`)
      >- (simp[] >> rename1 `vvs' = []` >> Cases_on `vvs'` >> fs[]) >>
      fs[LENGTH_NIL, LENGTH_NIL_SYM] >> rfs[] >> res_tac >>
      fs[UNCURRY]))

val kvrel_LIST_REL_val_approx = Q.store_thm(
  "kvrel_LIST_REL_val_approx",
  `∀vs1 vs2.
      LIST_REL (kvrel g) vs1 vs2 ⇒
      ∀as. LIST_REL val_approx_val as vs1 ⇔ LIST_REL val_approx_val as vs2`,
  Induct_on `LIST_REL` >> simp[] >> metis_tac[kvrel_val_approx]);

val state_rel_def = Define`
  state_rel g (s1:'a closSem$state) (s2:'a closSem$state) ⇔
     s2.clock = s1.clock ∧ s2.ffi = s1.ffi ∧ s2.max_app = s1.max_app ∧
     LIST_REL (OPTREL (kvrel g)) s1.globals s2.globals ∧
     fmap_rel (ref_rel (kvrel g)) s1.refs s2.refs ∧
     s1.code = FEMPTY ∧ s2.code = FEMPTY
`;
val _ = temp_overload_on ("ksrel", ``clos_knownProof$state_rel``)
val ksrel_def = state_rel_def

val state_rel_max_app = Q.store_thm("state_rel_max_app",
  `state_rel g s1 s2 ⇒ s1.max_app = s2.max_app`,
  rw[state_rel_def]);

val ksrel_flookup_refs = Q.store_thm("ksrel_flookup_refs",
  `ksrel g s1 s2 ∧ FLOOKUP s1.refs k = SOME v ⇒
   ∃v'. FLOOKUP s2.refs k = SOME v' ∧ ref_rel (kvrel g) v v'`,
  rw[ksrel_def,fmap_rel_OPTREL_FLOOKUP,OPTREL_def]
  \\  first_x_assum(qspec_then`k`mp_tac) \\ rw[]);

(* ksrel necessary *)
val ksrel_sga = Q.store_thm(
  "ksrel_sga",
  `ksrel g0 s1 s2 ⇒ (state_globals_approx s1 g ⇔ state_globals_approx s2 g)`,
  simp[ksrel_def, state_globals_approx_def, get_global_def, LIST_REL_EL_EQN] >>
  csimp[] >> rpt strip_tac >> eq_tac >> rpt strip_tac >>
  rename1 `EL kk (ss:α closSem$state).globals = SOME vv` >>
  rename1 `lookup kk gg` >>
  nailIHx mp_tac >>
  simp[optionTheory.OPTREL_def] >>
  metis_tac [kvrel_val_approx])

(* ksrel necessary *)
val ksrel_ssgc_free = Q.store_thm(
  "ksrel_ssgc_free",
  `ksrel g s1 s2 ⇒ (ssgc_free s1 ⇔ ssgc_free s2)`,
  simp[ksrel_def, ssgc_free_def] >> rpt strip_tac >> eq_tac >> rpt strip_tac >>
  fs[fmap_rel_OPTREL_FLOOKUP]
  >- (rename1 `FLOOKUP s2.refs kk = SOME (ValueArray vvl)` >>
      `OPTREL (ref_rel (kvrel g)) (FLOOKUP s1.refs kk) (FLOOKUP s2.refs kk)`
         by simp[] >> pop_assum mp_tac >>
      simp_tac(srw_ss()) [OPTREL_def] >> simp[PULL_EXISTS] >> Cases >>
      simp[] >> metis_tac[kvrel_EVERY_vsgc_free])
  >- (fs[LIST_REL_EL_EQN] >>
      imp_res_tac (MEM_EL |> SPEC_ALL |> EQ_IMP_RULE |> #1 |> GSYM) >>
      rename1 `EL kk s2.globals` >>
      `OPTREL (kvrel g) (EL kk s1.globals) (EL kk s2.globals)` by simp[] >>
      pop_assum mp_tac >> simp_tac(srw_ss()) [OPTREL_def] >> simp[] >>
      metis_tac[kvrel_vsgc_free, MEM_EL])
  >- (rename1 `FLOOKUP s1.refs kk = SOME (ValueArray vvl)` >>
      `OPTREL (ref_rel (kvrel g)) (FLOOKUP s1.refs kk) (FLOOKUP s2.refs kk)`
         by simp[] >> pop_assum mp_tac >>
      simp_tac(srw_ss()) [OPTREL_def] >> simp[PULL_EXISTS] >>
      metis_tac[kvrel_EVERY_vsgc_free])
  >- (fs[LIST_REL_EL_EQN] >>
      imp_res_tac (MEM_EL |> SPEC_ALL |> EQ_IMP_RULE |> #1 |> GSYM) >>
      rename1 `EL kk s1.globals` >>
      `OPTREL (kvrel g) (EL kk s1.globals) (EL kk s2.globals)` by simp[] >>
      pop_assum mp_tac >> simp_tac(srw_ss()) [OPTREL_def] >> simp[] >>
      metis_tac[kvrel_vsgc_free, MEM_EL]))

val res_rel_def = Define`
  (res_rel g (Rval vs1, s1) r ⇔
      ∃s2 vs2. r = (Rval vs2,s2) ∧ LIST_REL (kvrel g) vs1 vs2 ∧ ksrel g s1 s2) ∧
  (res_rel g (Rerr (Rabort Rtype_error), _) _ ⇔ T) ∧
  (res_rel g (Rerr (Rabort Rtimeout_error), s1) (Rerr e, s2) ⇔
     e = Rabort Rtimeout_error ∧ ksrel g s1 s2) ∧
  (res_rel g (Rerr (Rraise v1), s1) (Rerr (Rraise v2), s2) ⇔
     kvrel g v1 v2 ∧ ksrel g s1 s2) ∧
  (res_rel _ _ _ ⇔ F)
`;
val _ = export_rewrites ["res_rel_def"]
val _ = temp_overload_on ("krrel", ``clos_knownProof$res_rel``)
val krrel_def = res_rel_def

val krrel_errval = Q.store_thm(
  "krrel_errval[simp]",
  `(krrel g (Rerr e, s1) (Rval vs, s2) ⇔ e = Rabort Rtype_error)`,
  Cases_on `e` >> simp[] >> rename1 `Rabort a` >> Cases_on `a` >> simp[]);

val krrel_err_rw = Q.store_thm(
  "krrel_err_rw",
  `krrel g (Rerr e, s1) r ⇔
      e = Rabort Rtype_error ∨
      (∃s2. e = Rabort Rtimeout_error ∧ r = (Rerr (Rabort Rtimeout_error), s2) ∧
            ksrel g s1 s2) ∨
      (∃v1 v2 s2.
            e = Rraise v1 ∧ r = (Rerr (Rraise v2),s2) ∧ kvrel g v1 v2 ∧
            ksrel g s1 s2)`,
  Cases_on `e` >> simp[] >> Cases_on `r` >> simp[]
  >- (rename1 `krrel _ _ (r2, s2)` >> Cases_on `r2` >> simp[] >>
      rename1 `krrel _ _ (Rerr e,_)` >> Cases_on `e` >> simp[])
  >- (rename1 `Rabort abt` >> Cases_on `abt` >> simp[] >>
      rename1 `krrel _ _ (r2,s2)` >> Cases_on `r2` >> simp[]));

val krrel_ffi = Q.store_thm(
  "krrel_ffi",
  `krrel gmap (r1,s1) (r2,s2) ∧ r1 ≠ Rerr (Rabort Rtype_error) ⇒
   s2.ffi = s1.ffi`,
  Cases_on `r1` >> Cases_on`r2` >>
  simp[krrel_def, ksrel_def, krrel_err_rw, ksrel_def] >> rw[])

val krrel_arg2_typeerror = Q.store_thm(
  "krrel_arg2_typeerror[simp]",
  `krrel g (res1, s1) (Rerr (Rabort Rtype_error), s2) ⇔
    res1 = Rerr (Rabort Rtype_error)`,
  Cases_on `res1` >> simp[krrel_def, krrel_err_rw]);

(* necesssary kvrel *)
val kvrel_v_to_list = Q.store_thm(
  "kvrel_v_to_list",
  `∀g v1 v2 l1.
     kvrel g v1 v2 ∧ v_to_list v1 = SOME l1 ⇒
     ∃l2. v_to_list v2 = SOME l2 ∧ LIST_REL (kvrel g) l1 l2`,
  ho_match_mp_tac val_rel_ind >> simp[v_to_list_def, PULL_EXISTS] >>
  rpt strip_tac >> rename1 `v_to_list (closSem$Block _ vs2)` >>
  Cases_on `vs2` >> fs[v_to_list_def] >> rw[] >> fs[v_to_list_def] >>
  rename1 `v_to_list (closSem$Block _ (_ :: vs2'))` >>
  Cases_on `vs2'` >> fs[v_to_list_def] >> rw[] >> fs[v_to_list_def] >>
  rename1 `v_to_list (closSem$Block _ (_ :: _ :: vs2''))` >>
  Cases_on `vs2''` >> fs[v_to_list_def] >> rw[] >> fs[v_to_list_def] >>
  fs[case_eq_thms] >> rveq >> simp[PULL_EXISTS] >> metis_tac[MEM]);

val kvrel_do_eq0 = Q.prove(
  `(∀u1 v1 u2 v2 b g.
      kvrel g u1 u2 ∧ kvrel g v1 v2 ∧ do_eq u1 v1 = Eq_val b ⇒
      do_eq u2 v2 = Eq_val b) ∧
   (∀us1 vs1 us2 vs2 b g.
      LIST_REL (kvrel g) us1 us2 ∧ LIST_REL (kvrel g) vs1 vs2 ∧
      do_eq_list us1 vs1 = Eq_val b ⇒
      do_eq_list us2 vs2 = Eq_val b)`,
  ho_match_mp_tac do_eq_ind >> rpt conj_tac
  >- (Cases >> Cases >> strip_tac >>
      simp[SimpL ``$==>``, do_eq_def, v_case_eq, bool_case_eq, PULL_EXISTS] >>
      fs[] >> simp[do_eq_def] >> rw[] >> fs[LIST_REL_EL_EQN] >> metis_tac[])
  >- simp[]
  >- (simp[PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
      ONCE_REWRITE_TAC [do_eq_def] >>
      Cases_on `do_eq u1 v1` >> fs[] >> simp[bool_case_eq] >> dsimp[] >>
      rename1 `do_eq u1 v1 = Eq_val b` >> Cases_on `b` >> simp[] >>
      rpt strip_tac >> nailIHx strip_assume_tac >> simp[] >> metis_tac[])
  >- (simp[PULL_EXISTS] >> ONCE_REWRITE_TAC[do_eq_def] >> simp[])
  >- (simp[PULL_EXISTS] >> ONCE_REWRITE_TAC[do_eq_def] >> simp[]));

val kvrel_do_eq = save_thm("kvrel_do_eq", kvrel_do_eq0 |> CONJUNCT1);

(* necessary(!) *)
val kvrel_op_correct_Rval = Q.store_thm(
  "kvrel_op_correct_Rval",
  `LIST_REL (kvrel g) vs1 vs2 ∧ do_app opn vs1 s01 = Rval(v1,s1) ∧
   ksrel g s01 s02 ⇒
   ∃v2 s2. do_app opn vs2 s02 = Rval(v2,s2) ∧ ksrel g s1 s2 ∧
           kvrel g v1 v2`,
  Cases_on `opn` >> simp[do_app_def, case_eq_thms, bool_case_eq, PULL_EXISTS] >>
  TRY (rw[] >> fs[LIST_REL_EL_EQN] >> NO_TAC) \\
  TRY (rw[] >> fs[] >>
       imp_res_tac ksrel_flookup_refs \\ fs[ksrel_def] >>
       imp_res_tac fmap_rel_def \\ fs[] \\
       rveq \\ fs[LIST_REL_EL_EQN] \\
       TRY (CASE_TAC \\ fs[] \\ rveq \\ fs[]) \\
       TRY (match_mp_tac fmap_rel_FUPDATE_same) \\ fs[]
       \\ fs[LIST_REL_EL_EQN,OPTREL_def,LIST_REL_REPLICATE_same,EVERY2_LUPDATE_same]
       \\ first_x_assum match_mp_tac \\ rw[] \\ fs[] \\ intLib.COOPER_TAC)
  >- (csimp[get_global_def] >> simp[ksrel_def] >>
      simp[LIST_REL_EL_EQN, OPTREL_def] >> rpt strip_tac >> rveq >>
      res_tac >> fs[] >> rveq >> simp[])
  >- (csimp[get_global_def, PULL_EXISTS] >> simp[ksrel_def] >> rw[] >>
      fs[LIST_REL_EL_EQN] >> rfs[] >> res_tac >> fs[OPTREL_def] >> fs[] >>
      simp[EL_LUPDATE, bool_case_eq] >> metis_tac[])
  >- (
    rw [] >>
    fs [] >>
    rw [] >>
    imp_res_tac LIST_REL_LENGTH
    >- intLib.ARITH_TAC
    >- intLib.ARITH_TAC >>
    irule EVERY2_APPEND_suff >>
    simp [] >>
    irule EVERY2_TAKE >>
    irule EVERY2_DROP >>
    simp [])
  >- (rw[] >> fs[] >>
      imp_res_tac kvrel_v_to_list >> fs[ksrel_def] \\ rfs[] >>
      qpat_x_assum`_ = SOME wss`mp_tac >>
      DEEP_INTRO_TAC some_intro \\ fs[] \\ strip_tac \\
      DEEP_INTRO_TAC some_intro \\ fs[PULL_EXISTS] \\
      map_every qexists_tac[`wss`] \\
      reverse conj_asm2_tac >- (
        fs[LIST_EQ_REWRITE,EL_MAP,LIST_REL_EL_EQN,fmap_rel_def,FLOOKUP_DEF] \\
        rfs[EL_MAP] \\ rw[] \\ res_tac \\ res_tac \\ fs[] \\
        Cases_on`s02.refs ' (EL x ps)` \\ fs[] >>
        metis_tac[ref_rel_def,ref_11]) \\
      ntac 2 strip_tac >>
      imp_res_tac INJ_MAP_EQ \\ fs[INJ_DEF] \\
      imp_res_tac INJ_MAP_EQ \\ fs[INJ_DEF] )
  >- (rw[] >> fs[] >> metis_tac[kvrel_v_to_list])
  >- (
    rw[] \\ fs[] \\
    rpt(qpat_x_assum`$some _ = _`mp_tac) \\
    rpt(DEEP_INTRO_TAC some_intro) \\ rw[] \\
    spose_not_then strip_assume_tac \\
    imp_res_tac kvrel_v_to_list \\
    rfs[LIST_EQ_REWRITE,LIST_REL_EL_EQN,EL_MAP] \\ fs[EL_MAP] \\
    rfs[LIST_EQ_REWRITE,LIST_REL_EL_EQN,EL_MAP] \\
    fs[EVERY_MEM,EXISTS_MEM] \\
    metis_tac[v_11,integerTheory.INT_INJ,EL_MAP,o_THM,ORD_BOUND] )
  >- (rw[] >> fs[] >> rw[] >> metis_tac[kvrel_do_eq]));

val do_app_EQ_Rerr = Q.store_thm(
  "do_app_EQ_Rerr",
  `closSem$do_app opn vs s0 = Rerr e ⇒ e = Rabort Rtype_error`,
  Cases_on `opn` >> simp[do_app_def, case_eq_thms, bool_case_eq, pair_case_eq] >> rw[]);

val kvrel_lookup_vars = Q.store_thm(
  "kvrel_lookup_vars",
  `∀env01 env02 vars env1.
     LIST_REL (kvrel g) env01 env02 ∧ lookup_vars vars env01 = SOME env1 ⇒
     ∃env2. lookup_vars vars env02 = SOME env2 ∧
            LIST_REL (kvrel g) env1 env2`,
  Induct_on `vars` >> simp[lookup_vars_def, case_eq_thms, PULL_EXISTS] >>
  fs[LIST_REL_EL_EQN] >> metis_tac[]);

val loptrel_def = Define`
  loptrel fv numargs lopt1 lopt2 ⇔
     lopt2 = lopt1 ∨
     lopt1 = NONE ∧
     case (fv,lopt2) of
       | (Closure (SOME loc1) ae _ n bod, SOME loc2) =>
            loc1 = loc2 ∧ n = numargs ∧ ae = []
       | (Recclosure (SOME loc1) ae _ fns i, SOME loc2) =>
         i < LENGTH fns ∧ loc2 = loc1 + 2 * i ∧ numargs = FST (EL i fns) ∧
         ae = []
       | _ => F
`;

val ksrel_find_code = Q.store_thm(
  "ksrel_find_code",
  `ksrel g s1 s2 ⇒ find_code l (vs1:closSem$v list) s1.code = NONE`,
  simp[ksrel_def, find_code_def, case_eq_thms, pair_case_eq]);

val kvrel_dest_closure_SOME_Partial = Q.store_thm(
  "kvrel_dest_closure_SOME_Partial",
  `dest_closure max_app lopt1 f1 vs1 = SOME (Partial_app v1) ∧ kvrel g f1 f2 ∧
   LIST_REL (kvrel g) vs1 vs2 ∧ loptrel f2 n lopt1 lopt2 ∧ LENGTH vs2 = n ⇒
   ∃v2. dest_closure max_app lopt2 f2 vs2 = SOME (Partial_app v2) ∧
        kvrel g v1 v2`,
  simp[dest_closure_def, case_eq_thms, v_case_eq] >> rpt strip_tac >> rveq >> fs[] >>
  rpt strip_tac >> fs[case_eq_thms, bool_case_eq] >> rveq >> fs[loptrel_def] >> rveq
  >- (simp[EVERY2_APPEND_suff] >> fs[LIST_REL_EL_EQN] >> metis_tac[])
  >- (Cases_on `lopt2` >> simp[EVERY2_APPEND_suff] >> fs[LIST_REL_EL_EQN] >>
      rename1 `option_CASE lll` >> Cases_on `lll` >> fs[LIST_REL_EL_EQN])
  >- (rpt (pairarg_tac >> fs[]) >> fs[bool_case_eq] >>
      simp[EVERY2_APPEND_suff] >>
      rename1 `LIST_REL val_approx_val envapx env2` >> simp[PULL_EXISTS] >>
      qexists_tac `envapx` >>
      fs[LIST_REL_EL_EQN] >> rename1 `EL ii` >>
      qpat_x_assum `∀n. _ ⇒ UNCURRY f x y` mp_tac >>
      disch_then (qspec_then `ii` mp_tac) >> simp[] >> rw[] >> simp[])
  >- (rpt (pairarg_tac >> fs[]) >> fs[bool_case_eq] >>
      Cases_on `lopt2` >> fs[] >> rename1 `option_CASE lll` >>
      Cases_on `lll` >> fs[] >> rveq >>
      qpat_x_assum `LIST_REL (UNCURRY _) _ _` mp_tac >>
      CONV_TAC (LAND_CONV (REWRITE_CONV [LIST_REL_EL_EQN])) >>
      rename1 `EL ii` >>
      disch_then (CONJUNCTS_THEN2 assume_tac (qspec_then `ii` mp_tac)) >>
      strip_tac >> rfs[] >> fs[LIST_REL_EL_EQN]))

val kvrel_dest_closure_SOME_Full = Q.store_thm(
  "kvrel_dest_closure_SOME_Full",
  `dest_closure max_app lopt1 f1 vs1 = SOME (Full_app e1 env1 args1) ∧
   kvrel g f1 f2 ∧
   LIST_REL (kvrel g) vs1 vs2 ∧ loptrel f2 n lopt1 lopt2 ∧ LENGTH vs2 = n ⇒
   ∃eapx e2 env2 args2.
      dest_closure max_app lopt2 f2 vs2 = SOME (Full_app e2 env2 args2) ∧
      LIST_REL val_approx_val eapx env2 ∧
      LIST_REL (kvrel g) env1 env2 ∧ LIST_REL (kvrel g) args1 args2 ∧
      kerel eapx g e1 e2`,
  simp[dest_closure_def, case_eq_thms, bool_case_eq] >>
  csimp[revtakerev, revdroprev] >> dsimp[] >> rpt strip_tac >> rveq >>
  fs[] >> rveq >> fs[]
  >- (imp_res_tac LIST_REL_LENGTH >> simp[] >> fs[] >>
      simp[EVERY2_APPEND_suff, EVERY2_DROP, EVERY2_TAKE] >>
      fs[loptrel_def] >>
      qexists_tac `REPLICATE num_args Other ++ eapx` >> simp[] >>
      rpt conj_tac >>
      TRY (irule EVERY2_APPEND_suff >> simp[] >>
           simp[LIST_REL_EL_EQN, LENGTH_REPLICATE, EL_REPLICATE]) >>
      Cases_on `lopt2` >> fs[] >>
      rename1 `option_CASE lll` >> Cases_on `lll` >> fs[] >> rveq >>
      fs[check_loc_def])
  >- (rpt (pairarg_tac >> fs[]) >> imp_res_tac LIST_REL_LENGTH >> fs[] >>
      fs[bool_case_eq] >> rveq >>
      qpat_x_assum `LIST_REL (UNCURRY _) _ _`
        (fn th => (mp_tac o SIMP_RULE (srw_ss()) [LIST_REL_EL_EQN]) th >>
                  assume_tac th) >>
      rename1 `EL ii` >> simp[] >>
      disch_then (qspec_then `ii` mp_tac) >> simp[] >> strip_tac >> rveq >>
      simp[EVERY2_TAKE] >> rename1 `REPLICATE nargs Other` >>
      rename1 `GENLIST (option_CASE locc _ _)` >>
      rename1 `LIST_REL (UNCURRY _) fns1 fns2` >>
      rename1 `LIST_REL val_approx_val envapx _` >>
      qexists_tac `REPLICATE nargs Other ++
                   GENLIST (case locc of
                              | NONE => K Other
                              | SOME n => (λi. Clos (2*i + n) (FST (EL i fns1))))
                           (LENGTH fns2) ++ envapx` >> simp[] >>
      conj_tac
      >- (fs[loptrel_def] >> Cases_on `lopt2` >> fs[] >>
          rename1 `option_CASE lll` >> Cases_on `lll` >> fs[] >>
          fs[check_loc_def]) >>
      conj_tac >> rpt (irule EVERY2_APPEND_suff) >> simp[EVERY2_DROP]
      >- simp[LIST_REL_EL_EQN, EL_REPLICATE, LENGTH_REPLICATE]
      >- (simp[LIST_REL_GENLIST] >> Cases_on `locc` >> simp[] >>
          fs[LIST_REL_EL_EQN, UNCURRY])
      >- (simp[LIST_REL_GENLIST] >> rpt strip_tac >>
          qexists_tac `envapx` >> simp[])))

val kvrel_subspt = Q.store_thm(
  "kvrel_subspt",
  `∀g v1 v2 g'. kvrel g v1 v2 ∧ subspt g g' ⇒ kvrel g' v1 v2`,
  ho_match_mp_tac val_rel_ind >> simp[PULL_EXISTS] >> rpt strip_tac
  >- (irule EVERY2_MEM_MONO >> imp_res_tac LIST_REL_LENGTH >>
      simp[FORALL_PROD, MEM_ZIP, PULL_EXISTS] >> qexists_tac `kvrel g` >>
      simp[] >> metis_tac[MEM_EL])
  >- (rename1 `LIST_REL val_approx_val envapx _` >> qexists_tac `envapx` >>
      simp[] >> rpt conj_tac >>
      TRY (irule EVERY2_MEM_MONO >> imp_res_tac LIST_REL_LENGTH >>
           simp[FORALL_PROD, MEM_ZIP, PULL_EXISTS] >>
           qexists_tac `kvrel g` >> simp[] >> metis_tac[MEM_EL]) >>
      fs[exp_rel_def] >> metis_tac[subspt_trans])
  >- (rename1 `LIST_REL val_approx_val envapx _` >> qexists_tac `envapx` >>
      simp[] >> rpt conj_tac >>
      TRY (irule EVERY2_MEM_MONO >> imp_res_tac LIST_REL_LENGTH >>
           simp[FORALL_PROD, MEM_ZIP, PULL_EXISTS] >>
           qexists_tac `kvrel g` >> simp[] >> metis_tac[MEM_EL]) >>
      qpat_x_assum `LIST_REL (UNCURRY _) _ _` mp_tac >> simp[LIST_REL_EL_EQN] >>
      rpt strip_tac >> fs[] >> rfs[] >> rpt (pairarg_tac >> fs[]) >>
      rename1 `nn < LENGTH _` >> first_x_assum (qspec_then `nn` mp_tac) >>
      simp[] >> simp[exp_rel_def] >> metis_tac[subspt_trans]))

val kvrel_LIST_REL_subspt = Q.store_thm(
  "kvrel_LIST_REL_subspt",
  `∀vs1 vs2. LIST_REL (kvrel g) vs1 vs2 ⇒
             ∀g'. subspt g g' ⇒ LIST_REL (kvrel g') vs1 vs2`,
  Induct_on `LIST_REL` >> simp[] >> metis_tac[kvrel_subspt]);

val ksrel_subspt = Q.store_thm(
  "ksrel_subspt",
  `ksrel g s1 s2 ∧ subspt g g' ⇒ ksrel g' s1 s2`,
  simp[ksrel_def] >> rpt strip_tac
  >- (irule EVERY2_mono >>
      qexists_tac `OPTREL (kvrel g)` >> simp[] >> rpt strip_tac >>
      irule OPTREL_MONO >> qexists_tac `kvrel g` >>
      metis_tac[kvrel_subspt])
  >- (irule fmap_rel_mono >> qexists_tac `ref_rel (kvrel g)` >> simp[] >>
      Cases >> simp[PULL_EXISTS] >> metis_tac[kvrel_LIST_REL_subspt]));

val vsgc_free_Full_app_set_globals = Q.store_thm(
  "vsgc_free_Full_app_set_globals",
  `∀fval lopt args fe env args'.
     vsgc_free fval ∧ EVERY vsgc_free args ∧
     dest_closure max_app lopt fval args = SOME (Full_app fe env args')
   ⇒
     set_globals fe = {||} ∧ EVERY vsgc_free env ∧ EVERY vsgc_free args'`,
  simp[dest_closure_def, v_case_eq, bool_case_eq] >> rpt strip_tac >> fs[]
  >- (rveq >> simp[EVERY_REVERSE, EVERY_TAKE])
  >- (rveq >> simp[EVERY_REVERSE, EVERY_DROP])
  >- (pairarg_tac >> fs[bool_case_eq] >> rveq >>
      fs[elglobals_EQ_EMPTY, MEM_MAP, PULL_EXISTS, FORALL_PROD,
         NOT_LESS_EQUAL] >>
      metis_tac[MEM_EL])
  >- (pairarg_tac >> fs[bool_case_eq] >>
      simp[EVERY_REVERSE, EVERY_TAKE, EVERY_GENLIST])
  >- (pairarg_tac >> fs[bool_case_eq] >>
      simp[EVERY_REVERSE, EVERY_DROP, EVERY_GENLIST]))

val known_emptySetGlobals_unchanged_g = Q.store_thm(
  "known_emptySetGlobals_unchanged_g",
  `∀es as g0 alist g.
     known es as g0 = (alist, g) ∧ elist_globals es = {||} ⇒
     g = g0`,
  ho_match_mp_tac known_ind >> simp[known_def] >> rpt strip_tac >>
  rpt (pairarg_tac >> fs[]) >> imp_res_tac known_sing_EQ_E >> rveq >> fs[] >>
  rveq >> fs[] >>
  rename1 `known_op opn` >> Cases_on `opn` >>
  fs[known_op_def, case_eq_thms, op_gbag_def, va_case_eq, bool_case_eq]);

val krrel_better_subspt = Q.store_thm(
  "krrel_better_subspt",
  `krrel g (res1,s1) (res2,s2) ∧ subspt g g' ⇒ krrel g' (res1,s1) (res2,s2)`,
  Cases_on `res1` >> simp[krrel_err_rw] >>
  metis_tac[kvrel_LIST_REL_subspt, ksrel_subspt, kvrel_subspt]);

val dest_closure_SOME_Full_app_args_nil = Q.store_thm(
  "dest_closure_SOME_Full_app_args_nil",
  `dest_closure max_app (SOME loc) f args = SOME (Full_app exp1 env args1) ⇒
   args1 = []`,
  simp[dest_closure_def, case_eq_thms, bool_case_eq, revtakerev] >> strip_tac >> rveq
  >- (fs[check_loc_def] >> simp[DROP_LENGTH_NIL_rwt]) >>
  pairarg_tac >> fs[bool_case_eq] >> rveq >> fs[check_loc_def] >> rveq >>
  simp[DROP_LENGTH_NIL_rwt]);

val eqtI_thm = EQ_CLAUSES |> SPEC_ALL |> CONJUNCTS |> el 2 |> GSYM

val v_caseT = v_case_eq |> INST_TYPE [alpha |-> bool] |> Q.INST [`v` |-> `T`]
                        |> REWRITE_RULE []
val optcaset = ``option$option_CASE``
val opt_caseT = case_eq_thms |> CONJUNCTS
                    |> List.find (fn th => th |> concl |> lhs |> lhs
                                              |> strip_comb
                                              |> #1 |> same_const optcaset)
                    |> valOf
                    |> INST_TYPE [beta |-> bool]
                    |> Q.INST [`v'` |-> `T`]
                    |> SIMP_RULE (srw_ss()) []


val loptrel_arg1_SOME = save_thm(
  "loptrel_arg1_SOME",
  loptrel_def |> SPEC_ALL |> Q.INST [`lopt1` |-> `SOME loc1`]
              |> SIMP_RULE (srw_ss()) [opt_caseT, v_caseT])

val loptrel_arg1_NONE = save_thm(
  "loptrel_arg1_NONE",
  loptrel_def |> SPEC_ALL |> Q.INST [`lopt1` |-> `NONE`]
              |> SIMP_RULE (srw_ss()) [opt_caseT, v_caseT])

val kvrel_dest_closure_every_Fn_vs_NONE = Q.store_thm(
  "kvrel_dest_closure_every_Fn_vs_NONE",
  `kvrel g f1 f2 ∧ dest_closure max_app locopt f1 args0 = SOME (Full_app e env args) ⇒
   every_Fn_vs_NONE [e]`,
  simp[dest_closure_def, case_eq_thms, bool_case_eq] >> strip_tac >> rveq >> fs[] >>
  rveq >> simp[Once every_Fn_vs_NONE_EVERY] >> pairarg_tac >>
  fs[bool_case_eq] >> rveq >> fs[EVERY_MEM, FORALL_PROD, NOT_LESS_EQUAL] >>
  metis_tac[MEM_EL]);

val known_correct0 = Q.prove(
  `(∀a es env1 env2 (s01:α closSem$state) s02 res1 s1 g0 g g' as ealist.
      a = (es,env1,s01) ∧ evaluate (es, env1, s01) = (res1, s1) ∧
      EVERY esgc_free es ∧ subspt g0 g ∧ subspt g g' ∧
      LIST_REL val_approx_val as env1 ∧ EVERY vsgc_free env1 ∧
      every_Fn_vs_NONE es ∧
      LIST_REL (kvrel g') env1 env2 ∧ ksrel g' s01 s02 ∧
      state_globals_approx s01 g' ∧ BAG_ALL_DISTINCT (elist_globals es) ∧
      ssgc_free s01 ∧ known es as g0 = (ealist, g) ⇒
      ∃res2 s2.
        evaluate(MAP FST ealist, env2, s02) = (res2, s2) ∧
        krrel g' (res1,s1) (res2,s2)) ∧
   (∀lopt1 f1 args1 (s01:α closSem$state) res1 s1 lopt2 f2 args2 s02 g.
      evaluate_app lopt1 f1 args1 s01 = (res1,s1) ∧ ssgc_free s01 ∧
      kvrel g f1 f2 ∧ LIST_REL (kvrel g) args1 args2 ∧
      ksrel g s01 s02 ∧ state_globals_approx s01 g ∧ vsgc_free f1 ∧
      EVERY vsgc_free args1 ∧ loptrel f2 (LENGTH args1) lopt1 lopt2 ⇒
      ∃res2 s2.
        evaluate_app lopt2 f2 args2 s02 = (res2,s2) ∧
        krrel g (res1,s1) (res2,s2))`,
  ho_match_mp_tac evaluate_ind >> rpt conj_tac
  >- (say "nil" >> simp[evaluate_def, known_def])
  >- (say "cons" >>
      simp[evaluate_def, known_def, pair_case_eq, result_case_eq,
           BAG_ALL_DISTINCT_BAG_UNION] >>
      rpt strip_tac >> rveq >> rpt (pairarg_tac >> fs[]) >> rveq >> simp[] >>
      first_x_assum (patresolve `known [_] _ _ = _` last) >>
      disch_then (resolve_selected (el 4)) >> simp[] >>
      patresolve `known [_] _ _ = _` hd subspt_known_elist_globals >> simp[] >>
      disch_then (resolve_selected hd) >> simp[] >> strip_tac >>
      disch_then (resolve_selected last) >> simp[] >>
      (impl_keep_tac >- metis_tac[subspt_trans]) >>
      rw[]
      >- (imp_res_tac known_sing_EQ_E >> rveq >> fs[] >>
          sel_ihpc last >> simp[] >> disch_then (resolve_selected (el 3)) >>
          simp[] >> disch_then (resolve_selected hd) >> simp[] >> impl_tac
          >- (conj_tac
              >- (resolve_selected hd (GEN_ALL kca_sing_sga) >> simp[] >>
                  disch_then (resolve_selected last) >> simp[] >>
                  metis_tac[kvrel_LIST_REL_val_approx, kvrel_EVERY_vsgc_free,
                            ksrel_sga, ksrel_ssgc_free]) >>
              metis_tac[ssgc_free_preserved_SING']) >> rw[] >>
          simp[Once evaluate_CONS] >> imp_res_tac evaluate_SING >> rveq >>
          fs[])
      >- (imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> sel_ihpc last >>
          simp[] >> disch_then (resolve_selected (el 3)) >> simp[] >>
          disch_then (resolve_selected hd) >> simp[] >> impl_tac
          >- (conj_tac
              >- (resolve_selected hd (GEN_ALL kca_sing_sga) >> simp[] >>
                  disch_then (resolve_selected last) >> simp[] >>
                  metis_tac[kvrel_LIST_REL_val_approx, kvrel_EVERY_vsgc_free,
                            ksrel_sga, ksrel_ssgc_free]) >>
              metis_tac[ssgc_free_preserved_SING']) >> rw[] >>
          simp[Once evaluate_CONS, result_case_eq] >> fs[krrel_err_rw] >>
          dsimp[] >> metis_tac[result_CASES])
      >- (imp_res_tac known_sing_EQ_E >> rveq >> fs[] >>
          simp[Once evaluate_CONS, result_case_eq, pair_case_eq] >>
          dsimp[] >> fs[krrel_err_rw] >> metis_tac[pair_CASES, result_CASES]))
  >- (say "var" >>
      simp[evaluate_def, bool_case_eq, known_def] >>
      rpt strip_tac >> fs[LIST_REL_EL_EQN])
  >- (say "if" >>
      simp[evaluate_def, pair_case_eq, bool_case_eq, BAG_ALL_DISTINCT_BAG_UNION,
           result_case_eq, known_def] >> rpt strip_tac >> rveq >> fs[] >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >> fixeqs >>
      imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rveq >>
      map_every rename1 [`ksrel g' s01 s02`, `subspt g g'`,
                           `known [eb] as g2 = ([(eb',eapx)], g)`,
                           `known [tb] as g1 = ([(tb',tapx)], g2)`,
                           `known [gd] as g0 = ([(gd',gapx)], g1)`] >>
      `known [gd;tb] as g0 = ([(gd',gapx); (tb',tapx)], g2)`
        by simp[known_def] >>
      resolve_selected hd (subspt_known_elist_globals)>> simp[] >>
      disch_then (resolve_selected hd) >> simp[] >> strip_tac >>
      patresolve `known [gd] _ _ = _` hd subspt_known_elist_globals >> simp[] >>
      disch_then (resolve_selected hd) >> simp[] >> strip_tac
      >- (first_x_assum (patresolve `state_globals_approx _ _` (el 6)) >>
          rpt (disch_then (resolve_selected last) >> simp[]) >>
          impl_keep_tac >- metis_tac[subspt_trans] >> rw[] >>
          simp[evaluate_def] >> imp_res_tac evaluate_SING >> fs[] >> rveq >>
          fs[] >> rveq >> sel_ihpc last >> simp[] >> disch_then irule >>
          simp[]
          >- metis_tac[ssgc_free_preserved_SING']
          >- (patresolve `known [gd] _ _ = _` hd (GEN_ALL kca_sing_sga) >>
              simp[] >> disch_then (resolve_selected last) >> simp[] >>
              metis_tac[ksrel_sga, kvrel_LIST_REL_val_approx,
                        kvrel_EVERY_vsgc_free, ksrel_ssgc_free])
          >- metis_tac[subspt_trans])
      >- (first_x_assum (patresolve `state_globals_approx _ _` (el 6)) >>
          rpt (disch_then (resolve_selected last) >> simp[]) >>
          impl_keep_tac >- metis_tac[subspt_trans] >> rw[] >>
          simp[evaluate_def] >> imp_res_tac evaluate_SING >> fs[] >> rveq >>
          fs[] >> rveq >> sel_ihpc last >> simp[] >> disch_then irule >>
          simp[]
          >- metis_tac[ssgc_free_preserved_SING']
          >- (patresolve `known [gd] _ _ = _` hd (GEN_ALL kca_sing_sga) >>
              simp[] >> disch_then (resolve_selected last) >> simp[] >>
              metis_tac[ksrel_sga, kvrel_LIST_REL_val_approx,
                        kvrel_EVERY_vsgc_free, ksrel_ssgc_free,
                        state_approx_better_definedg, known_better_definedg]))
      >- ((* guard doesn't evaluate to T or F *) sel_ihpc (el 6) >> simp[] >>
          rpt (disch_then (resolve_selected last) >> simp[]) >>
          impl_keep_tac >- metis_tac[subspt_trans] >> rw[] >>
          simp[evaluate_def] >> imp_res_tac evaluate_SING >> fs[] >> rveq >>
          fs[] >> rveq >> dsimp[bool_case_eq] >> rpt disj2_tac >>
          rpt strip_tac >> rveq >> fs[])
      >- ((* guard errors *) sel_ihpc (el 6) >> simp[] >>
          rpt (disch_then (resolve_selected last) >> simp[]) >>
          impl_keep_tac >- metis_tac[subspt_trans] >> rw[] >>
          dsimp[evaluate_def, result_case_eq, bool_case_eq] >>
          fs[krrel_err_rw] >> metis_tac[pair_CASES, result_CASES]))
  >- (say "let" >>
      simp[evaluate_def, pair_case_eq, result_case_eq] >>
      rpt strip_tac >> rveq >> fs[known_def] >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[BAG_ALL_DISTINCT_BAG_UNION] >>
      map_every rename1 [`known [bod] _ g1 = (_, g)`,
                           `known _ _ g0 = (_, g1)`,
                           `subspt g gg`] >>
      patresolve `known _ _ g0 = _` hd subspt_known_elist_globals >> simp[] >>
      disch_then (resolve_selected hd) >> simp[] >>
      (impl_tac >- fs[BAG_DISJOINT, DISJOINT_SYM]) >> strip_tac >>
      first_x_assum (patresolve `known _ _ g0 = _` last) >> simp[] >>
      rpt (disch_then (resolve_selected last) >> simp[]) >>
      (impl_keep_tac >- metis_tac[subspt_trans]) >> rw[] >>
      simp[evaluate_def, result_case_eq]
      >- (imp_res_tac known_sing_EQ_E >> rveq >> fs[] >>
          rveq >> sel_ihpc last >> simp[] >> disch_then irule >> simp[]
          >- metis_tac[ssgc_evaluate]
          >- metis_tac[ssgc_evaluate,rsgc_free_def]
          >- (resolve_selected last known_correct_approx >> simp[] >>
              rpt (disch_then (resolve_selected hd) >> simp[]) >>
              metis_tac[ksrel_sga, kvrel_EVERY_vsgc_free,
                        kvrel_LIST_REL_val_approx, ksrel_ssgc_free])
          >- simp[EVERY2_APPEND_suff]
          >- (irule EVERY2_APPEND_suff >> simp[] >>
              resolve_selected last known_correct_approx >> simp[] >>
              rpt (disch_then (resolve_selected hd) >> simp[]) >>
              metis_tac[ksrel_sga, kvrel_EVERY_vsgc_free,
                        kvrel_LIST_REL_val_approx, ksrel_ssgc_free]))
      >- (fs[krrel_err_rw, result_case_eq] >> dsimp[] >>
          metis_tac[pair_CASES, result_CASES]))
  >- (say "raise" >>
      simp[evaluate_def, pair_case_eq, result_case_eq] >>
      rpt strip_tac >> rveq >> fs[known_def] >> pairarg_tac >> fs[] >>
      imp_res_tac known_sing_EQ_E >> fs[] >> rveq >> fs[] >>
      simp[evaluate_def, pair_case_eq, result_case_eq] >>
      nailIHx strip_assume_tac >> simp[] >> fs[]
      >- (imp_res_tac evaluate_SING >> fs[])
      >- (dsimp[] >> fs[krrel_err_rw] >> metis_tac[result_CASES]))
  >- (say "handle" >>
      simp[evaluate_def, pair_case_eq, result_case_eq,
           BAG_ALL_DISTINCT_BAG_UNION, error_case_eq, known_def] >>
      rpt strip_tac >> rveq >> fs[] >>
      rpt (pairarg_tac >> fs[]) >> rveq >>
      imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rveq >>
      map_every rename1 [`known _ (_ :: _) g1 = (_, g)`,
                           `known _ _ g0 = (_, g1)`,
                           `subspt g gg`] >>
      patresolve `known _ _ g0 = _` hd subspt_known_elist_globals >> simp[] >>
      rpt (disch_then (resolve_selected hd) >> simp[]) >> strip_tac >>
      first_x_assum (patresolve `state_globals_approx _ _`  (el 6)) >> simp[] >>
      rpt (disch_then (resolve_selected last) >> simp[]) >>
      (impl_keep_tac >- metis_tac[subspt_trans]) >> rw[] >>
      simp[evaluate_def, pair_case_eq, result_case_eq, error_case_eq]
      >- (dsimp[] >> fs[PULL_EXISTS] >> sel_ihpc last >> simp[] >>
          fs[krrel_err_rw] >> disch_then irule >> simp[]
          >- metis_tac[ssgc_free_preserved_SING']
          >- first_assum
               (mp_then (Pos last) (mp_tac >~ (simp[] >> NO_TAC)) ssgc_evaluate)
          >- (patresolve `known _ _ g0 = _` hd (GEN_ALL kca_sing_sga) >>
              simp[] >> disch_then (resolve_selected last) >> simp[] >>
              metis_tac[ksrel_ssgc_free,kvrel_EVERY_vsgc_free,ksrel_sga,
                        kvrel_LIST_REL_val_approx]))
      >- (fs[krrel_err_rw, result_case_eq, error_case_eq] >> dsimp[] >>
          metis_tac[pair_CASES, result_CASES, error_CASES]))
  >- (say "op" >>
      simp[evaluate_def, pair_case_eq, result_case_eq, known_def,
           BAG_ALL_DISTINCT_BAG_UNION] >>
      rpt gen_tac >> strip_tac >> rpt gen_tac >>
      rpt (pairarg_tac >> fs[]) >>
      rename[`isGlobal opn`, `gO_destApx apx`] >>
      Cases_on `isGlobal opn ∧ gO_destApx apx ≠ gO_None`
      >- (pop_assum strip_assume_tac >> simp[] >>
          Cases_on `opn` >> fs[isGlobal_def] >>
          Cases_on `apx` >> fs[gO_destApx_def] >> rveq >>
          fs[known_op_def, NULL_EQ, bool_case_eq, case_eq_thms] >> rveq >>
          imp_res_tac known_LENGTH_EQ_E >> fs[LENGTH_NIL_SYM] >> rveq >>
          simp[evaluate_def] >>
          rpt strip_tac >> rveq >> fs[evaluate_def, do_app_def, case_eq_thms] >>
          fs[state_globals_approx_def, subspt_def] >> rveq >> simp[] >>
          fs[known_def] >> rveq
          >- (rename[`lookup n g0 = SOME (Tuple tg [])`,
                     `kvrel g1 v (Block tg [])`] >>
              `lookup n g1 = SOME (Tuple tg [])` by metis_tac[domain_lookup] >>
              res_tac >> fs[] >> rveq >> fs[val_approx_val_def]) >>
          (* TODO: clos_known$ is only necessary because of HOL issue #430 *)
          rename[`lookup n g0 = SOME (clos_known$Int i)`, `kvrel g1 v (Number i)`] >>
          `lookup n g1 = SOME (Int i)` by metis_tac[domain_lookup] >>
          metis_tac[val_rel_def, val_approx_val_def, SOME_11]) >>
      rename[`closLang$Op tr opn (MAP FST es)`,
             `closSem$evaluate(MAP FST ealist,_,_)`] >>
      rpt strip_tac >>
      `ealist = [(Op tr opn (MAP FST es), apx)]`
         by (Cases_on `isGlobal opn` >> fs[] >>
             Cases_on `apx` >> fs[gO_destApx_def] >> every_case_tac >> fs[]) >>
      pop_assum SUBST_ALL_TAC >> rveq >>
      qpat_x_assum `¬(_ ∧ _)` kall_tac >> fs[] >>
      dsimp[evaluate_def, result_case_eq, pair_case_eq] >>
      sel_ihpc last >> simp[PULL_EXISTS] >>
      rpt (disch_then (resolve_selected last) >> simp[]) >>
      resolve_selected hd subspt_known_op_elist_globals >> simp[] >>
      rpt (disch_then (resolve_selected hd) >> simp[]) >> strip_tac >>
      (impl_keep_tac >- metis_tac[subspt_trans])
      >- ((* args evaluate OK, do_app evaluates OK *)
          metis_tac[kvrel_op_correct_Rval, EVERY2_REVERSE])
      >- ((* args evaluate OK, do_app errors *)
          rw[] >> imp_res_tac do_app_EQ_Rerr >> rw[] >>
          metis_tac[result_CASES, pair_CASES])
      >- ((* args error *) rw[] >> fs[krrel_err_rw] >>
         metis_tac[result_CASES, pair_CASES]))
  >- (say "fn" >>
      simp[evaluate_def, pair_case_eq, result_case_eq,
           known_def, bool_case_eq, case_eq_thms] >> rpt strip_tac >> rveq >> fs[] >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
      imp_res_tac state_rel_max_app >> fs[] >>
      dsimp[evaluate_def, case_eq_thms] >> imp_res_tac known_sing_EQ_E >> rveq >> fs[] >>
      rveq >>
      simp[exp_rel_def, PULL_EXISTS] >> metis_tac[kvrel_LIST_REL_val_approx])
  >- (say "letrec" >>
      simp[evaluate_def, pair_case_eq, result_case_eq, known_def, bool_case_eq,
           case_eq_thms] >> rpt strip_tac >> rveq >> fs[letrec_case_eq] >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
      fs[BAG_ALL_DISTINCT_BAG_UNION] >>
      imp_res_tac state_rel_max_app >> fs[] >>
      simp[evaluate_def, case_eq_thms, bool_case_eq] >> dsimp[] >>
      simp[EVERY_MAP, EXISTS_MAP]
      >- (disj1_tac >> simp[EVERY_MEM, FORALL_PROD] >>
          imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rveq >>
          sel_ihpc last >> simp[EVERY_GENLIST] >>
          rpt (disch_then (resolve_selected last) >> simp[]) >>
          rename1 `BAG_ALL_DISTINCT (elist_globals (MAP SND fns1))` >>
          `∀n e. MEM (n,e) fns1 ⇒ n ≤ s02.max_app ∧ n ≠ 0`
            by fs[EVERY_MEM, FORALL_PROD] >> simp[] >> strip_tac >>
          simp[GSYM PULL_EXISTS] >> simp[Once EQ_SYM_EQ] >>
          imp_res_tac LIST_REL_LENGTH >> fs[] >>
          first_x_assum irule
          >- (simp[LIST_REL_EL_EQN, EL_APPEND_EQN] >> qx_gen_tac `mm` >>
              strip_tac >> rw[]
              >- (fs[Once every_Fn_vs_NONE_EVERY] >>
                  fs[EVERY_MAP] >> fs[EVERY_MEM, FORALL_PROD] >>
                  metis_tac[])
              >- (rename1 `LIST_REL val_approx_val apxs env1` >>
                  qexists_tac `apxs` >> conj_tac
                  >- metis_tac[kvrel_LIST_REL_val_approx] >>
                  simp[LIST_REL_EL_EQN, EL_MAP] >>
                  qx_gen_tac `nn` >> strip_tac >> pairarg_tac >>
                  simp[] >> simp[exp_rel_def] >>
                  map_every rename1 [`ksrel gg ss1 ss2`, `subspt g gg`,
                                       `subspt g0 g`] >>
                  ntac 2 (qexists_tac `g0`) >> simp[] >>
                  rename1 `known [e1] env g0` >>
                  Cases_on `known [e1] env g0` >>
                  imp_res_tac known_sing_EQ_E >> fs[] >> rveq >>
                  conj_tac >- metis_tac[subspt_trans] >>
                  rename1 `known [subexp] env g0 = _` >>
                  `elist_globals [subexp] = {||}`
                    suffices_by metis_tac[known_emptySetGlobals_unchanged_g] >>
                  fs[elglobals_EQ_EMPTY, MEM_MAP, PULL_EXISTS, FORALL_PROD] >>
                  metis_tac[MEM_EL])
              >- fs[LIST_REL_EL_EQN])
          >- (irule EVERY2_APPEND_suff >> simp[] >>
              simp[LIST_REL_GENLIST] >> qx_gen_tac `ii` >> strip_tac >>
              rename1 `option_CASE lloc` >> Cases_on `lloc` >> simp[])) >>
      disj2_tac >> fs[EXISTS_MEM, EXISTS_PROD] >> metis_tac[])
  >- (say "app" >>
      rpt gen_tac >> strip_tac >>
      simp[evaluate_def, pair_case_eq, result_case_eq,
           bool_case_eq, known_def, BAG_ALL_DISTINCT_BAG_UNION] >>
      rpt strip_tac >> rveq >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
      map_every imp_res_tac [known_sing_EQ_E, evaluate_SING] >> rveq >> fs[] >>
      rveq
      >- (map_every rename1 [
            `known [fexp] apxs g1 = ([(fexp',fapx)], g)`,
            `known args apxs g0 = (alist, g1)`,
            `subspt g gg`] >>
          patresolve `known [_] _ _ = _` (el 2) subspt_known_elist_globals >>
          simp[] >> disch_then (resolve_selected (el 1)) >> simp[] >>
          impl_tac >- fs[BAG_DISJOINT, DISJOINT_SYM] >> strip_tac >>
          first_x_assum (patresolve `known args _ _ = _` last) >> simp[] >>
          `subspt g1 gg` by metis_tac[subspt_trans] >>
          rpt (disch_then (resolve_selected last) >> simp[]) >> rw[] >>
          simp[evaluate_def] >> imp_res_tac known_LENGTH_EQ_E >> fs[] >>
          first_x_assum (patresolve `known [_] _ _ = _` last) >> simp[] >>
          disch_then (resolve_selected (el 2)) >> simp[] >>
          disch_then (resolve_selected hd) >> simp[] >>
          resolve_selected hd ssgc_evaluate >> simp[] >>
          rpt (disch_then (resolve_selected hd) >> simp[]) >> strip_tac >>
          impl_keep_tac
          >- (patresolve `closSem$evaluate (MAP FST _, _, _) = _` last
                         known_correct_approx >>
              simp[] >> disch_then (resolve_selected hd) >> simp[] >>
              metis_tac[ksrel_ssgc_free,kvrel_EVERY_vsgc_free,ksrel_sga,
                        kvrel_LIST_REL_val_approx]) >>
          rw[] >> simp[] >>
          rename1 `evaluate_app loption1 v1 vs1 s21 = (result,ss1)` >>
          `ssgc_free s21`
            by metis_tac[ksrel_ssgc_free, ssgc_free_preserved_SING'] >> fs[] >>
          first_x_assum (resolve_selected hd) >> simp[] >>
          rpt (disch_then (resolve_selected hd) >> simp[]) >> strip_tac >>
          `state_globals_approx s21 gg`
            by (patresolve `known [_] _ _ = _` hd known_correct_approx >>
                simp[] >> disch_then (resolve_selected last) >> simp[] >>
                metis_tac[ksrel_ssgc_free,kvrel_EVERY_vsgc_free,ksrel_sga,
                          kvrel_LIST_REL_val_approx]) >> fs[] >>
          `vsgc_free v1`
            by (patresolve `closSem$evaluate ([_],_,_) = (Rval [v1],_)` last
                           ssgc_evaluate >> simp[]) >> fs[] >>
          reverse (Cases_on `loption1`) >> simp[]
          >- (first_x_assum irule >> simp[loptrel_def]) >>
          rename1 `dest_Clos fapprox` >> Cases_on `dest_Clos fapprox` >>
          simp[]
          >- (first_x_assum irule >> simp[loptrel_def]) >>
          rename1 `dest_Clos fapprox = SOME closapxvalue` >>
          `∃clloc clarity. closapxvalue = (clloc, clarity)`
            by metis_tac[pair_CASES] >> pop_assum SUBST_ALL_TAC >>
          simp[] >> rename1 `LENGTH args > 0` >>
          reverse (Cases_on `clarity = LENGTH args`) >> simp[]
          >- (first_x_assum irule >> simp[loptrel_def]) >>
          first_x_assum irule >> simp[loptrel_def] >>
          qspecl_then [`[fexp]`, `apxs`, `g1`, `[(fexp',fapprox)]`, `g`]
             mp_tac known_correct_approx >> simp[] >>
          disch_then (resolve_selected last) >> simp[] >>
          disch_then (qspec_then `gg` mp_tac) >> impl_tac
          >- metis_tac[kvrel_LIST_REL_val_approx, ksrel_ssgc_free,
                       kvrel_EVERY_vsgc_free, ksrel_sga] >>
          fs[dest_Clos_eq_SOME] >> rveq >> rw[] >> simp[] >>
          metis_tac[evaluate_length_imp])
      >- (map_every rename1 [
            `known [fexp] apxs g1 = ([(fexp',fapx)], g)`,
            `known args apxs g0 = (alist, g1)`,
            `subspt g gg`] >>
          patresolve `known [_] _ _ = _` (el 2) subspt_known_elist_globals >>
          simp[] >> disch_then (resolve_selected (el 1)) >> simp[] >>
          impl_tac >- fs[BAG_DISJOINT, DISJOINT_SYM] >> strip_tac >>
          first_x_assum (patresolve `known args _ _ = _` last) >> simp[] >>
          `subspt g1 gg` by metis_tac[subspt_trans] >>
          rpt (disch_then (resolve_selected last) >> simp[]) >> rw[] >>
          simp[evaluate_def] >> imp_res_tac known_LENGTH_EQ_E >> fs[] >>
          sel_ihpc last >> simp[] >>
          disch_then (resolve_selected (el 2)) >> simp[] >>
          disch_then (resolve_selected hd) >> simp[] >> reverse impl_tac
          >- (rw[] >> simp[] >> fs[krrel_err_rw] >>
              dsimp[result_case_eq] >> metis_tac[pair_CASES, result_CASES]) >>
          conj_tac
          >- (patresolve `closSem$evaluate (MAP FST _, _, _) = _` last
                         known_correct_approx >>
              simp[] >> disch_then (resolve_selected hd) >> simp[] >>
              metis_tac[ksrel_ssgc_free,kvrel_EVERY_vsgc_free,ksrel_sga,
                        kvrel_LIST_REL_val_approx]) >>
          metis_tac [ssgc_evaluate])
      >- (map_every rename1 [
            `known [fexp] apxs g1 = ([(fexp',fapx)], g)`,
            `known args apxs g0 = (alist, g1)`,
            `subspt g gg`] >>
          patresolve `known [_] _ _ = _` (el 2) subspt_known_elist_globals >>
          simp[] >> disch_then (resolve_selected (el 1)) >> simp[] >>
          impl_tac >- fs[BAG_DISJOINT, DISJOINT_SYM] >> strip_tac >>
          first_x_assum (patresolve `known args _ _ = _` last) >> simp[] >>
          `subspt g1 gg` by metis_tac[subspt_trans] >> strip_tac >>
          nailIHx strip_assume_tac >>
          simp[evaluate_def, bool_case_eq, result_case_eq, pair_case_eq] >>
          imp_res_tac known_LENGTH_EQ_E >> rveq >> fs[] >>
          fs[krrel_err_rw] >> dsimp[] >>
          metis_tac[result_CASES,pair_CASES])
      >- (map_every imp_res_tac [evaluate_IMP_LENGTH, known_LENGTH_EQ_E] >>
          fs[] >> rw[] >> simp[evaluate_def]))
  >- (say "tick" >> simp[dec_clock_def] >> rpt gen_tac >> strip_tac >>
      simp[evaluate_def, bool_case_eq, known_def] >>
      rename1 `(s0:α closSem$state).clock = 0` >> Cases_on `s0.clock = 0` >>
      fs[] >> rpt strip_tac >> rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
      simp[evaluate_def] >- fs[ksrel_def] >>
      fs[dec_clock_def] >> fixeqs >> imp_res_tac known_sing_EQ_E >> rveq >>
      fs[] >> rveq >>
      map_every rename1 [
        `known [exp1] apxs g0 = ([(exp2,apx)],g)`,
        `evaluate([exp1],env1,s01 with clock := s01.clock - 1) = (res1,s1)`,
        `ksrel gg s01 s02`] >>
      sel_ihpc last >> simp[] >>
      disch_then
        (qspecl_then [`env2`, `s02 with clock := s02.clock - 1`, `gg`]
                     mp_tac) >>
      simp[] >> impl_keep_tac >- fs[ksrel_def] >>
      `s02.clock = s01.clock` by fs[ksrel_def] >> simp[])
  >- (say "call" >>
      simp[evaluate_def, pair_case_eq, result_case_eq, case_eq_thms, bool_case_eq,
           known_def] >> rw[]
      >- (simp[] >> metis_tac[pair_CASES])
      >- (rpt (pairarg_tac >> fs[]) >> rveq >> nailIHx strip_assume_tac >>
          simp[evaluate_def] >> rw[] >>
          imp_res_tac ksrel_find_code >> fs[])
      >- (fixeqs >> rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
          nailIHx strip_assume_tac >>
          imp_res_tac ksrel_find_code >> fs[])
      >- (rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
          nailIHx strip_assume_tac >> simp[evaluate_def] >>
          fs[krrel_err_rw] >>
          dsimp[result_case_eq, case_eq_thms, pair_case_eq, bool_case_eq] >>
          metis_tac[option_CASES, pair_CASES, result_CASES]))
  >- (say "evaluate_app(nil)" >> simp[evaluate_def])
  >- (say "evaluate_app(cons)" >> rpt gen_tac >> strip_tac >>
      simp[evaluate_def, case_eq_thms, bool_case_eq, pair_case_eq, result_case_eq] >>
      rpt strip_tac >> rveq >> fs[]
      >- metis_tac[pair_CASES]
      >- (simp[evaluate_def, case_eq_thms, bool_case_eq, pair_case_eq] >>
          resolve_selected hd (GEN_ALL kvrel_dest_closure_SOME_Partial) >>
          simp[PULL_EXISTS] >> imp_res_tac LIST_REL_LENGTH >> fs[] >>
          rpt (disch_then (resolve_selected hd) >> simp[]) >>
          strip_tac >> simp[] >> fs[ksrel_def])
      >- (simp[evaluate_def, case_eq_thms, bool_case_eq, pair_case_eq] >>
          resolve_selected hd (GEN_ALL kvrel_dest_closure_SOME_Partial) >>
          simp[PULL_EXISTS] >> imp_res_tac LIST_REL_LENGTH >> fs[] >>
          rpt (disch_then (resolve_selected hd) >> simp[]) >> strip_tac >>
          simp[] >> fs[ksrel_def, dec_clock_def])
      >- (simp[evaluate_def, case_eq_thms, bool_case_eq, pair_case_eq] >>
          resolve_selected hd (GEN_ALL kvrel_dest_closure_SOME_Full) >>
          simp[PULL_EXISTS] >> imp_res_tac LIST_REL_LENGTH >> fs[] >>
          rpt (disch_then (resolve_selected hd) >> simp[]) >> strip_tac >>
          simp[] >> imp_res_tac LIST_REL_LENGTH >> fs[ksrel_def])
      >- (simp[evaluate_def, case_eq_thms, bool_case_eq, pair_case_eq] >>
          resolve_selected hd (GEN_ALL kvrel_dest_closure_SOME_Full) >>
          simp[PULL_EXISTS] >> imp_res_tac LIST_REL_LENGTH >> fs[] >>
          rpt (disch_then (resolve_selected hd) >> simp[]) >> strip_tac >>
          simp[] >> rename1 `ksrel g s01 s02` >>
          `s02.clock = s01.clock` by fs[ksrel_def] >>
          `s02.max_app = s01.max_app` by fs[ksrel_def] >>
          imp_res_tac LIST_REL_LENGTH >> fs[] >> simp[PULL_EXISTS] >>
          dsimp[] >> fs[PULL_EXISTS] >>
          map_every rename1 [
            `dest_closure _ lopt1 f1 (iarg1 :: iargs) =
               SOME (Full_app exp1 env1 args1)`,
            `evaluate([exp1],env1,dec_clock _ s01) = (Rval [v1], s11)`,
            `kerel envapx gg exp1 exp2`] >> fs[exp_rel_def] >>
          rpt disj1_tac >>
          first_x_assum (patresolve `known [exp1] _ _ = _` last) >> simp[] >>
          map_every rename1 [
            `evaluate([exp1],env1,
                      dec_clock (SUC (LENGTH iargs1) - LENGTH args2) s01)`,
            `LIST_REL (kvrel gg) env1 env2`] >>
          disch_then (qspecl_then [
             `env2`,
             `dec_clock (SUC (LENGTH iargs1) - LENGTH args2) s02`,
             `gg`] mp_tac) >> simp[] >>
          `set_globals exp1 = {||} ∧ EVERY vsgc_free env1 ∧
           EVERY vsgc_free args1 ∧ esgc_free exp1`
            by metis_tac[vsgc_free_Full_app_set_globals, EVERY_DEF,
                         set_globals_empty_esgc_free] >> simp[] >>
          qspec_then `[exp1]` mp_tac known_emptySetGlobals_unchanged_g >>
          disch_then (resolve_selected hd) >> simp[] >>
          disch_then SUBST_ALL_TAC >>
          rename1 `LIST_REL val_approx_val envapx env1` >>
          `LIST_REL val_approx_val envapx env1`
            by metis_tac[kvrel_LIST_REL_val_approx] >>
          `every_Fn_vs_NONE [exp1]`
            by metis_tac[kvrel_dest_closure_every_Fn_vs_NONE] >>
          impl_tac >- (simp[] >> fs[ksrel_def, dec_clock_def]) >> rw[] >>
          simp[] >>
          rename1 `loptrel f2 _ lopt1 lopt2` >>
          reverse (Cases_on `lopt1`)
          >- (fs[loptrel_arg1_SOME] >> rveq >>
              imp_res_tac dest_closure_SOME_Full_app_args_nil >> fs[] >>
              rveq >> simp[]) >>
          qpat_x_assum `loptrel _ _ _ _` mp_tac >>
          simp[loptrel_arg1_NONE] >> reverse strip_tac >> rveq
          >- (imp_res_tac dest_closure_SOME_Full_app_args_nil >> fs[] >>
              rveq >> simp[])
          >- (imp_res_tac dest_closure_SOME_Full_app_args_nil >> fs[] >>
              rveq >> simp[]) >>
          first_x_assum irule >> simp[]
          >- metis_tac[ssgc_free_preserved_SING', ssgc_free_dec_clock]
          >- (patresolve `evaluate([exp1],_,_) = _` last ssgc_evaluate >>
              simp[])
          >- (patresolve `known [exp1] _ _ = _` hd known_correct_approx >>
              simp[] >> disch_then (resolve_selected last) >> simp[] >>
              metis_tac[ksrel_sga, ksrel_ssgc_free, kvrel_EVERY_vsgc_free])
          >- simp[loptrel_def])
      >- (imp_res_tac evaluate_SING >> fs[])
      >- (simp[evaluate_def, case_eq_thms, bool_case_eq, pair_case_eq] >>
          resolve_selected hd (GEN_ALL kvrel_dest_closure_SOME_Full) >>
          simp[PULL_EXISTS] >> imp_res_tac LIST_REL_LENGTH >> fs[] >>
          rpt (disch_then (resolve_selected hd) >> simp[]) >> strip_tac >>
          simp[] >> rename1 `ksrel g s01 s02` >>
          `s02.clock = s01.clock` by fs[ksrel_def] >>
          imp_res_tac LIST_REL_LENGTH >> fs[] >> simp[PULL_EXISTS] >>
          dsimp[] >>
          map_every rename1 [
            `dest_closure _ lopt1 f1 (iarg1 :: iargs) =
               SOME (Full_app exp1 env1 args1)`,
            `evaluate([exp1],env1,dec_clock _ s01) = (Rerr err1, s1)`,
            `kerel envapx gg exp1 exp2`] >> fs[exp_rel_def] >>
          first_x_assum (patresolve `known [exp1] _ _ = _` last) >> simp[] >>             map_every rename1 [
            `evaluate([exp1],env1,
                      dec_clock (SUC (LENGTH iargs1) - LENGTH args2) s01)`,
            `LIST_REL (kvrel gg) env1 env2`] >>
          disch_then (qspecl_then [
             `env2`,
             `dec_clock (SUC (LENGTH iargs1) - LENGTH args2) s02`,
             `gg`] mp_tac) >> simp[] >>
          `set_globals exp1 = {||} ∧ EVERY vsgc_free env1 ∧
           EVERY vsgc_free args1 ∧ esgc_free exp1`
            by metis_tac[vsgc_free_Full_app_set_globals, EVERY_DEF,
                         set_globals_empty_esgc_free] >> simp[] >>
          qspec_then `[exp1]` mp_tac known_emptySetGlobals_unchanged_g >>
          disch_then (resolve_selected hd) >> simp[] >>
          disch_then SUBST_ALL_TAC >>
          rename1 `LIST_REL val_approx_val envapx env1` >>
          `LIST_REL val_approx_val envapx env1`
            by metis_tac[kvrel_LIST_REL_val_approx] >>
          `every_Fn_vs_NONE [exp1]`
            by metis_tac[kvrel_dest_closure_every_Fn_vs_NONE] >>
          impl_tac >- (simp[] >> fs[ksrel_def, dec_clock_def]) >> rw[] >>
          imp_res_tac state_rel_max_app >>
          simp[] >> fs[krrel_err_rw] >>
          rename1 `evaluate([exp2],_,_) = (res2,_)` >>
          Cases_on `res2`
          >- (imp_res_tac evaluate_SING >> simp[] >> metis_tac[pair_CASES]) >>
          simp[])))

val known_correct = save_thm(
  "known_correct",
  known_correct0 |> SIMP_RULE (srw_ss()) []);

val known_preserves_every_Fn_NONE = Q.store_thm(
  "known_preserves_every_Fn_NONE",
  `∀es as g0 alist g.
     known es as g0 = (alist,g) ∧ every_Fn_vs_NONE es ⇒
     every_Fn_vs_NONE (MAP FST alist)`,
  ho_match_mp_tac known_ind >> simp[known_def] >> rpt strip_tac >>
  rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
  imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rveq
  >- (simp[Once every_Fn_vs_NONE_EVERY] >> simp[GSYM every_Fn_vs_NONE_EVERY])
  >- (every_case_tac >> simp[Once every_Fn_vs_NONE_EVERY])
  >- (simp[Once every_Fn_vs_NONE_EVERY] >>
      simp[EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD] >> rpt strip_tac >>
      sel_ihpc hd >> rename1 `known[bod] env g0` >>
      Cases_on `known[bod] env g0` >> simp[] >> imp_res_tac known_sing_EQ_E >>
      rveq >> fs[] >> rveq >> disch_then irule >>
      fs[Once every_Fn_vs_NONE_EVERY] >>
      fs[EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD] >> metis_tac[]));

val known_preserves_every_Fn_SOME = Q.store_thm(
  "known_preserves_every_Fn_SOME",
  `∀es as g0 alist g.
     known es as g0 = (alist,g) ∧ every_Fn_SOME es ⇒
     every_Fn_SOME (MAP FST alist)`,
  ho_match_mp_tac known_ind >> simp[known_def] >> rpt strip_tac >>
  rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
  imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rveq
  >- (simp[Once every_Fn_SOME_EVERY]>>simp[GSYM every_Fn_SOME_EVERY])
  >- (every_case_tac >> simp[Once every_Fn_SOME_EVERY])
  >- (simp[Once every_Fn_SOME_EVERY] >>
      simp[EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD] >> rpt strip_tac >>
      sel_ihpc hd >> rename1 `known[bod] env g0` >>
      Cases_on `known[bod] env g0` >> simp[] >> imp_res_tac known_sing_EQ_E >>
      rveq >> fs[] >> rveq >> disch_then irule >>
      fs[Once every_Fn_SOME_EVERY] >>
      fs[EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD] >> metis_tac[]));

fun abbrevify (asl,g) =
  let val (l,r) = dest_imp g
      fun abc t = if is_forall t then REWR_CONV (GSYM markerTheory.Abbrev_def) t
                  else ALL_CONV t
  in
    if is_forall r then
      CONV_TAC (LAND_CONV (EVERY_CONJ_CONV abc)) >> strip_tac
    else ALL_TAC
  end (asl,g)

val unabbrevify = RULE_ASSUM_TAC (REWRITE_RULE [markerTheory.Abbrev_def])

val say = say0 "known_idem"
val merge_subapprox_cong = Q.store_thm(
  "merge_subapprox_cong",
  `a1 ◁ a2 ∧ b1 ◁ b2 ⇒ merge a1 b1 ◁ merge a2 b2`,
  simp[subapprox_def] >>
  metis_tac[merge_comm, merge_assoc]);

val known_op_increases_subspt_info = Q.store_thm(
  "known_op_increases_subspt_info",
  `∀opn as1 g0 a1 a2 g1 g2 as2 g.
     known_op opn as1 g0 = (a1,g1) ∧ subspt g0 g1 ∧ subspt g1 g2 ∧
     LIST_REL $◁ as2 as1 ∧ known_op opn as2 g2 = (a2,g)
    ⇒
     a2 ◁ a1 ∧ subspt g2 g`,
  rpt gen_tac >> Cases_on `opn` >>
  simp[known_op_def, case_eq_thms, va_case_eq, bool_case_eq, NULL_EQ] >>
  disch_then strip_assume_tac >> rveq >> simp[] >> fs[]
  >- (fs[subspt_def] >> metis_tac[domain_lookup, NOT_SOME_NONE])
  >- (fs[subspt_def] >> metis_tac[domain_lookup, subapprox_refl, SOME_11])
  >- fs[subspt_def, DISJ_IMP_THM, lookup_insert]
  >- (fs[subspt_def, DISJ_IMP_THM, lookup_insert, FORALL_AND_THM] >> rveq >>
      rw[] >> fs[subapprox_def, merge_comm])
  >- fs[subspt_def, lookup_insert, DISJ_IMP_THM]
  >- (fs[subspt_def, lookup_insert, DISJ_IMP_THM, FORALL_AND_THM] >> rveq >>
      rw[] >> fs[subapprox_def] >> metis_tac[merge_comm, merge_assoc])
  >- (fs[LIST_REL_EL_EQN] >>
      metis_tac[integerTheory.INT_INJ, integerTheory.INT_OF_NUM,
                integerTheory.INT_LT])
  >- (fs[LIST_REL_EL_EQN] >> rfs[]))

val known_increases_subspt_info = Q.store_thm(
  "known_increases_subspt_info",
  `∀es as1 g0 alist1 g1 g2 as2 alist2 g.
      known es as1 g0 = (alist1,g1) ∧ BAG_ALL_DISTINCT (elist_globals es) ∧
      subspt g0 g1 ∧ subspt g1 g2 ∧ LIST_REL $◁ as2 as1 ∧
      known es as2 g2 = (alist2,g)
     ⇒
      subspt g2 g ∧
      LIST_REL $◁ (MAP SND alist2) (MAP SND alist1)`,
  ho_match_mp_tac known_ind >> rpt conj_tac >> rpt gen_tac >> abbrevify >>
  fs[known_def, BAG_ALL_DISTINCT_BAG_UNION] >>
  rpt (gen_tac ORELSE disch_then strip_assume_tac)
  >- (rveq >> simp[])
  >- (rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
      imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rveq >>
      map_every rename1 [`LIST_REL _ (MAP SND alist2) (MAP SND alist1)`,
                           `known (exp2::es) as1 g01 = (alist1, g1)`,
                           `known [exp1] as1 g0 = ([(_,apx1)], g01)`,
                           `known [exp1] as2 g2 = ([(_,apx2)], g21)`] >>
      patresolve `known [_] _ g0 = _` hd subspt_known_elist_globals >> simp[] >>
      rpt (disch_then (resolve_selected hd) >> simp[]) >> strip_tac >> fs[] >>
      unabbrevify >>
      `subspt g01 g2` by metis_tac[subspt_trans] >>
      first_x_assum (resolve_selected hd) >> simp[] >>
      rpt (disch_then (resolve_selected hd) >> simp[]) >> strip_tac >>
      `subspt g2 g21` by metis_tac[] >>
      `subspt g1 g21` by metis_tac[subspt_trans] >>
      `subspt g21 g` by metis_tac[] >> metis_tac[subspt_trans])
  >- (say "var" >> rveq >> simp[any_el_ALT] >> fs[LIST_REL_EL_EQN] >> rw[])
  >- (say "if" >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
      imp_res_tac known_sing_EQ_E >> rveq >>
      fs[PULL_EXISTS, EXISTS_PROD] >> rveq >>
      map_every rename1 [
        `merge apx2' apx3' ◁ merge apx2 apx3`,
        `known [tb] as1 g01 = ([(_,apx2)], g02)`,
        `known [tb] as2 g11 = ([(_,apx2')], g12)`,
        `known [eb] as1 g02 = ([(_,apx3)], g1)`,
        `known [ge] as1 g0 = ([(_,apx1)], g01)`] >>
      `∃apxs. known [ge;tb] as1 g0 = (apxs, g02)` by simp[known_def] >>
      resolve_selected hd subspt_known_elist_globals >> simp[] >>
      rpt (disch_then (resolve_selected hd) >> simp[]) >> strip_tac >>
      patresolve `known [ge] as1 g0 = _` hd subspt_known_elist_globals >>
      simp[] >>
      rpt (disch_then (resolve_selected hd) >> simp[]) >> strip_tac >> fs[] >>
      unabbrevify >>
      `subspt g01 g2` by metis_tac[subspt_trans] >>
      first_x_assum (resolve_selected hd) >> simp[] >>
      disch_then (resolve_selected last) >> simp[] >> strip_tac >>
      first_x_assum (patresolve `known [tb] as2 _ = _` (el 3)) >> simp[] >>
      impl_keep_tac
      >- metis_tac[subspt_trans] >> strip_tac >>
      first_x_assum (patresolve `known [eb] as2 _ = _` (el 3)) >> simp[] >>
      impl_keep_tac
      >- metis_tac[subspt_trans] >> strip_tac >>
      conj_tac >- metis_tac[subspt_trans] >>
      metis_tac[merge_subapprox_cong])
  >- (say "let" >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
      imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rveq >>
      map_every rename1 [`apx' ◁ apx`,
                           `known [bod] _ g01 = ([(_, apx)], g02)`,
                           `known [bod] _ g21 = ([(_, apx')], g22)`,
                           `known binds as1 g0 = (_, g01)`,
                           `known binds as2 g2 = (_, g21)`] >>
      patresolve `known binds as1 g0 = _` hd subspt_known_elist_globals >>
      simp[] >>
      rpt (disch_then (resolve_selected hd) >> simp[]) >> impl_tac
      >- fs[BAG_DISJOINT, DISJOINT_SYM] >> strip_tac >> fs[] >> unabbrevify >>
      first_x_assum (patresolve `known binds as2 _ = _` (el 3)) >> simp[] >>
      impl_keep_tac >- metis_tac [subspt_trans] >> strip_tac >>
      first_x_assum (patresolve `known [bod] _ g21 = _` (el 3)) >>
      simp[EVERY2_APPEND_suff] >> impl_keep_tac >- metis_tac[subspt_trans] >>
      metis_tac[subspt_trans])
  >- (say "raise" >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
      imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rveq >> unabbrevify >>
      metis_tac[])
  >- (say "tick" >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
      imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rveq >> unabbrevify >>
      fs[EXISTS_PROD] >> metis_tac[CONS_11, PAIR_EQ])
  >- (say "handle" >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
      imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rveq >>
      map_every rename1 [
        `merge apx1' apx2' ◁ merge apx1 apx2`,
        `known [exp1] as1 g0 = ([(_,apx1)], g01)`,
        `known [exp1] as2 g2 = ([(_,apx1')], g21)`,
        `known [hndlr] (Other::as1) g01 = ([(_,apx2)], g1)`,
        `known [hndlr] (Other::as2) g21 = ([(_,apx2')], gg)`] >>
      patresolve `known [exp1] as1 g0 = _` hd subspt_known_elist_globals >>
      simp[] >> disch_then (resolve_selected hd) >> simp[] >> strip_tac >>
      fs[] >> unabbrevify >>
      first_x_assum (patresolve `known [exp1] _ g2 = _` last) >> simp[] >>
      impl_keep_tac >- metis_tac[subspt_trans] >> strip_tac >>
      fs[PULL_EXISTS, EXISTS_PROD] >>
      first_x_assum (patresolve `known [hndlr] _ g21 = _` last) >> simp[] >>
      impl_keep_tac >- metis_tac[subspt_trans] >>
      metis_tac[merge_subapprox_cong, subspt_trans])
  >- (say "call" >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >> unabbrevify >> metis_tac[])
  >- (say "op" >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
      map_every rename1 [`apx' ◁ apx`,
                           `known_op opn _ g01 = (apx,g1)`,
                           `known_op opn _ g21 = (apx',gg)`] >>
      patresolve `known_op _ _ g01 = _` (el 2) subspt_known_op_elist_globals >>
      simp[] >> disch_then (resolve_selected hd) >> simp[] >> strip_tac >>
      fs[] >> unabbrevify >>
      first_x_assum (patresolve `known _ _ g2 = _` last) >> simp[] >>
      impl_keep_tac >- metis_tac[subspt_trans] >> strip_tac >>
      patresolve `known_op _ _ g01 = _` hd known_op_increases_subspt_info >>
      simp[] >>
      disch_then (patresolve `known_op _ _ g21 = _` last) >>
      simp[LIST_REL_REVERSE_EQ] >> metis_tac[subspt_trans])
  >- (say "app" >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
      imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rveq >>
      map_every rename1 [`subspt g2 gg`, `subspt g1 g2`,
                           `known args as2 g2 = (_, g21)`,
                           `known [f] as1 g11 = (_, g1)`] >>
      patresolve `known _ _ _ = (_, g11)` hd subspt_known_elist_globals >>
      simp[] >>
      disch_then (resolve_selected hd) >> simp[] >> impl_keep_tac
      >- fs[BAG_DISJOINT, DISJOINT_SYM] >> strip_tac >> fs[] >> unabbrevify >>
      first_x_assum (patresolve `known _ _ g2 = _` last) >> simp[] >>
      impl_keep_tac >- metis_tac[subspt_trans] >> strip_tac >>
      first_x_assum (patresolve `known _ _ g21 = _` last) >> simp[] >>
      metis_tac[subspt_trans])
  >- (say "fn" >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >> rveq >> unabbrevify >>
      rename1 `subspt gg2 gg` >>
      first_x_assum (patresolve `known _ _ gg2 = _` last) >>
      simp[] >> reverse impl_tac >- metis_tac[subspt_trans] >>
      simp[LIST_REL_REPLICATE_same, EVERY2_APPEND_suff])
  >- (say "letrec" >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[letrec_case_eq] >> rveq >>
      imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rveq >>
      map_every rename1 [`apx1' ◁ apx1`,
                           `known [bod] _ g0 = ([(_,apx1)], g1)`,
                           `known [bod] _ g2 = ([(_,apx1')], g)`] >>
      unabbrevify >>
      first_x_assum (patresolve `subspt g1 _` hd) >> simp[] >>
      disch_then (first_assum o mp_then (Pos last) mp_tac) >> simp[] >>
      disch_then irule >> irule EVERY2_APPEND_suff >> simp[] >>
      simp[LIST_REL_GENLIST]))

val sga_subspt = Q.store_thm(
  "sga_subspt",
  `state_globals_approx s g0 ∧ subspt g0 g ⇒ state_globals_approx s g`,
  simp[state_globals_approx_def, subspt_def] >> rw[] >> fs[get_global_def] >>
  nailIHx strip_assume_tac >> metis_tac[domain_lookup]);

val state_globals_LN = Q.store_thm(
  "state_globals_LN",
  `state_globals_approx s LN ⇔ ∀n v. get_global n s.globals ≠ SOME (SOME v)`,
  simp[state_globals_approx_def] >> simp[lookup_def]);

(* Optionally applied state relation and result relation*)
val opt_state_rel_def = Define`
  opt_state_rel b g s1 s2 ⇔
  if b then state_rel g s1 s2
       else s1 = s2`

val opt_res_rel_def = Define`
  opt_res_rel b g r1 r2 ⇔
  if b then res_rel g r1 r2
        else r1 = r2`

(* Some assumptions can be removed if b = F *)
val compile_correct = Q.store_thm(
  "compile_correct",
  `compile b e0 = e ∧ evaluate ([e0], [], s01) = (res1, s1) ∧
   esgc_free e0 ∧ every_Fn_vs_NONE [e0] ∧
   opt_state_rel b LN s01 s02 ∧
   state_globals_approx s01 LN ∧ BAG_ALL_DISTINCT (set_globals e0) ∧
   ssgc_free s01
    ⇒
   ∃res2 s2 g.
     evaluate([e], [], s02) = (res2, s2) ∧
     opt_res_rel b g (res1,s1) (res2,s2)`,
  reverse (Cases_on`b`)>>
  simp[compile_def,opt_state_rel_def,opt_res_rel_def] >- metis_tac[]>>
  rpt (pairarg_tac >> simp[]) >>
  map_every rename1 [`known [e0] [] LN = (alist0, g1)`,
                       `known [e0] [] g1 = (alist, g)`] >>
  imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rw[] >>
  patresolve `known _ _ LN = _` hd known_increases_subspt_info >> simp[] >>
  disch_then (patresolve `known _ _ g1 = _` (el 2)) >> simp[] >> strip_tac >>
  patresolve `known _ _ g1 = _` last (CONJUNCT1 known_correct) >> simp[] >>
  disch_then (resolve_selected hd) >> simp[] >>
  `ksrel g s01 s02` by metis_tac[ksrel_subspt, subspt_LN] >>
  disch_then (resolve_selected (el 2)) >> simp[] >>
  metis_tac[sga_subspt, subspt_LN])

val known_code_locs = Q.store_thm("known_code_locs",
  `∀xs vs g.
   code_locs (MAP FST (FST (known xs vs g))) = code_locs xs`,
  ho_match_mp_tac known_ind
  \\ rw[known_def]
  \\ rpt(pairarg_tac \\ fs[])
  \\ rw[code_locs_append]
  \\ fs[code_locs_def]
  \\ imp_res_tac known_sing_EQ_E \\ fs[]
  >- (every_case_tac >> simp[code_locs_def] >>
      rename[`isGlobal opn`, `gO_destApx apx`] >>
      Cases_on `opn` >> fs[isGlobal_def] >> Cases_on `apx` >>
      fs[gO_destApx_def, known_op_def, bool_case_eq, NULL_EQ, case_eq_thms] >> rveq >>
      imp_res_tac known_LENGTH_EQ_E >> fs[LENGTH_NIL_SYM, code_locs_def])
  \\ fs[code_locs_map]
  \\ AP_TERM_TAC
  \\ simp[MAP_MAP_o,MAP_EQ_f,FORALL_PROD]
  \\ rw[]
  \\ first_x_assum drule
  \\ qmatch_goalsub_abbrev_tac`FST p`
  \\ Cases_on`p` \\ fs[markerTheory.Abbrev_def]
  \\ pop_assum(assume_tac o SYM)
  \\ imp_res_tac known_sing_EQ_E \\ fs[]);

val compile_code_locs = Q.store_thm("compile_code_locs",
  `code_locs [compile b e] = code_locs [e]`,
  Cases_on`b` \\ rw[compile_def]
  \\ rpt(pairarg_tac \\ fs[])
  \\ pop_assum mp_tac
  \\ specl_args_of_then``known``known_code_locs mp_tac
  \\ rw[] \\ fs[]
  \\ pop_assum mp_tac
  \\ specl_args_of_then``known``known_code_locs mp_tac
  \\ rw[] \\ fs[]
  \\ imp_res_tac known_sing_EQ_E \\ fs[]);

val _ = export_theory();
