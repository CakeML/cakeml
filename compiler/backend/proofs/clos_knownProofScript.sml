open HolKernel Parse boolLib bossLib;

open preamble
open closPropsTheory clos_knownTheory
open bagTheory

val _ = new_theory "clos_knownProof";

val bool_case_eq = Q.prove(
  `COND b t f = v ⇔ b /\ v = t ∨ ¬b ∧ v = f`,
  srw_tac[][] >> metis_tac[]);

val pair_case_eq = Q.prove (
`pair_CASE x f = v ⇔ ?x1 x2. x = (x1,x2) ∧ f x1 x2 = v`,
 Cases_on `x` >>
 srw_tac[][]);

val va_case_eq =
    prove_case_eq_thm{case_def = TypeBase.case_def_of ``:val_approx``,
                      nchotomy = TypeBase.nchotomy_of ``:val_approx``}
val result_ty = ``:(α,β)semanticPrimitives$result``
val result_case_eq =
    prove_case_eq_thm{case_def = TypeBase.case_def_of result_ty,
                      nchotomy = TypeBase.nchotomy_of result_ty}
val error_ty = ``:α semanticPrimitives$error_result``
val error_case_eq =
    prove_case_eq_thm{case_def = TypeBase.case_def_of error_ty,
                      nchotomy = TypeBase.nchotomy_of error_ty}

val merge_Other = Q.store_thm(
  "merge_Other[simp]",
  `merge Other a = Other ∧ merge a Other = Other`,
  Cases_on `a` >> simp[]);

val known_LENGTH = Q.store_thm(
  "known_LENGTH",
  `∀es vs g. LENGTH (FST (known es vs g)) = LENGTH es`,
  ho_match_mp_tac known_ind >> simp[known_def] >> rpt strip_tac >>
  rpt (pairarg_tac >> fs[]))

val known_sing = Q.store_thm(
  "known_sing",
  `∀e vs g. ∃e' a g'. known [e] vs g = ([(e',a)], g')`,
  rpt strip_tac >> Cases_on `known [e] vs g` >>
  qcase_tac `known [e] vs g = (res,g')` >>
  qspecl_then [`[e]`, `vs`, `g`] mp_tac known_LENGTH >> simp[] >>
  Cases_on `res` >> simp[LENGTH_NIL] >> metis_tac[pair_CASES])

val _ = export_rewrites ["closLang.exp_size_def"]

val merge_Impossible = Q.store_thm(
  "merge_Impossible[simp]",
  `merge a Impossible = a`,
  Cases_on `a` >> simp[]);

(* See merge as a join operation on a semi-lattice: it's a join because it's
   a little akin to a union: as merge is used, more and more values might
   inhabit the approximation, with Other at the top corresponding to
   anything at all. *)
val merge_comm = Q.store_thm(
  "merge_comm",
  `∀a1 a2. merge a1 a2 = merge a2 a1`,
  ho_match_mp_tac merge_ind >> rpt strip_tac >> simp_tac(srw_ss()) [] >>
  COND_CASES_TAC >> simp[] >>
  simp[MAP2_MAP, MAP_EQ_EVERY2, LIST_REL_EL_EQN, EL_ZIP] >>
  metis_tac[MEM_EL]);

val merge_assoc = Q.store_thm(
  "merge_assoc",
  `∀a1 a2 a3. merge a1 (merge a2 a3) = merge (merge a1 a2) a3`,
  ho_match_mp_tac merge_ind >> rpt strip_tac >> Cases_on `a3` >>
  simp[] >> rw[LENGTH_MAP2]
  >- (simp[MAP2_MAP, MAP_EQ_EVERY2, LIST_REL_EL_EQN, EL_ZIP, EL_MAP] >>
      metis_tac[MEM_EL]) >>
  rw[])

val merge_idem = Q.store_thm(
  "merge_idem[simp]",
  `merge a a = a`,
  completeInduct_on `val_approx_size a` >> Cases_on `a` >>
  simp[val_approx_size_def] >> strip_tac >> fs[PULL_FORALL] >>
  simp[MAP2_MAP, MAP_EQ_ID] >> rpt strip_tac >> first_x_assum match_mp_tac >>
  rw[] >> Induct_on `l` >> dsimp[val_approx_size_def] >> rpt strip_tac >>
  res_tac >> simp[]);

val subapprox_def = Define`
  subapprox a1 a2 ⇔ merge a1 a2 = a2
`;

val _ = set_mapped_fixity { fixity = Infix(NONASSOC, 450),
                            term_name = "subapprox",
                            tok = "<:" }

val subapprox_refl = Q.store_thm(
  "subapprox_refl[simp]",
  `a <: a`,
  simp[subapprox_def]);

val subapprox_trans = Q.store_thm(
  "subapprox_trans",
  `a1 <: a2 ∧ a2 <: a3 ⇒ a1 <: a3`,
  simp[subapprox_def] >> metis_tac[merge_assoc]);

val subapprox_antisym = Q.store_thm(
  "subapprox_antisym",
  `a1 <: a2 ∧ a2 <: a1 ⇒ a1 = a2`,
  simp[subapprox_def] >> metis_tac[merge_comm]);

val subapprox_merge = Q.store_thm(
  "subapprox_merge[simp]",
  `a <: merge a b ∧ a <: merge b a`,
  simp[subapprox_def] >>
  metis_tac[merge_assoc, merge_comm, merge_idem]);

val subapprox_Other = Q.store_thm(
  "subapprox_Other[simp]",
  `(Other <: a ⇔ (a = Other)) ∧ a <: Other`,
  simp[subapprox_def] >> metis_tac[]);

val subapprox_Int = Q.store_thm(
  "subapprox_Int[simp]",
  `(a <: Int i ⇔ a = Int i ∨ a = Impossible) ∧
   (Int i <: a ⇔ a = Int i ∨ a = Other)`,
  simp[subapprox_def] >> Cases_on `a` >> simp[] >> rw[]);

val subapprox_Clos = Q.store_thm(
  "subapprox_Clos[simp]",
  `(a <: Clos m n ⇔ a = Clos m n ∨ a = Impossible) ∧
   (Clos m n <: a ⇔ a = Clos m n ∨ a = Other)`,
  simp[subapprox_def] >> Cases_on `a` >> simp[] >> rw[]);

val subapprox_Impossible = Q.store_thm(
  "subapprox_Impossible[simp]",
  `(a <: Impossible ⇔ a = Impossible) ∧ Impossible <: a`,
  simp[subapprox_def]);

val subapprox_Tuple = Q.store_thm(
  "subapprox_Tuple[simp]",
  `Tuple as1 <: Tuple as2 ⇔ LIST_REL subapprox as1 as2`,
  simp[subapprox_def, MAP2_MAP, LIST_REL_EL_EQN] >>
  Cases_on `LENGTH as1 = LENGTH as2` >> simp[LIST_EQ_REWRITE, EL_MAP, EL_ZIP]);

val better_definedg_def = Define`
  better_definedg g1 g2 ⇔
    ∀k. k ∈ domain g1 ⇒ k ∈ domain g2 ∧ lookup k g1 = lookup k g2
`;

val better_definedg_refl = Q.store_thm(
  "better_definedg_refl[simp]",
  `better_definedg g g`,
  simp[better_definedg_def]);

val better_definedg_trans = Q.store_thm(
  "better_definedg_trans",
  `better_definedg g1 g2 ∧ better_definedg g2 g3 ⇒ better_definedg g1 g3`,
  simp[better_definedg_def])

val opn_fresh_def = Define`
  (opn_fresh (SetGlobal n) g ⇔ n ∉ domain g) ∧
  (opn_fresh _ g ⇔ T)
`;

val known_op_better_definedg = Q.store_thm(
  "known_op_better_definedg",
  `known_op opn apxs g0 = (a,g) ∧ opn_fresh opn g0 ⇒ better_definedg g0 g`,
  Cases_on `opn` >>
  simp[known_op_def, pair_case_eq, eqs, va_case_eq, opn_fresh_def,
       bool_case_eq] >> rw[] >> rw[]
  >- (rw[better_definedg_def, lookup_insert] >> rw[] >> fs[])
  >- fs[GSYM lookup_NONE_domain]);

val exp_size_MEM = Q.store_thm(
  "exp_size_MEM",
  `(∀e elist. MEM e elist ⇒ exp_size e < exp3_size elist) ∧
   (∀x e ealist. MEM (x,e) ealist ⇒ exp_size e < exp1_size ealist)`,
  conj_tac >| [Induct_on `elist`, Induct_on `ealist`] >> dsimp[] >>
  rpt strip_tac >> res_tac >> simp[]);

val op_gbag_def = Define`
  op_gbag (SetGlobal n) = BAG_INSERT n {||} ∧
  op_gbag _ = {||}
`;

val opn_fresh_gbag = Q.store_thm(
  "opn_fresh_gbag",
  `opn_fresh opn g ⇔ DISJOINT (SET_OF_BAG (op_gbag opn)) (domain g)`,
  Cases_on `opn` >> simp[opn_fresh_def, op_gbag_def] >>
  simp[DISJOINT_DEF, SET_OF_BAG_INSERT, EXTENSION]);

val known_op_adds_gbag = Q.store_thm(
  "known_op_adds_gbag",
  `known_op opn apxs g0 = (apx,g) ⇒
   domain g ⊆ domain g0 ∪ SET_OF_BAG (op_gbag opn)`,
  Cases_on `opn` >> dsimp[known_op_def, op_gbag_def, eqs, va_case_eq] >> rw[] >>
  simp[domain_insert]);

val set_globals_def = tDefine "set_globals" `
  (set_globals (Var _) = {||}) ∧
  (set_globals (If e1 e2 e3) =
    set_globals e1 ⊎ set_globals e2 ⊎ set_globals e3) ∧
  (set_globals (Let binds e) =
    FOLDR $BAG_UNION (set_globals e) (MAP set_globals binds)) ∧
  (set_globals (Raise e) = set_globals e) ∧
  (set_globals (Handle e1 e2) = set_globals e1 ⊎ set_globals e2) ∧
  (set_globals (Tick e) = set_globals e) ∧
  (set_globals (Call _ args) = FOLDR $BAG_UNION {||} (MAP set_globals args)) ∧
  (set_globals (App _ f args) =
    FOLDR $BAG_UNION (set_globals f) (MAP set_globals args)) ∧
  (set_globals (Fn _ _ _ bod) = set_globals bod) ∧
  (set_globals (Letrec _ _ fbinds bod) =
    FOLDR (λne s. set_globals (SND ne) ⊎ s) (set_globals bod) fbinds) ∧
  (set_globals (Op opn args) =
    FOLDR $BAG_UNION (op_gbag opn) (MAP set_globals args))
`
  (WF_REL_TAC `measure exp_size` >> simp[] >> rpt strip_tac >>
   imp_res_tac exp_size_MEM >> simp[])

val elist_globals_def = Define`
  elist_globals es = FOLDR BAG_UNION {||} (MAP set_globals es)
`;
val elist_globals_thm = Q.store_thm(
  "elist_globals_thm[simp]",
  `elist_globals [] = {||} ∧
   elist_globals (exp::rest) = set_globals exp ⊎ elist_globals rest`,
  simp[elist_globals_def]);
val FOLDR_BAG_UNION_extract_acc = Q.store_thm(
  "FOLDR_BAG_UNION_extract_acc",
  `∀l a b. a ⊎ FOLDR (BAG_UNION o f) b l = FOLDR (BAG_UNION o f) (a ⊎ b) l`,
  Induct_on `l` >> simp[] >> metis_tac[COMM_BAG_UNION, ASSOC_BAG_UNION])

val foldr_bu =
    FOLDR_BAG_UNION_extract_acc |> SPEC_ALL
                                |> INST_TYPE [alpha |-> ``:β bag``]
                                |> Q.INST [`b` |-> `{||}`, `f` |-> `I`]
                                |> SIMP_RULE (srw_ss()) []
                                |> GSYM

val foldr_bu' =
    FOLDR_BAG_UNION_extract_acc |> SPEC_ALL
                                |> Q.INST [`b` |-> `{||}`, `f` |-> `λa. g a`]
                                |> SIMP_RULE (srw_ss()) [o_ABS_R]
                                |> GSYM


val set_globals_def = save_thm("set_globals_def[simp]",
  set_globals_def |> ONCE_REWRITE_RULE [foldr_bu]
                  |> SIMP_RULE (srw_ss() ++ ETA_ss) [GSYM elist_globals_def])
val set_globals_ind = theorem "set_globals_ind"

val FINITE_BAG_FOLDR = Q.store_thm(
  "FINITE_BAG_FOLDR",
  `∀l f a.
     FINITE_BAG a ∧ (∀e a. FINITE_BAG a ∧ MEM e l ⇒ FINITE_BAG (f e a)) ⇒
     FINITE_BAG (FOLDR f a l)`,
  Induct >> simp[]);

val FINITE_set_globals = Q.store_thm(
  "FINITE_set_globals[simp]",
  `∀e. FINITE_BAG (set_globals e)`,
  ho_match_mp_tac set_globals_ind >> simp[elist_globals_def] >> rpt strip_tac >>
  TRY (irule FINITE_BAG_FOLDR >> dsimp[MEM_MAP] >> NO_TAC) >>
  qcase_tac `op_gbag opn` >> Cases_on `opn` >> simp[op_gbag_def]);

val FINITE_BAG_elist_globals = Q.store_thm(
  "FINITE_BAG_elist_globals[simp]",
  `FINITE_BAG (elist_globals es)`,
  Induct_on `es` >> fs[]);

val known_better_definedg = Q.store_thm(
  "known_better_definedg",
  `∀es apxs g0 alist g.
     known es apxs g0 = (alist, g) ∧ BAG_ALL_DISTINCT (elist_globals es) ∧
     DISJOINT (domain g0) (SET_OF_BAG (elist_globals es)) ⇒
     better_definedg g0 g ∧
     domain g ⊆ SET_OF_BAG (elist_globals es) ∪ domain g0`,
  ho_match_mp_tac known_ind >>
  simp[known_def, BAG_ALL_DISTINCT_BAG_UNION, SET_OF_BAG_UNION] >>
  rpt conj_tac >> rpt (gen_tac ORELSE disch_then strip_assume_tac) >>
  rpt (pairarg_tac >> fs[]) >> rveq >> fs[DISJOINT_SYM, BAG_DISJOINT]
  >- (qhdtm_x_assum `$==>` mp_tac >>
      impl_tac >- (fs[DISJOINT_DEF, EXTENSION, SUBSET_DEF] >> metis_tac[]) >>
      rpt strip_tac >- metis_tac[better_definedg_trans] >>
      fs[SUBSET_DEF] >> metis_tac[])
  >- (qcase_tac `known [guard] apxs g0 = (ga,g1)` >>
      qcase_tac `known [tb] apxs g1 = (ta,g2)` >>
      qpat_assum `DISJOINT (domain g1) (SET_OF_BAG (set_globals tb)) ⇒ _`
                 mp_tac >>
      impl_tac >- (fs[DISJOINT_DEF, EXTENSION, SUBSET_DEF] >> metis_tac[]) >>
      strip_tac >> qhdtm_x_assum `$==>` mp_tac >>
      impl_tac >- (fs[DISJOINT_DEF, EXTENSION, SUBSET_DEF] >> metis_tac[]) >>
      rpt strip_tac >- metis_tac[better_definedg_trans] >>
      fs[SUBSET_DEF] >> metis_tac[])
  >- (qhdtm_x_assum `$==>` mp_tac >>
      impl_tac >- (fs[DISJOINT_DEF, EXTENSION, SUBSET_DEF] >> metis_tac[]) >>
      rpt strip_tac >- metis_tac[better_definedg_trans] >>
      fs[SUBSET_DEF] >> metis_tac[])
  >- (qhdtm_x_assum `$==>` mp_tac >>
      impl_tac >- (fs[DISJOINT_DEF, EXTENSION, SUBSET_DEF] >> metis_tac[]) >>
      rpt strip_tac >- metis_tac[better_definedg_trans] >>
      fs[SUBSET_DEF] >> metis_tac[])
  >- ((* op case *)
      qcase_tac `known_op opn _ g1 = (aa, gg)` >>
      `opn_fresh opn g1`
        by (simp[opn_fresh_gbag] >> fs[DISJOINT_DEF, EXTENSION, SUBSET_DEF] >>
            metis_tac[]) >>
      conj_tac >- metis_tac[known_op_better_definedg, better_definedg_trans] >>
      imp_res_tac known_op_adds_gbag >> fs[SUBSET_DEF] >> metis_tac[])
  >- (qhdtm_x_assum `$==>` mp_tac >>
      impl_tac >- (fs[DISJOINT_DEF, EXTENSION, SUBSET_DEF] >> metis_tac[]) >>
      rpt strip_tac >- metis_tac[better_definedg_trans] >>
      fs[SUBSET_DEF] >> metis_tac[])
  >- (RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [Once foldr_bu']) >>
      fs[BAG_ALL_DISTINCT_BAG_UNION, SET_OF_BAG_UNION, DISJOINT_SYM] >>
      simp_tac (srw_ss()) [Once foldr_bu'] >>
      simp[SET_OF_BAG_UNION] >> fs[SUBSET_DEF] >> metis_tac[]))

val val_approx_val_def = tDefine "val_approx_val" `
  (val_approx_val (Clos n m) v ⇔ ∃e1 e2 b. v = Closure (SOME n) e1 e2 m b) ∧
  (val_approx_val (Tuple vas) v ⇔
    ∃n vs. v = Block n vs ∧ LIST_REL (λv va. val_approx_val v va) vas vs) ∧
  (val_approx_val Impossible v ⇔ F) ∧
  (val_approx_val (Int i) v ⇔ v = Number i) ∧
  (val_approx_val Other v ⇔ T)
` (WF_REL_TAC `measure (val_approx_size o FST)` >> simp[] >> Induct >>
   dsimp[val_approx_size_def] >> rpt strip_tac >> res_tac >> simp[])

val val_approx_val_def = save_thm(
  "val_approx_val_def[simp]",
  val_approx_val_def |> SIMP_RULE (srw_ss() ++ ETA_ss) []);

val any_el_ALT = Q.store_thm(
  "any_el_ALT",
  `∀l n d. any_el n l d = if n < LENGTH l then EL n l else d`,
  Induct_on `l` >> simp[any_el_def] >> Cases_on `n` >> simp[] >> rw[] >>
  fs[]);

val val_approx_val_merge_I = Q.store_thm(
  "val_approx_val_merge_I",
  `∀a1 v a2.
     val_approx_val a1 v ∨ val_approx_val a2 v ⇒
     val_approx_val (merge a1 a2) v`,
  ho_match_mp_tac (theorem "val_approx_val_ind") >>
  simp[] >> rpt strip_tac >> Cases_on `a2` >> simp[] >> fs[] >> rw[] >>
  fs[LIST_REL_EL_EQN, LENGTH_MAP2, MAP2_MAP, EL_MAP, EL_ZIP] >>
  metis_tac[MEM_EL])

val evaluate_list_members_individually = Q.store_thm(
  "evaluate_list_members_individually",
  `∀es env (s0:'a closSem$state) vs s.
     closSem$evaluate (es, env, s0) = (Rval vs, s) ⇒
     ∀n. n < LENGTH es ⇒
         ∃(s0':'a closSem$state) s'.
           evaluate([EL n es], env, s0') = (Rval [EL n vs], s')`,
  Induct >> simp[] >> Cases_on `es` >> fs[]
  >- (rpt strip_tac >> qcase_tac `evaluate ([exp], env, _)` >>
      `∃v. vs = [v]` by metis_tac[evaluate_SING] >> rw[] >> metis_tac[]) >>
  dsimp[closSemTheory.evaluate_def, pair_case_eq, result_case_eq] >>
  rpt strip_tac >> reverse (Cases_on `n` >> fs[]) >- metis_tac[] >>
  imp_res_tac evaluate_SING >> rw[] >> metis_tac[]);

val val_approx_better_approx = Q.store_thm(
  "val_approx_better_approx",
  `∀a1 v a2.
     a1 <: a2 ∧ val_approx_val a1 v ⇒ val_approx_val a2 v`,
  ho_match_mp_tac (theorem "val_approx_val_ind") >> dsimp[] >> rpt gen_tac >>
  qcase_tac `Tuple a2s <: apx2` >>
  Cases_on `apx2` >> dsimp[] >> simp[LIST_REL_EL_EQN] >> metis_tac[MEM_EL]);


val state_globals_approx_def = Define`
  state_globals_approx s g ⇔
    ∀k v a.
      lookup k g = SOME a ∧ get_global k s.globals = SOME (SOME v) ⇒
      val_approx_val a v
`;

(*
val state_approx_better_definedg = Q.store_thm(
  "state_approx_better_definedg",
  `better_definedg g1 g2 ∧ state_globals_approx s g1 ⇒
   state_globals_approx s g2`,
  simp[better_definedg_def, state_globals_approx_def] >> rpt strip_tac >>
  qcase_tac `lookup k g1 = SOME a` >>
  `k ∈ domain g1` by metis_tac[domain_lookup] >>
  `∃a'. lookup k g2 = SOME a' ∧ a <: a'` by metis_tac[domain_lookup, THE_DEF] >>



val eval_approx_def = Define`
  eval_approx g0 EA (:'ffi) es as ⇔
    ∀s0 env vs (s:'ffi closSem$state).
       evaluate(es, env, s0) = (Rval vs, s) ∧ state_globals_approx s0 g0 ∧
       LIST_REL val_approx_val EA env ⇒
       LIST_REL val_approx_val as vs
`;

val eval_approx_nil = Q.store_thm(
  "eval_approx_nil[simp]",
  `eval_approx g as (:'a) [] []`,
  simp[eval_approx_def, closSemTheory.evaluate_def]);

val evaluate_eq_nil = Q.store_thm(
  "evaluate_eq_nil[simp]",
  `closSem$evaluate(es,env,s0) = (Rval [], s) ⇔ s0 = s ∧ es = []`,
  Cases_on `es` >> simp[closSemTheory.evaluate_def] >>
  strip_tac >> qcase_tac `evaluate(h::t, env, s0)` >>
  Q.ISPECL_THEN [`h::t`, `env`, `s0`] mp_tac (CONJUNCT1 evaluate_LENGTH) >>
  simp[]);

val eval_approx_better_definedg = Q.store_thm(
  "eval_approx_better_definedg",
  `eval_approx g0 EA (:'a) exps apxs ∧ better_definedg g0 g ⇒
   eval_approx


val known_op_correct_approx = Q.store_thm(
  "known_op_correct_approx",
  `∀opn es apxs g0 a g EA.
      known_op opn apxs g0 = (a, g) ∧
      eval_approx g0 EA (:'a) es (REVERSE apxs) ⇒
      eval_approx g EA (:'a) [Op opn es] [a]`,
  Cases >> simp[eval_approx_def] >>
  dsimp[closSemTheory.evaluate_def, result_case_eq, pair_case_eq,
        closSemTheory.do_app_def, eqs, known_op_def]
  >- (simp[state_globals_approx_def, closSemTheory.get_global_def] >>
      rw[] >> metis_tac[])
  >- metis_tac[EVERY2_REVERSE1]
  >- (dsimp[va_case_eq, eqs, bool_case_eq] >> rpt strip_tac >>
      qcase_tac `closSem$evaluate (exps, ENV, S0) = (Rval vals, S1)` >>
      first_x_assum (qspecl_then [`S0`, `ENV`, `vals`, `S1`] mp_tac) >>
      simp[] >> strip_tac >> fs[] >> rw[] >> fs[LIST_REL_EL_EQN]))


val known_correct_approx = Q.store_thm(
  "known_correct_approx",
  `∀es as g0 all g.
     known es as g0 = (all,g) ⇒
     eval_approx g0 as (:'a) es (MAP SND all) ∧
     eval_approx g as (:'a) es (MAP SND all)`,
     ∀e a vs s0 s v.
        MEM (e,a) all ∧ LIST_REL val_approx_val as vs ∧
        evaluate([e], vs, s0) = (Rval [v], s) ⇒
        val_approx_val a v`,
  ho_match_mp_tac known_ind >> simp[known_def] >> rpt strip_tac
  >- (qcase_tac `known [exp1] as g0` >>
      `∃exp1' a1 g1. known [exp1] as g0 = ([(exp1',a1)], g1)`
         by metis_tac[known_sing] >> fs[] >>
      qcase_tac `known (exp2::erest) as g1` >>
      `∃arest g2. known (exp2::erest) as g1 = (arest, g2)`
         by metis_tac[pair_CASES] >> fs[] >> rw[] >> fs[] >> metis_tac[])
  >- (fs[any_el_ALT, closSemTheory.evaluate_def, bool_case_eq] >>
      fs[LIST_REL_EL_EQN])
  >- (qcase_tac `known [ge] as g0` >>
      `∃ge' a1 g1. known [ge] as g0 = ([(ge',a1)], g1)`
         by metis_tac[known_sing] >> fs[] >>
      qcase_tac `known [tb] as g1` >>
      `∃tb' a2 g2. known [tb] as g1 = ([(tb',a2)], g2)`
         by metis_tac[known_sing] >> fs[] >>
      qcase_tac `known [eb] as g2` >>
      `∃eb' a3 g3. known [eb] as g2 = ([(eb',a3)], g3)`
         by metis_tac[known_sing] >> fs[] >> rw[] >> fs[] >> rw[] >>
      fs[closSemTheory.evaluate_def, pair_case_eq, result_case_eq,
         bool_case_eq] >> metis_tac[val_approx_val_merge_I])
  >- ((* let *) qcase_tac `known binds as g0` >>
      `∃al1 g1. known binds as g0 = (al1,g1)` by metis_tac[pair_CASES] >>
      fs[] >>
      qcase_tac `known [bod] (MAP SND al1 ++ as) g1` >>
      `∃bod' ba g2. known [bod] (MAP SND al1 ++ as) g1 = ([(bod',ba)], g2)`
        by metis_tac [known_sing] >> fs[] >> rw[] >> fs[] >> rw[] >>
      fs[closSemTheory.evaluate_def, pair_case_eq, result_case_eq] >> rw[] >>
      qcase_tac `evaluate (MAP FST al1,vs,s0) = (Rval res1, s1)` >>
      `LENGTH res1 = LENGTH al1`
        by (Q.ISPECL_THEN [`MAP FST al1`, `vs`, `s0`] mp_tac
                          (evaluate_LENGTH |> CONJUNCT1) >> simp[]) >>
      first_x_assum (qspecl_then [`res1 ++ vs`, `s1`, `s`, `v`] mp_tac) >>
      impl_tac >> simp[] >> irule EVERY2_APPEND_suff >> simp[] >>
      simp[LIST_REL_EL_EQN, EL_MAP] >> rpt strip_tac >> first_x_assum irule >>
      simp[] >>
      qspecl_then [`MAP FST al1`, `vs`, `s0`, `res1`, `s1`] mp_tac
        evaluate_list_members_individually >> simp[] >>
      disch_then (qspec_then `n` mp_tac) >> simp[EL_MAP] >>
      metis_tac[PAIR, MEM_EL])
  >- ((* raise *) qcase_tac `known [exp1] as g0` >>
      `∃exp' ea g1. known [exp1] as g0 = ([(exp',ea)], g1)`
        by metis_tac [known_sing] >> fs[] >> rw[] >> fs[] >> rw[] >>
      fs[closSemTheory.evaluate_def, pair_case_eq, result_case_eq])
  >- ((* tick *) qcase_tac `known [exp1] as g0` >>
      `∃exp' ea g1. known [exp1] as g0 = ([(exp',ea)], g1)`
        by metis_tac [known_sing] >> fs[] >> rw[] >> fs[] >> rw[] >>
      fs[closSemTheory.evaluate_def, pair_case_eq, result_case_eq,
         bool_case_eq] >> metis_tac[])
  >- ((* handle *) qcase_tac `known [exp1] as g0` >>
      `∃exp1' ea1 g1. known [exp1] as g0 = ([(exp1',ea1)], g1)`
        by metis_tac [known_sing] >> fs[] >> rw[] >>
      qcase_tac `known [exp2] (Other::as) g1` >>
      `∃exp2' ea2 g2. known [exp2] (Other::as) g1 = ([(exp2',ea2)], g2)`
        by metis_tac [known_sing] >> fs[] >> rw[] >> fs[] >> rw[] >>
      fs[closSemTheory.evaluate_def, pair_case_eq, result_case_eq,
         error_case_eq] >> rw[] >- metis_tac[val_approx_val_merge_I] >>
      irule val_approx_val_merge_I >> disj2_tac >> first_x_assum irule >>
      dsimp[] >> metis_tac[])
  >- ((* call *) qcase_tac `known exps as g0` >>
      `∃al1 g1. known exps as g0 = (al1, g1)` by metis_tac[pair_CASES] >>
      fs[] >> rw[] >> fs[])
  >- ((* op *) qcase_tac `known exps as g0` >>
      `∃al1 g1. known exps as g0 = (al1, g1)` by metis_tac[pair_CASES] >>
      fs[] >> rw[] >> fs[]
  >> cheat )



*)

val _ = export_theory();
