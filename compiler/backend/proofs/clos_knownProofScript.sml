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

(* MOVE candidates *)
val evaluate_eq_nil = Q.store_thm(
  "evaluate_eq_nil[simp]",
  `closSem$evaluate(es,env,s0) = (Rval [], s) ⇔ s0 = s ∧ es = []`,
  Cases_on `es` >> simp[closSemTheory.evaluate_def] >>
  strip_tac >> qcase_tac `evaluate(h::t, env, s0)` >>
  Q.ISPECL_THEN [`h::t`, `env`, `s0`] mp_tac (CONJUNCT1 evaluate_LENGTH) >>
  simp[]);

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

(* simple properties of constants from clos_known: i.e., merge and known *)

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

val _ = overload_on ("<:", ``subapprox``)

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
    ∀k. k ∈ domain g1 ⇒ k ∈ domain g2 ∧ THE (lookup k g1) <: THE (lookup k g2)
`;

val better_definedg_refl = Q.store_thm(
  "better_definedg_refl[simp]",
  `better_definedg g g`,
  simp[better_definedg_def]);

val better_definedg_trans = Q.store_thm(
  "better_definedg_trans",
  `better_definedg g1 g2 ∧ better_definedg g2 g3 ⇒ better_definedg g1 g3`,
  simp[better_definedg_def] >> metis_tac[subapprox_trans])

val opn_fresh_def = Define`
  (opn_fresh (SetGlobal n) g ⇔ n ∉ domain g) ∧
  (opn_fresh _ g ⇔ T)
`;

val known_op_better_definedg = Q.store_thm(
  "known_op_better_definedg",
  `known_op opn apxs g0 = (a,g) ⇒ better_definedg g0 g`,
  Cases_on `opn` >>
  simp[known_op_def, pair_case_eq, eqs, va_case_eq, opn_fresh_def,
       bool_case_eq] >> rw[] >> rw[better_definedg_def, lookup_insert] >>
  rw[] >> fs[lookup_NONE_domain])

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
     known es apxs g0 = (alist, g) ⇒ better_definedg g0 g`,
  ho_match_mp_tac known_ind >> simp[known_def] >> rpt strip_tac >>
  rpt (pairarg_tac >> fs[]) >> rw[] >>
  metis_tac[better_definedg_trans, known_op_better_definedg]);

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

(* would be nice to have something akin to
val state_approx_better_definedg = Q.store_thm(
  "state_approx_better_definedg",
  `better_definedg g1 g2 ∧ state_globals_approx s g1 ⇒
   state_globals_approx s g2`, ...)

but this is not true without also knowing that the extra approximations in g2
are valid

*)

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

val known_preserves_gwf = Q.store_thm(
  "known_preserves_gwf",
  `∀exps apxs g0 alist g. known exps apxs g0 = (alist,g) ∧ wf g0 ⇒ wf g`,
  ho_match_mp_tac known_ind >> simp[known_def] >> rpt strip_tac >>
  rpt (pairarg_tac >> fs[]) >> rw[] >> qcase_tac `known_op opn` >>
  Cases_on `opn` >> fs[known_op_def, eqs, va_case_eq, bool_case_eq] >>
  rw[wf_insert]);

val mapped_globals_def = Define`
  mapped_globals (s:'a closSem$state) =
    { i | ∃v. get_global i s.globals = SOME (SOME v) }
`;

val mapped_globals_refupdate = Q.store_thm(
  "mapped_globals_refupdate[simp]",
  `mapped_globals (s with refs := v) = mapped_globals s`,
  simp[mapped_globals_def]);

val mapped_globals_ffiupdate = Q.store_thm(
  "mapped_globals_ffiupdate[simp]",
  `mapped_globals (s with ffi := v) = mapped_globals s`,
  simp[mapped_globals_def]);

val mapped_globals_dec_clock = Q.store_thm(
  "mapped_globals_dec_clock[simp]",
  `mapped_globals (dec_clock n s) = mapped_globals s`,
  simp[mapped_globals_def, closSemTheory.dec_clock_def])

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

val state_globals_approx_dec_clock = Q.store_thm(
  "state_globals_approx_dec_clock[simp]",
  `state_globals_approx (dec_clock n s) g ⇔ state_globals_approx s g`,
  simp[state_globals_approx_def, closSemTheory.dec_clock_def]);

val v_size_lemma = prove(
  ``MEM (v:closSem$v) vl ⇒ v_size v < v1_size vl``,
  Induct_on `vl` >> dsimp[closSemTheory.v_size_def] >> rpt strip_tac >>
  res_tac >> simp[]);

(* value is setglobal-closure free *)
val vsgc_free_def = tDefine "vsgc_free" `
  (vsgc_free (Closure _ VL1 VL2 _ body) ⇔
     set_globals body = {||} ∧
     EVERY vsgc_free VL1 ∧ EVERY vsgc_free VL2) ∧
  (vsgc_free (Recclosure _ VL1 VL2 bods _) ⇔
     elist_globals (MAP SND bods) = {||} ∧
     EVERY vsgc_free VL1 ∧ EVERY vsgc_free VL2) ∧
  (vsgc_free (Block _ VL) ⇔ EVERY vsgc_free VL) ∧
  (vsgc_free _ ⇔ T)
` (WF_REL_TAC `measure closSem$v_size` >> simp[closSemTheory.v_size_def] >>
   rpt strip_tac >> imp_res_tac v_size_lemma >> simp[])

val vsgc_free_def = save_thm(
  "vsgc_free_def[simp]",
  SIMP_RULE (bool_ss ++ ETA_ss) [] vsgc_free_def)

val vsgc_free_Unit = Q.store_thm(
  "vsgc_free_Unit[simp]",
  `vsgc_free Unit`,
  simp[closSemTheory.Unit_def]);

val vsgc_free_Boolv = Q.store_thm(
  "vsgc_free_Boolv[simp]",
  `vsgc_free (Boolv b)`,
  simp[closSemTheory.Boolv_def]);

(* result is setglobal-closure free *)
val rsgc_free_def = Define`
  (rsgc_free (Rval vs) ⇔ EVERY vsgc_free vs) ∧
  (rsgc_free (Rerr (Rabort _)) ⇔ T) ∧
  (rsgc_free (Rerr (Rraise v)) ⇔ vsgc_free v)
`;
val _ = export_rewrites ["rsgc_free_def"]

(* state is setglobal-closure free *)
val ssgc_free_def = Define`
  ssgc_free (s:'a closSem$state) ⇔
    (∀n m e. FLOOKUP s.code n = SOME (m,e) ⇒ set_globals e = {||}) ∧
    (∀n vl. FLOOKUP s.refs n = SOME (ValueArray vl) ⇒ EVERY vsgc_free vl) ∧
    (∀v. MEM (SOME v) s.globals ⇒ vsgc_free v)
`;

val esgc_free_def = tDefine "esgc_free" `
  (esgc_free (Var _) ⇔ T) ∧
  (esgc_free (If e1 e2 e3) ⇔ esgc_free e1 ∧ esgc_free e2 ∧ esgc_free e3) ∧
  (esgc_free (Let binds e) ⇔ EVERY esgc_free binds ∧ esgc_free e) ∧
  (esgc_free (Raise e) ⇔ esgc_free e) ∧
  (esgc_free (Handle e1 e2) ⇔ esgc_free e1 ∧ esgc_free e2) ∧
  (esgc_free (Tick e) ⇔ esgc_free e) ∧
  (esgc_free (Call _ args) ⇔ EVERY esgc_free args) ∧
  (esgc_free (App _ e args) ⇔ esgc_free e ∧ EVERY esgc_free args) ∧
  (esgc_free (Fn _ _ _ b) ⇔ set_globals b = {||}) ∧
  (esgc_free (Letrec _ _ binds bod) ⇔
    elist_globals (MAP SND binds) = {||} ∧ esgc_free bod) ∧
  (esgc_free (Op _ args) ⇔ EVERY esgc_free args)
` (WF_REL_TAC `measure exp_size` >> simp[] >> rpt strip_tac >>
   imp_res_tac exp_size_MEM >> simp[])
val esgc_free_def = save_thm("esgc_free_def[simp]",
  SIMP_RULE (bool_ss ++ ETA_ss) [] esgc_free_def)

val value_ind =
  TypeBase.induction_of ``:closSem$v``
   |> Q.SPECL [`P`, `EVERY P`]
   |> SIMP_RULE (srw_ss()) []
   |> UNDISCH |> CONJUNCT1 |> DISCH_ALL |> Q.GEN `P`


val do_app_ssgc = Q.store_thm(
  "do_app_ssgc",
  `∀opn args s0 res.
     do_app opn args s0 = res ⇒
     EVERY vsgc_free args ∧ ssgc_free s0 ⇒
     (∀v s. res = Rval(v,s) ⇒
            vsgc_free v ∧ ssgc_free s ∧
            mapped_globals s ⊆ mapped_globals s0 ∪ SET_OF_BAG (op_gbag opn)) ∧
     (∀v. res = Rerr (Rraise v) ⇒ vsgc_free v)`,
  Cases_on `opn` >>
  simp[closSemTheory.do_app_def, eqs, op_gbag_def, PULL_EXISTS, bool_case_eq,
       pair_case_eq]
  >- ((* GetGlobal *)
      simp[closSemTheory.get_global_def, ssgc_free_def] >> metis_tac[MEM_EL])
  >- ((* SetGlobal *)
      simp[ssgc_free_def, mapped_globals_def]>> rpt strip_tac
      >- metis_tac[]
      >- metis_tac[]
      >- (fs[MEM_LUPDATE] >> metis_tac[MEM_EL])
      >- (dsimp[SUBSET_DEF, closSemTheory.get_global_def,
               EL_LUPDATE, bool_case_eq] >> metis_tac[]))
  >- (dsimp[ssgc_free_def, mapped_globals_def, SUBSET_DEF,
            closSemTheory.get_global_def, EL_APPEND_EQN, bool_case_eq] >>
      reverse (rpt strip_tac)
      >- (qcase_tac `ii < LENGTH (ss:α closSem$state).globals` >>
          Cases_on `ii < LENGTH ss.globals` >> simp[] >>
          Cases_on `ii - LENGTH ss.globals = 0`
          >- (pop_assum SUBST_ALL_TAC >> simp[]) >> simp[]) >>
      metis_tac[])
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
  >- (simp[PULL_FORALL] >> rpt gen_tac >> qcase_tac `v_to_list v = SOME vs` >>
      map_every qid_spec_tac [`vs`, `v`] >> ho_match_mp_tac value_ind >>
      simp[closSemTheory.v_to_list_def] >> Cases >>
      simp[closSemTheory.v_to_list_def] >>
      qcase_tac `closSem$Block _ (v1::vs)` >> Cases_on `vs` >>
      simp[closSemTheory.v_to_list_def] >>
      qcase_tac `closSem$Block _ (v1::v2::vs)` >> Cases_on `vs` >>
      simp[closSemTheory.v_to_list_def, eqs, PULL_EXISTS, PULL_FORALL])
  >- (simp[PULL_FORALL] >> rpt gen_tac >> qcase_tac `EVERY vsgc_free vs` >>
      Induct_on `vs` >> simp[closSemTheory.list_to_v_def])
  >- (dsimp[ssgc_free_def, FLOOKUP_UPDATE, bool_case_eq] >> metis_tac[])
  >- (dsimp[ssgc_free_def] >>
      metis_tac[MEM_EL, EVERY_MEM, integerTheory.INT_INJ,
                integerTheory.INT_OF_NUM, integerTheory.INT_LT])
  >- (dsimp[ssgc_free_def, FLOOKUP_UPDATE, bool_case_eq] >>
      rpt strip_tac
      >- metis_tac[]
      >- (irule IMP_EVERY_LUPDATE >> simp[] >> metis_tac[])
      >- metis_tac[])
  >- (dsimp[ssgc_free_def, FLOOKUP_UPDATE, bool_case_eq] >> metis_tac[]))

val ssgc_evaluate = Q.store_thm(
  "ssgc_evaluate",
  `(∀a es env (s0:α closSem$state) res s.
      ssgc_free s0 ∧ EVERY vsgc_free env ∧
      EVERY esgc_free es ∧ a = (es,env,s0) ∧
      evaluate a = (res,s) ⇒
      ssgc_free s ∧ rsgc_free res ∧
      mapped_globals s ⊆ mapped_globals s0 ∪ SET_OF_BAG (elist_globals es)) ∧
   (∀lopt f args (s0:α closSem$state) res s.
      ssgc_free s0 ∧ vsgc_free f ∧ EVERY vsgc_free args ∧
      evaluate_app lopt f args s0 = (res, s) ⇒
      ssgc_free s ∧ rsgc_free res ∧
      mapped_globals s = mapped_globals s0)`,
  ho_match_mp_tac closSemTheory.evaluate_ind >> rpt conj_tac >> simp[]
  >- (* nil *) simp[closSemTheory.evaluate_def]
  >- ((* cons *) rpt gen_tac >> strip_tac >>
      simp[closSemTheory.evaluate_def, pair_case_eq, result_case_eq,
           PULL_EXISTS] >>
      qcase_tac `evaluate([e1], env, s0)` >>
      rpt gen_tac >> strip_tac >> rveq >> fs[]
      >- (imp_res_tac evaluate_SING >> rveq >> fs[] >>
          fs[SET_OF_BAG_UNION, SUBSET_DEF] >> metis_tac[])
      >- (fs[SET_OF_BAG_UNION, SUBSET_DEF] >> metis_tac[])
      >- (fs[SET_OF_BAG_UNION, SUBSET_DEF] >> metis_tac[]))
  >- ((* var *) simp[closSemTheory.evaluate_def] >> rw[] >> rw[] >>
      metis_tac[EVERY_MEM, MEM_EL])
  >- ((* If *) rpt gen_tac >> strip_tac >>
      simp[closSemTheory.evaluate_def, pair_case_eq, result_case_eq,
           bool_case_eq] >>
      rpt gen_tac >> strip_tac >> rveq >> fixeqs >>
      fs[SUBSET_DEF, SET_OF_BAG_UNION] >> metis_tac[])
  >- ((* let *) rpt gen_tac >> strip_tac >>
      simp[closSemTheory.evaluate_def, pair_case_eq, result_case_eq] >>
      rpt gen_tac >> strip_tac >> rveq >> fs[SUBSET_DEF, SET_OF_BAG_UNION] >>
      metis_tac[])
  >- ((* raise *) rpt gen_tac >> strip_tac >>
      simp[closSemTheory.evaluate_def, pair_case_eq, result_case_eq] >>
      rpt gen_tac >> strip_tac >> rveq >> fs[SUBSET_DEF, SET_OF_BAG_UNION] >>
      metis_tac[evaluate_SING, HD, EVERY_DEF])
  >- ((* handle *) rpt gen_tac >> strip_tac >>
      simp[closSemTheory.evaluate_def, pair_case_eq, result_case_eq,
           error_case_eq] >>
      rpt gen_tac >> strip_tac >> rveq >> fs[SUBSET_DEF, SET_OF_BAG_UNION] >>
      metis_tac[])
  >- ((* op *) rpt gen_tac >> strip_tac >>
      simp[closSemTheory.evaluate_def, pair_case_eq, result_case_eq] >>
      rpt gen_tac >> strip_tac >> rveq >> fs[]
      >- (IMP_RES_THEN mp_tac do_app_ssgc >> simp[EVERY_REVERSE] >>
          fs[SUBSET_DEF, SET_OF_BAG_UNION] >> metis_tac[])
      >- (IMP_RES_THEN mp_tac do_app_ssgc >> simp[EVERY_REVERSE] >>
          qcase_tac `Rerr err` >> Cases_on `err` >> simp[] >>
          fs[SUBSET_DEF, SET_OF_BAG_UNION] >> metis_tac[])
      >- (fs[SUBSET_DEF, SET_OF_BAG_UNION] >> metis_tac[]))
  >- ((* Fn *) cheat)
  >- ((* Letrec *) cheat)
  >- ((* App *) cheat)
  >- ((* Tick *) cheat)
  >- ((* Call *) cheat)
  >- ((* evaluate_app *) cheat))


(*
val known_correct_approx = Q.store_thm(
  "known_correct_approx",
  `∀es as g0 all g.
     known es as g0 = (all,g) ⇒
     ∀env s0 s vs result.
        LIST_REL val_approx_val as env ∧
        state_globals_approx s0 g0 ∧
        evaluate(MAP FST all, env, s0) = (result, s) ⇒
        state_globals_approx s g ∧
        ∀vs. result = Rval vs ⇒ LIST_REL val_approx_val (MAP SND all) vs`,
  ho_match_mp_tac known_ind >> simp[known_def] >>
  rpt conj_tac >> rpt (gen_tac ORELSE disch_then strip_assume_tac)
  >- (* nil *) (fs[closSemTheory.evaluate_def] >> rw[])
  >- (rpt (pairarg_tac >> fs[]) >> rveq >>
      qcase_tac `known [exp1] as g0` >>
      `∃exp1' a1 g1. known [exp1] as g0 = ([(exp1',a1)], g1)`
         by metis_tac[known_sing] >> fs[] >> rveq >> fs[] >>
      qcase_tac `known [exp1] EA g0 = ([(exp1',a1)], g1)` >>
      qcase_tac `known (exp2::erest) EA g1 = (al2,g)` >>
      `LENGTH al2 = LENGTH (exp2::erest)` by metis_tac[known_LENGTH, FST] >>
      fs[] >>
      `∃exp2' a2 arest. al2 = (exp2',a2)::arest`
        by (Cases_on `al2` >> fs[] >> metis_tac[pair_CASES]) >> rveq >>
      fs[closSemTheory.evaluate_def, pair_case_eq, result_case_eq] >> rveq
      >- (qcase_tac `evaluate ([exp1'], env, s0) = (Rval v1, s1)` >>
          first_x_assum (fn th =>
            qspecl_then [`env`, `s0`, `s1`, `Rval v1`] mp_tac th >>
            simp[] >>
            disch_then (CONJUNCTS_THEN strip_assume_tac)) >>
          rveq >> fs[] >>
          qcase_tac `evaluate(_::_, env, s1) = (Rval vs, s)` >>
          first_x_assum (qspecl_then [`env`, `s1`, `s`, `Rval vs`] mp_tac) >>
          simp[])
      >- (simp[] >>
          qcase_tac `evaluate ([exp1'], env, s0) = (Rval v1, s1)` >>
          first_x_assum (fn th =>
            qspecl_then [`env`, `s0`, `s1`, `Rval v1`] mp_tac th >>
            simp[] >>
            disch_then (CONJUNCTS_THEN strip_assume_tac)) >> metis_tac[])
      >- (simp[] >> metis_tac[]
        rveq >> simp[]) >>
      first_x_assum irule >> metis_tac[])
  >- ((* Var *)
      fs[any_el_ALT, closSemTheory.evaluate_def, bool_case_eq] >>
      fs[LIST_REL_EL_EQN])
  >- ((* If *)
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
      qcase_tac `known [ge] as g0 = (_, g1)` >>
      `∃ge' apx1. known [ge] as g0 = ([(ge',apx1)], g1)`
         by metis_tac[known_sing, PAIR_EQ] >>
      qcase_tac `known [tb] as g1 = (_, g2)` >>
      `∃tb' apx2. known [tb] as g1 = ([(tb',apx2)], g2)`
         by metis_tac[known_sing, PAIR_EQ] >>
      qcase_tac `known [eb] as g1 = (_, g3)` >>
      `∃eb' apx3. known [eb] as g1 = ([(eb',apx3)], g3)`
         by metis_tac[known_sing, PAIR_EQ] >> fs[] >> rveq >> fs[] >> rveq >>
      fs[closSemTheory.evaluate_def, pair_case_eq, result_case_eq,
         bool_case_eq] >> rveq >> fixeqs >> (* two cases from here on *)
      qcase_tac `evaluate ([ge'], env, s0) = (Rval gvs, s1)` >>
      first_x_assum
       (fn th => qspecl_then [`env`, `s0`, `s1`, `gvs`] mp_tac th >>
                 simp[] >>
                 disch_then (CONJUNCTS_THEN2 assume_tac
                                (qx_choose_then `gval` strip_assume_tac)))>>
      rveq >> fs[] >> rveq >>
      qcase_tac `evaluate ([tb'], env, s1) = (Rval tvs, s2)` >>
      first_x_assum
       (fn th => qspecl_then [`env`, `s1`, `s2`, `tvs`] mp_tac th >>
                 simp[] >>
                 disch_then (CONJUNCTS_THEN2 assume_tac
                                (qx_choose_then `tval` strip_assume_tac)))>>
      rveq >> fs[] >>
      metis_tac[val_approx_val_merge_I])
  >- ((* let *)
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
      fs[closSemTheory.evaluate_def, eqs, pair_case_eq, result_case_eq] >>
      rveq >>
      qcase_tac `evaluate (MAP FST binds', env, s0) = (Rval bvs, s1)` >>
      first_x_assum
       (fn th => qspecl_then [`env`, `s0`, `s1`, `bvs`] mp_tac th >>
                 simp[] >> disch_then (CONJUNCTS_THEN assume_tac)) >>
      qcase_tac `evaluate ([bod'], bvs ++ env, s1) = (Rval vs, s)` >>
      qcase_tac `known [bod] (MAP SND binds' ++ as) g1 = (kres,g)` >>
      qcase_tac `HD kres = (bod',kapx)` >>
      `kres = [(bod',kapx)]` by metis_tac[known_sing, HD, PAIR_EQ] >>
      pop_assum SUBST_ALL_TAC >> fs[] >>
      first_x_assum (qspecl_then [`bvs ++ env`, `s1`, `s`, `vs`] mp_tac) >>
      simp[EVERY2_APPEND_suff])
  >- ((* raise *) qcase_tac `known [exp1] as g0` >>
      `∃exp' ea g1. known [exp1] as g0 = ([(exp',ea)], g1)`
        by metis_tac [known_sing] >> fs[] >> rw[] >> fs[] >> rw[] >>
      fs[closSemTheory.evaluate_def, pair_case_eq, result_case_eq])
  >- ((* tick *) qcase_tac `known [exp1] as g0` >>
      `∃exp' ea g1. known [exp1] as g0 = ([(exp',ea)], g1)`
        by metis_tac [known_sing] >> fs[] >> rw[] >> fs[] >> rw[] >>
      fs[closSemTheory.evaluate_def, pair_case_eq, result_case_eq,
         bool_case_eq] >> metis_tac[state_globals_approx_dec_clock])
  >- ((* handle *)
      qcase_tac `known [exp1] as g0` >>
      `∃exp1' ea1 g1. known [exp1] as g0 = ([(exp1',ea1)], g1)`
        by metis_tac [known_sing] >> fs[] >>
      qcase_tac `known [exp2] (Other::as) g1` >>
      `∃exp2' ea2 g2. known [exp2] (Other::as) g1 = ([(exp2',ea2)], g2)`
        by metis_tac [known_sing] >> fs[] >> rveq >> fs[] >>
      fs[closSemTheory.evaluate_def, pair_case_eq, result_case_eq,
         error_case_eq] >> rveq
      >- metis_tac[val_approx_val_merge_I, state_globals_approx_mergegs] >>
      fs[PULL_EXISTS]
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
