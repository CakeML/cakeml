open HolKernel Parse boolLib bossLib;

open preamble
open closPropsTheory clos_knownTheory closSemTheory
open bagTheory

val _ = new_theory "clos_knownProof";

val bool_case_eq = Q.prove(
  `COND b t f = v ⇔ b /\ v = t ∨ ¬b ∧ v = f`,
  srw_tac[][] >> metis_tac[]);

val pair_case_eq = Q.prove (
`pair_CASE x f = v ⇔ ?x1 x2. x = (x1,x2) ∧ f x1 x2 = v`,
 Cases_on `x` >>
 srw_tac[][]);

val v_case_eq =
    prove_case_eq_thm{case_def = TypeBase.case_def_of ``:closSem$v``,
                      nchotomy = TypeBase.nchotomy_of ``:closSem$v``}

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
  Cases_on `es` >> simp[evaluate_def] >>
  strip_tac >> rename1 `evaluate(h::t, env, s0)` >>
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
  >- (rpt strip_tac >> rename1 `evaluate ([exp], env, _)` >>
      `∃v. vs = [v]` by metis_tac[evaluate_SING] >> rw[] >> metis_tac[]) >>
  dsimp[evaluate_def, pair_case_eq, result_case_eq] >>
  rpt strip_tac >> reverse (Cases_on `n` >> fs[]) >- metis_tac[] >>
  imp_res_tac evaluate_SING >> rw[] >> metis_tac[]);

(* simple properties of constants from clos_known: i.e., merge and known *)
val dest_Clos_eq_SOME = Q.store_thm(
  "dest_Clos_eq_SOME[simp]",
  `dest_Clos a = SOME (i, j) ⇔ a = Clos i j`,
  Cases_on `a` >> simp[]);


val merge_Other = Q.store_thm(
  "merge_Other[simp]",
  `merge Other a = Other ∧ merge a Other = Other`,
  Cases_on `a` >> simp[]);

val known_LENGTH = Q.store_thm(
  "known_LENGTH",
  `∀es vs g. LENGTH (FST (known es vs g)) = LENGTH es`,
  ho_match_mp_tac known_ind >> simp[known_def] >> rpt strip_tac >>
  rpt (pairarg_tac >> fs[]))

val known_LENGTH_EQ_E = Q.store_thm(
  "known_LENGTH_EQ_E",
  `known es vs g0 = (alist, g) ⇒ LENGTH alist = LENGTH es`,
  metis_tac[FST, known_LENGTH]);

val known_sing = Q.store_thm(
  "known_sing",
  `∀e vs g. ∃e' a g'. known [e] vs g = ([(e',a)], g')`,
  rpt strip_tac >> Cases_on `known [e] vs g` >>
  rename1 `known [e] vs g = (res,g')` >>
  qspecl_then [`[e]`, `vs`, `g`] mp_tac known_LENGTH >> simp[] >>
  Cases_on `res` >> simp[LENGTH_NIL] >> metis_tac[pair_CASES])

val known_sing_EQ_E = Q.store_thm(
  "known_sing_EQ_E",
  `∀e vs g0 all g. known [e] vs g0 = (all, g) ⇒ ∃e' apx. all = [(e',apx)]`,
  metis_tac[PAIR_EQ, known_sing]);

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

val _ = set_fixity "◁" (Infix(NONASSOC,450))
val _ = overload_on ("◁", ``subapprox``)

val subapprox_refl = Q.store_thm(
  "subapprox_refl[simp]",
  `a ◁ a`,
  simp[subapprox_def]);

val subapprox_trans = Q.store_thm(
  "subapprox_trans",
  `a1 ◁ a2 ∧ a2 ◁ a3 ⇒ a1 ◁ a3`,
  simp[subapprox_def] >> metis_tac[merge_assoc]);

val subapprox_antisym = Q.store_thm(
  "subapprox_antisym",
  `a1 ◁ a2 ∧ a2 ◁ a1 ⇒ a1 = a2`,
  simp[subapprox_def] >> metis_tac[merge_comm]);

val subapprox_merge = Q.store_thm(
  "subapprox_merge[simp]",
  `a ◁ merge a b ∧ a ◁ merge b a`,
  simp[subapprox_def] >>
  metis_tac[merge_assoc, merge_comm, merge_idem]);

val subapprox_Other = Q.store_thm(
  "subapprox_Other[simp]",
  `(Other ◁ a ⇔ (a = Other)) ∧ a ◁ Other`,
  simp[subapprox_def] >> metis_tac[]);

val subapprox_Int = Q.store_thm(
  "subapprox_Int[simp]",
  `(a ◁ Int i ⇔ a = Int i ∨ a = Impossible) ∧
   (Int i ◁ a ⇔ a = Int i ∨ a = Other)`,
  simp[subapprox_def] >> Cases_on `a` >> simp[] >> rw[]);

val subapprox_Clos = Q.store_thm(
  "subapprox_Clos[simp]",
  `(a ◁ Clos m n ⇔ a = Clos m n ∨ a = Impossible) ∧
   (Clos m n ◁ a ⇔ a = Clos m n ∨ a = Other)`,
  simp[subapprox_def] >> Cases_on `a` >> simp[] >> rw[]);

val subapprox_Impossible = Q.store_thm(
  "subapprox_Impossible[simp]",
  `(a ◁ Impossible ⇔ a = Impossible) ∧ Impossible ◁ a`,
  simp[subapprox_def]);

val subapprox_Tuple = Q.store_thm(
  "subapprox_Tuple[simp]",
  `Tuple as1 ◁ Tuple as2 ⇔ LIST_REL subapprox as1 as2`,
  simp[subapprox_def, MAP2_MAP, LIST_REL_EL_EQN] >>
  Cases_on `LENGTH as1 = LENGTH as2` >> simp[LIST_EQ_REWRITE, EL_MAP, EL_ZIP]);

val better_definedg_def = Define`
  better_definedg g1 g2 ⇔
    ∀k. k ∈ domain g1 ⇒ k ∈ domain g2 ∧ THE (lookup k g1) ◁ THE (lookup k g2)
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
  rename1 `op_gbag opn` >> Cases_on `opn` >> simp[op_gbag_def]);

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
  (val_approx_val (Clos m n) v ⇔
     (∃e2 b. v = Closure (SOME m) [] e2 n b) ∨
     (∃base env fs j.
        v = Recclosure (SOME base) [] env fs j ∧
        m = base + j ∧
        n = FST (EL j fs))) ∧
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
     a1 ◁ a2 ∧ val_approx_val a1 v ⇒ val_approx_val a2 v`,
  ho_match_mp_tac (theorem "val_approx_val_ind") >> dsimp[] >> rpt gen_tac >>
  rename1 `Tuple a2s ◁ apx2` >>
  Cases_on `apx2` >> dsimp[] >> simp[LIST_REL_EL_EQN] >> metis_tac[MEM_EL]);


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
  simp[eval_approx_def, evaluate_def]);

val known_preserves_gwf = Q.store_thm(
  "known_preserves_gwf",
  `∀exps apxs g0 alist g. known exps apxs g0 = (alist,g) ∧ wf g0 ⇒ wf g`,
  ho_match_mp_tac known_ind >> simp[known_def] >> rpt strip_tac >>
  rpt (pairarg_tac >> fs[]) >> rw[] >> rename1 `known_op opn` >>
  Cases_on `opn` >> fs[known_op_def, eqs, va_case_eq, bool_case_eq] >>
  rw[wf_insert]);

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

val v_size_lemma = prove(
  ``MEM (v:closSem$v) vl ⇒ v_size v < v1_size vl``,
  Induct_on `vl` >> dsimp[v_size_def] >> rpt strip_tac >>
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
` (WF_REL_TAC `measure closSem$v_size` >> simp[v_size_def] >>
   rpt strip_tac >> imp_res_tac v_size_lemma >> simp[])

val vsgc_free_def = save_thm(
  "vsgc_free_def[simp]",
  SIMP_RULE (bool_ss ++ ETA_ss) [] vsgc_free_def)

val vsgc_free_Unit = Q.store_thm(
  "vsgc_free_Unit[simp]",
  `vsgc_free Unit`,
  simp[Unit_def]);

val vsgc_free_Boolv = Q.store_thm(
  "vsgc_free_Boolv[simp]",
  `vsgc_free (Boolv b)`,
  simp[Boolv_def]);

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

val ssgc_free_clockupd = Q.store_thm(
  "ssgc_free_clockupd[simp]",
  `ssgc_free (s with clock updated_by f) = ssgc_free s`,
  simp[ssgc_free_def])

val ssgc_free_dec_clock = Q.store_thm(
  "ssgc_free_dec_clock[simp]",
  `ssgc_free (dec_clock n s) ⇔ ssgc_free s`,
  simp[dec_clock_def])

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
  simp[do_app_def, eqs, op_gbag_def, PULL_EXISTS, bool_case_eq,
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
  >- dsimp[]
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
  >- (simp[PULL_FORALL] >> rpt gen_tac >> rename1 `v_to_list v = SOME vs` >>
      map_every qid_spec_tac [`vs`, `v`] >> ho_match_mp_tac value_ind >>
      simp[v_to_list_def] >> Cases >>
      simp[v_to_list_def] >>
      rename1 `closSem$Block _ (v1::vs)` >> Cases_on `vs` >>
      simp[v_to_list_def] >>
      rename1 `closSem$Block _ (v1::v2::vs)` >> Cases_on `vs` >>
      simp[v_to_list_def, eqs, PULL_EXISTS, PULL_FORALL])
  >- (simp[PULL_FORALL] >> rpt gen_tac >> rename1 `EVERY vsgc_free vs` >>
      Induct_on `vs` >> simp[list_to_v_def])
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
  >- dsimp[]
  >- dsimp[])

val EVERY_lookup_vars = Q.store_thm(
  "EVERY_lookup_vars",
  `∀vs env env'. EVERY P env ∧ lookup_vars vs env = SOME env' ⇒ EVERY P env'`,
  Induct >> simp[lookup_vars_def, eqs, PULL_EXISTS] >>
  metis_tac[MEM_EL, EVERY_MEM]);

val FOLDR_BU_EQ_EMPTY = Q.store_thm(
  "FOLDR_BU_EQ_EMPTY",
  `FOLDR (λx. BAG_UNION (f x)) a l = {||} ⇔
     a = {||} ∧ ∀e. MEM e l ⇒ f e = {||}`,
  Induct_on `l` >> dsimp[] >> metis_tac[])

val elglobals_EQ_EMPTY = Q.store_thm(
  "elglobals_EQ_EMPTY",
  `elist_globals l = {||} ⇔ ∀e. MEM e l ⇒ set_globals e = {||}`,
  Induct_on `l` >> dsimp[]);

val set_globals_empty_esgc_free = Q.store_thm(
  "set_globals_empty_esgc_free",
  `set_globals e = {||} ⇒ esgc_free e`,
  completeInduct_on `exp_size e` >> fs[PULL_FORALL] >> Cases >>
  simp[] >> strip_tac >> rveq >> fs[AND_IMP_INTRO] >>
  simp[EVERY_MEM, elglobals_EQ_EMPTY, FOLDR_BU_EQ_EMPTY, MEM_MAP] >>
  rw[] >> rw[] >>
  first_x_assum irule >> simp[] >> imp_res_tac exp_size_MEM >> simp[])

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
      fs[do_app_def, eqs, bool_case_eq, pair_case_eq] >> rw[] >>
      fs[]
      >- (rename1 `closSem$evaluate(_,_,s0) = (_, s1)` >>
          irule SUBSET_TRANS >> qexists_tac `mapped_globals s1` >> simp[] >>
          simp[mapped_globals_def] >>
          fs[SUBSET_DEF, PULL_EXISTS, get_global_def,
             EL_LUPDATE, bool_case_eq] >> metis_tac[])
      >- (simp[mapped_globals_def, SUBSET_DEF, get_global_def,
               EL_APPEND_EQN, bool_case_eq] >> rpt strip_tac >>
          simp[]))
  >- fs[evaluate_def, bool_case_eq, eqs]
  >- (fs[eqs, PULL_EXISTS] >> rveq >> fs[])
  >- (fs[pair_case_eq, result_case_eq] >> rveq >> fs[] >>
      metis_tac[SUBSET_TRANS])
  >- (fs[pair_case_eq, result_case_eq, eqs, bool_case_eq] >> rveq >> fixeqs >>
      fs[] >> metis_tac[SUBSET_TRANS])
  >- (fs[eqs, bool_case_eq, pair_case_eq] >> rveq >> fs[] >>
      metis_tac[SUBSET_TRANS]))

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
      simp[evaluate_def, eqs, bool_case_eq] >> rpt gen_tac >>
      strip_tac >> rveq >> fs[] >> metis_tac[EVERY_lookup_vars])
  >- ((* Letrec *) say "letrec" >>
      simp[Once foldr_bu', SET_OF_BAG_UNION] >>
      simp[evaluate_def, bool_case_eq, eqs] >>
      rpt (gen_tac ORELSE disch_then strip_assume_tac) >> rveq >>
      fs[EVERY_GENLIST]
      >- (metis_tac[mglobals_extend_SUBSET, SUBSET_UNION])
      >- (imp_res_tac EVERY_lookup_vars >> fs[] >>
          metis_tac[mglobals_extend_SUBSET, SUBSET_UNION]))
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
      simp[evaluate_def, pair_case_eq, result_case_eq, eqs,
           bool_case_eq] >>
      rpt (gen_tac ORELSE disch_then strip_assume_tac) >> rveq >> fixeqs >>
      fs[] >> fs[find_code_def, eqs, pair_case_eq] >> rveq >>
      rename1 `FLOOKUP _.code _ = SOME (_, fbody)` >>
      `set_globals fbody = {||}` suffices_by
        (strip_tac >> fs[] >> imp_res_tac set_globals_empty_esgc_free >>
         fs[] >> metis_tac[mglobals_extend_trans, UNION_EMPTY]) >>
      fs[ssgc_free_def] >> metis_tac[])
  >- ((* evaluate_app *)
      say "evaluate_app" >> rpt gen_tac >> strip_tac >>
      simp[evaluate_def, eqs, bool_case_eq, pair_case_eq] >>
      rpt (gen_tac ORELSE disch_then strip_assume_tac) >> rveq >> fixeqs >>
      fs[]
      >- (fs[dest_closure_def, eqs, bool_case_eq] >> rveq >>
          fs[] >> pairarg_tac >> fs[bool_case_eq])
      >- (fs[dest_closure_def, eqs, bool_case_eq] >> rveq >>
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
      >- (fs[dest_closure_def, eqs, bool_case_eq] >> rveq >>
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
      >- (fs[dest_closure_def, eqs, bool_case_eq] >> rveq >>
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
  rw[] >> fs[] >> rw[] >> simp[FOLDR_MAP] >>
  irule FOLDR_CONG >> simp[] >> rpt strip_tac >> pairarg_tac >>
  simp[]>> rw[] >>
  qmatch_abbrev_tac `set_globals (FST (HD (FST (known [X] ENV G0)))) =
                     set_globals X` >>
  rename1 `MEM (nn,X) fns` >> res_tac >> rfs[] >>
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
  >- (imp_res_tac known_preserves_setGlobals >> fs[elist_globals_def])
  >- (fs[elglobals_EQ_EMPTY, MEM_MAP, PULL_EXISTS] >> rpt strip_tac >>
      pairarg_tac >> rw[] >> fs[FORALL_PROD] >>
      qmatch_abbrev_tac
        `set_globals (FST (HD (FST (known [X] ENV g00)))) = _` >>
      rename1 `MEM (nn, X) fns` >>
      rpt (first_x_assum (qspecl_then [`nn`, `X`] mp_tac)) >> simp[] >>
      `∃X' APX gg. known [X] ENV g00 = ([(X',APX)], gg)`
        by metis_tac[known_sing] >> simp[] >>
      imp_res_tac known_preserves_setGlobals >> fs[elist_globals_def]))

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
   state_globals_approx s0 g0 ∧
   do_app opn vs s0 = Rval (v, s) ⇒
   state_globals_approx s g ∧ val_approx_val a v`,
  Cases_on `opn` >>
  simp[known_op_def, do_app_def, eqs, va_case_eq, bool_case_eq,
       pair_case_eq] >>
  rpt strip_tac >> rveq >> fs[]
  >- (fs[state_globals_approx_def] >> metis_tac[SOME_11])
  >- (fs[state_globals_approx_def, get_global_def, EL_LUPDATE,
         lookup_insert, bool_case_eq] >> rw[] >> simp[] >> metis_tac[])
  >- (fs[state_globals_approx_def, get_global_def, EL_LUPDATE,
         bool_case_eq, lookup_insert] >> rw[] >>
      metis_tac[val_approx_val_merge_I])
  >- (fs[state_globals_approx_def, get_global_def, EL_APPEND_EQN,
         bool_case_eq] >> rw[]
      >- metis_tac[]
      >- (rename1 `nn - LENGTH (ss:'a closSem$state).globals` >>
          `nn - LENGTH ss.globals = 0` by simp[] >>
          pop_assum (fn th => fs[th])))
  >- (rveq >> fs[LIST_REL_EL_EQN]));

val say = say0 "known_correct_approx"
val known_correct_approx = Q.store_thm(
  "known_correct_approx",
  `∀es as g0 all g.
     known es as g0 = (all,g) ⇒
     ∀env s0 s vs result.
        LIST_REL val_approx_val as env ∧
        state_globals_approx s0 g0 ∧ ssgc_free s0 ∧ EVERY vsgc_free env ∧
        EVERY esgc_free es ∧
        evaluate(MAP FST all, env, s0) = (result, s) ⇒
        state_globals_approx s g ∧
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
      fs[evaluate_def, pair_case_eq, result_case_eq] >> rveq
      >- (rename1 `evaluate ([exp1'], env, s0) = (Rval v1, s1)` >>
          first_x_assum (fn th =>
            qspecl_then [`env`, `s0`, `s1`, `Rval v1`] mp_tac th >>
            simp[] >>
            disch_then (CONJUNCTS_THEN strip_assume_tac)) >>
          rveq >> fs[] >>
          rename1 `evaluate(_::_, env, s1) = (Rval vs, s)` >>
          `ssgc_free s1` by metis_tac[ssgc_free_preserved_SING] >>
          first_x_assum (qspecl_then [`env`, `s1`, `s`, `Rval vs`] mp_tac) >>
          simp[])
      >- (simp[] >>
          rename1 `evaluate ([exp1'], env, s0) = (Rval v1, s1)` >>
          first_x_assum (fn th =>
            qspecl_then [`env`, `s0`, `s1`, `Rval v1`] mp_tac th >>
            simp[] >>
            disch_then (CONJUNCTS_THEN strip_assume_tac)) >>
          `ssgc_free s1` suffices_by metis_tac[] >>
          metis_tac[ssgc_free_preserved_SING])
      >- (simp[] >>
          rename1 `evaluate ([exp1'], env, s0) = (Rerr error, s1)` >>
          first_x_assum (qspecl_then [`env`, `s0`, `s1`, `Rerr error`] mp_tac)>>
          simp[] >>
          metis_tac[known_better_definedg, state_approx_better_definedg]))
  >- ((* Var *) say "var" >>
      fs[any_el_ALT, evaluate_def, bool_case_eq] >>
      fs[LIST_REL_EL_EQN])
  >- ((* If *) say "if" >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
      rename1 `known [ge] as g0 = (_, g1)` >>
      `∃ge' apx1. known [ge] as g0 = ([(ge',apx1)], g1)`
         by metis_tac[known_sing, PAIR_EQ] >>
      rename1 `known [tb] as g1 = (_, g2)` >>
      `∃tb' apx2. known [tb] as g1 = ([(tb',apx2)], g2)`
         by metis_tac[known_sing, PAIR_EQ] >>
      rename1 `known [eb] as g2 = (_, g3)` >>
      `∃eb' apx3. known [eb] as g2 = ([(eb',apx3)], g3)`
         by metis_tac[known_sing, PAIR_EQ] >> fs[] >> rveq >> fs[] >> rveq >>
      reverse
        (fs[evaluate_def, pair_case_eq, result_case_eq,
            bool_case_eq]) >> rveq >> fixeqs >> simp[]
      >- metis_tac[known_better_definedg, state_approx_better_definedg]
      >- metis_tac[known_better_definedg, state_approx_better_definedg] >>
      (* two cases from here on *)
      rename1 `evaluate ([ge'], env, s0) = (Rval gvs, s1)` >>
      first_x_assum
       (fn th => qspecl_then [`env`, `s0`, `s1`, `Rval gvs`] mp_tac th >>
                 simp[] >>
                 disch_then (CONJUNCTS_THEN strip_assume_tac)) >>
      rveq >> fs[] >> rveq >>
      rename1 `evaluate ([somebr], env, s1) = (someres, s2)` >>
      `state_globals_approx s1 g2`
        by metis_tac[known_better_definedg, state_approx_better_definedg] >>
      `ssgc_free s1` by metis_tac[ssgc_free_preserved_SING] >>
      first_x_assum
       (fn th => qspecl_then [`env`, `s1`, `s2`, `someres`] mp_tac th >>
                 simp[] >>
                 disch_then (CONJUNCTS_THEN strip_assume_tac)) >>
      metis_tac[val_approx_val_merge_I, known_better_definedg,
                state_approx_better_definedg])
  >- ((* let *) say "let" >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
      fs[evaluate_def, eqs, pair_case_eq, result_case_eq] >>
      rveq
      >- (rename1 `evaluate (MAP FST binds', env, s0) = (Rval bvs, s1)` >>
          first_x_assum
            (fn th => qspecl_then [`env`, `s0`, `s1`, `Rval bvs`] mp_tac th >>
                      simp[] >> disch_then (CONJUNCTS_THEN assume_tac)) >>
          rename1 `evaluate ([bod'], bvs ++ env, s1) = (result, s)` >>
          qspecl_then [`MAP FST binds'`, `env`, `s0`, `Rval bvs`, `s1`]
                      mp_tac ssgc_evaluate >> simp[] >> impl_tac
          >- (simp[ALL_EL_MAP] >> metis_tac [known_preserves_esgc_free]) >>
          strip_tac >> imp_res_tac known_sing_EQ_E >> fs[] >> rveq >>
          first_x_assum
            (qspecl_then [`bvs ++ env`, `s1`, `s`, `result`] mp_tac) >>
          simp[EVERY2_APPEND_suff])
      >- (rename1 `evaluate (MAP FST binds',env,s0) = (Rerr err, s)` >>
          first_x_assum
            (fn th =>
               qspecl_then [`env`, `s0`, `s`, `Rerr err`] mp_tac th >>
               simp[] >>
               disch_then (assume_tac o assert (not o is_imp o concl))) >>
          metis_tac[state_approx_better_definedg, known_better_definedg]))
  >- ((* raise *) say "raise" >>
      pairarg_tac >> fs[] >> imp_res_tac known_sing_EQ_E >> fs[] >> rveq >>
      fs[evaluate_def, pair_case_eq, result_case_eq] >> rveq >>
      simp[] >> metis_tac[])
  >- ((* tick *) say "tick" >>
      pairarg_tac >> fs[] >> imp_res_tac known_sing_EQ_E >> fs[] >> rveq >>
      fs[evaluate_def, pair_case_eq, result_case_eq,
         bool_case_eq] >> rveq >> simp[]
      >- metis_tac[state_approx_better_definedg, known_better_definedg] >>
      fixeqs >> first_x_assum irule >>
      map_every qexists_tac [`env`, `dec_clock 1 s0`] >> simp[])
  >- ((* handle *) say "handle" >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
      fs[evaluate_def, pair_case_eq, result_case_eq,
         error_case_eq] >> rveq >> fs[]
      >- (imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rveq >>
          rename1 `evaluate([e1],env,s0) = (Rval vs,s)` >>
          first_x_assum
            (fn th => qspecl_then [`env`, `s0`, `s`, `Rval vs`] mp_tac th >>
                      simp[] >> disch_then (CONJUNCTS_THEN strip_assume_tac)) >>
          fs[] >> metis_tac[val_approx_val_merge_I, known_better_definedg,
                            state_approx_better_definedg])
      >- (imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rveq >>
          rename1 `evaluate([exp1],env,s0) = (Rerr(Rraise exc),s1)` >>
          first_x_assum
            (fn th => qspecl_then [`env`, `s0`, `s1`, `Rerr (Rraise exc)`]
                                  mp_tac th >> simp[] >>
                      disch_then
                        (assume_tac o assert (not o is_imp o concl))) >>
          rename1 `evaluate([hnd],exc::env,s1) = (result,s)` >>
          first_x_assum (qspecl_then [`exc::env`, `s1`, `s`, `result`] mp_tac)>>
          simp[] >>
          qspecl_then [`[exp1]`, `env`, `s0`, `Rerr (Rraise exc)`, `s1`]
                      mp_tac ssgc_evaluate >> simp[] >> impl_tac
          >- (rename1 `known [exp0] as g0 = ([(exp1,_)], _)` >>
              qspecl_then [`[exp0]`, `as`] mp_tac known_preserves_esgc_free >>
              disch_then (IMP_RES_THEN mp_tac) >> simp[]) >> simp[] >>
          rpt strip_tac >> simp[] >> fs[] >> metis_tac[val_approx_val_merge_I])
      >- (imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rveq >>
          rename1 `evaluate([exp1],env,s0) = (Rerr (Rabort abt), s)` >>
          first_x_assum
            (fn th => qspecl_then [`env`, `s0`, `s`, `Rerr (Rabort abt)`]
                                  mp_tac th >> simp[] >>
                      disch_then
                        (assume_tac o assert (not o is_imp o concl))) >>
          metis_tac[known_better_definedg, state_approx_better_definedg]))
  >- ((* call *) say "call" >> pairarg_tac >> fs[] >> rveq >> fs[] >>
      fs[evaluate_def, pair_case_eq, result_case_eq, eqs,
         bool_case_eq] >>
      rveq >> fs[]
      >- (rename1 `evaluate(MAP FST args,env,s0) = (Rval vs, s)` >>
          first_x_assum (qspecl_then [`env`, `s0`, `s`, `Rval vs`] mp_tac) >>
          simp[])
      >- (rename1 `evaluate(MAP FST arg_es,env,s0) = (Rval vs, s)` >>
          first_x_assum (qspecl_then [`env`, `s0`, `s`, `Rval vs`] mp_tac) >>
          simp[])
      >- (fixeqs >>
          rename1 `evaluate(MAP FST arg_es, env, s0) = (Rval vs, s1)` >>
          first_x_assum (qspecl_then [`env`, `s0`, `s1`, `Rval vs`] mp_tac) >>
          simp[] >> rw[]
          >- (rename1 `evaluate([body],args,dec_clock 1 s1) = (result,s)` >>
              qspecl_then [`MAP FST arg_es`, `env`, `s0`, `Rval vs`, `s1`]
                          mp_tac ssgc_evaluate >> simp[] >>
              impl_tac
              >- (simp[ALL_EL_MAP] >> metis_tac[known_preserves_esgc_free]) >>
              rw[] >>
              qspecl_then [`[body]`, `args`, `dec_clock 1 s1`, `result`, `s`]
                          mp_tac ssgc_evaluate >> simp[] >>
              fs[find_code_def, eqs, pair_case_eq] >> rveq >>
              simp[] >>
              `set_globals body = {||}`
                by (Q.UNDISCH_THEN `ssgc_free s1` mp_tac >>
                    simp[ssgc_free_def] >> metis_tac[])  >>
              simp[set_globals_empty_esgc_free] >> strip_tac >>
              `mapped_globals s1 ⊆ mapped_globals s`
                by metis_tac[mapped_globals_grow, mapped_globals_dec_clock] >>
              metis_tac[mglobals_extend_EMPTY_state_globals_approx])
          >- metis_tac[evaluate_SING])
      >- (rename1 `evaluate(MAP FST arg_es,env,s0) = (Rerr err, s)` >>
          first_x_assum (qspecl_then [`env`, `s0`] mp_tac) >> simp[]))
  >- ((* op *) say "op" >> rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
      fs[evaluate_def, pair_case_eq, result_case_eq] >> rveq >>
      fs[] >>
      rename1 `evaluate(MAP FST args,env,s0)` >>
      first_x_assum (qspecl_then [`env`, `s0`] mp_tac) >> simp[]
      >- metis_tac[known_op_correct_approx, LIST_REL_REVERSE_EQ] >>
      metis_tac[state_approx_better_definedg, known_op_better_definedg])
  >- (say "app" >> rpt (pairarg_tac >> fs[]) >> rveq >>
      imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rveq >>
      fs[evaluate_def, bool_case_eq, pair_case_eq,
         result_case_eq] >> rveq >> fs[]
      >- (rename1 `evaluate(MAP FST args, env, s0) = (Rval argvs, s1)` >>
          first_x_assum
            (fn th => qspecl_then [`env`, `s0`] mp_tac th >>
                      simp[] >>
                      disch_then (CONJUNCTS_THEN strip_assume_tac)) >>
          first_x_assum (qspecl_then [`env`, `s1`] mp_tac) >> simp[] >>
          qspecl_then [`MAP FST args`, `env`, `s0`, `Rval argvs`, `s1`]
                      mp_tac ssgc_evaluate >> simp[] >>
          impl_tac
          >- (simp[ALL_EL_MAP] >> metis_tac[known_preserves_esgc_free]) >>
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
          qpat_assum `evaluate_app _ _ _ _ = _`
             (fn th =>
                 (mp_tac o PART_MATCH (last o strip_conj o #1 o dest_imp)
                                      (CONJUNCT2 ssgc_evaluate0) o concl) th >>
                 assume_tac th) >> simp[] >>
          strip_tac >>
          `mapped_globals s2 ⊆ mapped_globals s` suffices_by
            metis_tac[mglobals_extend_EMPTY_state_globals_approx] >>
          metis_tac[lem])
      >- (rename1 `evaluate(MAP FST args, env, s0) = (Rval argvs, s1)` >>
          first_x_assum
            (fn th => qspecl_then [`env`, `s0`] mp_tac th >>
                      simp[] >>
                      disch_then (CONJUNCTS_THEN strip_assume_tac)) >>
          first_x_assum (qspecl_then [`env`, `s1`] mp_tac) >> simp[] >>
          disch_then irule >>
          qspecl_then [`MAP FST args`, `env`, `s0`, `Rval argvs`, `s1`]
                      mp_tac ssgc_evaluate >> simp[] >>
          impl_tac
          >- (simp[ALL_EL_MAP] >> metis_tac[known_preserves_esgc_free]) >>
          simp[])
      >- (rename1 `evaluate(MAP FST args, env, s0)` >>
          first_x_assum
            (fn th => qspecl_then [`env`, `s0`] mp_tac th >>
                      simp[] >>
                      disch_then
                        (assume_tac o assert (not o is_imp o concl))) >>
          metis_tac[state_approx_better_definedg, known_better_definedg])
      >- metis_tac[state_approx_better_definedg, known_better_definedg])
  >- (say "fn" >> rpt (pairarg_tac >> fs[]) >> rveq >>
      imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rveq >>
      fs[evaluate_def, bool_case_eq, eqs] >> rveq >> fs[]
      >- (conj_tac
          >- metis_tac[state_approx_better_definedg, known_better_definedg] >>
          rename1 `Closure lopt` >> Cases_on `lopt` >> simp[])
      >- metis_tac[state_approx_better_definedg, known_better_definedg]
      >- (conj_tac
          >- metis_tac[state_approx_better_definedg, known_better_definedg] >>
          rename1 `Closure lopt` >> Cases_on `lopt` >> simp[])
      >- metis_tac[state_approx_better_definedg, known_better_definedg]
      >- metis_tac[state_approx_better_definedg, known_better_definedg])
  >- (say "letrec" >> rpt (pairarg_tac >> fs[]) >> imp_res_tac known_sing_EQ_E>>
      rveq >> fs[] >> rveq >>
      fs[evaluate_def, bool_case_eq]
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
          simp[LIST_REL_EL_EQN, EL_GENLIST, EL_APPEND_EQN, EVERY_MEM,
               MEM_GENLIST, PULL_EXISTS] >> impl_tac
          >- (rpt conj_tac
              >- fs[LIST_REL_EL_EQN]
              >- (qx_gen_tac `i` >> reverse (Cases_on `i < LENGTH fns`) >>
                  simp[] >- fs[LIST_REL_EL_EQN] >>
                  Cases_on `lopt` >> simp[] >>
                  simp[Abbr`ff`, EL_MAP] >> pairarg_tac >> simp[])
              >- (fs[elglobals_EQ_EMPTY, MEM_MAP, PULL_EXISTS, FORALL_PROD] >>
                  simp[Abbr`ff`] >> rpt strip_tac >>
                  qmatch_abbrev_tac `
                    set_globals (FST (HD (FST (known [_] ENV g0)))) = {||}` >>
                  rename1 `MEM (nargs, fbody) fns` >>
                  `set_globals fbody = {||}` by metis_tac[] >>
                  Cases_on `known [fbody] ENV g0` >> simp[] >>
                  imp_res_tac known_sing_EQ_E >> fs[] >> rveq >>
                  first_x_assum (mp_tac o MATCH_MP known_preserves_setGlobals)>>
                  simp[])) >>
          metis_tac[])
      >- metis_tac[state_approx_better_definedg, known_better_definedg]))

val kca_sing_sga =
    known_correct_approx
      |> Q.SPECL [`[e]`, `as`, `g0`, `[(e',a)]`, `g`]
      |> SIMP_RULE (srw_ss()) [PULL_FORALL]
      |> SPEC_ALL |> UNDISCH_ALL |> CONJUNCT1 |> DISCH_ALL
val say = say0 "known_correct";
val nailIH =
    first_assum (fn lr => first_assum (fn knwnth => first_assum (fn sga =>
      first_x_assum (mp_tac o C MATCH_MP (CONJ lr (CONJ sga knwnth))))))
fun sel_ihpc f =
    first_assum (fn asm => first_x_assum (fn ih =>
      mp_tac (PART_MATCH (f o strip_conj o #1 o dest_imp) ih (concl asm))))

val evaluate_app_NONE_SOME = Q.store_thm(
  "evaluate_app_NONE_SOME",
  `evaluate_app NONE fval argvs s0 = (res, s) ∧
   res ≠ Rerr (Rabort Rtype_error) ∧
   ((∃e2 b. fval = Closure (SOME mm) [] e2 (LENGTH argvs) b) ∨
    (∃base env fs j.
            fval = Recclosure (SOME base) [] env fs j ∧ mm = base + j ∧
            LENGTH argvs = FST (EL j fs))) ⇒
   evaluate_app (SOME mm) fval argvs s0 = (res, s)`,
  Cases_on `argvs = []` >>
  simp[evaluate_app_rw] >> Cases_on `fval` >>
  simp[eqs, result_case_eq, bool_case_eq, pair_case_eq] >>
  rpt strip_tac >> fs[dest_closure_def] >> rveq >> fs[] >>
  rpt (pairarg_tac >> fs[]) >> rveq >>
  fs[check_loc_def, revdroprev, revtakerev]);

val known_correct0 = Q.prove(
  `(∀a es env (s0:α closSem$state) res s g0 g as ealist.
      a = (es,env,s0) ∧ evaluate (es, env, s0) = (res, s) ∧ EVERY esgc_free es ∧
      LIST_REL val_approx_val as env ∧ EVERY vsgc_free env ∧
      state_globals_approx s0 g0 ∧
      ssgc_free s0 ∧ known es as g0 = (ealist, g) ∧
      res ≠ Rerr (Rabort Rtype_error) ⇒
      evaluate(MAP FST ealist, env, s0) = (res, s)) ∧
   (∀lopt f args (s0:α closSem$state) res s.
      evaluate_app lopt f args s0 = (res,s) ∧ EVERY vsgc_free args ⇒ T)`,
  ho_match_mp_tac evaluate_ind >> rpt conj_tac
  >- (say "nil" >> simp[evaluate_def, known_def])
  >- (say "cons" >>
      simp[evaluate_def, known_def, pair_case_eq,
           result_case_eq] >>
      rpt strip_tac >> rveq >> rpt (pairarg_tac >> fs[]) >> rveq >> simp[] >>
      nailIH
      >- (imp_res_tac evaluate_SING >> rveq >> fs[] >>
          imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> strip_tac >>
          simp[Once evaluate_CONS, pair_case_eq, result_case_eq] >>
          first_x_assum irule >>
          metis_tac[kca_sing_sga, ssgc_free_preserved_SING])
      >- (imp_res_tac evaluate_SING >> rveq >> fs[] >>
          imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> strip_tac >>
          simp[Once evaluate_CONS, pair_case_eq, result_case_eq] >>
          first_x_assum irule >>
          metis_tac[ssgc_free_preserved_SING, kca_sing_sga])
      >- (imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> strip_tac >>
          simp[Once evaluate_CONS]))
  >- (say "var" >>
      simp[evaluate_def, bool_case_eq, known_def] >> csimp[])
  >- (say "if" >>
      simp[evaluate_def, pair_case_eq, bool_case_eq,
           result_case_eq, known_def] >> rpt strip_tac >> rveq >> fs[] >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >> fixeqs >> nailIH
      >- (imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rveq >>
          imp_res_tac evaluate_SING >> rveq >> fs[] >> rveq >> strip_tac >>
          simp[evaluate_def] >> sel_ihpc last >> simp[] >>
          disch_then irule >- metis_tac[ssgc_free_preserved_SING] >>
          metis_tac[kca_sing_sga])
      >- (imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rveq >>
          imp_res_tac evaluate_SING >> rveq >> fs[] >> rveq >> strip_tac >>
          simp[evaluate_def] >> sel_ihpc last >> simp[] >>
          disch_then irule >- metis_tac[ssgc_free_preserved_SING] >>
          irule state_approx_better_definedg >>
          imp_res_tac known_better_definedg >>
          metis_tac[kca_sing_sga])
      >- (imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rveq >>
          simp[evaluate_def]))
  >- (say "let" >>
      simp[evaluate_def, pair_case_eq, result_case_eq] >>
      rpt strip_tac >> rveq >> fs[known_def] >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >> nailIH
      >- (strip_tac >> simp[evaluate_def] >>
          imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rveq >>
          sel_ihpc last >> simp[] >> disch_then MATCH_MP_TAC >>
          rename1 `evaluate (MAP FST al1,env,s0) = (Rval vs, s1)` >>
          rename1 `evaluate ([bod], vs ++ env, s1) = (res,ss)` >>
          rename1 `known [bod] (MAP SND al1 ++ as) g1 = ([(bod',ba)], g)` >>
          qspecl_then [`MAP FST al1`, `env`, `s0`, `Rval vs`, `s1`] mp_tac
                      ssgc_evaluate >> simp[] >> impl_tac
          >- (simp[ALL_EL_MAP] >> metis_tac[known_preserves_esgc_free]) >>
          strip_tac >>
          rename1 `known es as g0 = (al1,g1)` >>
          qspecl_then [`es`, `as`, `g0`] mp_tac known_correct_approx >> simp[]>>
          disch_then (qspecl_then [`env`, `s0`, `s1`, `Rval vs`] mp_tac) >>
          simp[EVERY2_APPEND_suff])
      >- simp[evaluate_def])
  >- (say "raise" >>
      simp[evaluate_def, pair_case_eq, result_case_eq] >>
      rpt strip_tac >> rveq >> fs[known_def] >> pairarg_tac >> fs[] >>
      imp_res_tac known_sing_EQ_E >> fs[] >> rveq >> fs[] >>
      simp[evaluate_def, pair_case_eq, result_case_eq] >>
      nailIH>> simp[])
  >- (say "handle" >>
      simp[evaluate_def, pair_case_eq, result_case_eq,
           error_case_eq, known_def] >> rpt strip_tac >> rveq >> fs[] >>
      rpt (pairarg_tac >> fs[]) >> rveq >>
      imp_res_tac known_sing_EQ_E >> rveq >> fs[] >> rveq >>
      nailIH >> simp[evaluate_def] >>
      fs[PULL_EXISTS] >> strip_tac >> sel_ihpc last >> simp[] >>
      reverse impl_tac >- simp[] >>
      rename1 `state_globals_approx s0 g0` >>
      rename1 `known [exp1] _ g0` >>
      rename1 `evaluate([exp1], env, s0) = (Rerr (Rraise exnv), ss)` >>
      qspecl_then [`[exp1]`, `env`, `s0`, `Rerr (Rraise exnv)`, `ss`]
                  mp_tac ssgc_evaluate >> simp[] >>
      metis_tac[kca_sing_sga])
  >- (say "op" >>
      simp[evaluate_def, pair_case_eq, result_case_eq, known_def] >>
      rpt strip_tac >> rveq >> fs[] >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >> nailIH >>
      simp[evaluate_def])
  >- (say "fn" >>
      simp[evaluate_def, pair_case_eq, result_case_eq,
           known_def, bool_case_eq, eqs] >> rpt strip_tac >> rveq >> fs[] >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
      simp[evaluate_def] >> cheat)
  >- (say "letrec" >> cheat)
  >- (say "app" >>
      simp[evaluate_def, pair_case_eq, result_case_eq,
           bool_case_eq, known_def] >> rpt strip_tac >> rveq >>
      rpt (pairarg_tac >> fs[]) >> rveq >> fs[] >>
      nailIH >> strip_tac >>
      simp[evaluate_def, pair_case_eq, result_case_eq, bool_case_eq]
      >- (imp_res_tac evaluate_SING >> imp_res_tac known_sing_EQ_E >>
          rveq >> fs[] >> rveq >>
          imp_res_tac known_LENGTH_EQ_E >> fs[PULL_EXISTS] >>
          sel_ihpc last >> simp[] >> impl_keep_tac
          >- metis_tac[ssgc_evaluate, known_correct_approx] >>
          pop_assum strip_assume_tac >>
          strip_tac >> simp[] >> imp_res_tac evaluate_IMP_LENGTH >> fs[] >>
          every_case_tac >> rveq >> simp[] >> fs[] >> rw[] >>
          rename1 `
            known [fexp] apxs g1 = ([(fexp', Clos mm (LENGTH argalist))], g)` >>
          rename1 `evaluate([fexp'],env,s1) = (Rval[fval],s2)` >>
          qspecl_then [`[fexp]`, `apxs`, `g1`] mp_tac known_correct_approx >>
          simp[] >>
          disch_then (qspecl_then [`env`, `s1`, `s2`, `Rval [fval]`] mp_tac) >>
          simp[] >> metis_tac[evaluate_app_NONE_SOME])
      >- (sel_ihpc last >> simp[] >>
          imp_res_tac known_sing_EQ_E >> fs[] >>
          imp_res_tac known_LENGTH_EQ_E >> rveq >> fs[] >>
          reverse impl_tac >- simp[] >>
          metis_tac[ssgc_evaluate, known_correct_approx])
      >- (imp_res_tac known_LENGTH_EQ_E >> fs[]))
  >- (say "tick" >> cheat)
  >- (say "call" >> cheat)
  >- (say "evaluate_app(nil)" >> simp[])
  >- (say "evaluate_app(cons)" >> simp[]))

val known_correct = save_thm(
  "known_correct",
  known_correct0 |> SIMP_RULE (srw_ss()) []);


val _ = export_theory();
