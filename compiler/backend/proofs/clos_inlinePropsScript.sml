open HolKernel Parse boolLib bossLib;

open preamble
open closPropsTheory clos_inlineTheory

val _ = new_theory "clos_inlineProps";

val va_case_eq =
    prove_case_eq_thm{case_def = TypeBase.case_def_of ``:val_approx``,
                      nchotomy = TypeBase.nchotomy_of ``:val_approx``}

val dest_Clos_eq_SOME = Q.store_thm(
  "dest_Clos_eq_SOME[simp]",
  `dest_Clos a = SOME (i, j, e) ⇔ a = Clos i j e`,
  Cases_on `a` >> simp[]);


val merge_Other = Q.store_thm(
  "merge_Other[simp]",
  `merge Other a = Other ∧ merge a Other = Other`,
  Cases_on `a` >> simp[]);

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
  `(a ◁ Clos m n e ⇔ a = Clos m n e ∨ a = Impossible) ∧
   (Clos m n e ◁ a ⇔ a = Clos m n e ∨ a = Other)`,
  simp[subapprox_def] >> Cases_on `a` >> simp[] >> rw[] >>
  fs [DE_MORGAN_THM]);

val subapprox_Impossible = Q.store_thm(
  "subapprox_Impossible[simp]",
  `(a ◁ Impossible ⇔ a = Impossible) ∧ Impossible ◁ a`,
  simp[subapprox_def]);

val subapprox_Tuple = Q.store_thm(
  "subapprox_Tuple[simp]",
  `Tuple tg1 as1 ◁ Tuple tg2 as2 ⇔ tg1 = tg2 ∧ LIST_REL subapprox as1 as2`,
  simp[subapprox_def, MAP2_MAP, LIST_REL_EL_EQN, bool_case_eq] >>
  Cases_on `LENGTH as1 = LENGTH as2` >> Cases_on `tg1 = tg2` >>
  simp[LIST_EQ_REWRITE, EL_MAP, EL_ZIP] >> metis_tac[]);

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

val known_op_better_definedg = Q.store_thm(
  "known_op_better_definedg",
  `known_op opn apxs g0 = (a,g) ⇒ better_definedg g0 g`,
  Cases_on `opn` >>
  simp[known_op_def, pair_case_eq, closSemTheory.case_eq_thms, va_case_eq, bool_case_eq] >> rw[] >>
  rw[better_definedg_def, lookup_insert] >>
  rw[] >> fs[lookup_NONE_domain])

val known_better_definedg = Q.store_thm(
  "known_better_definedg",
  `∀limit es apxs g0 alist g.
     known limit es apxs g0 = (alist, g) ⇒ better_definedg g0 g`,
  ho_match_mp_tac known_ind >> simp[known_def] >>
  reverse (rpt strip_tac) >> rpt (pairarg_tac >> fs[]) >> rw[]
  >- (EVERY_CASE_TAC >> rpt (pairarg_tac >> fs[]) >>
      metis_tac[better_definedg_trans, known_op_better_definedg]) >>
  metis_tac[better_definedg_trans, known_op_better_definedg]);

val val_approx_val_def = tDefine "val_approx_val" `
  (val_approx_val (Clos m n e) v ⇔
     (∃e2 b. v = Closure (SOME m) [] e2 n b) ∨
     (∃base env fs j.
        v = Recclosure (SOME base) [] env fs j ∧
        m = base + 2*j ∧ j < LENGTH fs ∧
        n = FST (EL j fs))) ∧
  (val_approx_val (Tuple tg vas) v ⇔
     ∃vs. v = Block tg vs ∧ LIST_REL (λv va. val_approx_val v va) vas vs) ∧
  (val_approx_val Impossible v ⇔ F) ∧
  (val_approx_val (Int i) v ⇔ v = Number i) ∧
  (val_approx_val Other v ⇔ T)
` (WF_REL_TAC `measure (val_approx_size o FST)` >> simp[] >> Induct >>
   dsimp[val_approx_size_def] >> rpt strip_tac
   >- (rename1 `val_approx1_size vvs` >> Induct_on `vvs` >>
       dsimp[val_approx_size_def] >> rpt strip_tac >> res_tac >> simp[]) >>
   res_tac >> simp[])

val val_approx_val_def = save_thm(
  "val_approx_val_def[simp]",
  val_approx_val_def |> SIMP_RULE (srw_ss() ++ ETA_ss) []);

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
  rename1 `Tuple _ a2s ◁ apx2` >>
  Cases_on `apx2` >> dsimp[] >> simp[LIST_REL_EL_EQN] >> metis_tac[MEM_EL]);

val _ = export_theory();
