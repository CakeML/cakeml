open HolKernel boolLib bossLib lcsymtacs miscLib
open miscTheory finite_mapTheory alistTheory listTheory pairTheory
open holSyntaxTheory holSemanticsTheory holSemanticsExtraTheory holExtensionTheory
val _ = new_theory"holConstrainedExtension"

val constrain_assignment_def = Define`
  constrain_assignment cs f =
    λname args. case cs name args of SOME x => x | NONE => f name args`

val constrain_interpretation_def = Define`
  constrain_interpretation (tycs,tmcs) ((δ,γ):'U interpretation) =
    (constrain_assignment tycs δ,
     constrain_assignment tmcs γ)`

(*
val add_constraints_thm = store_thm("add_constraints_thm",
  ``∀i upd ctxt cs.
      theory_ok (thyof ctxt) ∧ upd updates ctxt ∧
      i models (thyof (upd::ctxt)) ∧
      (∀name args. IS_SOME (FST cs name args) ⇒
        MEM (name,LENGTH args) (types_of_upd upd) ∧
        inhabited (THE (FST cs name args))) ∧
      (∀name args. IS_SOME (SND cs name args) ⇒
        ∃ty. MEM (name,ty) (consts_of_upd upd) ∧
             (LENGTH (tyvars ty) = LENGTH args) ∧
             ∀τ. is_type_valuation τ ∧
                 (MAP τ (STRING_SORT (tyvars ty)) = args) ⇒
             (THE (SND cs name args)) <: typesem (constrain_assignment (FST cs) (FST i)) τ ty) ∧
      (∀p. MEM p (axioms_of_upd upd) ⇒
        constrain_interpretation cs i satisfies (sigof (upd::ctxt),[],p))
      ⇒
      (constrain_interpretation cs i) models (thyof (upd::ctxt))``,
  rw[] >> fs[models_def] >>
  conj_tac >- (
    Cases_on`i`>>Cases_on`cs`>>fs[is_interpretation_def,constrain_interpretation_def] >>
    conj_tac >- (
      fs[is_type_assignment_def,FEVERY_ALL_FLOOKUP] >> rw[] >>
      res_tac >> rw[constrain_assignment_def] >>
      BasicProvers.CASE_TAC >> rw[] >>
      fs[IS_SOME_EXISTS,PULL_EXISTS] >>
      res_tac >> metis_tac[] ) >>
    fs[is_term_assignment_def,FEVERY_ALL_FLOOKUP] >> rw[] >>
    first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
    first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
    rw[constrain_assignment_def] >>
    reverse BasicProvers.CASE_TAC >- (
      fs[IS_SOME_EXISTS,PULL_EXISTS] >>
      first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
      qpat_assum`FLOOKUP X Y = Z`mp_tac >>
      simp[FLOOKUP_FUNION] >>
      BasicProvers.CASE_TAC >- (
        imp_res_tac ALOOKUP_FAILS >> fs[] ) >>
      rw[] >>
      `v = ty` by (
        fs[Once updates_cases] >> rw[] >> fs[] >>
        qmatch_assum_abbrev_tac`ALOOKUP al k = SOME v` >>
        `ALL_DISTINCT (MAP FST al)` by (
          simp[Abbr`al`,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] ) >>
        imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >>
        fs[Abbr`al`] ) >>
      rw[] >> res_tac >> fs[constrain_assignment_def]) >>
    qpat_assum`FLOOKUP X Y = Z`mp_tac >>
    simp[FLOOKUP_FUNION] >>
    BasicProvers.CASE_TAC >- (
      strip_tac >>
      `type_ok (tysof ctxt) v` by (
        fs[theory_ok_def] >>
        first_x_assum match_mp_tac >>
        simp[IN_FRANGE_FLOOKUP] >>
        metis_tac[] ) >>
      qmatch_abbrev_tac`a <: b` >>
      qmatch_assum_abbrev_tac`a <: c` >>
      qsuff_tac `b = c` >- rw[] >>
      unabbrev_all_tac >>
      match_mp_tac typesem_consts >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      simp[type_ok_def] >> rw[FUN_EQ_THM] >>
      BasicProvers.CASE_TAC >>
      fs[IS_SOME_EXISTS,PULL_EXISTS] >> res_tac >>
      fs[Once updates_cases] >> rw[] >> fs[] >> rw[] >>
      imp_res_tac ALOOKUP_MEM >> fs[MEM_MAP,EXISTS_PROD] >>
      metis_tac[] ) >>
    rw[] >>
    fs[Once updates_cases] >> rw[] >> fs[] >> rw[]
*)

val _ = export_theory()
