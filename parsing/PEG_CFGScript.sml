open HolKernel Parse boolLib bossLib;

open mmlPEGTheory gramTheory gramPropsTheory
open lcsymtacs

val _ = new_theory "PEG_CFG";
(*
val peg_correct = store_thm(
  "peg_correct",
  ``(∀i0 s r. peg_eval mmlPEG (i0,s) r ⇒ s ∈ Gexprs mmlPEG ⇒
              ∀i pts.
                r = SOME(i,pts) ⇒
                (∀pt. MEM pt pts ⇒
                      valid_ptree mmlG pt ∧
                      ptree_fringe pt ++ MAP TOK i = MAP TOK i0) ∧
                (∀N f. s = nt N f ⇒ ∃pt. pts = [pt] ∧ ptree_head pt = NT N))
      ∧
    (∀i0 s i ptls.
      peg_eval_list mmlPEG (i0,s) (i,ptls) ⇒
      (∀ptl. MEM ptl ptls ⇒ ∀pt. MEM pt ptl ⇒ valid_ptree mmlG pt) ∧
      FLAT (FLAT (MAP (MAP ptree_fringe) ptls)) ++ MAP TOK i = MAP TOK i0)`
     suffices_by metis_tac[] >>
  ho_match_mp_tac pegTheory.peg_eval_strongind' >> simp[] >> rpt conj_tac
  >- (*empty *) simp[PEG_exprs, pnt_def]
  >- (* NT *) ALL_TAC
  >- (* any *) simp[PEG_exprs, pnt_def]
  >- (* tok *) (simp[PEG_exprs, pnt_def] >> rw[] >>
                fs[mktokLf_def, bindNT_def] >> rw[mmlG_applied


`

)

*)
val _ = export_theory();
