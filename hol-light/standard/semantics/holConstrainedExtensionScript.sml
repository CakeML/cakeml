open HolKernel boolLib bossLib lcsymtacs
open holExtensionTheory
val _ = new_theory"holConstrainedExtension"

val constrain_assignment_def = Define`
  constrain_assignment cs f =
    λname args. case cs name args of SOME x => x | NONE => f name args`

val constrain_interpretation_def = Define`
  constrain_interpretation (tycs,tmcs) (δ,γ) =
    (constrain_assignment tycs δ,
     constrain_assignment tmcs γ)`

(*
val add_constraints_thm = store_thm("add_constraints_thm",
  ``∀i upd ctxt cs.
      i models (thyof (upd::ctxt)) ∧
      (∀name args. IS_SOME ((FST cs) name args) ⇒ MEM (name,LENGTH args) (types_of_upd upd)) ∧
      (∀name args. IS_SOME ((SND cs) name args) ⇒ MEM (name,LENGTH args) (consts_of_upd upd)) ∧
      (∀p. MEM p (axioms_of_upd upd) ⇒
        constrain_interpretation cs i satisfies (sigof (upd::ctxt),[],p))
      ⇒
      (constrain_interpretation cs i) models (thyof (upd::ctxt))``,
*)

val _ = export_theory()
