open HolKernel boolLib bossLib lcsymtacs
open setSpecTheory holSyntaxTheory holSoundnessTheory
val _ = temp_tight_equality()
val _ = new_theory"holConsistency"

val mem = ``mem:'U->'U->bool``

val is_consistent_def = xDefine "is_consistent_def"`
  is_consistent0 ^mem ctxt ⇔
    ∀i. i models (sigof ctxt, set (axexts ctxt)) ⇒
        ∃i'. i' models (thyof ctxt)`
val _ = Parse.overload_on("is_consistent",``is_consistent0 ^mem``)

(*
val consistency = store_thm("consistency",
  ``is_set_theory ^mem ⇒
    ∀ctxt. context_ok ctxt ∧
           FILTER (λu. ∃p. u = NewAxiom p) ctxt = [] ⇒
      (ctxt,[]) |- (Var "x" Bool === Var "x" Bool) ∧
      ¬((ctxt,[]) |- (Var "x" Bool === Var "y" Bool))``,
  rw[] >- (
    match_mp_tac (List.nth(CONJUNCTS proves_rules,8)) >>
    simp[term_ok_def,type_ok_def] >>
    imp_res_tac context_ok_sig >>
    fs[is_std_sig_def] ) >>
  spose_not_then strip_assume_tac >>
  imp_res_tac soundness >>
  fs[entails_def]
*)

val _ = export_theory()
