open HolKernel boolLib bossLib lcsymtacs
open setSpecTheory holSyntaxTheory holSyntaxExtraTheory holSemanticsTheory holSoundnessTheory
val _ = temp_tight_equality()
val _ = new_theory"holConsistency"

val mem = ``mem:'U->'U->bool``

val is_consistent_def = xDefine "is_consistent_def"`
  is_consistent0 ^mem ctxt ⇔
    ∀i. i models (sigof ctxt, set (axexts ctxt)) ⇒
        ∃i'. i' models (thyof ctxt)`
val _ = Parse.overload_on("is_consistent",``is_consistent0 ^mem``)

val _ = export_theory()
