open HolKernel boolLib bossLib lcsymtacs
open setSpecTheory holSyntaxTheory holSyntaxExtraTheory holSemanticsTheory holSoundnessTheory
val _ = temp_tight_equality()
val _ = new_theory"holConsistency"

val mem = ``mem:'U->'U->bool``

val _ = export_theory()
