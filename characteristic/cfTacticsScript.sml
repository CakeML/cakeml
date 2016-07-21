open HolKernel Parse boolLib bossLib preamble
open set_sepTheory helperLib ConseqConv ml_translatorTheory
open cfHeapsBaseTheory cfHeapsTheory cfHeapsBaseLib cfStoreTheory
open cfNormalizeTheory cfAppTheory cfTheory
open cfTacticsBaseLib cfHeapsLib

val _ = new_theory "cfTactics"

val xret_lemma = store_thm ("xret_lemma",
  ``!H Q.
    (H ==>> Q v * GC) ==>
    local (\H' Q'. H' ==>> Q' v) H Q``,
  rpt strip_tac \\ irule (Q.SPEC `GC` local_gc_pre_on) \\
  fs [local_is_local] \\ cheat (* need hchange/evars *)
)

(* todo: does it even happen? *)
val xret_lemma_unify = store_thm ("xret_lemma_unify",
  ``!v H. local (\H' Q'. H' ==>> Q' v) H (\x. cond (x = v) * H)``,
  rpt strip_tac \\ irule local_elim \\ fs [] \\ hsimpl
)

val xret_no_gc_lemma = store_thm ("xret_no_gc_lemma",
  ``!v H Q.
      (H ==>> Q v) ==>
      local (\H' Q'. H' ==>> Q' v) H Q``,
  fs [local_elim]
)

val _ = export_theory()
