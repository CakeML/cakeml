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

(*------------------------------------------------------------------*)
(* Automatic rewrites *)


val INT_Litv = store_thm ("INT_Litv[simp]",
  ``INT i (Litv (IntLit k)) = (i = k)``,
  fs [INT_def] \\ eq_tac \\ fs []
)

val CHAR_Litv = store_thm ("CHAR_Litv[simp]",
  ``CHAR c (Litv (Char c')) = (c = c')``,
  fs [CHAR_def] \\ eq_tac \\ fs []
)

val STRING_Litv = store_thm ("STRING_Litv[simp]",
  ``STRING_TYPE s (Litv (StrLit s')) = (s' = explode s)``,
  fs [STRING_TYPE_def] \\ eq_tac \\ fs []
)

val WORD8_Litv = store_thm ("WORD8_Litv[simp]",
  ``WORD w (Litv (Word8 w')) = (w = w')``,
  fs [WORD_def, w2w_def] \\ eq_tac \\ fs []
)

val WORD64_Litv = store_thm ("WORD64_Litv[simp]",
  ``WORD w (Litv (Word64 w')) = (w = w')``,
  fs [WORD_def, w2w_def] \\ eq_tac \\ fs []
)

val UNIT_Conv = store_thm ("UNIT_Conv[simp]",
  ``UNIT_TYPE () (Conv NONE []) = T``,
  fs [UNIT_TYPE_def]
)

val _ = export_theory()
