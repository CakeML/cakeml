open preamble
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

val NUM_Litv = store_thm ("NUM_Litv[simp]",
  ``NUM n (Litv (IntLit k)) = (k = &n)``,
  fs [NUM_def] \\ eq_tac \\ fs []
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

val BOOL_T_Conv = store_thm ("BOOL_T_Conv[simp]",
  ``BOOL T (Conv (SOME ("true", TypeId (Short "bool"))) []) = T``,
  fs [BOOL_def, semanticPrimitivesTheory.Boolv_def]
)

val BOOL_F_Conv = store_thm ("BOOL_F_Conv[simp]",
  ``BOOL F (Conv (SOME ("false", TypeId (Short "bool"))) []) = T``,
  fs [BOOL_def, semanticPrimitivesTheory.Boolv_def]
)

val BOOL_Boolv = store_thm ("BOOL_Boolv[simp]",
  ``BOOL b (Boolv bv) = (b = bv)``,
  fs [BOOL_def, semanticPrimitivesTheory.Boolv_def] \\
  every_case_tac \\ fs []
)

(*------------------------------------------------------------------*)
(* Used for cleaning up after unfolding [build_cases] (in cf_match) *)

val exists_v_of_pat_norest_length = store_thm (
  "exists_v_of_pat_norest_length",
  ``!envC pat insts v.
     (?insts. v_of_pat_norest envC pat insts = SOME v) <=>
     (?insts. LENGTH insts = LENGTH (pat_bindings pat []) /\
              v_of_pat_norest envC pat insts = SOME v)``,
  rpt strip_tac \\ eq_tac \\ fs [] \\ rpt strip_tac \\ instantiate \\
  progress v_of_pat_norest_insts_length
)

val forall_v_of_pat_norest_length = store_thm (
  "forall_v_of_pat_norest_length",
  ``!envC pat insts v P.
     (!insts. v_of_pat_norest envC pat insts = SOME v ==> P insts) <=>
     (!insts. LENGTH insts = LENGTH (pat_bindings pat []) ==>
              v_of_pat_norest envC pat insts = SOME v ==>
              P insts)``,
  rpt strip_tac \\ eq_tac \\ fs [] \\ rpt strip_tac \\
  progress v_of_pat_norest_insts_length \\ first_assum progress
)

val _ = export_theory()
