(*
  Lemmas that aid the tactics for reasoning about CF-based goals in HOL.
*)
open preamble
open set_sepTheory helperLib ConseqConv ml_translatorTheory
open cfHeapsBaseTheory cfHeapsTheory cfHeapsBaseLib cfStoreTheory
open cfNormaliseTheory cfAppTheory cfTheory
open cfTacticsBaseLib cfHeapsLib

val _ = new_theory "cfTactics"

(*
val xret_lemma = Q.store_thm ("xret_lemma",
  `!H Q.
    (H ==>> Q v * GC) ==>
    local (\H' Q'. H' ==>> Q' v) H Q`,
  rpt strip_tac \\ irule (Q.SPEC `GC` local_gc_pre_on) \\
  fs [local_is_local] \\ first_assum hchanges \\ hinst \\
  irule local_elim \\ fs [] \\ hsimpl
)*)

val xret_lemma = Q.store_thm ("xret_lemma",
  `!H Q R.
    H ==>> Q v * GC /\ R Q ==>
    local (\H' Q'. H' ==>> Q' v /\ R Q') H Q`,
  rpt strip_tac \\ irule (Q.SPEC `GC` local_gc_pre_on) \\
  fs [local_is_local] \\ first_assum hchanges \\ hinst \\
  irule local_elim \\ fs [] \\ hsimpl
)

(* todo: does it even happen? *)
val xret_lemma_unify = Q.store_thm ("xret_lemma_unify",
  `!v H. local (\H' Q'. H' ==>> Q' v) H (\x. cond (x = v) * H)`,
  rpt strip_tac \\ irule local_elim \\ fs [] \\ hsimpl
)

(*
val xret_no_gc_lemma = Q.store_thm ("xret_no_gc_lemma",
  `!v H Q.
      (H ==>> Q v) ==>
      local (\H' Q'. H' ==>> Q' v) H Q`,
  fs [local_elim]
)
*)

val xret_no_gc_lemma = Q.store_thm ("xret_no_gc_lemma",
  `!v H Q R.
      H ==>> Q v /\ R Q ==>
      local (\H' Q'. H' ==>> Q' v /\ R Q') H Q`,
  fs [local_elim]
)

(*------------------------------------------------------------------*)
(* Automatic rewrites *)


val INT_Litv = Q.store_thm ("INT_Litv[simp]",
  `INT i (Litv (IntLit k)) = (i = k)`,
  fs [INT_def] \\ eq_tac \\ fs []
)

val NUM_Litv = Q.store_thm ("NUM_Litv[simp]",
  `NUM n (Litv (IntLit k)) = (k = &n)`,
  fs [NUM_def] \\ eq_tac \\ fs []
)

val CHAR_Litv = Q.store_thm ("CHAR_Litv[simp]",
  `CHAR c (Litv (Char c')) = (c = c')`,
  fs [CHAR_def] \\ eq_tac \\ fs []
)

val STRING_Litv = Q.store_thm ("STRING_Litv[simp]",
  `STRING_TYPE s (Litv (StrLit s')) = (s = strlit s')`,
  Cases_on`s` \\ fs [STRING_TYPE_def] \\ eq_tac \\ fs []
)

val WORD8_Litv = Q.store_thm ("WORD8_Litv[simp]",
  `WORD w (Litv (Word8 w')) = (w = w')`,
  fs [WORD_def, w2w_def] \\ eq_tac \\ fs []
)

val WORD64_Litv = Q.store_thm ("WORD64_Litv[simp]",
  `WORD w (Litv (Word64 w')) = (w = w')`,
  fs [WORD_def, w2w_def] \\ eq_tac \\ fs []
)

val UNIT_Conv = Q.store_thm ("UNIT_Conv[simp]",
  `UNIT_TYPE () (Conv NONE []) = T`,
  fs [UNIT_TYPE_def]
)

val BOOL_T_Conv = Q.store_thm ("BOOL_T_Conv[simp]",
  `BOOL T (Conv (SOME (TypeStamp "true" bool_type_num)) []) = T`,
  fs [BOOL_def, semanticPrimitivesTheory.Boolv_def]
)

val BOOL_F_Conv = Q.store_thm ("BOOL_F_Conv[simp]",
  `BOOL F (Conv (SOME (TypeStamp "false" bool_type_num)) []) = T`,
  fs [BOOL_def, semanticPrimitivesTheory.Boolv_def]
)

val BOOL_Boolv = Q.store_thm ("BOOL_Boolv[simp]",
  `BOOL b (Boolv bv) = (b = bv)`,
  fs [BOOL_def, semanticPrimitivesTheory.Boolv_def] \\
  every_case_tac \\ fs []
)

(*------------------------------------------------------------------*)
(* Used for cleaning up after unfolding [build_cases] (in cf_match) *)

val exists_v_of_pat_norest_length = Q.store_thm (
  "exists_v_of_pat_norest_length",
  `!envC pat insts v.
     (?insts wildcards. v_of_pat_norest envC pat insts wildcards = SOME v) <=>
     (?insts wildcards. LENGTH insts = LENGTH (pat_bindings pat []) /\
                        LENGTH wildcards = pat_wildcards pat /\
                        v_of_pat_norest envC pat insts wildcards = SOME v)`,
  rpt strip_tac \\ eq_tac \\ fs [] \\ rpt strip_tac \\ instantiate \\
  progress v_of_pat_norest_insts_length \\
  progress v_of_pat_norest_wildcards_count \\ fs []
);

val forall_v_of_pat_norest_length = Q.store_thm (
  "forall_v_of_pat_norest_length",
  `!envC pat insts v P.
     (!insts wildcards. v_of_pat_norest envC pat insts wildcards = SOME v ==> P insts) <=>
     (!insts wildcards. LENGTH insts = LENGTH (pat_bindings pat []) ==>
                        LENGTH wildcards = pat_wildcards pat ==>
                        v_of_pat_norest envC pat insts wildcards = SOME v ==>
                        P insts)`,
  rpt strip_tac \\ eq_tac \\ fs [] \\ rpt strip_tac \\
  progress v_of_pat_norest_insts_length \\
  progress v_of_pat_norest_wildcards_count \\
  first_assum progress
);

val BOOL_T = save_thm("BOOL_T",
  EVAL ``BOOL T (Conv (SOME (TypeStamp "true" 0)) [])``);

val BOOL_F = save_thm("BOOL_F",
  EVAL ``BOOL F (Conv (SOME (TypeStamp "false" 0)) [])``);

val _ = export_theory()
