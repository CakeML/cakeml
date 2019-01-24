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
Theorem xret_lemma
  `!H Q.
    (H ==>> Q v * GC) ==>
    local (\H' Q'. H' ==>> Q' v) H Q`
  (rpt strip_tac \\ irule (Q.SPEC `GC` local_gc_pre_on) \\
  fs [local_is_local] \\ first_assum hchanges \\ hinst \\
  irule local_elim \\ fs [] \\ hsimpl
)*)

Theorem xret_lemma
  `!H Q R.
    H ==>> Q v * GC /\ R Q ==>
    local (\H' Q'. H' ==>> Q' v /\ R Q') H Q`
  (rpt strip_tac \\ irule (Q.SPEC `GC` local_gc_pre_on) \\
  fs [local_is_local] \\ first_assum hchanges \\ hinst \\
  irule local_elim \\ fs [] \\ hsimpl
)

(* todo: does it even happen? *)
Theorem xret_lemma_unify
  `!v H. local (\H' Q'. H' ==>> Q' v) H (\x. cond (x = v) * H)`
  (rpt strip_tac \\ irule local_elim \\ fs [] \\ hsimpl
)

(*
Theorem xret_no_gc_lemma
  `!v H Q.
      (H ==>> Q v) ==>
      local (\H' Q'. H' ==>> Q' v) H Q`
  (fs [local_elim]
)
*)

Theorem xret_no_gc_lemma
  `!v H Q R.
      H ==>> Q v /\ R Q ==>
      local (\H' Q'. H' ==>> Q' v /\ R Q') H Q`
  (fs [local_elim]
)

(*------------------------------------------------------------------*)
(* Automatic rewrites *)


Theorem INT_Litv[simp]
  `INT i (Litv (IntLit k)) = (i = k)`
  (fs [INT_def] \\ eq_tac \\ fs []
)

Theorem NUM_Litv[simp]
  `NUM n (Litv (IntLit k)) = (k = &n)`
  (fs [NUM_def] \\ eq_tac \\ fs []
)

Theorem CHAR_Litv[simp]
  `CHAR c (Litv (Char c')) = (c = c')`
  (fs [CHAR_def] \\ eq_tac \\ fs []
)

Theorem STRING_Litv[simp]
  `STRING_TYPE s (Litv (StrLit s')) = (s = strlit s')`
  (Cases_on`s` \\ fs [STRING_TYPE_def] \\ eq_tac \\ fs []
)

Theorem WORD_Litv[simp]
  `WORD w (Litv_WORD w') = (w = w')`
  (fs [WORD_def, Litv_WORD_def] \\ eq_tac \\ fs [bitstring_extraTheory.w2v_eq]
)

Theorem UNIT_Conv[simp]
  `UNIT_TYPE () (Conv NONE []) = T`
  (fs [UNIT_TYPE_def]
)

Theorem BOOL_T_Conv[simp]
  `BOOL T (Conv (SOME (TypeStamp "True" bool_type_num)) []) = T`
  (fs [BOOL_def, semanticPrimitivesTheory.Boolv_def]
)

Theorem BOOL_F_Conv[simp]
  `BOOL F (Conv (SOME (TypeStamp "False" bool_type_num)) []) = T`
  (fs [BOOL_def, semanticPrimitivesTheory.Boolv_def]
)

Theorem BOOL_Boolv[simp]
  `BOOL b (Boolv bv) = (b = bv)`
  (fs [BOOL_def, semanticPrimitivesTheory.Boolv_def] \\
  every_case_tac \\ fs []
)

(*------------------------------------------------------------------*)
(* Used for cleaning up after unfolding [build_cases] (in cf_match) *)

Theorem exists_v_of_pat_norest_length
  `!envC pat insts v.
     (?insts wildcards. v_of_pat_norest envC pat insts wildcards = SOME v) <=>
     (?insts wildcards. LENGTH insts = LENGTH (pat_bindings pat []) /\
                        LENGTH wildcards = pat_wildcards pat /\
                        v_of_pat_norest envC pat insts wildcards = SOME v)`
  (rpt strip_tac \\ eq_tac \\ fs [] \\ rpt strip_tac \\ instantiate \\
  progress v_of_pat_norest_insts_length \\
  progress v_of_pat_norest_wildcards_count \\ fs []
);

Theorem forall_v_of_pat_norest_length
  `!envC pat insts v P.
     (!insts wildcards. v_of_pat_norest envC pat insts wildcards = SOME v ==> P insts) <=>
     (!insts wildcards. LENGTH insts = LENGTH (pat_bindings pat []) ==>
                        LENGTH wildcards = pat_wildcards pat ==>
                        v_of_pat_norest envC pat insts wildcards = SOME v ==>
                        P insts)`
  (rpt strip_tac \\ eq_tac \\ fs [] \\ rpt strip_tac \\
  progress v_of_pat_norest_insts_length \\
  progress v_of_pat_norest_wildcards_count \\
  first_assum progress
);

val BOOL_T = save_thm("BOOL_T",
  EVAL ``BOOL T (Conv (SOME (TypeStamp "True" 0)) [])``);

val BOOL_F = save_thm("BOOL_F",
  EVAL ``BOOL F (Conv (SOME (TypeStamp "False" 0)) [])``);

val _ = export_theory()
