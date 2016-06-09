open HolKernel Parse boolLib bossLib preamble
open set_sepTheory cfHeapsBaseTheory cfHeapsLib

val _ = new_theory "cfHeaps"

(*------------------------------------------------------------------*)
(** Locality *)

(* local = frame rule + consequence rule + garbage collection *)

val local_def = Define `
  local cf env (H: hprop) (Q: v -> hprop) =
    !(h: heap). H h ==> ?H1 H2 Q1.
      (H1 * H2) h /\
      cf env H1 Q1 /\
      (Q1 *+ H2 ==+> Q *+ GC)`

val is_local_def = Define `
  is_local cf = (cf = local cf)`

(* Properties of [local] *)

val local_elim = store_thm ("local_elim",
  ``!cf env H Q. cf env H Q ==> local cf env H Q``,
  fs [local_def] \\ rpt strip_tac \\
  Q.LIST_EXISTS_TAC [`H`, `emp`, `Q`] \\
  rew_heap \\ fs [SEP_IMP_def, STAR_def] \\
  rpt strip_tac \\ qcase_tac `Q x s` \\ Q.LIST_EXISTS_TAC [`{}`, `s`] \\
  fs [GC_def, SEP_EXISTS] \\ strip_tac THEN1 SPLIT_TAC \\
  qexists_tac `emp` \\ fs [emp_def]
)

val local_local = store_thm ("local_local",
  ``!cf. local (local cf) = local cf``,
  qsuff_tac `!cf env H Q. local (local cf) env H Q = local cf env H Q`
  THEN1 (metis_tac []) \\
  rpt strip_tac \\ eq_tac \\
  fs [local_elim] \\
  fs [local_def] \\ rpt strip_tac \\ first_x_assum drule \\
  disch_then (qx_choosel_then [`H1`, `H2`, `Q1`] strip_assume_tac) \\
  fs [STAR_def] \\ qcase_tac `SPLIT h (h1, h2)` \\
  first_x_assum drule \\
  disch_then (qx_choosel_then [`H1'`, `H2'`, `Q1'`] strip_assume_tac) \\
  Q.LIST_EXISTS_TAC [`H1'`, `H2' * H2`, `Q1'`] \\ fs [PULL_EXISTS] \\
  qcase_tac `SPLIT h1 (h11, h12)` \\
  `SPLIT h (h11, h12 UNION h2)` by SPLIT_TAC \\
  `(H2' * H2) (h12 UNION h2)` by (fs [STAR_def] \\ SPLIT_TAC) \\
  asm_exists_tac \\ fs [] \\
  fs [SEP_IMPPOST_def, STARPOST_def] \\ qx_gen_tac `x` \\
  rpt (first_x_assum (qspec_then `x` assume_tac)) \\
  rewrite_tac [STAR_ASSOC] \\
  match_mp_tac SEP_IMP_TRANS \\ qexists_tac `Q1 x * GC * H2` \\ strip_tac
  THEN1 (match_mp_tac SEP_IMP_STAR \\ fs [SEP_IMP_REFL]) \\
  match_mp_tac SEP_IMP_TRANS \\ qexists_tac `Q x * (GC * GC)` \\ strip_tac
  THENL [all_tac, fs [GC_STAR_GC, SEP_IMP_REFL]] \\
  qsuff_tac `SEP_IMP ((Q1 x * H2) * GC) ((Q x * GC) * GC)`
  THEN1 fs [AC STAR_ASSOC STAR_COMM] \\
  match_mp_tac SEP_IMP_STAR \\ fs [SEP_IMP_REFL]
)

val local_is_local = store_thm ("local_is_local",
  ``!F. is_local (local F) = T``,
  metis_tac [is_local_def, local_local]
)

val _ = export_theory()
