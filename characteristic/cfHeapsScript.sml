(*
  Defines what is means for a CF separation logic assertion to be "local".
*)
open preamble set_sepTheory
open cfHeapsBaseTheory cfHeapsBaseLib

val _ = new_theory "cfHeaps"

fun sing x = [x]

(*------------------------------------------------------------------*)
(* hchange: using a [H1 ==>> H2] theorem modulo frame rule *)

Theorem hchange_lemma':
   !H1 H1' H H' H2.
    H1 ==>> H1' ==>
    H ==>> H1 * H2 /\
    H1' * H2 ==>> H' ==>
    H ==>> H'
Proof
  rpt strip_tac \\ irule SEP_IMP_TRANS \\ qexists_tac `H1 * H2` \\ fs [] \\
  irule SEP_IMP_TRANS \\ qexists_tac `H1' * H2` \\ hsimpl \\ fs []
QED

Theorem hchange_lemma:
   !H1 H1' H H' H2.
    H1 ==>> H1' /\
    H ==>> H1 * H2 /\
    H1' * H2 ==>> H' ==>
    H ==>> H'
Proof
  rpt strip_tac \\ irule SEP_IMP_TRANS \\ qexists_tac `H1 * H2` \\ fs [] \\
  irule SEP_IMP_TRANS \\ qexists_tac `H1' * H2` \\ hsimpl \\ fs []
QED

(*------------------------------------------------------------------*)
(** Locality *)

(* local = frame rule + consequence rule + garbage collection *)

val local_def = Define `
  local cf (H: hprop) (Q: res -> hprop) =
    !(h: heap). H h ==> ?H1 H2 Q1.
      (H1 * H2) h /\
      cf H1 Q1 /\
      (Q1 *+ H2 ==+> Q *+ GC)`

val is_local_def = Define `
  is_local cf = (cf = local cf)`

(* Properties of [local] *)

Theorem local_elim:
   !cf H Q. cf H Q ==> local cf H Q
Proof
  fs [local_def] \\ rpt strip_tac \\
  Q.LIST_EXISTS_TAC [`H`, `emp`, `Q`] \\ hsimpl \\ rew_heap
QED

Theorem local_local:
   !cf. local (local cf) = local cf
Proof
  qsuff_tac `!cf H Q. local (local cf) H Q = local cf H Q`
  THEN1 (metis_tac []) \\
  rpt strip_tac \\ eq_tac \\
  fs [local_elim] \\
  fs [local_def] \\ rpt strip_tac \\ first_x_assum drule \\
  disch_then (qx_choosel_then [`H1`, `H2`, `Q1`] strip_assume_tac) \\
  fs [STAR_def] \\ rename1 `SPLIT h (h1, h2)` \\
  first_x_assum drule \\
  disch_then (qx_choosel_then [`H1'`, `H2'`, `Q1'`] strip_assume_tac) \\
  Q.LIST_EXISTS_TAC [`H1'`, `H2' * H2`, `Q1'`] \\ fs [PULL_EXISTS] \\
  rename1 `SPLIT h1 (h11, h12)` \\
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
QED

Theorem local_is_local:
   !F. is_local (local F) = T
Proof
  metis_tac [is_local_def, local_local]
QED

Theorem is_local_prove:
   !F. (!H Q. F H Q <=> local F H Q) ==> is_local F
Proof
  rpt strip_tac \\ fs [is_local_def] \\
  NTAC 2 (irule EQ_EXT \\ gen_tac) \\ fs []
QED

Theorem local_frame_gc:
   !F H H1 H2 Q1 Q.
      is_local F ==>
      F H1 Q1 ==>
      H ==>> H1 * H2 ==>
      Q1 *+ H2 ==+> Q *+ GC ==>
      F H Q
Proof
  fs [is_local_def] \\ rpt strip_tac \\
  qpat_x_assum `_ = local _` (once_rewrite_tac o sing) \\
  rewrite_tac [local_def] \\ rpt strip_tac \\
  Q.LIST_EXISTS_TAC [`H1`, `H2`, `Q1`] \\ strip_tac \\ fs [SEP_IMP_def]
QED

Theorem local_frame:
   !H1 H2 Q1 F H Q.
      is_local F ==>
      F H1 Q1 ==>
      H ==>> H1 * H2 ==>
      Q1 *+ H2 ==+> Q ==>
      F H Q
Proof
  fs [is_local_def] \\ rpt strip_tac \\
  qpat_x_assum `_ = local _` (once_rewrite_tac o sing) \\
  rewrite_tac [local_def] \\ rpt strip_tac \\
  Q.LIST_EXISTS_TAC [`H1`, `H2`, `Q1`] \\ strip_tac
  THEN1 (fs [SEP_IMP_def])
  THEN1 (
    rew_heap \\ qx_gen_tac `x` \\
    first_assum (fn t => irule (MATCH_MP hchange_lemma' (Q.SPEC `x` t))) \\
    QUANT_TAC [("x'", `x`, [])] \\ hsimpl \\ qexists_tac `emp` \\ hsimpl
  )
QED

Theorem local_gc_pre_on:
   !HG H' F H Q.
     is_local F ==>
     H ==>> HG * H' ==>
     F H' Q ==>
     F H Q
Proof
  rpt strip_tac \\ fs [is_local_def] \\
  qpat_x_assum `_ = local _` (once_rewrite_tac o sing) \\
  fs [local_def] \\ rpt strip_tac \\
  Q.LIST_EXISTS_TAC [`H'`, `HG`, `Q`] \\ rpt strip_tac
  THEN1 (once_rewrite_tac [STAR_COMM] \\ fs [SEP_IMP_def])
  THEN1 (fs [])
  THEN1 hsimpl
QED

Theorem local_gc_post:
   !Q' F H Q.
     is_local F ==>
     F H Q' ==>
     Q' ==+> Q *+ GC ==>
     F H Q
Proof
  rpt strip_tac \\ fs [is_local_def] \\
  qpat_x_assum `_ = local _` (once_rewrite_tac o sing) \\
  fs [local_def] \\ rpt strip_tac \\
  Q.LIST_EXISTS_TAC [`H`, `&T`, `Q'`] \\ rpt strip_tac
  THEN1 (fs [STAR_def, cond_def, SPLIT_emp2])
  THEN1 (fs [])
  THEN1 (hsimpl \\ fs [SEP_IMPPOST_def, STARPOST_def])
QED

(* Extraction of premisses from [local] *)

Theorem local_intro_prop:
   !F H P Q.
      is_local F ==>
      (P ==> F H Q) ==>
      F (H * cond P) Q
Proof
  rpt strip_tac \\ fs [is_local_def] \\
  qpat_x_assum `_ = local _` (once_rewrite_tac o sing) \\
  fs [local_def] \\ rpt strip_tac \\
  Q.LIST_EXISTS_TAC [`H`, `emp`, `Q`] \\ rew_heap \\ rpt strip_tac \\
  TRY (fs [STAR_def, cond_def] \\ SPLIT_TAC) \\ hsimpl
QED

(** Extraction of existentials from [local] *)

Theorem local_extract_exists:
   !F A J Q.
      is_local F ==>
      (!x. F (J x) Q) ==>
      F ($SEP_EXISTS J) Q
Proof
  rpt strip_tac \\ fs [is_local_def] \\
  qpat_x_assum `_ = local _` (once_rewrite_tac o sing) \\
  fs [local_def] \\ rpt strip_tac \\ fs [SEP_EXISTS] \\ rename1 `J x _` \\
  Q.LIST_EXISTS_TAC [`J x`, `emp`, `Q`] \\ rpt strip_tac \\ rew_heap \\
  hsimpl
QED

(** Auxiliary lemmas for [hclean]. Mostly repackaging of previous lemmas *)

Theorem hclean_prop:
  !F H P Q.
      is_local F /\
      (P ==> F H Q) ==>
      F (H * cond P) Q
Proof
  fs [local_intro_prop]
QED

Theorem hclean_prop_single:
   !F P Q.
      is_local F /\
      (P ==> F emp Q) ==>
      F (cond P) Q
Proof
  qx_gen_tac `HF` \\
  qspecl_then [`HF`, `emp`] mp_tac local_intro_prop \\
  rew_heap
QED

Theorem hclean_exists_single:
   !F A J Q.
      is_local F /\
      (!x. F (J x) Q) ==>
      F ($SEP_EXISTS J) Q
Proof
  fs [local_extract_exists]
QED

val _ = export_theory()
