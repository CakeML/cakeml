open HolKernel Parse boolLib bossLib preamble
open set_sepTheory helperLib ConseqConv

val _ = new_theory "cfHeaps"

(*------------------------------------------------------------------*)
(** Heaps *)

val _ = type_abbrev("loc", ``:num``)
val _ = type_abbrev("heap", ``:(loc # v semanticPrimitives$store_v) set``)
val _ = type_abbrev("hprop", ``:heap -> bool``)

val SPLIT3_def = Define `
  SPLIT3 (s:'a set) (u,v,w) =
    ((u UNION v UNION w = s) /\
     DISJOINT u v /\ DISJOINT v w /\ DISJOINT u w)`

(* val SPLIT_ss = rewrites [SPLIT_def,SPLIT3_def,SUBSET_DEF,DISJOINT_DEF,DELETE_DEF,IN_INSERT, *)
(*                          UNION_DEF,SEP_EQ_def,EXTENSION,NOT_IN_EMPTY,IN_DEF,IN_UNION,IN_INTER, *)
(*                          IN_DIFF] *)

(* val SPLIT_TAC = FULL_SIMP_TAC (pure_ss++SPLIT_ss) [] \\ METIS_TAC [] *)
val SPLIT_TAC = fs [SPLIT_def,SPLIT3_def,SUBSET_DEF,DISJOINT_DEF,DELETE_DEF,IN_INSERT,UNION_DEF,
                         SEP_EQ_def,EXTENSION,NOT_IN_EMPTY,IN_DEF,IN_UNION,IN_INTER,IN_DIFF]
                \\ metis_tac []

(*------------------------------------------------------------------*)
(** Heap predicates *)

(* in set_sepTheory: emp, one, STAR, SEP_EXISTS, cond *)

(* STAR for post-conditions *)
val STARPOST_def = Define `
  STARPOST (Q: v -> hprop) (H: hprop) =
    \x. (Q x) * H`

(* SEP_IMP lifted for post-conditions *)
val SEP_IMPPOST_def = Define `
  SEP_IMPPOST (Q1: v -> hprop) (Q2: v -> hprop) =
    !x. SEP_IMP (Q1 x) (Q2 x)`

(* Garbage collection predicate *)
val GC_def = Define `GC: hprop = SEP_EXISTS H. H`

(*------------------------------------------------------------------*)
(** Notations for heap predicates *)

val _ = overload_on ("*+", Term `STARPOST`)
val _ = add_infix ("*+", 480, HOLgrammars.LEFT)

(* todo *)

(*------------------------------------------------------------------*)
(** Additionnal properties of STAR *)

val STARPOST_emp = Q.prove (
  `!Q. Q *+ emp = Q`,
  strip_tac \\ fs [STARPOST_def] \\ metis_tac [SEP_CLAUSES]
)

val SEP_IMP_frame_single_l = Q.prove (
  `!H' R.
     SEP_IMP emp H' ==>
     SEP_IMP R (H' * R)`,
  rpt strip_tac \\ fs [SEP_IMP_def, STAR_def, emp_def] \\
  qx_gen_tac `s` \\ strip_tac \\ Q.LIST_EXISTS_TAC [`{}`, `s`] \\
  SPLIT_TAC
)

val SEP_IMP_frame_single_r = Q.prove (
  `!H R.
     SEP_IMP H emp ==>
     SEP_IMP (H * R) R`,
  rpt strip_tac \\ fs [SEP_IMP_def, STAR_def, emp_def] \\
  qx_gen_tac `s` \\ strip_tac \\ res_tac \\ SPLIT_TAC
)

val SEP_IMP_one_frame = Q.prove (
  `!H H' l v v'.
     v = v' /\ SEP_IMP H H' ==>
     SEP_IMP (H * one (l, v)) (H' * one (l, v'))`,
  rpt strip_tac \\ fs [SEP_IMP_def, one_def, STAR_def] \\ SPLIT_TAC
)

val SEP_IMP_one_frame_single_l = Q.prove (
  `!H' l v v'.
     v = v' /\ SEP_IMP emp H' ==>
     SEP_IMP (one (l, v)) (H' * one (l, v'))`,
  rpt strip_tac \\ fs [SEP_IMP_def, one_def, emp_def, STAR_def] \\
  simp [Once CONJ_COMM] \\ asm_exists_tac \\ SPLIT_TAC
)

val SEP_IMP_one_frame_single_r = Q.prove (
  `!H l v v'.
     v = v' /\ SEP_IMP H emp ==>
     SEP_IMP (H * one (l, v)) (one (l, v'))`,
  rpt strip_tac \\ fs [SEP_IMP_def, one_def, emp_def, STAR_def] \\
  rpt strip_tac \\ res_tac \\ SPLIT_TAC
)

(*------------------------------------------------------------------*)
(** Normalization of STAR *)

val rew_heap_thms =
  [AC STAR_COMM STAR_ASSOC, SEP_CLAUSES, STARPOST_emp,
   SEP_IMPPOST_def, STARPOST_def]

val rew_heap = full_simp_tac bool_ss rew_heap_thms

(*------------------------------------------------------------------*)
(** Properties of GC *)

val GC_STAR_GC = Q.prove (
  `GC * GC = GC`,
  fs [GC_def] \\ irule EQ_EXT \\ strip_tac \\ rew_heap \\
  fs [SEP_EXISTS] \\ eq_tac \\ rpt strip_tac
  THENL [all_tac, qexists_tac `emp` \\ rew_heap] \\
  metis_tac []
)

(*------------------------------------------------------------------*)
(** Specification predicates for values *)

(* todo *)

val Ref_def = Define `
  Ref (v: v) (r: v) : hprop =
    SEP_EXISTS l. cond (r = Loc l) * one (l, Refv v)`

(*------------------------------------------------------------------*)
(** Extraction from H1 in SEP_IMP H1 H2 *)

val hpull_prop = Q.prove (
  `!H H' P.
    (P ==> SEP_IMP H H') ==>
    SEP_IMP (H * cond P) H'`,
  rpt strip_tac \\ fs [SEP_IMP_def, STAR_def, cond_def] \\
  SPLIT_TAC
)

val hpull_prop_single = Q.prove (
  `!H' P.
    (P ==> SEP_IMP emp H') ==>
    SEP_IMP (cond P) H'`,
  rpt strip_tac \\ fs [SEP_IMP_def, STAR_def, cond_def, emp_def] \\
  SPLIT_TAC
)

val hpull_exists_single = Q.prove (
  `!A H' J.
    (!x. SEP_IMP (J x) H') ==>
    SEP_IMP ($SEP_EXISTS J) H'`,
  rpt strip_tac \\ fs [SEP_IMP_def, STAR_def, SEP_EXISTS, emp_def] \\
  SPLIT_TAC
)

val SEP_IMP_rew = Q.prove (
  `!H1 H2 H1' H2'. H1 = H2 ==> H1' = H2' ==> SEP_IMP H1 H1' = SEP_IMP H2 H2'`,
  rew_heap
)

(*------------------------------------------------------------------*)
(** Simplification in H2 on SEP_IMP H1 H2 *)

(** Lemmas *)

val hsimpl_prop = Q.prove (
  `!H' H P.
    P /\ SEP_IMP H' H ==>
    SEP_IMP H' (H * cond P)`,
  rpt strip_tac \\ fs [SEP_IMP_def, STAR_def, cond_def] \\
  SPLIT_TAC
)

val hsimpl_prop_single = Q.prove (
  `!H' P.
    P /\ SEP_IMP H' emp ==>
    SEP_IMP H' (cond P)`,
  rpt strip_tac \\ fs [SEP_IMP_def, STAR_def, cond_def, emp_def] \\
  SPLIT_TAC
)

val hsimpl_exists_single = Q.prove (
  `!x H' J.
    SEP_IMP H' (J x) ==>
    SEP_IMP H' ($SEP_EXISTS J)`,
  rpt strip_tac \\ fs [SEP_IMP_def, STAR_def, SEP_EXISTS, emp_def] \\
  SPLIT_TAC
)

val hsimpl_gc = Q.prove (
  `!H. SEP_IMP H GC`,
  fs [GC_def, SEP_IMP_def, SEP_EXISTS] \\ metis_tac []
)

val _ = export_theory()
