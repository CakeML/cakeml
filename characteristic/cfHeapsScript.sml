open HolKernel Parse boolLib bossLib preamble
open set_sepTheory

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

(* in set_sepTheory: emp, one, STAR, SEP_IMP, SEP_EXISTS, cond *)

(* STAR for post-conditions *)
val STARPOST_def = Define `
  STARPOST (Q: v -> hprop) (H: hprop) =
    \x. (Q x) * H`

(* SEP_IMP lifted to post-conditions *)
val SEP_IMPPOST_def = Define `
  SEP_IMPPOST (Q1: v -> hprop) (Q2: v -> hprop) =
    !x. SEP_IMP (Q1 x) (Q2 x)`

(* Garbage collection predicate *)
val GC_def = Define `GC: hprop = SEP_EXISTS H. H`

(* cond specialized to equality to some value; as a post-condition *)
val cond_eq_def = Define `
  cond_eq v = \x. cond (x = v)`

(* A single memory cell. *)
val cell_def = Define `
  cell (l: loc) (v: v semanticPrimitives$store_v) = one (l, v)`

(*------------------------------------------------------------------*)
(** Notations for heap predicates *)

val _ = overload_on ("*+", Term `STARPOST`)
val _ = add_infix ("*+", 580, HOLgrammars.LEFT)

val _ = overload_on ("==>>", Term `SEP_IMP`)
val _ = add_infix ("==>>", 470, HOLgrammars.RIGHT)

val _ = overload_on ("==+>", Term `SEP_IMPPOST`)
val _ = add_infix ("==+>", 470, HOLgrammars.RIGHT)

(* val _ = add_rule {fixity = Closefix, term_name = "cond", *)
(*                   block_style = (AroundEachPhrase, (PP.CONSISTENT,2)), *)
(*                   paren_style = OnlyIfNecessary, *)
(*                   pp_elements = [TOK "<", TM, TOK ">"]} *)

(* val _ = add_rule {fixity = Closefix, term_name = "cond_eq", *)
(*                   block_style = (AroundEachPhrase, (PP.CONSISTENT,2)), *)
(*                   paren_style = OnlyIfNecessary, *)
(*                   pp_elements = [TOK "<=", TM, TOK ">"]} *)

val _ = overload_on ("~~>", Term `cell`)
val _ = add_infix ("~~>", 690, HOLgrammars.NONASSOC)

(*------------------------------------------------------------------*)
(** Low level lemmas about SPLIT and SPLIT3 *)

val SPLIT3_of_SPLIT_emp3 = store_thm ("SPLIT3_of_SPLIT_emp3",
  ``!h h1 h2. SPLIT h (h1, h2) ==> SPLIT3 h (h1, h2, {})``,
  SPLIT_TAC
)

val SPLIT3_swap23 = store_thm ("SPLIT3_swap23",
  ``!h h1 h2 h3. SPLIT3 h (h1, h2, h3) ==> SPLIT3 h (h1, h3, h2)``,
  SPLIT_TAC
)

val SPLIT_emp2 = store_thm ("SPLIT_emp2",
  ``!h h'. SPLIT h (h', {}) = (h' = h)``,
  SPLIT_TAC
)

val SPLIT_of_SPLIT3_2u3 = store_thm ("SPLIT_of_SPLIT3_2u3",
  ``!h h1 h2 h3. SPLIT3 h (h1, h2, h3) ==> SPLIT h (h1, h2 UNION h3)``,
  SPLIT_TAC
)

(*------------------------------------------------------------------*)
(** Additionnal properties of STAR *)

val STARPOST_emp = store_thm ("STARPOST_emp",
  ``!Q. Q *+ emp = Q``,
  strip_tac \\ fs [STARPOST_def] \\ metis_tac [SEP_CLAUSES]
)

val SEP_IMP_frame_single_l = store_thm ("SEP_IMP_frame_single_l",
  ``!H' R.
     (emp ==>> H') ==>
     (R ==>> H' * R)``,
  rpt strip_tac \\ fs [SEP_IMP_def, STAR_def, emp_def] \\
  qx_gen_tac `s` \\ strip_tac \\ Q.LIST_EXISTS_TAC [`{}`, `s`] \\
  SPLIT_TAC
)

val SEP_IMP_frame_single_r = store_thm ("SEP_IMP_frame_single_r",
  ``!H R.
     (H ==>> emp) ==>
     (H * R ==>> R)``,
  rpt strip_tac \\ fs [SEP_IMP_def, STAR_def, emp_def] \\
  qx_gen_tac `s` \\ strip_tac \\ res_tac \\ SPLIT_TAC
)

val SEP_IMP_cell_frame = store_thm ("SEP_IMP_cell_frame",
  ``!H H' l v v'.
     (v = v') /\ (H ==>> H') ==>
     (H * l ~~> v ==>> H' * l ~~> v')``,
  rpt strip_tac \\ fs [SEP_IMP_def, cell_def, one_def, STAR_def] \\ SPLIT_TAC
)

val SEP_IMP_cell_frame_single_l = store_thm ("SEP_IMP_cell_frame_single_l",
  ``!H' l v v'.
     (v = v') /\ (emp ==>> H') ==>
     (l ~~> v ==>> H' * l ~~> v')``,
  rpt strip_tac \\ fs [SEP_IMP_def, cell_def, one_def, emp_def, STAR_def] \\
  simp [Once CONJ_COMM] \\ asm_exists_tac \\ SPLIT_TAC
)

val SEP_IMP_cell_frame_single_r = store_thm ("SEP_IMP_cell_frame_single_r",
  ``!H l v v'.
     (v = v') /\ (H ==>> emp) ==>
     (H * l ~~> v ==>> l ~~> v')``,
  rpt strip_tac \\ fs [SEP_IMP_def, cell_def, one_def, emp_def, STAR_def] \\
  rpt strip_tac \\ res_tac \\ SPLIT_TAC
)

(*------------------------------------------------------------------*)
(** Normalization of STAR *)

val rew_heap_thms =
  [AC STAR_COMM STAR_ASSOC, SEP_CLAUSES, STARPOST_emp,
   SEP_IMPPOST_def, STARPOST_def, cond_eq_def]

val rew_heap = full_simp_tac bool_ss rew_heap_thms

(*------------------------------------------------------------------*)
(** Properties of GC *)

val GC_STAR_GC = store_thm ("GC_STAR_GC",
  ``GC * GC = GC``,
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
    SEP_EXISTS l. cond (r = Loc l) * l ~~> Refv v`

(*------------------------------------------------------------------*)
(** Extraction from H1 in SEP_IMP H1 H2 *)

val hpull_prop = store_thm ("hpull_prop",
  ``!H H' P.
     (P ==> H ==>> H') ==>
     (H * cond P ==>> H')``,
  rpt strip_tac \\ fs [SEP_IMP_def, STAR_def, cond_def] \\
  SPLIT_TAC
)

val hpull_prop_single = store_thm ("hpull_prop_single",
  ``!H' P.
     (P ==> emp ==>> H') ==>
     (cond P ==>> H')``,
  rpt strip_tac \\ fs [SEP_IMP_def, STAR_def, cond_def, emp_def] \\
  SPLIT_TAC
)

val hpull_exists_single = store_thm ("hpull_exists_single",
  ``!A H' J.
     (!x. (J x) ==>> H') ==>
     ($SEP_EXISTS J ==>> H')``,
  rpt strip_tac \\ fs [SEP_IMP_def, STAR_def, SEP_EXISTS, emp_def] \\
  SPLIT_TAC
)

val SEP_IMP_rew = store_thm ("SEP_IMP_rew",
  ``!H1 H2 H1' H2'. (H1 = H2) ==> (H1' = H2') ==> (H1 ==>> H1') = (H2 ==>> H2')``,
  rew_heap
)

(*------------------------------------------------------------------*)
(** Simplification in H2 on SEP_IMP H1 H2 *)

(** Lemmas *)

val hsimpl_prop = store_thm ("hsimpl_prop",
  ``!H' H P.
     P /\ (H' ==>> H) ==>
     (H' ==>> H * cond P)``,
  rpt strip_tac \\ fs [SEP_IMP_def, STAR_def, cond_def] \\
  SPLIT_TAC
)

val hsimpl_prop_single = store_thm ("hsimpl_prop_single",
  ``!H' P.
     P /\ (H' ==>> emp) ==>
     (H' ==>> cond P)``,
  rpt strip_tac \\ fs [SEP_IMP_def, STAR_def, cond_def, emp_def] \\
  SPLIT_TAC
)

val hsimpl_exists_single = store_thm ("hsimpl_exists_single",
  ``!x H' J.
     (H' ==>> J x) ==>
     (H' ==>> $SEP_EXISTS J)``,
  rpt strip_tac \\ fs [SEP_IMP_def, STAR_def, SEP_EXISTS, emp_def] \\
  SPLIT_TAC
)

val hsimpl_gc = store_thm ("hsimpl_gc",
  ``!H. H ==>> GC``,
  fs [GC_def, SEP_IMP_def, SEP_EXISTS] \\ metis_tac []
)

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
