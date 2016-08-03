open preamble set_sepTheory

val _ = new_theory "cfHeapsBase"

(*------------------------------------------------------------------*)
(** Heaps *)

val _ = Datatype `
  ffi = Str string
      | Num num
      | Cons ffi ffi
      | Stream (num llist)`

val _ = type_abbrev("loc", ``:num``) (* should be: temp_type_abbrev *)

val _ = Datatype `
  heap_part = Mem loc (v semanticPrimitives$store_v)
            | FFI_part num ffi (word8 list -> ffi -> (word8 list # ffi) option)`

val _ = type_abbrev("heap", ``:heap_part set``)
val _ = type_abbrev("hprop", ``:heap -> bool``)

val _ = type_abbrev("ffi_proj",
  ``: ('ffi -> (num |-> ffi)) #
      ((num |-> ffi) -> 'ffi -> 'ffi)``)

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
  cell l v = one (Mem l v)`

(* A reference cell, as a convenience wrapper over cell and Refv *)
val REF_def = Define `
  REF rv xv =
    SEP_EXISTS loc. cond (rv = Loc loc) * cell loc (Refv xv)`

(* An array cell, as a wrapper over cell and Varray *)
val ARRAY_def = Define `
  ARRAY av vl =
    SEP_EXISTS loc. cond (av = Loc loc) * cell loc (Varray vl)`

(* A bytearray cell, as a wrapper over cell and W8array *)
val W8ARRAY_def = Define `
  W8ARRAY av wl =
    SEP_EXISTS loc. cond (av = Loc loc) * cell loc (W8array wl)`

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

val _ = overload_on ("&", Term `cond`)

val _ = overload_on ("~~>>", Term `cell`)
val _ = add_infix ("~~>>", 690, HOLgrammars.NONASSOC)

val _ = overload_on ("~~>", Term `REF`)
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

val SPLIT_emp1 = store_thm ("SPLIT_emp1",
  ``!h h'. SPLIT h ({}, h') = (h' = h)``,
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
     (H * l ~~>> v ==>> H' * l ~~>> v')``,
  rpt strip_tac \\ fs [SEP_IMP_def, cell_def, one_def, STAR_def] \\ SPLIT_TAC
)

val SEP_IMP_cell_frame_single_l = store_thm ("SEP_IMP_cell_frame_single_l",
  ``!H' l v v'.
     (v = v') /\ (emp ==>> H') ==>
     (l ~~>> v ==>> H' * l ~~>> v')``,
  rpt strip_tac \\ fs [SEP_IMP_def, cell_def, one_def, emp_def, STAR_def] \\
  simp [Once CONJ_COMM] \\ asm_exists_tac \\ SPLIT_TAC
)

val SEP_IMP_cell_frame_single_r = store_thm ("SEP_IMP_cell_frame_single_r",
  ``!H l v v'.
     (v = v') /\ (H ==>> emp) ==>
     (H * l ~~>> v ==>> l ~~>> v')``,
  rpt strip_tac \\ fs [SEP_IMP_def, cell_def, one_def, emp_def, STAR_def] \\
  rpt strip_tac \\ res_tac \\ SPLIT_TAC
)

val SEP_IMP_cell_frame_single = store_thm ("SEP_IMP_cell_frame_single",
  ``!H l v v'.
     (v = v') /\ (emp ==>> emp) ==>
     (l ~~>> v ==>> l ~~>> v')``,
  rpt strip_tac \\ fs [SEP_IMP_def, cell_def, one_def, emp_def, STAR_def] \\
  rpt strip_tac \\ res_tac \\ SPLIT_TAC
)

val SEP_IMP_REF_frame = store_thm ("SEP_IMP_REF_frame",
  ``!H H' r v v'.
     (v = v') /\ (H ==>> H') ==>
     (H * r ~~> v ==>> H' * r ~~> v')``,
  rpt strip_tac \\
  fs [SEP_IMP_def, REF_def, cond_def, cell_def, one_def, STAR_def] \\ SPLIT_TAC
)

val SEP_IMP_REF_frame_single_l = store_thm ("SEP_IMP_REF_frame_single_l",
  ``!H' r v v'.
     (v = v') /\ (emp ==>> H') ==>
     (r ~~> v ==>> H' * r ~~> v')``,
  rpt strip_tac \\
  fs [SEP_IMP_def, REF_def, cond_def, SEP_EXISTS, cell_def] \\
  fs [one_def, emp_def, STAR_def] \\ rpt strip_tac \\ rw [] \\
  asm_exists_tac \\ SPLIT_TAC
)

val SEP_IMP_REF_frame_single_r = store_thm ("SEP_IMP_REF_frame_single_r",
  ``!H r v v'.
     (v = v') /\ (H ==>> emp) ==>
     (H * r ~~> v ==>> r ~~> v')``,
  rpt strip_tac \\
  fs [SEP_IMP_def, REF_def, cond_def, SEP_EXISTS, cell_def, one_def] \\
  fs [emp_def, STAR_def] \\ rpt strip_tac \\ res_tac \\ SPLIT_TAC
)

val SEP_IMP_REF_frame_single = store_thm ("SEP_IMP_REF_frame_single",
  ``!H r v v'.
     (v = v') /\ (emp ==>> emp) ==>
     (r ~~> v ==>> r ~~> v')``,
  rpt strip_tac \\
  fs [SEP_IMP_def, REF_def, cond_def, SEP_EXISTS, cell_def, one_def] \\
  fs [emp_def, STAR_def] \\ rpt strip_tac \\ res_tac \\ SPLIT_TAC
)

val SEP_IMP_ARRAY_frame = store_thm ("SEP_IMP_ARRAY_frame",
  ``!H H' a vl vl'.
     (vl = vl') /\ (H ==>> H') ==>
     (H * ARRAY a vl ==>> H' * ARRAY a vl')``,
  rpt strip_tac \\
  fs [SEP_IMP_def, ARRAY_def, cond_def, cell_def, one_def, STAR_def] \\
  SPLIT_TAC
)

val SEP_IMP_ARRAY_frame_single_l = store_thm ("SEP_IMP_ARRAY_frame_single_l",
  ``!H' a vl vl'.
     (vl = vl') /\ (emp ==>> H') ==>
     (ARRAY a vl ==>> H' * ARRAY a vl')``,
  rpt strip_tac \\
  fs [SEP_IMP_def, ARRAY_def, cond_def, SEP_EXISTS, cell_def] \\
  fs [one_def, emp_def, STAR_def] \\ rpt strip_tac \\ rw [] \\
  asm_exists_tac \\ SPLIT_TAC
)

val SEP_IMP_ARRAY_frame_single_r = store_thm ("SEP_IMP_ARRAY_frame_single_r",
  ``!H a vl vl'.
     (vl = vl') /\ (H ==>> emp) ==>
     (H * ARRAY a vl ==>> ARRAY a vl')``,
  rpt strip_tac \\
  fs [SEP_IMP_def, ARRAY_def, cond_def, SEP_EXISTS, cell_def, one_def] \\
  fs [emp_def, STAR_def] \\ rpt strip_tac \\ res_tac \\ SPLIT_TAC
)

val SEP_IMP_ARRAY_frame_single = store_thm ("SEP_IMP_ARRAY_frame_single",
  ``!H a vl vl'.
     (vl = vl') /\ (emp ==>> emp) ==>
     (ARRAY a vl ==>> ARRAY a vl')``,
  rpt strip_tac \\
  fs [SEP_IMP_def, ARRAY_def, cond_def, SEP_EXISTS, cell_def, one_def] \\
  fs [emp_def, STAR_def] \\ rpt strip_tac \\ res_tac \\ SPLIT_TAC
)

val SEP_IMP_W8ARRAY_frame = store_thm ("SEP_IMP_W8ARRAY_frame",
  ``!H H' a wl wl'.
     (wl = wl') /\ (H ==>> H') ==>
     (H * W8ARRAY a wl ==>> H' * W8ARRAY a wl')``,
  rpt strip_tac \\
  fs [SEP_IMP_def, W8ARRAY_def, cond_def, cell_def, one_def, STAR_def] \\
  SPLIT_TAC
)

val SEP_IMP_W8ARRAY_frame_single_l = store_thm (
  "SEP_IMP_W8ARRAY_frame_single_l",
  ``!H' a wl wl'.
     (wl = wl') /\ (emp ==>> H') ==>
     (W8ARRAY a wl ==>> H' * W8ARRAY a wl')``,
  rpt strip_tac \\
  fs [SEP_IMP_def, W8ARRAY_def, cond_def, SEP_EXISTS, cell_def] \\
  fs [one_def, emp_def, STAR_def] \\ rpt strip_tac \\ rw [] \\
  asm_exists_tac \\ SPLIT_TAC
)

val SEP_IMP_W8ARRAY_frame_single_r = store_thm (
  "SEP_IMP_W8ARRAY_frame_single_r",
  ``!H a wl wl'.
     (wl = wl') /\ (H ==>> emp) ==>
     (H * W8ARRAY a wl ==>> W8ARRAY a wl')``,
  rpt strip_tac \\
  fs [SEP_IMP_def, W8ARRAY_def, cond_def, SEP_EXISTS, cell_def, one_def] \\
  fs [emp_def, STAR_def] \\ rpt strip_tac \\ res_tac \\ SPLIT_TAC
)

val SEP_IMP_W8ARRAY_frame_single = store_thm (
  "SEP_IMP_W8ARRAY_frame_single",
  ``!H a wl wl'.
     (wl = wl') /\ (emp ==>> emp) ==>
     (W8ARRAY a wl ==>> W8ARRAY a wl')``,
  rpt strip_tac \\
  fs [SEP_IMP_def, W8ARRAY_def, cond_def, SEP_EXISTS, cell_def, one_def] \\
  fs [emp_def, STAR_def] \\ rpt strip_tac \\ res_tac \\ SPLIT_TAC
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
(** Extraction from H1 in H1 ==>> H2 *)

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
(** Simplification in H2 on H1 ==>> H2 *)

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

val _ = export_theory()
