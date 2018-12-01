(*
  Defines the heap type that the separation logic used by CF uses.
  Also defines POSTv etc.
*)
open preamble set_sepTheory
open cfTacticsBaseLib cfFFITypeTheory

val _ = new_theory "cfHeapsBase"

(*------------------------------------------------------------------*)
(** Heaps *)

(* the following is now defined in cfFFITypeTheory
val _ = Datatype `
  ffi = Str string
      | Num num
      | Cons ffi ffi
      | List (ffi list)
      | Stream (num llist)`
*)

val encode_pair_def = Define`
  encode_pair e1 e2 (x,y) = Cons (e1 x) (e2 y)`;

val encode_list_def = Define`
  encode_list e l = List (MAP e l)`;

val encode_list_11 = store_thm("encode_list_11",
  ``!xs ys.
      encode_list f xs = encode_list f ys /\
      (!x y. f x = f y <=> x = y) ==>
      xs = ys``,
  Induct \\ Cases_on `ys` \\ fs [encode_list_def] \\ rw [] \\ fs []);

val encode_option_def = Define`
  encode_option e NONE = List [] ∧
  encode_option e (SOME x) = List [e x]`;

val encode_option_11 = Q.store_thm("encode_option_11",
  `∀x y. encode_option f x = encode_option f y ∧ (∀x y. f x = f y ⇔ x = y) ⇒ x = y`,
  Cases \\ Cases \\ rw[encode_option_def] \\ metis_tac[]);

val encode_bool_def = Define
  `encode_bool F = Num 0 ∧
   encode_bool T = Num 1`;

val encode_bool_11 = Q.store_thm("encode_bool_11[simp]",
  `∀x y. encode_bool x = encode_bool y ⇔ x = y`,
  Cases \\ Cases \\ rw[encode_bool_def]);

val encode_int_def = Define`
  encode_int i = Cons (encode_bool (0 ≤ i)) (Num(Num(ABS i)))`;

val encode_int_11 = Q.store_thm("encode_int_11[simp]",
  `∀x y. encode_int x = encode_int y ⇔ x = y`,
  Cases \\ Cases \\ rw[encode_int_def]);

val _ = Datatype `
  ffi_result = FFIreturn (word8 list) 'ffi | FFIdiverge`

(* make an ffi_next function from base functions and encode/decode *)
val mk_ffi_next_def = Define`
  mk_ffi_next (encode,decode,ls) name conf bytes s =
    OPTION_BIND (ALOOKUP ls name) (λf.
    OPTION_BIND (decode s) (λs.
    OPTION_BIND (f conf bytes s) (λr.
     case r of
       FFIreturn bytes s => SOME(FFIreturn bytes (encode s))
     | FFIdiverge => SOME FFIdiverge)))`;

val _ = temp_type_abbrev("loc", ``:num``)

val _ = temp_type_abbrev("ffi_next", ``:string -> word8 list -> word8 list -> ffi -> ffi ffi_result option``);

val _ = Datatype `
  heap_part = Mem loc (v semanticPrimitives$store_v)
            | FFI_split
            | FFI_part ffi ffi_next (string list) (io_event list)
            | FFI_full (io_event list)`

val _ = type_abbrev("heap", ``:heap_part set``)
val _ = type_abbrev("hprop", ``:heap -> bool``)

val _ = Datatype `
  res = Val v
      | Exn v
      | FFIDiv string (word8 list) (word8 list)
      | Div (io_event llist)`

val _ = type_abbrev("ffi_proj",
  ``: ('ffi -> (string |-> ffi)) #
      ((string list # ffi_next) list)``)

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

val ffi_proj_pack = save_thm("ffi_proj_pack", packLib.pack_type ``:'ffi ffi_proj``);
val heap_pack = save_thm("heap_pack", packLib.pack_type ``:heap``);
val hprop_pack = save_thm("hprop_pack", packLib.pack_type ``:hprop``);

(*------------------------------------------------------------------*)
(** Heap predicates *)

(* in set_sepTheory: emp, one, STAR, SEP_IMP, SEP_EXISTS, cond *)

(* STAR for post-conditions *)
val STARPOST_def = Define `
  STARPOST (Q: res -> hprop) (H: hprop) =
    \r. (Q r) * H`

(* SEP_IMP lifted to post-conditions *)
val SEP_IMPPOST_def = Define `
  SEP_IMPPOST (Q1: res -> hprop) (Q2: res -> hprop) =
    !r. SEP_IMP (Q1 r) (Q2 r)`

val SEP_IMPPOSTv_def = Define `
  SEP_IMPPOSTv (Q1: res -> hprop) (Q2: res -> hprop) =
    !v. SEP_IMP (Q1 (Val v)) (Q2 (Val v))`

val SEP_IMPPOSTe_def = Define `
  SEP_IMPPOSTe (Q1: res -> hprop) (Q2: res -> hprop) =
    !e. SEP_IMP (Q1 (Exn e)) (Q2 (Exn e))`

val SEP_IMPPOSTf_def = Define `
  SEP_IMPPOSTf (Q1: res -> hprop) (Q2: res -> hprop) =
    !name conf bytes. SEP_IMP (Q1 (FFIDiv name conf bytes)) (Q2 (FFIDiv name conf bytes))`

val SEP_IMPPOSTd_def = Define `
  SEP_IMPPOSTd (Q1: res -> hprop) (Q2: res -> hprop) =
    !io. SEP_IMP (Q1 (Div io)) (Q2 (Div io))`

val SEP_IMPPOSTv_inv_def = Define `
  SEP_IMPPOSTv_inv (Q1: res -> hprop) (Q2: res -> hprop) =
    (SEP_IMPPOSTe Q1 Q2 /\ SEP_IMPPOSTf Q1 Q2 /\ SEP_IMPPOSTd Q1 Q2)`

val SEP_IMPPOSTe_inv_def = Define `
  SEP_IMPPOSTe_inv (Q1: res -> hprop) (Q2: res -> hprop) =
    (SEP_IMPPOSTv Q1 Q2 /\ SEP_IMPPOSTf Q1 Q2 /\ SEP_IMPPOSTd Q1 Q2)`

(* Garbage collection predicate *)
val GC_def = Define `GC: hprop = SEP_EXISTS H. H`

(* Injections for post-conditions *)
val POST_def = Define `
  POST (Qv: v -> hprop) (Qe: v -> hprop) (Qf: string -> word8 list -> word8 list -> hprop) (Qd: io_event llist -> bool) = \r.
    case r of
     | Val v => Qv v
     | Exn e => Qe e
     | FFIDiv name conf bytes => Qf name conf bytes
     | Div io => cond (Qd io)`

val POSTv_def = new_binder_definition("POSTv_def",
  ``($POSTv) (Qv: v -> hprop) =
      POST Qv (\e. cond F) (\name conf bytes. cond F) (\io. F)``)

val POSTe_def = new_binder_definition("POSTe_def",
  ``($POSTe) (Qe: v -> hprop) =
      POST (\v. cond F) Qe (\name conf bytes. cond F) (\io. F)``)

val POSTf_def = new_binder_definition("POSTf_def",
  ``($POSTf) (Qf: string -> word8 list -> word8 list -> hprop) =
      POST (\v. cond F) (\e. cond F) Qf (\io. F)``)

val POSTd_def = new_binder_definition("POSTd_def",
  ``($POSTd) (Qd: io_event llist -> bool) =
      POST (\v. cond F) (\e. cond F) (\name conf bytes. cond F) Qd``)

val POSTve_def = Define `
  POSTve (Qv: v -> hprop) (Qe: v -> hprop) =
    POST Qv Qe (\name conf bytes. cond F) (\io. F)`

val POSTvd_def = Define `
  POSTvd (Qv: v -> hprop) (Qd: io_event llist -> bool) =
    POST Qv (\e. cond F) (\name conf bytes. cond F) Qd`

val POSTed_def = Define `
  POSTed (Qe: v -> hprop) (Qd: io_event llist -> bool) =
    POST (\v. cond F) Qe (\name conf bytes. cond F) Qd`

val POST_F_def = Define `
  POST_F (r: res): hprop = cond F`

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

val IO_def = Define `
  IO s u ns = SEP_EXISTS events. one (FFI_part s u ns events) * cond (~MEM "" ns)`;

val IOx_def = Define`
  IOx (encode,decode,ls) s =
    IO (encode s) (mk_ffi_next (encode,decode,ls)) (MAP FST ls)`;

val mk_proj1_def = Define`
  mk_proj1 (encode,decode,ls) s =
    MAP (λx. (x, encode s)) (MAP FST ls)`;

val mk_proj2_def = Define`
  mk_proj2 (encode,decode,ls) =
    (MAP FST ls, mk_ffi_next (encode,decode,ls))`;

(*------------------------------------------------------------------*)
(** Notations for heap predicates *)

val _ = overload_on ("*+", Term `STARPOST`)
val _ = add_infix ("*+", 580, HOLgrammars.LEFT)

val _ = overload_on ("==>>", Term `SEP_IMP`)
val _ = add_infix ("==>>", 470, HOLgrammars.RIGHT)

val _ = overload_on ("==+>", Term `SEP_IMPPOST`)
val _ = add_infix ("==+>", 470, HOLgrammars.RIGHT)

val _ = overload_on ("==v>", Term `SEP_IMPPOSTv`)
val _ = add_infix ("==v>", 470, HOLgrammars.RIGHT)

val _ = overload_on ("==e>", Term `SEP_IMPPOSTe`)
val _ = add_infix ("==e>", 470, HOLgrammars.RIGHT)

val _ = overload_on ("==f>", Term `SEP_IMPPOSTf`)
val _ = add_infix ("==f>", 470, HOLgrammars.RIGHT)

val _ = overload_on ("==d>", Term `SEP_IMPPOSTd`)
val _ = add_infix ("==d>", 470, HOLgrammars.RIGHT)

val _ = overload_on ("=~v>", Term `SEP_IMPPOSTv_inv`)
val _ = add_infix ("=~v>", 470, HOLgrammars.RIGHT)

val _ = overload_on ("=~e>", Term `SEP_IMPPOSTe_inv`)
val _ = add_infix ("=~e>", 470, HOLgrammars.RIGHT)

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

val SPLIT3_of_SPLIT_emp3 = Q.store_thm ("SPLIT3_of_SPLIT_emp3",
  `!h h1 h2. SPLIT h (h1, h2) ==> SPLIT3 h (h1, h2, {})`,
  SPLIT_TAC
)

val SPLIT3_of_SPLIT_emp2 = Q.store_thm ("SPLIT3_of_SPLIT_emp2",
  `!h h1 h3. SPLIT h (h1, h3) ==> SPLIT3 h (h1, {}, h3)`,
  SPLIT_TAC
)

val SPLIT3_swap23 = Q.store_thm ("SPLIT3_swap23",
  `!h h1 h2 h3. SPLIT3 h (h1, h2, h3) ==> SPLIT3 h (h1, h3, h2)`,
  SPLIT_TAC
)

val SPLIT_emp1 = Q.store_thm ("SPLIT_emp1",
  `!h h'. SPLIT h ({}, h') = (h' = h)`,
  SPLIT_TAC
)

val SPLIT_emp2 = Q.store_thm ("SPLIT_emp2",
  `!h h'. SPLIT h (h', {}) = (h' = h)`,
  SPLIT_TAC
)

val SPLIT3_emp1 = Q.store_thm ("SPLIT3_emp1",
  `!h h1 h2. SPLIT3 h ({}, h1, h2) = SPLIT h (h1, h2)`,
  SPLIT_TAC
)

val SPLIT3_emp3 = Q.store_thm("SPLIT3_emp3",
  `!h h1 h2. SPLIT3 h (h1,h2,{}) = SPLIT h (h1,h2)`,
  SPLIT_TAC)

val SPLIT_of_SPLIT3_2u3 = Q.store_thm ("SPLIT_of_SPLIT3_2u3",
  `!h h1 h2 h3. SPLIT3 h (h1, h2, h3) ==> SPLIT h (h1, h2 UNION h3)`,
  SPLIT_TAC
)

(*------------------------------------------------------------------*)
(** Additionnal properties of STAR *)

val STARPOST_emp = Q.store_thm ("STARPOST_emp",
  `!Q. Q *+ emp = Q`,
  strip_tac \\ fs [STARPOST_def] \\ metis_tac [SEP_CLAUSES]
);

val SEP_IMP_frame_single_l = Q.store_thm ("SEP_IMP_frame_single_l",
  `!H' R.
     (emp ==>> H') ==>
     (R ==>> H' * R)`,
  rpt strip_tac \\ progress SEP_IMP_FRAME \\ fs [SEP_CLAUSES]
);

val SEP_IMP_frame_single_r = Q.store_thm ("SEP_IMP_frame_single_r",
  `!H R.
     (H ==>> emp) ==>
     (H * R ==>> R)`,
  rpt strip_tac \\ progress SEP_IMP_FRAME \\ fs [SEP_CLAUSES]
);

val SEP_IMP_cell_frame = Q.store_thm ("SEP_IMP_cell_frame",
  `!H H' l v v'.
     (v = v') /\ (H ==>> H') ==>
     (H * l ~~>> v ==>> H' * l ~~>> v')`,
  rpt strip_tac \\ progress SEP_IMP_FRAME \\ fs [SEP_CLAUSES]
);

val SEP_IMP_cell_frame_single_l = Q.store_thm ("SEP_IMP_cell_frame_single_l",
  `!H' l v v'.
     (v = v') /\ (emp ==>> H') ==>
     (l ~~>> v ==>> H' * l ~~>> v')`,
  rpt strip_tac \\ progress SEP_IMP_FRAME \\ fs [SEP_CLAUSES]
);

val SEP_IMP_cell_frame_single_r = Q.store_thm ("SEP_IMP_cell_frame_single_r",
  `!H l v v'.
     (v = v') /\ (H ==>> emp) ==>
     (H * l ~~>> v ==>> l ~~>> v')`,
  rpt strip_tac \\ progress SEP_IMP_FRAME \\ fs [SEP_CLAUSES]
);

val SEP_IMP_cell_frame_single = Q.store_thm ("SEP_IMP_cell_frame_single",
  `!H l v v'.
     (v = v') /\ (emp ==>> emp) ==>
     (l ~~>> v ==>> l ~~>> v')`,
  fs [SEP_IMP_REFL]
);

val SEP_IMP_REF_frame = Q.store_thm ("SEP_IMP_REF_frame",
  `!H H' r v v'.
     (v = v') /\ (H ==>> H') ==>
     (H * r ~~> v ==>> H' * r ~~> v')`,
  rpt strip_tac \\ progress SEP_IMP_FRAME \\ fs [SEP_CLAUSES]
);

val SEP_IMP_REF_frame_single_l = Q.store_thm ("SEP_IMP_REF_frame_single_l",
  `!H' r v v'.
     (v = v') /\ (emp ==>> H') ==>
     (r ~~> v ==>> H' * r ~~> v')`,
  rpt strip_tac \\ progress SEP_IMP_FRAME \\ fs [SEP_CLAUSES]
);

val SEP_IMP_REF_frame_single_r = Q.store_thm ("SEP_IMP_REF_frame_single_r",
  `!H r v v'.
     (v = v') /\ (H ==>> emp) ==>
     (H * r ~~> v ==>> r ~~> v')`,
  rpt strip_tac \\ progress SEP_IMP_FRAME \\ fs [SEP_CLAUSES]
);

val SEP_IMP_REF_frame_single = Q.store_thm ("SEP_IMP_REF_frame_single",
  `!H r v v'.
     (v = v') /\ (emp ==>> emp) ==>
     (r ~~> v ==>> r ~~> v')`,
  fs [SEP_IMP_REFL]
);

val SEP_IMP_ARRAY_frame = Q.store_thm ("SEP_IMP_ARRAY_frame",
  `!H H' a vl vl'.
     (vl = vl') /\ (H ==>> H') ==>
     (H * ARRAY a vl ==>> H' * ARRAY a vl')`,
  rpt strip_tac \\ progress SEP_IMP_FRAME \\ fs [SEP_CLAUSES]
);

val SEP_IMP_ARRAY_frame_single_l = Q.store_thm ("SEP_IMP_ARRAY_frame_single_l",
  `!H' a vl vl'.
     (vl = vl') /\ (emp ==>> H') ==>
     (ARRAY a vl ==>> H' * ARRAY a vl')`,
  rpt strip_tac \\ progress SEP_IMP_FRAME \\ fs [SEP_CLAUSES]
);

val SEP_IMP_ARRAY_frame_single_r = Q.store_thm ("SEP_IMP_ARRAY_frame_single_r",
  `!H a vl vl'.
     (vl = vl') /\ (H ==>> emp) ==>
     (H * ARRAY a vl ==>> ARRAY a vl')`,
  rpt strip_tac \\ progress SEP_IMP_FRAME \\ fs [SEP_CLAUSES]
);

val SEP_IMP_ARRAY_frame_single = Q.store_thm ("SEP_IMP_ARRAY_frame_single",
  `!H a vl vl'.
     (vl = vl') /\ (emp ==>> emp) ==>
     (ARRAY a vl ==>> ARRAY a vl')`,
  fs [SEP_IMP_REFL]
);

val SEP_IMP_W8ARRAY_frame = Q.store_thm ("SEP_IMP_W8ARRAY_frame",
  `!H H' a wl wl'.
     (wl = wl') /\ (H ==>> H') ==>
     (H * W8ARRAY a wl ==>> H' * W8ARRAY a wl')`,
  rpt strip_tac \\ progress SEP_IMP_FRAME \\ fs [SEP_CLAUSES]
);

val SEP_IMP_W8ARRAY_frame_single_l = Q.store_thm (
  "SEP_IMP_W8ARRAY_frame_single_l",
  `!H' a wl wl'.
     (wl = wl') /\ (emp ==>> H') ==>
     (W8ARRAY a wl ==>> H' * W8ARRAY a wl')`,
  rpt strip_tac \\ progress SEP_IMP_FRAME \\ fs [SEP_CLAUSES]
);

val SEP_IMP_W8ARRAY_frame_single_r = Q.store_thm (
  "SEP_IMP_W8ARRAY_frame_single_r",
  `!H a wl wl'.
     (wl = wl') /\ (H ==>> emp) ==>
     (H * W8ARRAY a wl ==>> W8ARRAY a wl')`,
  rpt strip_tac \\ progress SEP_IMP_FRAME \\ fs [SEP_CLAUSES]
);

val SEP_IMP_W8ARRAY_frame_single = Q.store_thm (
  "SEP_IMP_W8ARRAY_frame_single",
  `!H a wl wl'.
     (wl = wl') /\ (emp ==>> emp) ==>
     (W8ARRAY a wl ==>> W8ARRAY a wl')`,
  fs [SEP_IMP_REFL]
);

val SEP_IMP_IO_frame = Q.store_thm ("SEP_IMP_IO_frame",
  `!H H' idx st u st' u'.
     (st = st' /\ u = u') /\ (H ==>> H') ==>
     (H * IO st u idx ==>> H' * IO st' u' idx)`,
  rpt strip_tac \\ progress SEP_IMP_FRAME \\ fs [SEP_CLAUSES]
);

val SEP_IMP_IO_frame_single_l = Q.store_thm ("SEP_IMP_IO_frame_single_l",
  `!H' idx st u st' u'.
     (st = st' /\ u = u') /\ (emp ==>> H') ==>
     (IO st u idx ==>> H' * IO st' u' idx)`,
  rpt strip_tac \\ progress SEP_IMP_FRAME \\ fs [SEP_CLAUSES]
);

val SEP_IMP_IO_frame_singel_r = Q.store_thm ("SEP_IMP_IO_frame_single_r",
  `!H idx st u st' u'.
     (st = st' /\ u = u') /\ (H ==>> emp) ==>
     (H * IO st u idx ==>> IO st' u' idx)`,
  rpt strip_tac \\ progress SEP_IMP_FRAME \\ fs [SEP_CLAUSES]
);

val SEP_IMP_IO_frame_single = Q.store_thm ("SEP_IMP_IO_frame_single",
  `!idx st u st' u'.
     (st = st' /\ u = u') /\ (emp ==>> emp) ==>
     (IO st u idx ==>> IO st' u' idx)`,
  fs [SEP_IMP_REFL]
);

(*------------------------------------------------------------------*)
(** Normalization of STAR *)

val rew_heap_thms =
  [AC STAR_COMM STAR_ASSOC, SEP_CLAUSES, STARPOST_emp,
   SEP_IMPPOST_def, SEP_IMPPOSTv_def, SEP_IMPPOSTe_def,
   STARPOST_def, cond_eq_def]

val rew_heap = full_simp_tac bool_ss rew_heap_thms

(*------------------------------------------------------------------*)
(* Workaround because of SEP_CLAUSES turning &F into SEP_F *)

val SEP_F_to_cond = Q.store_thm ("SEP_F_to_cond",
  `SEP_F = &F`,
  irule EQ_EXT \\ fs [SEP_F_def, cond_def]
);

(*------------------------------------------------------------------*)
(** Properties of GC *)

val GC_STAR_GC = Q.store_thm ("GC_STAR_GC",
  `GC * GC = GC`,
  fs [GC_def] \\ irule EQ_EXT \\ strip_tac \\ rew_heap \\
  fs [SEP_EXISTS] \\ eq_tac \\ rpt strip_tac
  THENL [all_tac, qexists_tac `emp` \\ rew_heap] \\
  metis_tac []
)

(*------------------------------------------------------------------*)
(* Unfolding + case split lemma for SEP_IMPPOST *)

val SEP_IMPPOST_unfold = Q.store_thm ("SEP_IMPPOST_unfold",
  `!Q1 Q2.
      (Q1 ==+> Q2) <=>
      (!v. Q1 (Val v) ==>> Q2 (Val v)) /\
      (!v. Q1 (Exn v) ==>> Q2 (Exn v)) /\
      (!name conf bytes. Q1 (FFIDiv name conf bytes) ==>> Q2 (FFIDiv name conf bytes)) /\
      (!io. Q1 (Div io) ==>> Q2 (Div io))`,
  rpt strip_tac \\ eq_tac \\ rpt strip_tac \\ fs [SEP_IMPPOST_def] \\
  Cases \\ fs []
);

(*------------------------------------------------------------------*)
(** Extraction from H1 in H1 ==>> H2 *)

val hpull_prop = Q.store_thm ("hpull_prop",
  `!H H' P.
     (P ==> H ==>> H') ==>
     (H * cond P ==>> H')`,
  rpt strip_tac \\ fs [SEP_IMP_def, STAR_def, cond_def] \\
  SPLIT_TAC
)

val hpull_prop_single = Q.store_thm ("hpull_prop_single",
  `!H' P.
     (P ==> emp ==>> H') ==>
     (cond P ==>> H')`,
  rpt strip_tac \\ fs [SEP_IMP_def, STAR_def, cond_def, emp_def] \\
  SPLIT_TAC
)

val hpull_exists_single = Q.store_thm ("hpull_exists_single",
  `!A H' J.
     (!x. (J x) ==>> H') ==>
     ($SEP_EXISTS J ==>> H')`,
  rpt strip_tac \\ fs [SEP_IMP_def, STAR_def, SEP_EXISTS, emp_def] \\
  SPLIT_TAC
)

val SEP_IMP_rew = Q.store_thm ("SEP_IMP_rew",
  `!H1 H2 H1' H2'. (H1 = H2) ==> (H1' = H2') ==> (H1 ==>> H1') = (H2 ==>> H2')`,
  rew_heap
)

(*------------------------------------------------------------------*)
(** Simplification in H2 on H1 ==>> H2 *)

(** Lemmas *)

val hsimpl_prop = Q.store_thm ("hsimpl_prop",
  `!H' H P.
     P /\ (H' ==>> H) ==>
     (H' ==>> H * cond P)`,
  rpt strip_tac \\ fs [SEP_IMP_def, STAR_def, cond_def] \\
  SPLIT_TAC
)

val hsimpl_prop_single = Q.store_thm ("hsimpl_prop_single",
  `!H' P.
     P /\ (H' ==>> emp) ==>
     (H' ==>> cond P)`,
  rpt strip_tac \\ fs [SEP_IMP_def, STAR_def, cond_def, emp_def] \\
  SPLIT_TAC
)

val hsimpl_exists_single = Q.store_thm ("hsimpl_exists_single",
  `!x H' J.
     (H' ==>> J x) ==>
     (H' ==>> $SEP_EXISTS J)`,
  rpt strip_tac \\ fs [SEP_IMP_def, STAR_def, SEP_EXISTS, emp_def] \\
  SPLIT_TAC
)

val hsimpl_gc = Q.store_thm ("hsimpl_gc",
  `!H. H ==>> GC`,
  fs [GC_def, SEP_IMP_def, SEP_EXISTS] \\ metis_tac []
)

(*------------------------------------------------------------------*)
(* Automatic rewrites for post-condition injections *)

val POST_Val = Q.store_thm ("POST_Val[simp]",
  `!Qv Qe Qf Qd v. POST Qv Qe Qf Qd (Val v) = Qv v`,
  fs [POST_def]
);

val POST_Exn = Q.store_thm ("POST_Exn[simp]",
  `!Qv Qe Qf Qd v. POST Qv Qe Qf Qd (Exn v) = Qe v`,
  fs [POST_def]
);

val POST_FFIDiv = Q.store_thm ("POST_FFIDiv[simp]",
  `!Qv Qe Qf Qd name conf bytes. POST Qv Qe Qf Qd (FFIDiv name conf bytes) = Qf name conf bytes`,
  fs [POST_def]
);

val POST_Div = Q.store_thm ("POST_Div[simp]",
  `!Qv Qe Qf Qd io. POST Qv Qe Qf Qd (Div io) = &(Qd io)`,
  fs [POST_def]
);

val POSTv_Val = Q.store_thm ("POSTv_Val[simp]",
  `!Qv v. $POSTv Qv (Val v) = Qv v`,
  fs [POSTv_def, POST_def]
);

val POSTv_Exn = Q.store_thm ("POSTv_Exn[simp]",
  `!Qv v. $POSTv Qv (Exn v) = &F`,
  fs [POSTv_def, POST_def]
);

val POSTv_FFIDiv = Q.store_thm ("POSTv_FFIDiv[simp]",
  `!Qv name conf bytes. $POSTv Qv (FFIDiv name conf bytes) = &F`,
  fs [POSTv_def, POST_def]
);

val POSTv_Div = Q.store_thm ("POSTv_Div[simp]",
  `!Qv io. $POSTv Qv (Div io) = &F`,
  fs [POSTv_def, POST_def]
);

val POSTe_Val = Q.store_thm ("POSTe_Val[simp]",
  `!Qe v. $POSTe Qe (Val v) = &F`,
  fs [POSTe_def, POST_def]
);

val POSTe_Exn = Q.store_thm ("POSTe_Exn[simp]",
  `!Qe v. $POSTe Qe (Exn v) = Qe v`,
  fs [POSTe_def, POST_def]
);

val POSTe_FFIDiv = Q.store_thm ("POSTe_FFIDiv[simp]",
  `!Qe name conf bytes. $POSTe Qe (FFIDiv name conf bytes) = &F`,
  fs [POSTe_def, POST_def]
);

val POSTe_Div = Q.store_thm ("POSTe_Div[simp]",
  `!Qe io. $POSTe Qe (Div io) = &F`,
  fs [POSTe_def, POST_def]
);

val POSTf_Val = Q.store_thm ("POSTf_Val[simp]",
  `!Qf v. $POSTf Qf (Val v) = &F`,
  fs [POSTf_def, POST_def]
);

val POSTf_Exn = Q.store_thm ("POSTf_Exn[simp]",
  `!Qf v. $POSTf Qf (Exn v) = &F`,
  fs [POSTf_def, POST_def]
);

val POSTf_FFIDiv = Q.store_thm ("POSTf_FFIDiv[simp]",
  `!Qf name conf bytes. $POSTf Qf (FFIDiv name conf bytes) = Qf name conf bytes`,
  fs [POSTf_def, POST_def]
);

val POSTf_Div = Q.store_thm ("POSTf_Div[simp]",
  `!Qf io. $POSTf Qf (Div io) = &F`,
  fs [POSTf_def, POST_def]
);

val POSTd_Val = Q.store_thm ("POSTd_Val[simp]",
  `!Qd v. $POSTd Qd (Val v) = &F`,
  fs [POSTd_def, POST_def]
);

val POSTd_Exn = Q.store_thm ("POSTd_Exn[simp]",
  `!Qd v. $POSTd Qd (Exn v) = &F`,
  fs [POSTd_def, POST_def]
);

val POSTd_FFIDiv = Q.store_thm ("POSTd_FFIDiv[simp]",
  `!Qd name conf bytes. $POSTd Qd (FFIDiv name conf bytes) = &F`,
  fs [POSTd_def, POST_def]
);

val POSTd_Div = Q.store_thm ("POSTd_Div[simp]",
  `!Qd io. $POSTd Qd (Div io) = &(Qd io)`,
  fs [POSTd_def, POST_def]
);

val POSTve_Val = Q.store_thm ("POSTve_Val[simp]",
  `!Qv Qe v. POSTve Qv Qe (Val v) = Qv v`,
  fs [POSTve_def, POST_def]
);

val POSTve_Exn = Q.store_thm ("POSTve_Exn[simp]",
  `!Qv Qe v. POSTve Qv Qe (Exn v) = Qe v`,
  fs [POSTve_def, POST_def]
);

val POSTve_FFIDiv = Q.store_thm ("POSTve_FFIDiv[simp]",
  `!Qv Qe name conf bytes. POSTve Qv Qe (FFIDiv name conf bytes) = &F`,
  fs [POSTve_def, POST_def]
);

val POSTve_Div = Q.store_thm ("POSTve_Div[simp]",
  `!Qv Qe io. POSTve Qv Qe (Div io) = &F`,
  fs [POSTve_def, POST_def]
);

val POSTvd_Val = Q.store_thm ("POSTvd_Val[simp]",
  `!Qv Qd v. POSTvd Qv Qd (Val v) = Qv v`,
  fs [POSTvd_def, POST_def]
);

val POSTvd_Exn = Q.store_thm ("POSTvd_Exn[simp]",
  `!Qv Qd v. POSTvd Qv Qd (Exn v) = &F`,
  fs [POSTvd_def, POST_def]
);

val POSTvd_FFIDiv = Q.store_thm ("POSTvd_FFIDiv[simp]",
  `!Qv Qd name conf bytes. POSTvd Qv Qd (FFIDiv name conf bytes) = &F`,
  fs [POSTvd_def, POST_def]
);

val POSTvd_Div = Q.store_thm ("POSTvd_Div[simp]",
  `!Qv Qd io. POSTvd Qv Qd (Div io) = &(Qd io)`,
  fs [POSTvd_def, POST_def]
);

val POSTed_Val = Q.store_thm ("POSTed_Val[simp]",
  `!Qe Qd v. POSTed Qe Qd (Val v) = &F`,
  fs [POSTed_def, POST_def]
);

val POSTed_Exn = Q.store_thm ("POSTed_Exn[simp]",
  `!Qe Qd v. POSTed Qe Qd (Exn v) = Qe v`,
  fs [POSTed_def, POST_def]
);

val POSTed_FFIDiv = Q.store_thm ("POSTed_FFIDiv[simp]",
  `!Qe Qd name conf bytes. POSTed Qe Qd (FFIDiv name conf bytes) = &F`,
  fs [POSTed_def, POST_def]
);

val POSTed_Div = Q.store_thm ("POSTed_Div[simp]",
  `!Qe Qd io. POSTed Qe Qd (Div io) = &(Qd io)`,
  fs [POSTed_def, POST_def]
);

(* other lemmas about POSTv *)

val POSTv_ignore = Q.store_thm("POSTv_ignore",
   `(POSTv v. P) r h ⇔ ∃v. r = Val v ∧ P h`,
   Cases_on `r` \\ rw[cond_def]);

(*------------------------------------------------------------------*)
(* Lemmas for ==v> / ==e> / ==f> / ==d> / =~v> / =~e> *)

val SEP_IMPPOSTv_POSTe_left = Q.store_thm ("SEP_IMPPOSTv_POSTe_left",
  `!Qe Q. $POSTe Qe ==v> Q`,
  fs [POSTe_def, SEP_IMPPOSTv_def, SEP_IMP_def, cond_def]
);

val SEP_IMPPOSTv_POSTf_left = Q.store_thm ("SEP_IMPPOSTv_POSTf_left",
  `!Qf Q. $POSTf Qf ==v> Q`,
  fs [POSTf_def, SEP_IMPPOSTv_def, SEP_IMP_def, cond_def]
);

val SEP_IMPPOSTv_POSTd_left = Q.store_thm ("SEP_IMPPOSTv_POSTd_left",
  `!Qd Q. $POSTd Qd ==v> Q`,
  fs [POSTd_def, SEP_IMPPOSTv_def, SEP_IMP_def, cond_def]
);

val SEP_IMPPOSTv_POSTed_left = Q.store_thm ("SEP_IMPPOSTv_POSTed_left",
  `!Qe Qd Q. POSTed Qe Qd ==v> Q`,
  fs [POSTed_def, SEP_IMPPOSTv_def, SEP_IMP_def, cond_def]
);

val SEP_IMPPOSTe_POSTv_left = Q.store_thm ("SEP_IMPPOSTe_POSTv_left",
  `!Qv Q. $POSTv Qv ==e> Q`,
  fs [POSTv_def, SEP_IMPPOSTe_def, SEP_IMP_def, cond_def]
);

val SEP_IMPPOSTe_POSTf_left = Q.store_thm ("SEP_IMPPOSTe_POSTf_left",
  `!Qf Q. $POSTf Qf ==e> Q`,
  fs [POSTf_def, SEP_IMPPOSTe_def, SEP_IMP_def, cond_def]
);

val SEP_IMPPOSTe_POSTd_left = Q.store_thm ("SEP_IMPPOSTe_POSTd_left",
  `!Qd Q. $POSTd Qd ==e> Q`,
  fs [POSTd_def, SEP_IMPPOSTe_def, SEP_IMP_def, cond_def]
);

val SEP_IMPPOSTe_POSTvd_left = Q.store_thm ("SEP_IMPPOSTe_POSTvd_left",
  `!Qv Qd Q. POSTvd Qv Qd ==e> Q`,
  fs [POSTvd_def, SEP_IMPPOSTe_def, SEP_IMP_def, cond_def]
);

val SEP_IMPPOSTf_POSTv_left = Q.store_thm ("SEP_IMPPOSTf_POSTv_left",
  `!Qv Q. $POSTv Qv ==f> Q`,
  fs [POSTv_def, SEP_IMPPOSTf_def, SEP_IMP_def, cond_def]
);

val SEP_IMPPOSTf_POSTe_left = Q.store_thm ("SEP_IMPPOSTf_POSTe_left",
  `!Qe Q. $POSTe Qe ==f> Q`,
  fs [POSTe_def, SEP_IMPPOSTf_def, SEP_IMP_def, cond_def]
);

val SEP_IMPPOSTf_POSTd_left = Q.store_thm ("SEP_IMPPOSTf_POSTd_left",
  `!Qd Q. $POSTd Qd ==f> Q`,
  fs [POSTd_def, SEP_IMPPOSTf_def, SEP_IMP_def, cond_def]
);

val SEP_IMPPOSTf_POSTve_left = Q.store_thm ("SEP_IMPPOSTf_POSTve_left",
  `!Qv Qe Q. POSTve Qv Qe ==f> Q`,
  fs [POSTve_def, SEP_IMPPOSTf_def, SEP_IMP_def, cond_def]
);

val SEP_IMPPOSTf_POSTvd_left = Q.store_thm ("SEP_IMPPOSTf_POSTvd_left",
  `!Qv Qd Q. POSTvd Qv Qd ==f> Q`,
  fs [POSTvd_def, SEP_IMPPOSTf_def, SEP_IMP_def, cond_def]
);

val SEP_IMPPOSTf_POSTed_left = Q.store_thm ("SEP_IMPPOSTf_POSTed_left",
  `!Qe Qd Q. POSTed Qe Qd ==f> Q`,
  fs [POSTed_def, SEP_IMPPOSTf_def, SEP_IMP_def, cond_def]
);

val SEP_IMPPOSTd_POSTv_left = Q.store_thm ("SEP_IMPPOSTd_POSTv_left",
  `!Qv Q. $POSTv Qv ==d> Q`,
  fs [POSTv_def, SEP_IMPPOSTd_def, SEP_IMP_def, cond_def]
);

val SEP_IMPPOSTd_POSTe_left = Q.store_thm ("SEP_IMPPOSTd_POSTe_left",
  `!Qe Q. $POSTe Qe ==d> Q`,
  fs [POSTe_def, SEP_IMPPOSTd_def, SEP_IMP_def, cond_def]
);

val SEP_IMPPOSTd_POSTf_left = Q.store_thm ("SEP_IMPPOSTd_POSTf_left",
  `!Qf Q. $POSTf Qf ==d> Q`,
  fs [POSTf_def, SEP_IMPPOSTd_def, SEP_IMP_def, cond_def]
);

val SEP_IMPPOSTd_POSTve_left = Q.store_thm ("SEP_IMPPOSTd_POSTve_left",
  `!Qv Qe Q. POSTve Qv Qe ==d> Q`,
  fs [POSTve_def, SEP_IMPPOSTd_def, SEP_IMP_def, cond_def]
);

val SEP_IMPPOSTv_inv_POSTv_left = Q.store_thm ("SEP_IMPPOSTv_inv_POSTv_left",
  `!Qv Q. $POSTv Qv =~v> Q`,
  fs [POSTv_def, SEP_IMPPOSTv_inv_def,
      SEP_IMPPOSTe_def, SEP_IMPPOSTf_def, SEP_IMPPOSTd_def,
      SEP_IMP_def, cond_def]
);

val SEP_IMPPOSTe_inv_POSTe_left = Q.store_thm ("SEP_IMPPOSTe_inv_POSTe_left",
  `!Qe Q. $POSTe Qe =~e> Q`,
  fs [POSTe_def, SEP_IMPPOSTe_inv_def,
      SEP_IMPPOSTv_def, SEP_IMPPOSTf_def, SEP_IMPPOSTd_def,
      SEP_IMP_def, cond_def]
);

val _ = export_theory()
