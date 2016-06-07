open HolKernel Parse boolLib bossLib preamble
open set_sepTheory helperLib ml_translatorTheory
open ConseqConv

val _ = new_theory "ml_cf"

(* TODO: clean & generalize *)
fun instantiate g =
  rpt ((asm_exists_tac \\ fs []) ORELSE
       (once_rewrite_tac [CONJ_COMM] \\ asm_exists_tac \\ fs []))
      g

fun rpt_drule_then thm_tac thm =
  drule thm \\ rpt (disch_then drule) \\ disch_then thm_tac

fun progress thm = rpt_drule_then strip_assume_tac thm

fun sing x = [x]

(*------------------------------------------------------------------*)
(** Heaps *)

val _ = type_abbrev("loc", ``:num``)
val _ = type_abbrev("heap", ``:(loc # v semanticPrimitives$store_v) set``)
val _ = type_abbrev("hprop", ``:heap -> bool``)

val SPLIT3_def = Define `
  SPLIT3 (s:'a set) (u,v,w) =
    ((u UNION v UNION w = s) /\
     DISJOINT u v /\ DISJOINT v w /\ DISJOINT u w)`

val SPLIT_ss = rewrites [SPLIT_def,SPLIT3_def,SUBSET_DEF,DISJOINT_DEF,DELETE_DEF,IN_INSERT,
                         UNION_DEF,SEP_EQ_def,EXTENSION,NOT_IN_EMPTY,IN_DEF,IN_UNION,IN_INTER,
                         IN_DIFF]

val SPLIT_TAC = FULL_SIMP_TAC (pure_ss++SPLIT_ss) [] \\ METIS_TAC []
val SPLIT2_TAC = fs [SPLIT_def,SPLIT3_def,SUBSET_DEF,DISJOINT_DEF,DELETE_DEF,IN_INSERT,UNION_DEF,
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

val rew_heap_AC = full_simp_tac bool_ss [AC STAR_COMM STAR_ASSOC]

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

(** Tactics *)

fun dest_sep_imp tm = let
  val format = (fst o dest_eq o concl o SPEC_ALL) SEP_IMP_def
  in if can (match_term format) tm then (cdr (car tm), cdr tm) else fail() end

fun SEP_IMP_conv convl convr t =
  let val (l, r) = dest_sep_imp t handle _ => raise UNCHANGED
      val rew_t = MATCH_MP (MATCH_MP SEP_IMP_rew (convl l)) (convr r)
  in REWR_CONV rew_t t
  end

fun find_map f [] = NONE
  | find_map f (x :: xs) =
    (case f x of
         NONE => find_map f xs
       | SOME y => SOME y)

fun rearrange_star_conv tm rest =
  let val rearranged = list_mk_star (rest @ [tm]) ``:hprop`` in
    fn t => prove (mk_eq (t, rearranged), rew_heap_AC)
  end


fun hpull_one_conseq_conv t =
  let
    val (l, r) = dest_sep_imp t handle _ => raise UNCHANGED
    val ls = list_dest dest_star l
    fun rearrange_conv tm =
      let val rest = filter (fn tm' => tm' <> tm) ls in
        SEP_IMP_conv (rearrange_star_conv tm rest) REFL
      end
    fun pull tm =
      let val (c, args) = strip_comb tm in
        if is_const c andalso #Name (dest_thy_const c) = "cond" then
          SOME (
            THEN_CONSEQ_CONV
              (rearrange_conv tm)
              (CONSEQ_REWRITE_CONV ([], [hpull_prop, hpull_prop_single], [])
                CONSEQ_CONV_STRENGTHEN_direction)
          )
        else if is_const c andalso #Name (dest_thy_const c) = "SEP_EXISTS" then
          SOME (
            EVERY_CONSEQ_CONV [
              rearrange_conv tm,
              CONSEQ_REWRITE_CONV ([], [hpull_exists_single], [])
                CONSEQ_CONV_STRENGTHEN_direction,
              REDEPTH_STRENGTHEN_CONSEQ_CONV (REDEPTH_CONV BETA_CONV)
            ]
          )
        else
          NONE
      end
  in
    case find_map pull ls of
        NONE => raise UNCHANGED
      | SOME cc => cc t
  end

val hpull_setup_conv =
  (* remove ``emp`` in the left heap, pull SEP_EXISTS *)
  QCONV (SEP_IMP_conv (QCONV (SIMP_CONV bool_ss [SEP_CLAUSES])) REFL)

val hpull =
  TRY (DEPTH_CONSEQ_CONV_TAC (STRENGTHEN_CONSEQ_CONV hpull_setup_conv)) \\
  REDEPTH_CONSEQ_CONV_TAC (STRENGTHEN_CONSEQ_CONV hpull_one_conseq_conv)

(* test goals:
  g `SEP_IMP (A * cond P * (SEP_EXISTS x. G x) * cond Q:hprop) Z`;
  g `SEP_IMP (A * emp * cond P * (SEP_EXISTS x. emp * G x) * cond Q:hprop) Z`;
*)

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

(** Quantifiers Heuristic parameters *)

val sep_qp = combine_qps [
      instantiation_qp [
        SEP_IMP_REFL,
        hsimpl_gc
      ]
    ]

(** Tactics *)

fun hsimpl_cancel_one_conseq_conv t =
  let
    val (l, r) = dest_sep_imp t handle _ => raise UNCHANGED
    val ls = list_dest dest_star l
    val rs = list_dest dest_star r
    val is = intersect ls rs
    fun rearrange_conv tm1 tm2 =
      let
        val ls' = filter (fn tm' => tm' <> tm1) ls
        val rs' = filter (fn tm' => tm' <> tm2) rs
        val convl = rearrange_star_conv tm1 ls'
        val convr = rearrange_star_conv tm2 rs'
      in SEP_IMP_conv convl convr
      end
    fun one_loc tm =
      let val (c, args) = strip_comb tm in
        if is_const c andalso #Name (dest_thy_const c) = "one" then
          SOME (hd (snd (strip_comb (hd args))))
        else
          NONE
      end
    fun find_matching_ones () =
      find_map (fn tm1 =>
        Option.mapPartial (fn loc =>
          find_map (fn tm2 =>
            Option.mapPartial (fn loc' =>
              if loc = loc' then SOME (tm1, tm2) else NONE
            ) (one_loc tm2)
          ) rs
        ) (one_loc tm1)
      ) ls

    val frame_thms = [
      SEP_IMP_FRAME,
      SEP_IMP_frame_single_l,
      SEP_IMP_frame_single_r
    ]
    val frame_one_thms = [
      SEP_IMP_one_frame,
      SEP_IMP_one_frame_single_l,
      SEP_IMP_one_frame_single_r
    ]
  in
    (case is of
         tm :: _ =>
         THEN_CONSEQ_CONV
           (rearrange_conv tm tm)
           (CONSEQ_REWRITE_CONV ([], frame_thms, [])
              CONSEQ_CONV_STRENGTHEN_direction)
       | [] =>
         case find_matching_ones () of
             SOME (tm1, tm2) =>
             THEN_CONSEQ_CONV
               (rearrange_conv tm1 tm2)
               (CONSEQ_REWRITE_CONV ([], frame_one_thms, [])
                  CONSEQ_CONV_STRENGTHEN_direction)
           | NONE => raise UNCHANGED)
      t
  end

val hsimpl_cancel =
    REDEPTH_CONSEQ_CONV_TAC
      (STRENGTHEN_CONSEQ_CONV hsimpl_cancel_one_conseq_conv)

(* test goal:
  g `SEP_IMP (A:hprop * B * C * one (l, v) * D) (B * Z * one (l, v') * Y * D * A)`;
*)

fun hsimpl_step_conseq_conv t =
  let
    val (l, r) = dest_sep_imp t
    val rs = list_dest dest_star r
    fun rearrange_conv tm =
      let val rest = filter (fn tm' => tm' <> tm) rs in
        SEP_IMP_conv REFL (rearrange_star_conv tm rest)
      end
    fun simpl tm =
      let val (c, args) = strip_comb tm in
        if is_const c andalso #Name (dest_thy_const c) = "cond" then
          SOME (
            EVERY_CONSEQ_CONV [
              rearrange_conv tm,
              CONSEQ_REWRITE_CONV ([], [hsimpl_prop, hsimpl_prop_single], [])
                CONSEQ_CONV_STRENGTHEN_direction
            ]
          )
        else if is_const c andalso #Name (dest_thy_const c) = "SEP_EXISTS" then
          SOME (
            EVERY_CONSEQ_CONV [
              rearrange_conv tm,
              CONSEQ_REWRITE_CONV ([], [hsimpl_exists_single], [])
                CONSEQ_CONV_STRENGTHEN_direction,
              REDEPTH_STRENGTHEN_CONSEQ_CONV (REDEPTH_CONV BETA_CONV)
            ]
          )
        else
          NONE
      end
  in
    case find_map simpl rs of
        NONE => raise UNCHANGED
      | SOME cc => cc t
  end

val hsimpl_steps =
    REDEPTH_CONSEQ_CONV_TAC
      (STRENGTHEN_CONSEQ_CONV hsimpl_step_conseq_conv)

(* test goal:
  g `SEP_IMP Z (A * cond P * (SEP_EXISTS x. G x) * cond Q:hprop)`;
*)

val hsimpl_setup_conv =
  SEP_IMP_conv
      (QCONV (SIMP_CONV bool_ss [SEP_CLAUSES]))
      (QCONV (SIMP_CONV bool_ss [SEP_CLAUSES]))

val hsimpl =
  TRY (DEPTH_CONSEQ_CONV_TAC (STRENGTHEN_CONSEQ_CONV hsimpl_setup_conv)) \\
  TRY hpull \\
  QUANT_INSTANTIATE_TAC [sep_qp] \\
  rpt (hsimpl_cancel ORELSE (hsimpl_steps \\ QUANT_INSTANTIATE_TAC [sep_qp])) \\
  fs [hsimpl_gc, SEP_IMP_REFL]

(* test goal:
  g `SEP_IMP (A:hprop * B * C * one (l, v) * one (l', u) * D) (B * Z * one (l, v') * one (l', u') * Y * cond Q * D * A)`;
*)

(*------------------------------------------------------------------*)
(** Conversion from semantic stores to heaps *)

val store2heap_aux_def = Define `
  store2heap_aux n [] = ({}: heap) /\
  store2heap_aux n (v :: t) = (n, v) INSERT (store2heap_aux (n+1: num) t)`

val store2heap_def = Define `store2heap l = store2heap_aux (0: num) l`

val store2heap_aux_append = Q.prove (
  `!s n x. store2heap_aux n (s ++ [x]) = (LENGTH s + n, x) INSERT store2heap_aux n s`,
  Induct THENL [all_tac, Cases] \\ fs [store2heap_aux_def, INSERT_COMM]
  \\ fs [DECIDE ``(LENGTH s + 1) = SUC (LENGTH s)``]
)

val store2heap_append = Q.prove (
  `!s x. store2heap (s ++ [x]) = (LENGTH s, x) INSERT store2heap s`,
  fs [store2heap_def, store2heap_aux_append]
)

val store2heap_aux_suc = Q.prove (
  `!s n u v. ((u, v) IN store2heap_aux n s) = ((SUC u, v) IN store2heap_aux (SUC n) s)`,
  Induct
  THEN1 (strip_tac \\ fs [store2heap_def, store2heap_aux_def])
  THEN1 (
    Cases \\
    once_rewrite_tac [store2heap_aux_def] \\ rpt strip_tac \\
    pop_assum (qspecl_then [`n+1`, `u`, `v`] assume_tac) \\
    fs [DECIDE ``SUC n + 1 = SUC (n + 1)``]
  )
)

val store2heap_aux_IN_bound = Q.prove (
  `!s n u v. (u, v) IN store2heap_aux n s ==> (u >= n)`,
  Induct THENL [all_tac, Cases] \\ fs [store2heap_aux_def] \\
  rpt strip_tac \\ fs [] \\ first_assum (qspecl_then [`n+1`, `u`, `v`] drule) \\
  rw_tac arith_ss []
)


val store2heap_alloc_disjoint = Q.prove (
  `!s x. ~ ((LENGTH s, x) IN (store2heap s))`,
  Induct
  THEN1 (strip_tac \\ fs [store2heap_def, store2heap_aux_def])
  THEN1 (
    Cases \\ fs [store2heap_def, store2heap_aux_def] \\
    rewrite_tac [ONE] \\
    fs [GSYM store2heap_aux_suc]
  )
)

val store2heap_IN_LENGTH = Q.prove (
  `!s r x. (r, x) IN (store2heap s) ==> r < LENGTH s`,
  Induct THENL [all_tac, Cases] \\
  fs [store2heap_def, store2heap_aux_def] \\
  Cases_on `r` \\ fs [] \\ rewrite_tac [ONE] \\
  rpt strip_tac \\ fs [GSYM store2heap_aux_suc] \\ metis_tac []
)

val tac_store2heap_IN =
  Induct THENL [all_tac, Cases] \\ fs [store2heap_def, store2heap_aux_def] \\
  Cases_on `r` \\ fs [] \\
  rewrite_tac [ONE] \\ rpt strip_tac \\
  fs [GSYM store2heap_aux_suc] \\ TRY (metis_tac []) \\
  qspecl_then [`s`, `1`, `0`, `x'`] drule store2heap_aux_IN_bound \\
  rw_tac arith_ss []

val store2heap_IN_EL = Q.prove (
  `!s r x. (r, x) IN (store2heap s) ==> EL r s = x`,
  tac_store2heap_IN
)

val store2heap_IN_unique_key = Q.prove (
  `!s r x. (r, x) IN (store2heap s) ==> !x'. (r, x') IN (store2heap s) ==> x = x'`,
  tac_store2heap_IN
)

(* todo: fix fragile names & refactor *)
val store2heap_LUPDATE = Q.prove (
  `!s r x y.
    (r, y) IN (store2heap s) ==>
    store2heap (LUPDATE x r s) = (r, x) INSERT ((store2heap s) DELETE (r, y))`,
  Induct \\
  fs [store2heap_def, store2heap_aux_def] \\
  Cases_on `r` \\ qx_genl_tac [`v`, `x`, `y`] \\
  qspecl_then [`s`, `1`, `0`, `y`] assume_tac store2heap_aux_IN_bound \\
  fs [LUPDATE_def, INSERT_DEF, DELETE_DEF, EXTENSION, store2heap_aux_def]
  THEN1 (metis_tac [])

  THEN1 (
    strip_tac \\ qx_gen_tac `u` \\
    Cases_on `u = (0,v)` \\ Cases_on `u` \\ fs []

    (* fix names *)
    THEN1 (
      Cases_on `q` \\ fs [] \\
      qcase_tac `(SUC nn, xx) IN store2heap_aux 1 (LUPDATE _ _ _)` \\
      qpat_assum `_ IN store2heap_aux 1 _` mp_tac \\
      rewrite_tac [ONE, GSYM store2heap_aux_suc] \\ rpt strip_tac \\
      first_assum drule \\ disch_then (qspecl_then [`x`, `(nn, xx)`] assume_tac) \\
      fs []
    )
    THEN1 (
      qspecl_then [`s`, `1`, `0`, `r`] assume_tac store2heap_aux_IN_bound \\
      qspecl_then [`LUPDATE x n s`, `1`, `0`, `r`] assume_tac store2heap_aux_IN_bound \\
      Cases_on `q` \\ fs [] \\
      qpat_assum `(SUC _,_) IN store2heap_aux 1 _` mp_tac \\
      rewrite_tac [ONE, GSYM store2heap_aux_suc] \\ rpt strip_tac \\
      first_assum drule \\ disch_then (qspecl_then [`x`, `(n', r)`] assume_tac) \\
      fs []
    )
  )
)

(* st2heap: 'ffi state -> heap *)
val st2heap_def = Define `
  st2heap (:'ffi) (st: 'ffi state) = store2heap st.refs`

(* Locality *)

(* local = frame rule + consequence rule + garbage collection *)

val local_def = Define `
  local cf env (H: hprop) (Q: v -> hprop) =
    !(h: heap). H h ==> ?H1 H2 Q1.
      (H1 * H2) h /\
      cf env H1 Q1 /\
      SEP_IMPPOST (Q1 *+ H2) (Q *+ GC)`

val is_local_def = Define `
  is_local cf = (cf = local cf)`

(* Properties of [local] *)

val local_elim = Q.prove (
  `!cf env H Q. cf env H Q ==> local cf env H Q`,
  fs [local_def] \\ rpt strip_tac \\
  Q.LIST_EXISTS_TAC [`H`, `emp`, `Q`] \\
  rew_heap \\ hsimpl
)

val local_local = Q.prove (
  `!cf. local (local cf) = local cf`,
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

val local_is_local = Q.prove (
  `!F. is_local (local F) = T`,
  metis_tac [is_local_def, local_local]
)

(** App *)

val app_basic_def = Define `
  app_basic (:'ffi) (f: v) (x: v) (H: hprop) (Q: v -> hprop) =
    !(h: heap) (i: heap) (st: 'ffi state).
      SPLIT (st2heap (:'ffi) st) (h, i) ==> H h ==>
      ?env exp (v': v) (h': heap) (g: heap) (st': 'ffi state).
        SPLIT3 (st2heap (:'ffi) st') (h', g, i) /\
        Q v' h' /\
        (do_opapp [f;x] = SOME (env, exp)) /\
        evaluate F env st exp (st', Rval v')`

val app_basic_local = Q.prove(
  `!f x. is_local (\env. app_basic (:'ffi) f x)`,
  cheat)

val app_def = Define `
  app (:'ffi) (f: v) ([]: v list) (H: hprop) (Q: v -> hprop) = F /\
  app (:'ffi) f [x] H Q = app_basic (:'ffi) f x H Q /\
  app (:'ffi) f (x::xs) H Q =
    app_basic (:'ffi) f x H
      (\g. SEP_EXISTS H'. H' * (cond (app (:'ffi) g xs H' Q)))`

val app_alt_ind = Q.prove (
  `!f xs x H Q.
     xs <> [] ==>
     app (:'ffi) f (xs ++ [x]) H Q =
     app (:'ffi) f xs H
       (\g. SEP_EXISTS H'. H' * (cond (app_basic (:'ffi) g x H' Q)))`,
  Induct_on `xs` \\ fs [] \\ rpt strip_tac \\
  Cases_on `xs` \\ fs [app_def]
)

val app_alt_ind_w = Q.prove (
  `!F xs x H Q.
     app (:'ffi) f (xs ++ [x]) H Q ==> xs <> [] ==>
     app (:'ffi) f xs H
       (\g. SEP_EXISTS H'. H' * (cond (app_basic (:'ffi) g x H' Q)))`,
  rpt strip_tac \\ fs [app_alt_ind]
)

val app_local = Q.prove(
  `!f xs. is_local (\env. app (:'ffi) f xs)`,
  cheat)

val curried_def = Define `
  curried (:'ffi) (n: num) (f: v) =
    case n of
     | 0 => F
     | SUC 0 => T
     | SUC n =>
       !x.
         app_basic (:'ffi) f x emp
           (\g. cond (curried (:'ffi) n g /\
                      !xs H Q.
                        LENGTH xs = n ==>
                        app (:'ffi) f (x::xs) H Q ==>
                        app (:'ffi) g xs H Q))`

(* app_over_app / app_over_take *)

(** When [curried n f] holds and the number of the arguments [xs] is less than
    [n], then [app f xs] is a function [g] such that [app g ys] has the same
    behavior as [app f (xs++ys)]. *)

val app_partial = Q.prove (
  `!n xs f. curried (:'ffi) n f ==> (0 < LENGTH xs /\ LENGTH xs < n) ==>
   app (:'ffi) f xs emp (\g. cond (
     curried (:'ffi) (n - LENGTH xs) g /\
     !ys H Q. (LENGTH xs + LENGTH ys = n) ==>
       app (:'ffi) f (xs ++ ys) H Q ==> app (:'ffi) g ys H Q))`,
  completeInduct_on `n` \\ Cases_on `n`
  THEN1 (rpt strip_tac \\ fs [])

  THEN1 (
    Cases_on `xs` \\ rpt strip_tac \\ fs [] \\
    qcase_tac `x::zs` \\ qcase_tac `LENGTH zs < n` \\
    Cases_on `zs` \\ fs []

    THEN1 (
      (* xs = x :: zs = [x] *)
      fs [app_def] \\ cheat
    )
    THEN1 (
      (* xs = x :: zs = [x::y::t] *)
      qcase_tac `x::y::t` \\ fs [app_def] \\ cheat
    )
  )
)

(* Extracting multiarguments lambda/app from the ast *)
val dest_opapp_def = Define `
  dest_opapp (App Opapp l) =
       (case l of
          | [f; x] =>
            (case dest_opapp f of
               | SOME (f', args) => SOME (f', args ++ [x])
               | NONE => SOME (f, [x]))
          | _ => NONE) /\
  dest_opapp _ = NONE`

val dest_opapp_not_empty_arglist = Q.prove (
  `!e f args. dest_opapp e = SOME (f, args) ==> args <> []`,
  Cases \\ fs [dest_opapp_def] \\ qcase_tac `App op _` \\
  Cases_on `op` \\ fs [dest_opapp_def] \\ every_case_tac \\
  fs []
)

(* // *)

val app_ref_def = Define `
  app_ref (x: v) H Q =
    !(r: num). SEP_IMP (H * one (r, Refv x)) (Q (Loc r))`

val app_assign_def = Define `
  app_assign (r: num) (x: v) H Q =
    ?x' F.
      SEP_IMP H (F * one (r, Refv x')) /\
      SEP_IMP (F * one (r, Refv x)) (Q (Conv NONE []))`

val app_deref_def = Define `
  app_deref (r: num) H Q =
    ?x F.
      SEP_IMP H (F * one (r, Refv x)) /\
      SEP_IMP H (Q x)`

val app_aw8alloc_def = Define `
  app_aw8alloc (n: int) w H Q =
    !(loc: num).
      n >= 0 /\
      SEP_IMP (H * one (loc, W8array (REPLICATE (Num (ABS n)) w)))
              (Q (Loc loc))`

val app_aw8sub_def = Define `
  app_aw8sub (loc: num) (i: int) H Q =
    ?ws F.
      let n = Num (ABS i) in
      0 <= i /\ n < LENGTH ws /\
      SEP_IMP H (F * one (loc, W8array ws)) /\
      SEP_IMP H (Q (Litv (Word8 (EL n ws))))`

val app_aw8length_def = Define `
  app_aw8length (loc: num) H Q =
    ?ws F.
      SEP_IMP H (F * one (loc, W8array ws)) /\
      SEP_IMP H (Q (Litv (IntLit (int_of_num (LENGTH ws)))))`

val app_aw8update_def = Define `
  app_aw8update (loc: num) (i: int) w H Q =
    ?ws F.
      let n = Num (ABS i) in
      0 <= i /\ n < LENGTH ws /\
      SEP_IMP H (F * one (loc, W8array ws)) /\
      SEP_IMP (F * one (loc, W8array (LUPDATE w n ws))) (Q (Conv NONE []))`

val app_opn_def = Define `
  app_opn opn i1 i2 H Q =
    ((if opn = Divide \/ opn = Modulo then i2 <> 0 else T) /\
     SEP_IMP H (Q (Litv (IntLit (opn_lookup opn i1 i2)))))`

val app_opb_def = Define `
  app_opb opb i1 i2 H Q =
    SEP_IMP H (Q (Boolv (opb_lookup opb i1 i2)))`

(* ANF related *)

val exp2v_def = Define `
  exp2v _ (Lit l) = SOME (Litv l) /\
  exp2v env (Var name) = lookup_var_id name env /\
  exp2v _ _ = NONE`

val exp2v_evaluate = Q.prove (
  `!e env st v. exp2v env e = SOME v ==>
   evaluate F env st e (st, Rval v)`,
  Induct \\ fs [exp2v_def] \\ prove_tac [bigStepTheory.evaluate_rules]
)

val exp2v_list_def = Define `
  exp2v_list env [] = SOME [] /\
  exp2v_list env (x :: xs) =
    (case exp2v env x of
      | NONE => NONE
      | SOME v =>
        (case exp2v_list env xs of
          | NONE => NONE
          | SOME vs => SOME (v :: vs)))`

val exp2v_list_evaluate = Q.prove (
  `!l lv env st. exp2v_list env l = SOME lv ==>
   evaluate_list F env st l (st, Rval lv)`,
  Induct
  THEN1 (fs [exp2v_list_def] \\ prove_tac [bigStepTheory.evaluate_rules])
  THEN1 (
    rpt strip_tac \\ fs [exp2v_list_def] \\
    Cases_on `exp2v env h` \\ fs [] \\
    Cases_on `exp2v_list env l` \\ fs [] \\
    qpat_assum `_::_ = _` (assume_tac o GSYM) \\
    once_rewrite_tac [bigStepTheory.evaluate_cases] \\ fs [] \\
    qexists_tac `st` \\ fs [exp2v_evaluate]
  )
)

val evaluate_list_rcons = Q.prove (
  `!env st st' st'' l x lv v.
     evaluate_list F env st l (st', Rval lv) /\
     evaluate F env st' x (st'', Rval v) ==>
     evaluate_list F env st (l ++ [x]) (st'', Rval (lv ++ [v]))`,

  Induct_on `l`
  THEN1 (
    rpt strip_tac \\ fs [] \\
    qpat_assum `evaluate_list _ _ _ _ _` mp_tac \\
    once_rewrite_tac [bigStepTheory.evaluate_cases] \\ fs [] \\
    rpt strip_tac \\ qexists_tac `st''` \\ fs [] \\
    prove_tac [bigStepTheory.evaluate_rules]
  )
  THEN1 (
    rpt strip_tac \\ fs [] \\
    qpat_assum `evaluate_list _ _ _ _ _` mp_tac \\
    once_rewrite_tac [bigStepTheory.evaluate_cases] \\ fs [] \\
    rpt strip_tac \\
    Q.LIST_EXISTS_TAC [`v'`, `vs ++ [v]`] \\ fs [] \\
    asm_exists_tac \\ fs [] \\
    metis_tac []
  )
)

val exp2v_list_REVERSE = Q.prove (
  `!l (st: 'ffi state) lv env. exp2v_list env l = SOME lv ==>
   evaluate_list F env st (REVERSE l) (st, Rval (REVERSE lv))`,
  Induct \\ rpt gen_tac \\ disch_then (assume_tac o GSYM) \\
  fs [exp2v_list_def]
  THEN1 (prove_tac [bigStepTheory.evaluate_rules])
  THEN1 (
    Cases_on `exp2v env h` \\ Cases_on `exp2v_list env l` \\ fs [] \\
    first_assum progress \\ irule evaluate_list_rcons \\
    metis_tac [exp2v_evaluate]
  )
)

val exp2v_list_rcons = Q.prove (
  `!xs x l env.
     exp2v_list env (xs ++ [x]) = SOME l ==>
     ?xvs xv.
       l = xvs ++ [xv] /\
       exp2v_list env xs = SOME xvs /\
       exp2v env x = SOME xv`,
  Induct_on `xs` \\ fs [exp2v_list_def] \\ rpt strip_tac \\
  every_case_tac \\ fs [] \\
  first_assum progress \\ fs [] \\ rw []
)

val exp2v_list_LENGTH = Q.prove (
  `!l lv env. exp2v_list env l = SOME lv ==> LENGTH l = LENGTH lv`,
  Induct_on `l` \\ fs [exp2v_list_def] \\ rpt strip_tac \\
  every_case_tac \\ res_tac \\ fs [] \\ rw []
)

(* CF *)

val extend_env_def = Define `
  extend_env [] [] env = env /\
  extend_env (n::ns) (xv::xvs) env =
    extend_env ns xvs (env with v := (n,xv)::env.v)`

val extend_env_rec_def = Define `
  extend_env_rec rec_ns rec_xvs ns xvs env =
    extend_env ns xvs (env with v := ZIP (rec_ns, rec_xvs) ++ env.v)`

val extend_env_rcons = Q.prove (
  `!ns xvs n xv env.
     LENGTH ns = LENGTH xvs ==>
     extend_env (ns ++ [n]) (xvs ++ [xv]) env =
     let env' = extend_env ns xvs env in
     (env' with v := (n,xv) :: env'.v)`,
  Induct \\ rpt strip_tac \\ first_assum (assume_tac o GSYM) \\
  fs [LENGTH_NIL, LENGTH_CONS, extend_env_def] 
)

val build_rec_env_aux_def = Define `
  build_rec_env_aux funs (fs: (tvarN, tvarN # exp) alist) env add_to_env =  
    FOLDR
      (\ (f,x,e) env'. (f, Recclosure env funs f) :: env')
      add_to_env
      fs`

val naryFun_def = Define `
  naryFun [] body = body /\
  naryFun (n::ns) body = Fun n (naryFun ns body)`

val naryClosure_def = Define `
  naryClosure env (n::ns) body = Closure env n (naryFun ns body)`

val naryRecclosure_def = Define `
  naryRecclosure env naryfuns f =
    Recclosure env
    (MAP (\ (f, ns, body). (f, HD ns, naryFun (TL ns) body)) naryfuns)
    f`

val app_one_naryClosure = Q.prove (
  `!env n ns x xs body H Q.
     ns <> [] ==> xs <> [] ==>
     app (:'ffi) (naryClosure env (n::ns) body) (x::xs) H Q ==>
     app (:'ffi) (naryClosure (env with v := (n, x)::env.v) ns body) xs H Q`,

  rpt strip_tac \\ Cases_on `ns` \\ Cases_on `xs` \\ fs [] \\
  qcase_tac `app _ (naryClosure _ (n::n'::ns) _) (x::x'::xs) _ _` \\
  Cases_on `xs` THENL [all_tac, qcase_tac `_::_::x''::xs`] \\
  fs [app_def, naryClosure_def, naryFun_def] \\
  fs [app_basic_def] \\ rpt strip_tac \\ first_x_assum progress \\
  fs [SEP_EXISTS, cond_def, STAR_def] \\
  fs [Q.prove(`!h h'. SPLIT h (h',{}) = (h = h')`, SPLIT_TAC)] \\
  qpat_assum `do_opapp _ = _`
    (assume_tac o REWRITE_RULE [semanticPrimitivesTheory.do_opapp_def]) \\
  fs [] \\ qpat_assum `Fun _ _ = _` (assume_tac o GSYM) \\ fs [] \\
  qpat_assum `evaluate _ _ _ _ _`
    (assume_tac o ONCE_REWRITE_RULE [bigStepTheory.evaluate_cases]) \\ fs []
  \\ fs [semanticPrimitivesTheory.do_opapp_def] \\
  qcase_tac `SPLIT _ (h_f, h_k)` \\
  qcase_tac `SPLIT3 _ (h_f', h_g, h_k)` \\ qcase_tac `H' h_f'` \\
  `SPLIT (st2heap (:'ffi) st) (h_f', h_g UNION h_k)` by SPLIT_TAC \\
  first_assum progress \\
  qcase_tac `SPLIT3 (st2heap _ st'') (h_f'', h_g'', _)` \\
  `SPLIT3 (st2heap (:'ffi) st'') (h_f'', h_g UNION h_g'', h_k)` by SPLIT_TAC
  \\ rpt (asm_exists_tac \\ fs []) \\ (* first goal is proved here *)
  rewrite_tac [Once CONJ_COMM] \\ rpt (asm_exists_tac \\ fs [])
)

val curried_naryClosure = Q.prove (
  `!env len ns body.
     ns <> [] ==> len = LENGTH ns ==>
     curried (:'ffi) len (naryClosure env ns body)`,

  Induct_on `ns` \\ fs [naryClosure_def, naryFun_def] \\ Cases_on `ns`
  THEN1 (once_rewrite_tac [ONE] \\ fs [Once curried_def])
  THEN1 (
    rpt strip_tac \\ fs [naryClosure_def, naryFun_def] \\
    rw [Once curried_def] \\ fs [app_basic_def] \\ rpt strip_tac \\
    fs [emp_def, cond_def, semanticPrimitivesTheory.do_opapp_def] \\
    qcase_tac `SPLIT (st2heap _ st) ({}, h_k)` \\
    `SPLIT3 (st2heap (:'ffi) st) ({}, {}, h_k)` by SPLIT_TAC \\
    instantiate \\ qcase_tac `(n, x) :: _` \\
    first_x_assum (qspecl_then [`env with v := (n,x)::env.v`, `body`]
      assume_tac) \\
    rpt (asm_exists_tac \\ fs []) \\ rpt strip_tac \\
    fs [Once bigStepTheory.evaluate_cases] \\
    fs [GSYM naryFun_def, GSYM naryClosure_def] \\
    irule app_one_naryClosure \\ Cases_on `xs` \\ fs []
  )
)

val cf_lit_def = Define `
  cf_lit l = local (\env H Q. SEP_IMP H (Q (Litv l)))`

val cf_con_def = Define `
  cf_con cn args = local (\env H Q.
    ?argsv cv.
      do_con_check env.c cn (LENGTH args) /\
      (build_conv env.c cn argsv = SOME cv) /\
      (exp2v_list env args = SOME argsv) /\
      SEP_IMP H (Q cv))`

val cf_var_def = Define `
  cf_var name = local (\env H Q.
    !h. H h ==> ?v. lookup_var_id name env = SOME v /\ Q v h)`

val cf_let_def = Define `
  cf_let n F1 F2 = local (\env H Q.
    ?Q'. F1 env H Q' /\
         !xv. F2 (env with <| v := opt_bind n xv env.v |>) (Q' xv) Q)`

val cf_opn_def = Define `
  cf_opn opn x1 x2 = local (\env H Q.
    ?i1 i2.
      exp2v env x1 = SOME (Litv (IntLit i1)) /\
      exp2v env x2 = SOME (Litv (IntLit i2)) /\
      app_opn opn i1 i2 H Q)`

val cf_opb_def = Define `
  cf_opb opb x1 x2 = local (\env H Q.
    ?i1 i2.
      exp2v env x1 = SOME (Litv (IntLit i1)) /\
      exp2v env x2 = SOME (Litv (IntLit i2)) /\
      app_opb opb i1 i2 H Q)`

val cf_app_def = Define `
  cf_app (:'ffi) f args = local (\env H Q.
    ?fv argsv.
      exp2v env f = SOME fv /\
      exp2v_list env args = SOME argsv /\
      app (:'ffi) fv argsv H Q)`

val cf_fundecl_def = Define `
  cf_fundecl (:'ffi) f ns F1 F2 = local (\env H Q.
    !fv.
      curried (:'ffi) (LENGTH ns) fv /\
      (!xvs H' Q'.
        LENGTH xvs = LENGTH ns ==>
        F1 (extend_env ns xvs env) H' Q' ==>
        app (:'ffi) fv xvs H' Q')
      ==>
      F2 (env with v := (f, fv)::env.v) H Q)`

val fundecl_rec_aux_def = Define `
  fundecl_rec_aux (:'ffi) fs fvs [] [] [] F2 env H Q =
    (F2 (extend_env_rec fs fvs [] [] env) H Q) /\
  fundecl_rec_aux (:'ffi) fs fvs (ns::ns_acc) (fv::fv_acc) (Fbody::Fs) F2 env H Q =
    ((!xvs H' Q'.
        LENGTH xvs = LENGTH ns ==>
        Fbody (extend_env_rec fs fvs ns xvs env) H' Q' ==>
        app (:'ffi) fv xvs H' Q')
     ==>
     (fundecl_rec_aux (:'ffi) fs fvs ns_acc fv_acc Fs F2 env H Q)) /\
  fundecl_rec_aux _ _ _ _ _ _ _ _ _ _ = F`

val cf_fundecl_rec_def = Define `
  cf_fundecl_rec (:'ffi) fs Fs F2 = local (\env H Q.
    let f_names = MAP (\ (f,_,_). f) fs in
    let f_args = MAP (\ (_,ns,_). ns) fs in
    !(fvs: v list).
      LENGTH fvs = LENGTH fs ==>
      ALL_DISTINCT f_names /\
      fundecl_rec_aux (:'ffi) f_names fvs f_args fvs Fs F2 env H Q)`

val cf_ref_def = Define `
  cf_ref x = local (\env H Q.
    ?xv.
      exp2v env x = SOME xv /\
      app_ref xv H Q)`

val cf_assign_def = Define `
  cf_assign r x = local (\env H Q.
    ?rv xv.
      exp2v env r = SOME (Loc rv) /\
      exp2v env x = SOME xv /\
      app_assign rv xv H Q)`

val cf_deref_def = Define `
  cf_deref r = local (\env H Q.
    ?rv.
      exp2v env r = SOME (Loc rv) /\
      app_deref rv H Q)`

val cf_aw8alloc_def = Define `
  cf_aw8alloc xn xw = local (\env H Q.
    ?n w.
      exp2v env xn = SOME (Litv (IntLit n)) /\
      exp2v env xw = SOME (Litv (Word8 w)) /\
      app_aw8alloc n w H Q)`

val cf_aw8sub_def = Define `
  cf_aw8sub xl xi = local (\env H Q.
    ?l i.
      exp2v env xl = SOME (Loc l) /\
      exp2v env xi = SOME (Litv (IntLit i)) /\
      app_aw8sub l i H Q)`

val cf_aw8length_def = Define `
  cf_aw8length xl = local (\env H Q.
    ?l.
      exp2v env xl = SOME (Loc l) /\
      app_aw8length l H Q)`

val cf_aw8update_def = Define `
  cf_aw8update xl xi xw = local (\env H Q.
    ?l i w.
      exp2v env xl = SOME (Loc l) /\
      exp2v env xi = SOME (Litv (IntLit i)) /\
      exp2v env xw = SOME (Litv (Word8 w)) /\
      app_aw8update l i w H Q)`

val is_bound_Fun_def = Define `
  is_bound_Fun (SOME _) (Fun _ _) = T /\
  is_bound_Fun _ _ = F`

val Fun_body_def = Define `
  Fun_body (Fun _ body) =
    (case Fun_body body of
       | NONE => SOME body
       | SOME body' => SOME body') /\
  Fun_body _ = NONE`

val Fun_body_exp_size = Q.prove (
  `!e e'. Fun_body e = SOME e' ==> exp_size e' < exp_size e`,
  Induct \\ fs [Fun_body_def] \\ every_case_tac \\ fs [astTheory.exp_size_def]
)

val is_bound_Fun_unfold = Q.prove (
  `!opt e. is_bound_Fun opt e ==> (?n body. e = Fun n body)`,
  Cases_on `e` \\ fs [is_bound_Fun_def]
)

val Fun_params_def = Define `
  Fun_params (Fun n body) =
    n :: (Fun_params body) /\
  Fun_params _ =
    []`

val Fun_params_Fun_body_NONE = Q.prove (
  `!e. Fun_body e = NONE ==> Fun_params e = []`,
  Cases \\ fs [Fun_body_def, Fun_params_def] \\ every_case_tac
)

val Fun_params_Fun_body_repack = Q.prove (
  `!e e'.
     Fun_body e = SOME e' ==>
     naryFun (Fun_params e) e' = e`,
  Induct \\ fs [Fun_body_def, Fun_params_def] \\ every_case_tac \\
  rpt strip_tac \\ fs [Once naryFun_def] \\ TRY every_case_tac \\
  TRY (fs [Fun_params_Fun_body_NONE, Once naryFun_def] \\ NO_TAC) \\
  once_rewrite_tac [naryFun_def] \\ fs []
)

val letrec_pull_params_def = Define `
  letrec_pull_params [] = [] /\
  letrec_pull_params ((f, n, body)::funs) =
    (case Fun_body body of
       | NONE => (f, [n], body)
       | SOME body' => (f, n::Fun_params body, body')) ::
    (letrec_pull_params funs)`

val letrec_pull_params_names = Q.prove (
  `!funs P.
     MAP (\ (f,_,_). P f) (letrec_pull_params funs) =
     MAP (\ (f,_,_). P f) funs`,
  Induct \\ fs [letrec_pull_params_def] \\ rpt strip_tac \\
  qcase_tac `ftuple::funs` \\ PairCases_on `ftuple` \\
  fs [letrec_pull_params_def] \\ every_case_tac \\ fs []
)

val letrec_pull_params_LENGTH = Q.prove (
  `!funs. LENGTH (letrec_pull_params funs) = LENGTH funs`,
  Induct \\ fs [letrec_pull_params_def] \\ rpt strip_tac \\
  qcase_tac `ftuple::funs` \\ PairCases_on `ftuple` \\
  fs [letrec_pull_params_def] \\ every_case_tac \\ fs []
)

val letrec_pull_params_append = Q.prove (
  `!l l'.
     letrec_pull_params (l ++ l') =
     letrec_pull_params l ++ letrec_pull_params l'`,
  Induct \\ rpt strip_tac \\ fs [letrec_pull_params_def] \\
  qcase_tac `ftuple::_` \\ PairCases_on `ftuple` \\ qcase_tac `(f,n,body)` \\
  fs [letrec_pull_params_def]
)

val letrec_pull_params_repack = Q.prove (
  `!funs f env.
     naryRecclosure env (letrec_pull_params funs) f =
     Recclosure env funs f`,
  Induct \\ rpt strip_tac \\ fs [naryRecclosure_def, letrec_pull_params_def] \\
  qcase_tac `ftuple::_` \\ PairCases_on `ftuple` \\ qcase_tac `(f,n,body)` \\
  fs [letrec_pull_params_def] \\ every_case_tac \\ fs [naryFun_def] \\
  fs [Fun_params_Fun_body_repack]
)

val letrec_pull_params_cancel = Q.prove (
  `!funs.
     MAP (\ (f,ns,body). (f, HD ns, naryFun (TL ns) body))
         (letrec_pull_params funs) =
     funs`,
  Induct \\ rpt strip_tac \\ fs [letrec_pull_params_def] \\
  qcase_tac `ftuple::_` \\ PairCases_on `ftuple` \\ qcase_tac `(f,n,body)` \\
  fs [letrec_pull_params_def] \\ every_case_tac \\ fs [naryFun_def] \\
  fs [Fun_params_Fun_body_repack]
)

val SOME_val_def = Define `
  SOME_val (SOME x) = x`

val cf_def = tDefine "cf" `
  cf (:'ffi) (Lit l) = cf_lit l /\
  cf (:'ffi) (Con opt args) = cf_con opt args /\
  cf (:'ffi) (Var name) = cf_var name /\
  cf (:'ffi) (Let opt e1 e2) =
    (if is_bound_Fun opt e1 then
       (case Fun_body e1 of
          | SOME body =>
            cf_fundecl (:'ffi) (SOME_val opt) (Fun_params e1)
              (cf (:'ffi) body) (cf (:'ffi) e2)
          | NONE => local (\env H Q. F))
     else
       cf_let opt (cf (:'ffi) e1) (cf (:'ffi) e2)) /\
  cf (:'ffi) (Letrec funs e) =
    (cf_fundecl_rec (:'ffi) (letrec_pull_params funs)
       (MAP (\x. cf (:'ffi) (SND (SND x))) (letrec_pull_params funs))
       (cf (:'ffi) e)) /\
  cf (:'ffi) (App op args) =
    (case op of
        | Opn opn =>
          (case args of
            | [x1; x2] => cf_opn opn x1 x2
            | _ => local (\env H Q. F))
        | Opb opb =>
          (case args of
            | [x1; x2] => cf_opb opb x1 x2
            | _ => local (\env H Q. F))
        | Opapp =>
          (case dest_opapp (App op args) of
            | SOME (f, xs) => cf_app (:'ffi) f xs
            | NONE => local (\env H Q. F))
        | Opref =>
          (case args of
             | [x] => cf_ref x
             | _ => local (\env H Q. F))
        | Opassign =>
          (case args of
             | [r; x] => cf_assign r x
             | _ => local (\env H Q. F))
        | Opderef =>
          (case args of
             | [r] => cf_deref r
             | _ => local (\env H Q. F))
        | Aw8alloc =>
          (case args of
             | [n; w] => cf_aw8alloc n w
             | _ => local (\env H Q. F))
        | Aw8sub =>
          (case args of
             | [l; n] => cf_aw8sub l n
             | _ => local (\env H Q. F))
        | Aw8length =>
          (case args of
             | [l] => cf_aw8length l
             | _ => local (\env H Q. F))
        | Aw8update =>
          (case args of
             | [l; n; w] => cf_aw8update l n w
             | _ => local (\env H Q. F))
        | _ => local (\env H Q.F)) /\
  cf _ _ = local (\env H Q. F)`

  (WF_REL_TAC `measure (exp_size o SND)` \\ rw []
     THEN1 (
       Cases_on `opt` \\ Cases_on `e1` \\ fs [is_bound_Fun_def] \\
       drule Fun_body_exp_size \\ strip_tac \\ fs [astTheory.exp_size_def]
     )
     THEN1 (
       Induct_on `funs` \\ fs [MEM, letrec_pull_params_def] \\ rpt strip_tac \\
       qcase_tac `f::funs` \\ PairCases_on `f` \\ qcase_tac `(f,ns,body)::funs` \\
       fs [letrec_pull_params_def] \\ fs [astTheory.exp_size_def] \\
       every_case_tac \\ fs [astTheory.exp_size_def] \\
       drule Fun_body_exp_size \\ strip_tac \\ fs [astTheory.exp_size_def]
     )
  )

val cf_ind = fetch "-" "cf_ind"

val cf_defs = [cf_def, cf_lit_def, cf_con_def, cf_var_def, cf_fundecl_def, cf_let_def,
               cf_opn_def, cf_opb_def, cf_aw8alloc_def, cf_aw8sub_def, cf_aw8length_def,
               cf_aw8update_def, cf_app_def, cf_ref_def, cf_assign_def, cf_deref_def,
               cf_fundecl_rec_def]

val cf_local = Q.prove (
  `!e. is_local (cf (:'ffi) e)`,
  qsuff_tac `!(r: 'ffi itself) e. is_local (cf (:'ffi) e)`
  THEN1 (fs []) \\
  recInduct cf_ind \\ rpt strip_tac \\
  fs (local_local :: local_is_local :: cf_defs)
  THEN1 (
    Cases_on `opt` \\ Cases_on `e1` \\ fs [is_bound_Fun_def, local_is_local] \\
    fs [Fun_body_def] \\ every_case_tac \\ fs [local_is_local]
  )
  THEN1 (
    Cases_on `op` \\ fs [local_is_local] \\
    every_case_tac \\ fs [local_is_local]
  )
)

(* Soundness of cf *)

val EnvCorr_def = Define `
  EnvCorr env certs =
    FEVERY (\(name, P). ?v. lookup_var_id name env = SOME v /\ P v) certs`

val DeclCorr_def = Define `
  DeclCorr mn ds certs =
    ?env tys. DeclAssum mn ds env tys /\ EnvCorr env certs`

val sound_def = Define `
  sound (:'ffi) e R =
    !env H Q. R env H Q ==>
    !st h_i h_k. SPLIT (st2heap (:'ffi) st) (h_i, h_k) ==>
    H h_i ==>
      ?v st' h_f h_g.
        SPLIT3 (st2heap (:'ffi) st') (h_f, h_k, h_g) /\
        evaluate F env st e (st', Rval v) /\
        Q v h_f`

val star_split = Q.prove (
  `!H1 H2 H3 H4 h1 h2 h3 h4.
     ((H1 * H2) (h1 UNION h2) ==> (H3 * H4) (h3 UNION h4)) ==>
     DISJOINT h1 h2 ==> H1 h1 ==> H2 h2 ==>
     ?u v. H3 u /\ H4 v /\ SPLIT (h3 UNION h4) (u, v)`,
  fs [STAR_def] \\ rpt strip_tac \\
  `SPLIT (h1 UNION h2) (h1, h2)` by SPLIT_TAC \\
  metis_tac []
)

val sound_local = Q.prove (
  `!e R. sound (:'ffi) e R ==> sound (:'ffi) e (local R)`,
  rpt strip_tac \\ rewrite_tac [sound_def, local_def] \\ rpt strip_tac \\
  res_tac \\ qcase_tac `(H_i * H_k) h_i` \\ qcase_tac `R env H_i Q_f` \\
  qcase_tac `SEP_IMPPOST (Q_f *+ H_k) (Q *+ H_g)` \\
  fs [STAR_def] \\ qcase_tac `H_i h'_i` \\ qcase_tac `H_k h'_k` \\
  `SPLIT (st2heap (:'ffi) st) (h'_i, h_k UNION h'_k)` by SPLIT_TAC \\
  qpat_assum `sound _ _ _` (progress o REWRITE_RULE [sound_def]) \\
  qcase_tac `SPLIT3 _ (h'_f, _, h'_g)` \\
  fs [SEP_IMPPOST_def, STARPOST_def, SEP_IMP_def, STAR_def] \\
  first_x_assum (qspecl_then [`v`, `h'_f UNION h'_k`] assume_tac) \\
  `DISJOINT h'_f h'_k` by SPLIT_TAC \\
  `?h_f h''_g. Q v h_f /\ H_g h''_g /\ SPLIT (h'_f UNION h'_k) (h_f, h''_g)` by
    metis_tac [star_split] \\
  Q.LIST_EXISTS_TAC [`v`, `st'`, `h_f`, `h'_g UNION h''_g`] \\ fs [] \\
  SPLIT_TAC
)

val sound_false = Q.prove (
  `!e. sound (:'ffi) e (\env H Q. F)`,
  rewrite_tac [sound_def]
)

val cf_base_case_tac =
  irule sound_local \\ rewrite_tac [sound_def] \\ rpt strip_tac \\ fs [] \\
  res_tac \\ qcase_tac `SPLIT (st2heap _ st) (h_i, h_k)` \\
  `SPLIT3 (st2heap (:'ffi) st) (h_i, h_k, {})` by SPLIT_TAC \\ instantiate \\
  once_rewrite_tac [bigStepTheory.evaluate_cases] \\ fs [SEP_IMP_def]

val cf_strip_sound_tac =
  TRY (irule sound_local) \\ rewrite_tac [sound_def] \\ rpt strip_tac \\ fs []

val cf_evaluate_step_tac =
  once_rewrite_tac [bigStepTheory.evaluate_cases] \\
  fs [libTheory.opt_bind_def, PULL_EXISTS]

val cf_strip_sound_full_tac = cf_strip_sound_tac \\ cf_evaluate_step_tac

fun cf_evaluate_list_tac [] = prove_tac [bigStepTheory.evaluate_rules]
  | cf_evaluate_list_tac (st::sts) =
    once_rewrite_tac [bigStepTheory.evaluate_cases] \\ fs [] \\
    qexists_tac st \\ strip_tac THENL [fs [exp2v_evaluate], all_tac] \\
    cf_evaluate_list_tac sts

val build_rec_env_zip_aux = Q.prove (
  `!(fs: (tvarN, tvarN # exp) alist) funs env env_v.
    ZIP (MAP (\ (f,_,_). f) fs,
         MAP (\ (f,_,_). naryRecclosure env (letrec_pull_params funs) f) fs)
      ++ env_v =
    FOLDR (\ (f,x,e) env'. (f,Recclosure env funs f)::env') env_v fs`,
  Induct \\ rpt strip_tac THEN1 (fs []) \\
  qcase_tac `ftuple::fs` \\ PairCases_on `ftuple` \\ qcase_tac `(f,n,body)` \\
  fs [letrec_pull_params_repack]
)

val build_rec_env_zip = Q.prove (
  `!funs env env_v.
    ZIP (MAP (\ (f,_,_). f) funs,
         MAP (\ (f,_,_). naryRecclosure env (letrec_pull_params funs) f) funs)
      ++ env_v =
    build_rec_env funs env env_v`,
  fs [semanticPrimitivesTheory.build_rec_env_def, build_rec_env_zip_aux]
)

val extend_env_rec_build_rec_env = Q.prove (
  `!funs env.
     extend_env_rec
       (MAP (\ (f,_,_). f) funs)
       (MAP (\ (f,_,_). naryRecclosure env (letrec_pull_params funs) f) funs)
       [] [] env =
     (env with v := build_rec_env funs env env.v)`,
  rpt strip_tac \\ fs [extend_env_rec_def, extend_env_def, build_rec_env_zip]
)

val app_basic_of_sound_cf = Q.prove (
  `!clos body x env env' v H Q.
    do_opapp [clos; x] = SOME (env', body) ==>
    sound (:'ffi) body (cf (:'ffi) body) ==>
    cf (:'ffi) body env' H Q ==>
    app_basic (:'ffi) clos x H Q`,
  fs [app_basic_def, sound_def] \\ rpt strip_tac \\ first_x_assum progress \\
  instantiate \\ SPLIT_TAC
)

val app_of_sound_cf = Q.prove (
  `!ns xvs env body H Q.
     ns <> [] ==>
     LENGTH ns = LENGTH xvs ==>
     sound (:'ffi) body (cf (:'ffi) body) ==>
     cf (:'ffi) body (extend_env ns xvs env) H Q ==>
     app (:'ffi) (naryClosure env ns body) xvs H Q`,

  Induct \\ rpt strip_tac \\ fs [naryClosure_def, LENGTH_CONS] \\ rw [] \\
  qcase_tac `extend_env (n::ns) (xv::xvs) _` \\ Cases_on `ns` \\
  rfs [LENGTH_NIL, LENGTH_CONS, extend_env_def, naryFun_def, app_def]
  THEN1 (
    irule app_basic_of_sound_cf \\
    fs [semanticPrimitivesTheory.do_opapp_def]
  )
  THEN1 (
    rw [] \\ fs [] \\ qcase_tac `extend_env (n'::ns) (xv'::xvs) _` \\
    fs [app_basic_def] \\ rpt strip_tac \\
    fs [semanticPrimitivesTheory.do_opapp_def] \\
    fs [SEP_EXISTS, cond_def, STAR_def, PULL_EXISTS] \\
    fs [naryFun_def, naryClosure_def, Once bigStepTheory.evaluate_cases] \\
    fs [Q.prove(`!h h'. SPLIT h (h',{}) = (h' = h)`, SPLIT_TAC)] \\
    first_assum progress \\ instantiate \\ qexists_tac `{}` \\ SPLIT_TAC
  )
)

val find_recfun_letrec_pull_params = Q.prove (
  `!funs f n ns body.
     find_recfun f (letrec_pull_params funs) = SOME (n::ns, body) ==>
     find_recfun f funs = SOME (n, naryFun ns body)`,
  Induct \\ fs [letrec_pull_params_def]
  THEN1 (fs [Once semanticPrimitivesTheory.find_recfun_def]) \\
  rpt strip_tac \\ qcase_tac `ftuple::funs` \\ PairCases_on `ftuple` \\
  qcase_tac `(f',n',body')` \\ fs [letrec_pull_params_def] \\
  every_case_tac \\ pop_assum mp_tac \\
  once_rewrite_tac [semanticPrimitivesTheory.find_recfun_def] \\ fs [] \\
  every_case_tac \\ rw [] \\ fs [naryFun_def, Fun_params_Fun_body_repack]
)

val do_opapp_naryRecclosure = Q.prove (
  `!funs f n ns body x env env' exp.
     find_recfun f (letrec_pull_params funs) = SOME (n::ns, body) ==>
     (do_opapp [naryRecclosure env (letrec_pull_params funs) f; x] =
      SOME (env', exp)
     <=>
     (ALL_DISTINCT (MAP (\ (f,_,_). f) funs) /\
      env' = (env with v := (n, x)::build_rec_env funs env env.v) /\
      exp = naryFun ns body))`,
  rpt strip_tac \\ progress find_recfun_letrec_pull_params \\
  fs [naryRecclosure_def, semanticPrimitivesTheory.do_opapp_def] \\
  fs [letrec_pull_params_cancel] \\ eq_tac \\ every_case_tac \\ fs []
)

val find_recfun_map = Q.prove (
  `!l a b c f u v.
     (!a b c. FST (f (a, b, c)) = a) ==>
     f (a, b, c) = (a, u, v) ==>
     find_recfun a l = SOME (b, c) ==>
     find_recfun a (MAP f l) = SOME (u, v)`,
  Induct_on `l`
  THEN1 (fs [semanticPrimitivesTheory.find_recfun_def]) \\ rpt gen_tac \\
  NTAC 2 DISCH_TAC \\
  qcase_tac `x::_` \\ PairCases_on `x` \\ qcase_tac `(a',b',c')` \\
  rewrite_tac [Once semanticPrimitivesTheory.find_recfun_def] \\ fs [] \\
  Cases_on `a' = a` \\ fs [] \\ rpt strip_tac
  THEN1 (fs [Once semanticPrimitivesTheory.find_recfun_def])
  THEN1 (
    rewrite_tac [Once semanticPrimitivesTheory.find_recfun_def] \\ fs [] \\
    `?u' v'. f (a', b', c') = (a', u', v')` by (
      first_assum (qspecl_then [`a'`, `b'`, `c'`] assume_tac) \\
      qabbrev_tac `x' = f (a',b',c')` \\ PairCases_on `x'` \\ fs []
    ) \\ fs [] \\
    fs [Once semanticPrimitivesTheory.find_recfun_def]
  )
)

val app_rec_of_sound_cf_aux = Q.prove (
  `!f body params xvs funs naryfuns env H Q fvs.
     params <> [] ==>
     LENGTH params = LENGTH xvs ==>
     naryfuns = letrec_pull_params funs ==>
     ALL_DISTINCT (MAP (\ (f,_,_). f) naryfuns) ==>
     find_recfun f naryfuns = SOME (params, body) ==>
     sound (:'ffi) body (cf (:'ffi) body) ==>
     fvs = MAP (\ (f,_,_). naryRecclosure env naryfuns f) naryfuns ==>
     cf (:'ffi) body
       (extend_env_rec (MAP (\ (f,_,_). f) naryfuns) fvs params xvs env) H Q ==>
     app (:'ffi) (naryRecclosure env naryfuns f) xvs H Q`,
  
  Cases_on `params` \\ rpt strip_tac \\ rw [] \\
  fs [LENGTH_CONS] \\ rfs [] \\ qpat_assum `xvs = _` (K all_tac) \\
  qcase_tac `extend_env_rec _ _ (n::params) (xv::xvs) _` \\
  Cases_on `params` \\ rfs [LENGTH_NIL, LENGTH_CONS, extend_env_rec_def] \\
  fs [extend_env_def, app_def]
  THEN1 (
    irule app_basic_of_sound_cf \\
    rpt_drule_then (fs o sing) do_opapp_naryRecclosure \\ 
    fs [naryFun_def, letrec_pull_params_names, build_rec_env_zip]
  )
  THEN1 (
    rw [] \\ qcase_tac `extend_env (n'::params) (xv'::xvs) _` \\
    fs [app_basic_def] \\ rpt strip_tac \\
    rpt_drule_then (fs o sing) do_opapp_naryRecclosure \\
    fs [SEP_EXISTS, cond_def, STAR_def, PULL_EXISTS] \\
    fs [Q.prove(`!h h'. SPLIT h (h',{}) = (h' = h)`, SPLIT_TAC)] \\
    qcase_tac `SPLIT _ (h, i)` \\
    `SPLIT3 (st2heap (:'ffi) st) (h, {}, i)` by SPLIT_TAC \\ instantiate \\
    (* fixme *)
    qexists_tac `naryClosure
      (env with v := (n,xv)::(ZIP (MAP (\ (f,_,_). f) (letrec_pull_params funs),
        MAP (\ (f,_,_). naryRecclosure env (letrec_pull_params funs) f)
            (letrec_pull_params funs)) ++ env.v))
      (n'::params) body` \\ strip_tac
    THEN1 (irule app_of_sound_cf \\ fs [])
    THEN1 (
      fs [naryFun_def, naryClosure_def, Once bigStepTheory.evaluate_cases] \\
      fs [letrec_pull_params_cancel, letrec_pull_params_names] \\
      fs [build_rec_env_zip]
    )
  )
)

val app_rec_of_sound_cf = Q.prove (
  `!f params body funs xvs env H Q.
     params <> [] ==>
     LENGTH params = LENGTH xvs ==>
     ALL_DISTINCT (MAP (\ (f,_,_). f) funs) ==>
     MEM (f,params,body) (letrec_pull_params funs) ==>
     sound (:'ffi) body (cf (:'ffi) body) ==>
     cf (:'ffi) body
       (extend_env_rec
          (MAP (\ (f,_,_). f) funs) 
          (MAP (\ (f,_,_). naryRecclosure env (letrec_pull_params funs) f) funs)
          params xvs env)
        H Q ==>
     app (:'ffi) (naryRecclosure env (letrec_pull_params funs) f) xvs H Q`,
  rpt strip_tac \\ irule app_rec_of_sound_cf_aux
  THEN1 (fs [letrec_pull_params_names])
  THEN1 (qexists_tac `funs` \\ fs [])
  THEN1 (
    fs [evalPropsTheory.find_recfun_ALOOKUP] \\
    CONSEQ_REWRITE_TAC ([ALOOKUP_ALL_DISTINCT_MEM], [], []) \\
    `FST = (\ ((f:tvarN),(_:tvarN list),(_:exp)). f)` by (
      irule EQ_EXT \\ qx_gen_tac `x` \\ PairCases_on `x` \\ fs []
    ) \\ instantiate \\ fs [letrec_pull_params_names] 
  )
)

val DROP_EL_CONS = Q.prove (
  `!l n.
    n < LENGTH l ==>
    DROP n l = EL n l :: DROP (SUC n) l`,
  Induct \\ rpt strip_tac \\ fs [] \\ every_case_tac \\ fs [] \\
  Cases_on `n` \\ fs []
)

val cf_letrec_sound_aux = Q.prove (
  `!funs e.
     let naryfuns = letrec_pull_params funs in
     (∀x. MEM x naryfuns ==>
          sound (:'ffi) (SND (SND x)) (cf (:'ffi) (SND (SND x)))) ==>
     sound (:'ffi) e (cf (:'ffi) e) ==>
     !fns rest.
       funs = rest ++ fns ==>
       let naryrest = letrec_pull_params rest in
       let naryfns = letrec_pull_params fns in
       sound (:'ffi) (Letrec funs e)
         (\env H Q.
            let fvs = MAP (\ (f,_,_). naryRecclosure env naryfuns f) naryfuns in
            ALL_DISTINCT (MAP (\ (f,_,_). f) naryfuns) /\
            fundecl_rec_aux (:'ffi)
              (MAP (\ (f,_,_). f) naryfuns) fvs
              (MAP (\ (_,ns,_). ns) naryfns)
              (DROP (LENGTH naryrest) fvs)
              (MAP (\x. cf (:'ffi) (SND (SND x))) naryfns)
              (cf (:'ffi) e) env H Q)`,

  rpt gen_tac \\ rpt (CONV_TAC let_CONV) \\ rpt DISCH_TAC \\ Induct
  THEN1 (
    rpt strip_tac \\ fs [letrec_pull_params_def, DROP_LENGTH_TOO_LONG] \\
    fs [fundecl_rec_aux_def] \\
    qpat_assum `_ = rest` (mp_tac o GSYM) \\ rw [] \\
    cf_strip_sound_full_tac \\ qpat_assum `sound _ e _` mp_tac \\
    fs [letrec_pull_params_names, extend_env_rec_build_rec_env] \\
    rewrite_tac [sound_def] \\ disch_then progress \\ instantiate
  )
  THEN1 (
    qx_gen_tac `ftuple` \\ PairCases_on `ftuple` \\ qcase_tac `(f, n, body)` \\
    rpt strip_tac \\
    (* rest := rest ++ [(f,n,body)] *)
    (fn x => first_x_assum (qspec_then x mp_tac))
      `rest ++ [(f, n, body)]` \\ impl_tac THEN1 (fs []) \\ strip_tac \\
    qpat_assum `funs = _` (assume_tac o GSYM) \\ rpt (CONV_TAC let_CONV) \\
    rewrite_tac [sound_def] \\ BETA_TAC \\ rpt gen_tac \\
    qmatch_abbrev_tac `(LET _ fvs) ==> _` \\ fs [] \\
    (* unfold letrec_pull_params (_::_); extract the body/params *)
    rewrite_tac [letrec_pull_params_def] \\ 
    fs [Q.prove(`!opt a b c a' b' c'.
       (case opt of NONE => (a,b,c) | SOME x => (a', b', c' x)) =
       ((case opt of NONE => a | SOME x => a'),
        (case opt of NONE => b | SOME x => b'),
        (case opt of NONE => c | SOME x => c' x))`,
      rpt strip_tac \\ every_case_tac \\ fs [])] \\
    qmatch_goalsub_abbrev_tac `cf _ inner_body::_ _` \\
    qmatch_goalsub_abbrev_tac `fundecl_rec_aux _ _ _ (params::_)` \\
    (* unfold "sound _ (Letrec _ _)" in the goal *)
    cf_strip_sound_full_tac \\
    qpat_assum `fundecl_rec_aux _ _ _ _ _ _ _ _ _ _` mp_tac \\
    (* Rewrite (DROP _ _) to a (_::DROP _ _) *)
    qpat_abbrev_tac `tail = DROP _ _` \\
    `tail = (naryRecclosure env (letrec_pull_params funs) f) ::
            DROP (LENGTH (letrec_pull_params rest) + 1) fvs` by (
      qunabbrev_tac `tail` \\ rewrite_tac [GSYM ADD1] \\
      fs [letrec_pull_params_LENGTH] \\ 
      mp_tac (Q.ISPECL [`fvs: v list`,
                        `LENGTH (rest: (tvarN, tvarN # exp) alist)`]
              DROP_EL_CONS) \\
      impl_tac THEN1 (
        qunabbrev_tac `fvs` \\ qpat_assum `_ = funs` (assume_tac o GSYM) \\
        fs [letrec_pull_params_LENGTH]
      ) \\
      fs [] \\ strip_tac \\ qunabbrev_tac `fvs` \\
      fs [letrec_pull_params_names] \\
      qpat_abbrev_tac `naryfuns = letrec_pull_params funs` \\
      `LENGTH rest < LENGTH funs` by (
        qpat_assum `_ = funs` (assume_tac o GSYM) \\ fs []) \\
      fs [EL_MAP] \\ qpat_assum `_ = funs` (assume_tac o GSYM) \\
      fs [el_append3, ADD1]
    ) \\ fs [] \\
    (* We can now unfold fundecl_rec_aux *)
    fs [fundecl_rec_aux_def] \\ rewrite_tac [ONE] \\
    fs [LENGTH_CONS, LENGTH_NIL, PULL_EXISTS] \\
    fs [letrec_pull_params_LENGTH, letrec_pull_params_names] \\
    impl_tac
    THEN1 (
      rpt strip_tac \\ irule app_rec_of_sound_cf
      THEN1 (fs [letrec_pull_params_names])
      THEN1 (
        Q.LIST_EXISTS_TAC [`inner_body`, `params`] \\ fs [] \\
        `MEM (f,params,inner_body) (letrec_pull_params funs)` by (
          qpat_assum `_ = funs` (assume_tac o GSYM) \\
          fs [letrec_pull_params_append, letrec_pull_params_def] \\
          qunabbrev_tac `params` \\ qunabbrev_tac `inner_body` \\
          every_case_tac \\ fs []
        ) \\ first_assum progress \\ qunabbrev_tac `params` \\
        every_case_tac \\ fs []
      )
    ) \\ strip_tac \\
    qpat_assum `sound _ (Letrec _ _) _` (mp_tac o REWRITE_RULE [sound_def]) \\
    fs [] \\ disch_then (qspecl_then [`env`, `H`, `Q`] mp_tac) \\ fs [] \\
    disch_then progress \\ instantiate \\ fs [Once bigStepTheory.evaluate_cases]
  )
)

val cf_letrec_sound = Q.prove (
  `!funs e.
    (!x. MEM x (letrec_pull_params funs) ==>
         sound (:'ffi) (SND (SND x)) (cf (:'ffi) (SND (SND x)))) ==>
    sound (:'ffi) e (cf (:'ffi) e) ==>
    sound (:'ffi) (Letrec funs e)
      (\env H Q.
        let fvs = MAP
          (\ (f,_,_). naryRecclosure env (letrec_pull_params funs) f)
          funs in
        ALL_DISTINCT (MAP (\ (f,_,_). f) funs) /\
        fundecl_rec_aux (:'ffi)
          (MAP (\ (f,_,_). f) funs) fvs
          (MAP (\ (_,ns,_). ns) (letrec_pull_params funs)) fvs
          (MAP (\x. cf (:'ffi) (SND (SND x))) (letrec_pull_params funs))
          (cf (:'ffi) e) env H Q)`,
  rpt strip_tac \\ mp_tac (Q.SPECL [`funs`, `e`] cf_letrec_sound_aux) \\
  fs [] \\ disch_then (qspecl_then [`funs`, `[]`] mp_tac) \\
  fs [letrec_pull_params_names, letrec_pull_params_def]
)

val cf_sound = Q.prove (
  `!(r: 'ffi itself) e. sound (:'ffi) e (cf (:'ffi) e)`,
  recInduct cf_ind \\ rpt strip_tac \\
  rewrite_tac cf_defs \\ fs [sound_local, sound_false]
  THEN1 (* Lit *) cf_base_case_tac
  THEN1 (
    (* Con *)
    cf_base_case_tac \\ fs [PULL_EXISTS, st2heap_def] \\
    progress exp2v_list_REVERSE \\ Q.LIST_EXISTS_TAC [`cv`, `REVERSE argsv`] \\
    fs []
  )
  THEN1 (* Var *) cf_base_case_tac
  THEN1 (
    (* Let *)
    Cases_on `is_bound_Fun opt e1` \\ fs []
    THEN1 (
      (* function declaration *)
      (* Eliminate the impossible case (Fun_body _ = NONE), then we call
        cf_strip_sound_tac *)
      progress is_bound_Fun_unfold \\ fs [Fun_body_def] \\
      BasicProvers.TOP_CASE_TAC \\ cf_strip_sound_tac \\
      (* Instantiate the hypothesis with the closure *) 
      qcase_tac `(case Fun_body _ of _ => _) = SOME inner_body` \\
      (fn tm => first_x_assum (qspec_then tm mp_tac))
        `naryClosure env (Fun_params (Fun n body)) inner_body` \\
      impl_tac \\ strip_tac
      THEN1 (irule curried_naryClosure \\ fs [Fun_params_def])
      THEN1 (fs [Fun_params_def, app_of_sound_cf]) \\
      qpat_assum `sound _ e2 _` (progress o REWRITE_RULE [sound_def]) \\
      cf_evaluate_step_tac \\ Cases_on `opt` \\
      fs [is_bound_Fun_def, SOME_val_def, Fun_params_def] \\ instantiate \\
      every_case_tac \\ qpat_assum `_ = inner_body` (assume_tac o GSYM) \\
      fs [naryClosure_def, naryFun_def, Fun_params_Fun_body_NONE,
          Fun_params_Fun_body_repack, Once bigStepTheory.evaluate_cases]
    )
    THEN1 (
      (* other cases of let-binding *)
      cf_strip_sound_full_tac \\
      qpat_assum `sound _ e1 _` (progress o REWRITE_RULE [sound_def]) \\
      first_assum (qspec_then `v` assume_tac) \\
      `SPLIT (st2heap (:'ffi) st') (h_f, h_k UNION h_g)` by SPLIT_TAC \\
      qpat_assum `sound _ e2 _` (progress o REWRITE_RULE [sound_def]) \\
      `SPLIT3 (st2heap (:'ffi) st'') (h_f',h_k, h_g UNION h_g')` by SPLIT_TAC \\
      instantiate
    )
  )
  THEN1 (
    (* Letrec *)
    irule sound_local \\ mp_tac (Q.SPECL [`funs`, `e`] cf_letrec_sound) \\
    fs [letrec_pull_params_LENGTH, letrec_pull_params_names] \\
    rewrite_tac [sound_def] \\ rpt strip_tac \\ fs [] \\
    first_assum (qspecl_then [`env`, `H`, `Q`] assume_tac) \\
    (fn x => first_assum (qspec_then x assume_tac))
      `MAP (\ (f,_,_). naryRecclosure env (letrec_pull_params funs) f) funs` \\
    fs [letrec_pull_params_LENGTH] \\ res_tac \\ instantiate
  )
  THEN1 (
    (* App *)
    Cases_on `op` \\ fs [sound_false] \\ every_case_tac \\
    fs [sound_false] \\ cf_strip_sound_tac \\
    (qcase_tac `(App Opapp _)` ORELSE cf_evaluate_step_tac) \\
    TRY (
      (* Opn & Opb *)
      (qcase_tac `app_opn op` ORELSE qcase_tac `app_opb op`) \\
      fs [app_opn_def, app_opb_def, st2heap_def] \\
      `SPLIT3 (store2heap st.refs) (h_i, h_k, {})` by SPLIT_TAC \\
      instantiate \\
      GEN_EXISTS_TAC "vs" `[Litv (IntLit i2); Litv (IntLit i1)]` \\
      Cases_on `op` \\ fs [semanticPrimitivesTheory.do_app_def] \\
      qexists_tac `st` \\ rpt strip_tac \\ fs [SEP_IMP_def] \\
      cf_evaluate_list_tac [`st`, `st`]
    )
    THEN1 (
      (* Opapp *)
      qcase_tac `dest_opapp _ = SOME (f, xs)` \\
      schneiderUtils.UNDISCH_ALL_TAC \\ SPEC_ALL_TAC \\
      CONV_TAC (RESORT_FORALL_CONV (fn l =>
        (op @) (partition (fn v => fst (dest_var v) = "xs") l))) \\
      gen_tac \\ completeInduct_on `LENGTH xs` \\ rpt strip_tac \\
      fs [] \\ qpat_assum `dest_opapp _ = _` mp_tac \\
      rewrite_tac [dest_opapp_def] \\ every_case_tac \\ fs [] \\
      rpt strip_tac \\ qpat_assum `_ = xs` (assume_tac o GSYM) \\ fs []
      (* 1 argument *)
      THEN1 (
        qcase_tac `xs = [x]` \\ fs [exp2v_list_def] \\ full_case_tac \\ fs [] \\
        qpat_assum `_ = argsv` (assume_tac o GSYM) \\ qcase_tac `argsv = [xv]` \\
        cf_evaluate_step_tac \\ GEN_EXISTS_TAC "vs" `[xv; fv]` \\
        fs [app_def, app_basic_def] \\ res_tac \\
        qcase_tac `SPLIT3 (st2heap _ st') (h_f, h_g, h_k)` \\
        `SPLIT3 (st2heap (:'ffi) st') (h_f, h_k, h_g)` by SPLIT_TAC \\
        instantiate \\ prove_tac [exp2v_evaluate, bigStepTheory.evaluate_rules]
      )
      (* 2+ arguments *)
      THEN1 (
        qcase_tac `dest_opapp papp_ = SOME (f, pxs)` \\
        qcase_tac `xs = pxs ++ [x]` \\ fs [LENGTH] \\
        progress exp2v_list_rcons \\ fs [] \\
        (* Do some unfolding, by definition of dest_opapp *)
        `?papp. papp_ = App Opapp papp` by (
          Cases_on `papp_` \\ TRY (fs [dest_opapp_def] \\ NO_TAC) \\
          qcase_tac `dest_opapp (App op _)` \\
          Cases_on `op` \\ TRY (fs [dest_opapp_def] \\ NO_TAC)
        ) \\ fs [] \\
        (* Prepare for, and apply lemma [app_alt_ind_w] to split app *)
        progress dest_opapp_not_empty_arglist \\
        `xvs <> []` by (progress exp2v_list_LENGTH \\ strip_tac \\
                       first_assum irule \\ fs [LENGTH_NIL]) \\
        progress app_alt_ind_w \\
        (* Specialize induction hypothesis with xs := pxs *)
        `LENGTH pxs < LENGTH pxs + 1` by (fs []) \\
        last_assum drule \\ disch_then (qspec_then `pxs` mp_tac) \\ fs [] \\
        disch_then progress \\ fs [SEP_EXISTS, cond_def, STAR_def] \\
        (* Cleanup *)
        qcase_tac `app_basic _ g xv H' Q` \\
        rfs [prove(``!h h'. SPLIT h (h', {}) = (h' = h)``, SPLIT_TAC)] \\
        (* Start unfolding the goal and instantiating exists *)
        cf_evaluate_step_tac \\ GEN_EXISTS_TAC "vs" `[xv; g]` \\
        GEN_EXISTS_TAC "s2" `st'` \\
        `SPLIT (st2heap (:'ffi) st') (h_f, h_k UNION h_g)` by SPLIT_TAC \\
        (* Exploit the [app_basic (:'ffi) g xv H' Q] we got from the ind. hyp. *)
        fs [app_basic_def] \\ first_assum progress \\
        (* Prove the goal *)
        qcase_tac `SPLIT3 (st2heap _ st'') (h_f', h_g', _)` \\
        `SPLIT3 (st2heap (:'ffi) st'') (h_f', h_k, h_g' UNION h_g)` by SPLIT_TAC
        \\ instantiate \\ cf_evaluate_list_tac [`st`, `st'`]
      )
    )
    THEN1 (
      (* Opassign *)
      fs [app_assign_def, SEP_IMP_def, STAR_def, one_def, st2heap_def] \\
      `evaluate_list F env st [h'; h] (st, Rval [xv; Loc rv])` by
        (cf_evaluate_list_tac [`st`, `st`]) \\
      qpat_assum `!s. H s ==> _` progress \\ 
      qcase_tac `SPLIT h_i (h_i', _)` \\ qcase_tac `FF h_i'` \\
      GEN_EXISTS_TAC "vs" `[xv; Loc rv]` \\
      fs [semanticPrimitivesTheory.do_app_def, semanticPrimitivesTheory.store_assign_def] \\
      `rv < LENGTH st.refs` by (mp_tac store2heap_IN_LENGTH \\ SPLIT2_TAC) \\
      `store_v_same_type (EL rv st.refs) (Refv xv)` by (
        `(rv, Refv x') IN (store2heap st.refs)` by SPLIT2_TAC \\
        fs [semanticPrimitivesTheory.store_v_same_type_def] \\
        qspecl_then [`st.refs`, `rv`, `Refv x'`] assume_tac store2heap_IN_EL \\
        fs []
       ) \\
      `SPLIT3 (store2heap (LUPDATE (Refv xv) rv st.refs))
         ((rv, Refv xv) INSERT h_i', h_k, {})` by (
        mp_tac store2heap_LUPDATE \\ mp_tac store2heap_IN_unique_key \\
        SPLIT2_TAC
      ) \\ instantiate \\ first_assum irule \\
      strip_assume_tac store2heap_IN_unique_key \\ SPLIT_TAC
    )
    THEN1 (
      (* Opref *)
      fs [semanticPrimitivesTheory.do_app_def, semanticPrimitivesTheory.store_alloc_def] \\
      fs [st2heap_def, app_ref_def, SEP_IMP_def, STAR_def, one_def] \\
      GEN_EXISTS_TAC "vs" `[xv]` \\
      (fn l => first_x_assum (qspecl_then l mp_tac))
        [`LENGTH st.refs`, `(LENGTH st.refs,Refv xv) INSERT h_i`] \\
      impl_tac
      THEN1 (qexists_tac `h_i` \\ assume_tac store2heap_alloc_disjoint \\ SPLIT_TAC)
      THEN1 (
        strip_tac \\
        `evaluate_list F env st [h] (st, Rval [xv])` by
          (cf_evaluate_list_tac [`st`, `st`]) \\
        instantiate \\ fs [store2heap_append] \\ assume_tac store2heap_alloc_disjoint \\
        qexists_tac `{}` \\ SPLIT_TAC
      )
    )
    THEN1 (
      (* Opderef *)
      `evaluate_list F env st [h] (st, Rval [Loc rv])` by
        (cf_evaluate_list_tac [`st`, `st`]) \\
      fs [st2heap_def, app_deref_def, SEP_IMP_def, STAR_def, one_def] \\
      rpt (qpat_assum `!s. H s ==> _` progress) \\ fs [] \\
      qcase_tac `SPLIT h_i (h_i', {(rv,Refv x)})` \\ qcase_tac `FF h_i'` \\
      GEN_EXISTS_TAC "vs" `[Loc rv]` \\
      fs [semanticPrimitivesTheory.do_app_def, semanticPrimitivesTheory.store_lookup_def] \\
      `rv < LENGTH st.refs` by (mp_tac store2heap_IN_LENGTH \\ SPLIT2_TAC) \\
      `SPLIT3 (store2heap st.refs) (h_i, h_k, {})` by SPLIT_TAC \\
      instantiate \\
      qspecl_then [`st.refs`, `rv`, `Refv x`] assume_tac store2heap_IN_EL \\
      `(rv,Refv x) IN store2heap st.refs` by SPLIT_TAC \\ fs []
    )
    THEN1 (
      (* Aw8alloc *)
      GEN_EXISTS_TAC "vs" `[Litv (Word8 w); Litv (IntLit n)]` \\
      fs [semanticPrimitivesTheory.do_app_def, semanticPrimitivesTheory.store_alloc_def] \\
      fs [st2heap_def, app_aw8alloc_def, SEP_IMP_def, STAR_def, one_def] \\
      first_x_assum (qspecl_then [`LENGTH st.refs`] strip_assume_tac) \\
      (fn l => first_x_assum (qspecl_then l mp_tac))
        [`(LENGTH st.refs, W8array (REPLICATE (Num (ABS n)) w)) INSERT h_i`] \\
      impl_tac
      THEN1 (qexists_tac `h_i` \\ assume_tac store2heap_alloc_disjoint \\ SPLIT_TAC)
      THEN1 (
        strip_tac \\ once_rewrite_tac [CONJ_COMM] \\
        `evaluate_list F env st [h'; h] (st, Rval [Litv (Word8 w); Litv (IntLit n)])` by
          (cf_evaluate_list_tac [`st`, `st`]) \\
        `~ (n < 0)` by (rw_tac (arith_ss ++ intSimps.INT_ARITH_ss) []) \\
        fs [] \\ instantiate \\ fs [store2heap_append] \\
        assume_tac store2heap_alloc_disjoint \\ qexists_tac `{}` \\ SPLIT_TAC
      )
    )
    THEN1 (
      (* Aw8sub *)
      GEN_EXISTS_TAC "vs" `[Litv (IntLit i); Loc l]` \\
      `evaluate_list F env st [h'; h] (st, Rval [Litv (IntLit i); Loc l])`
        by (cf_evaluate_list_tac [`st`, `st`]) \\
      fs [st2heap_def, app_aw8sub_def, SEP_IMP_def, STAR_def, one_def] \\
      rpt (qpat_assum `!s. H s ==> _` progress) \\ fs [] \\
      qcase_tac `SPLIT h_i (h_i', {(l,W8array ws)})` \\ qcase_tac `FF h_i'` \\
      `SPLIT3 (store2heap st.refs) (h_i, h_k, {})` by SPLIT_TAC \\
      instantiate \\
      fs [semanticPrimitivesTheory.do_app_def, semanticPrimitivesTheory.store_lookup_def] \\
      `l < LENGTH st.refs` by (mp_tac store2heap_IN_LENGTH \\ SPLIT2_TAC) \\ fs [] \\
      `EL l st.refs = W8array ws` by (match_mp_tac store2heap_IN_EL \\ SPLIT_TAC) \\
      `~ (i < 0)` by (rw_tac (arith_ss ++ intSimps.INT_ARITH_ss) []) \\ fs []
    )
    THEN1 (
      (* Aw8length *)
      GEN_EXISTS_TAC "vs" `[Loc l]` \\
      `evaluate_list F env st [h] (st, Rval [Loc l])` by
        (cf_evaluate_list_tac [`st`, `st`]) \\
      fs [st2heap_def, app_aw8length_def, SEP_IMP_def, STAR_def, one_def] \\
      rpt (qpat_assum `!s. H s ==> _` progress) \\ fs [] \\
      qcase_tac `SPLIT h_i (h_i', {(l,W8array ws)})` \\ qcase_tac `FF h_i'` \\
      `SPLIT3 (store2heap st.refs) (h_i, h_k, {})` by SPLIT_TAC \\
      instantiate \\
      fs [semanticPrimitivesTheory.do_app_def, semanticPrimitivesTheory.store_lookup_def] \\
      `l < LENGTH st.refs` by (mp_tac store2heap_IN_LENGTH \\ SPLIT2_TAC) \\ fs [] \\
      `EL l st.refs = W8array ws` by (match_mp_tac store2heap_IN_EL \\ SPLIT_TAC) \\
      fs []
    )
    THEN1 (
      (* Aw8update *)
      GEN_EXISTS_TAC "vs" `[Litv (Word8 w); Litv (IntLit i); Loc l]` \\
      `evaluate_list F env st [h''; h'; h]
         (st, Rval [Litv (Word8 w); Litv (IntLit i); Loc l])`
          by (cf_evaluate_list_tac [`st`, `st`, `st`]) \\
      fs [app_aw8update_def, SEP_IMP_def, STAR_def, one_def, st2heap_def] \\
      qpat_assum `!s. H s ==> _` progress \\
      qcase_tac `SPLIT h_i (h_i', _)` \\ qcase_tac `FF h_i'` \\
      GEN_EXISTS_TAC "s2" `st` \\
      `l < LENGTH st.refs` by (mp_tac store2heap_IN_LENGTH \\ SPLIT2_TAC) \\
      `EL l st.refs = W8array ws` by (match_mp_tac store2heap_IN_EL \\ SPLIT_TAC) \\
      `~ (i < 0)` by (rw_tac (arith_ss ++ intSimps.INT_ARITH_ss) []) \\
      fs [semanticPrimitivesTheory.do_app_def,
          semanticPrimitivesTheory.store_lookup_def,
          semanticPrimitivesTheory.store_assign_def,
          semanticPrimitivesTheory.store_v_same_type_def] \\
      qexists_tac `(l, W8array (LUPDATE w (Num (ABS i)) ws)) INSERT h_i'` \\
      qexists_tac `{}` \\ strip_tac
      THEN1 (
        mp_tac store2heap_LUPDATE \\ mp_tac store2heap_IN_unique_key \\
        SPLIT2_TAC
      )
      THEN1 (
        first_assum match_mp_tac \\ qexists_tac `h_i'` \\
        strip_assume_tac store2heap_IN_unique_key \\ SPLIT_TAC
      )
    )
  )
)

val cf_sound' = Q.prove (
  `!e env H Q st.
     cf (:'ffi) e env H Q ==> H (st2heap (:'ffi) st) ==>
     ?st' h_f h_g v.
       evaluate F env st e (st', Rval v) /\
       SPLIT (st2heap (:'ffi) st') (h_f, h_g) /\
       Q v h_f`,

  rpt strip_tac \\ qspecl_then [`(:'ffi)`, `e`] assume_tac cf_sound \\
  fs [sound_def, st2heap_def] \\
  `SPLIT (store2heap st.refs) (store2heap st.refs, {})` by SPLIT_TAC \\
  res_tac \\ qcase_tac `SPLIT3 (store2heap st'.refs) (h_f, {}, h_g)` \\
  `SPLIT (store2heap st'.refs) (h_f, h_g)` by SPLIT_TAC \\ instantiate
)

val cf_sound_local = Q.prove (
  `!e env H Q h i st.
     cf (:'ffi) e env H Q ==>
     SPLIT (st2heap (:'ffi) st) (h, i) ==>
     H h ==>
     ?st' h' g v.
       evaluate F env st e (st', Rval v) /\
       SPLIT3 (st2heap (:'ffi) st') (h', g, i) /\
       Q v h'`,
  rpt strip_tac \\
  `sound (:'ffi) e (local (cf (:'ffi) e))` by
    (match_mp_tac sound_local \\ fs [cf_sound]) \\
  fs [sound_def, st2heap_def] \\
  `local (cf (:'ffi) e) env H Q` by (fs [REWRITE_RULE [is_local_def] cf_local |> GSYM]) \\
  res_tac \\ `SPLIT3 (store2heap st'.refs) (h_f, h_g, i)` by SPLIT_TAC \\
  instantiate
)

val app_basic_of_cf = Q.prove (
  `!clos body x env env' v H Q.
    do_opapp [clos; x] = SOME (env', body) ==>
    cf (:'ffi) body env' H Q ==>
    app_basic (:'ffi) clos x H Q`,
  fs [app_basic_of_sound_cf, cf_sound]
)

val app_of_cf = Q.prove (
  `!ns env body xvs env' H Q.
     ns <> [] ==>
     LENGTH xvs = LENGTH ns ==>
     cf (:'ffi) body (extend_env ns xvs env) H Q ==>
     app (:'ffi) (naryClosure env ns body) xvs H Q`,
  fs [app_of_sound_cf, cf_sound]
)

val DeclCorr_NIL = Q.prove (
  `!mn. DeclCorr mn [] FEMPTY`,
  rpt gen_tac \\ fs [DeclCorr_def, EnvCorr_def] \\
  assume_tac (Q.SPEC `mn` DeclAssumExists_NIL) \\ fs [DeclAssumExists_def] \\
  asm_exists_tac \\ fs [FEVERY_FEMPTY]
)

val DeclCorr_SNOC_Dlet_Fun = Q.prove (
  `!mn name n body ds certs P.
     DeclCorr mn ds certs ==>
     (!env. EnvCorr env certs ==> P (Closure env n body)) ==>
     DeclCorr mn (SNOC (Dlet (Pvar name) (Fun n body)) ds)
       (certs |+ (Short name, P))`,

  rpt strip_tac \\ fs [DeclCorr_def, EnvCorr_def] \\
  fs [DeclAssum_def, Decls_SNOC, PULL_EXISTS] \\
  instantiate \\ fs [Decls_Dlet, write_def, PULL_EXISTS] \\
  once_rewrite_tac [bigStepTheory.evaluate_cases] \\ fs [] \\
  fs [FEVERY_FUPDATE, FEVERY_DEF, DRESTRICT_DEF, COMPL_DEF] \\
  strip_tac
  THEN1 (fs [semanticPrimitivesTheory.lookup_var_id_def])
  THEN1 (
    rpt strip_tac \\ rpt (first_x_assum progress) \\ instantiate \\
    fs [semanticPrimitivesTheory.lookup_var_id_def] \\ every_case_tac \\ fs []
  )
)

open initialProgramTheory

val decls_0 = Define `decls_0 = []`
val certs_0 = Define `certs_0 = FEMPTY`

val declcorr_0 = Q.prove (
  `DeclCorr NONE decls_0 certs_0`,
  metis_tac [decls_0, certs_0, DeclCorr_NIL]
)

val decls_1 = Define `
  decls_1 = SNOC (mk_unop "ref" Opref) decls_0`
val certs_1 = Define `
  certs_1 = certs_0
    |+ (Short "ref", (\f. !x. app_basic (:unit) f x emp (Ref x)))`

val declcorr_1 = Q.prove (
  `DeclCorr NONE decls_1 certs_1`,
  fs [decls_1, certs_1, mk_unop_def] \\ irule DeclCorr_SNOC_Dlet_Fun \\
  fs [declcorr_0] \\ rpt strip_tac \\ irule app_basic_of_cf \\
  fs [semanticPrimitivesTheory.do_opapp_def] \\
  fs cf_defs \\ irule local_elim \\
  fs [exp2v_def, semanticPrimitivesTheory.lookup_var_id_def] \\
  fs [app_ref_def, Ref_def] \\ rpt strip_tac \\ hsimpl
)

val decls_2 = Define `
  decls_2 = SNOC (mk_unop "!" Opderef) decls_1`
val certs_2 = Define `
  certs_2 = certs_1
    |+ (Short "!", (\f.
         !l x. app_basic (:unit) f (Loc l)
           (Ref x (Loc l)) (\y. cond (y = x) * Ref x (Loc l))))`

val declcorr_2 = Q.prove (
  `DeclCorr NONE decls_2 certs_2`,
  fs [decls_2, certs_2, mk_unop_def] \\ irule DeclCorr_SNOC_Dlet_Fun \\
  fs [declcorr_1] \\ rpt strip_tac \\ irule app_basic_of_cf \\
  fs [semanticPrimitivesTheory.do_opapp_def] \\
  fs cf_defs \\ irule local_elim \\
  fs [exp2v_def, semanticPrimitivesTheory.lookup_var_id_def] \\
  fs [app_deref_def, Ref_def] \\ hsimpl
)



val _ = export_theory()
