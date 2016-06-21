open HolKernel Parse boolLib bossLib preamble
open set_sepTheory helperLib ml_translatorTheory
open semanticPrimitivesTheory
open ConseqConv cfHeapsTheory cfHeapsBaseLib

val _ = new_theory "cfStore"

(*------------------------------------------------------------------*)
(** Conversion from semantic stores to heaps *)

(* Definitions *)

val store2heap_aux_def = Define `
  store2heap_aux n [] = ({}: heap) /\
  store2heap_aux n (v :: t) = (n, v) INSERT (store2heap_aux (n+1: num) t)`

(* store2heap: v store -> heap *)
val store2heap_def = Define `store2heap l = store2heap_aux (0: num) l`

(* st2heap: 'ffi state -> heap *)
val st2heap_def = Define `
  st2heap (:'ffi) (st: 'ffi state) = store2heap st.refs`


(* Lemmas *)

val store2heap_aux_append = store_thm ("store2heap_aux_append",
  ``!s n x.
      store2heap_aux n (s ++ [x]) =
      (LENGTH s + n, x) INSERT store2heap_aux n s``,
  Induct THENL [all_tac, Cases] \\ fs [store2heap_aux_def, INSERT_COMM]
  \\ fs [DECIDE ``(LENGTH s + 1) = SUC (LENGTH s)``]
)

val store2heap_append = store_thm ("store2heap_append",
  ``!s x. store2heap (s ++ [x]) = (LENGTH s, x) INSERT store2heap s``,
  fs [store2heap_def, store2heap_aux_append]
)

val store2heap_aux_suc = store_thm ("store2heap_aux_suc",
  ``!s n u v.
      ((u, v) IN store2heap_aux n s) =
      ((SUC u, v) IN store2heap_aux (SUC n) s)``,
  Induct
  THEN1 (strip_tac \\ fs [store2heap_def, store2heap_aux_def])
  THEN1 (
    Cases \\
    once_rewrite_tac [store2heap_aux_def] \\ rpt strip_tac \\
    pop_assum (qspecl_then [`n+1`, `u`, `v`] assume_tac) \\
    fs [DECIDE ``SUC n + 1 = SUC (n + 1)``]
  )
)

val store2heap_aux_IN_bound = store_thm ("store2heap_aux_IN_bound",
  ``!s n u v. (u, v) IN store2heap_aux n s ==> (u >= n)``,
  Induct THENL [all_tac, Cases] \\ fs [store2heap_aux_def] \\
  rpt strip_tac \\ fs [] \\ first_assum (qspecl_then [`n+1`, `u`, `v`] drule) \\
  rw_tac arith_ss []
)


val store2heap_alloc_disjoint = store_thm ("store2heap_alloc_disjoint",
  ``!s x. ~ ((LENGTH s, x) IN (store2heap s))``,
  Induct
  THEN1 (strip_tac \\ fs [store2heap_def, store2heap_aux_def])
  THEN1 (
    Cases \\ fs [store2heap_def, store2heap_aux_def] \\
    rewrite_tac [ONE] \\
    fs [GSYM store2heap_aux_suc]
  )
)

val store2heap_IN_LENGTH = store_thm ("store2heap_IN_LENGTH",
  ``!s r x. (r, x) IN (store2heap s) ==> r < LENGTH s``,
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

val store2heap_IN_EL = store_thm ("store2heap_IN_EL",
  ``!s r x. (r, x) IN (store2heap s) ==> EL r s = x``,
  tac_store2heap_IN
)

val store2heap_IN_unique_key = store_thm ("store2heap_IN_unique_key",
  ``!s r x.
      (r, x) IN (store2heap s) ==>
      !x'. (r, x') IN (store2heap s) ==> x = x'``,
  tac_store2heap_IN
)

(* todo: fix fragile names & refactor *)
val store2heap_LUPDATE = store_thm ("store2heap_LUPDATE",
  ``!s r x y.
     (r, y) IN (store2heap s) ==>
     store2heap (LUPDATE x r s) = (r, x) INSERT ((store2heap s) DELETE (r, y))``,
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

val _ = export_theory ()
