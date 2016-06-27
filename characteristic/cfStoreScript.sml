open HolKernel Parse boolLib bossLib preamble
open set_sepTheory helperLib ml_translatorTheory
open semanticPrimitivesTheory
open ConseqConv cfHeapsTheory cfHeapsLib

val _ = new_theory "cfStore"

(*------------------------------------------------------------------*)
(** Conversion from semantic stores to heaps *)

(* Definitions *)

val store2heap_aux_def = Define `
  store2heap_aux n [] = ({}: heap) /\
  store2heap_aux n (v :: t) = (Mem n v) INSERT (store2heap_aux (n+1: num) t)`

(* store2heap: v store -> heap *)
val store2heap_def = Define `store2heap l = store2heap_aux (0: num) l`

val ffi2heap_def = Define `
  ffi2heap ((proj,upd):'ffi ffi_proj) st =
    if IS_SOME st.final_event then {} else
      { FFI_part n s u | FLOOKUP (proj st.ffi_state) n = SOME s /\
                         !x bytes w new_bytes.
                           u bytes (proj x ' n) = SOME (new_bytes,w) ==>
                           ?y.
                             st.oracle n x bytes = Oracle_return y new_bytes /\
                             proj x |+ (n,w) = proj y }`

(* st2heap: 'ffi state -> heap *)
val st2heap_def = Define `
  st2heap (f:'ffi ffi_proj) (st: 'ffi state) =
    store2heap st.refs UNION ffi2heap f st.ffi`

(* Lemmas *)

val store2heap_aux_append = store_thm ("store2heap_aux_append",
  ``!s n x.
      store2heap_aux n (s ++ [x]) =
      (Mem (LENGTH s + n) x) INSERT store2heap_aux n s``,
  Induct THENL [all_tac, Cases] \\ fs [store2heap_aux_def, INSERT_COMM]
  \\ fs [DECIDE ``(LENGTH s + 1) = SUC (LENGTH s)``]
)

val store2heap_append = store_thm ("store2heap_append",
  ``!s x. store2heap (s ++ [x]) = Mem (LENGTH s) x INSERT store2heap s``,
  fs [store2heap_def, store2heap_aux_append]
)

val store2heap_aux_suc = store_thm ("store2heap_aux_suc",
  ``!s n u v.
      (Mem u v IN store2heap_aux n s) =
      (Mem (SUC u) v IN store2heap_aux (SUC n) s)``,
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
  ``!s n u v. Mem u v IN store2heap_aux n s ==> (u >= n)``,
  Induct THENL [all_tac, Cases] \\ fs [store2heap_aux_def] \\
  rpt strip_tac \\ fs [] \\ first_assum (qspecl_then [`n+1`, `u`, `v`] drule) \\
  rw_tac arith_ss []
)

val store2heap_alloc_disjoint = store_thm ("store2heap_alloc_disjoint",
  ``!s x. ~ (Mem (LENGTH s) x IN (store2heap s))``,
  Induct
  THEN1 (strip_tac \\ fs [store2heap_def, store2heap_aux_def])
  THEN1 (
    Cases \\ fs [store2heap_def, store2heap_aux_def] \\
    rewrite_tac [ONE] \\
    fs [GSYM store2heap_aux_suc]
  )
)

val store2heap_IN_LENGTH = store_thm ("store2heap_IN_LENGTH",
  ``!s r x. Mem r x IN (store2heap s) ==> r < LENGTH s``,
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
  ``!s r x. Mem r x IN (store2heap s) ==> EL r s = x``,
  tac_store2heap_IN
)

val store2heap_IN_unique_key = store_thm ("store2heap_IN_unique_key",
  ``!s r x.
      Mem r x IN (store2heap s) ==>
      !x'. Mem r x' IN (store2heap s) ==> x = x'``,
  tac_store2heap_IN
)

val Mem_NOT_IN_ffi2heap = store_thm("Mem_NOT_IN_ffi2heap",
  ``~(Mem rv x IN ffi2heap (p:'ffi ffi_proj) f)``,
  Cases_on `p` \\ fs [ffi2heap_def] \\ rw []);

val FFI_part_NOT_IN_store2heap_aux = store_thm("FFI_part_NOT_IN_store2heap_aux",
  ``∀n s. FFI_part x1 x2 x3 ∉ store2heap_aux n s``,
  Induct_on `s` \\ fs [store2heap_aux_def]);

val FFI_part_NOT_IN_store2heap = store_thm("FFI_part_NOT_IN_store2heap",
  ``!s. ~(FFI_part x1 x2 x3 ∈ store2heap s)``,
  fs [store2heap_def,FFI_part_NOT_IN_store2heap_aux]);

val store2heap_LUPDATE = store_thm ("store2heap_LUPDATE",
  ``!s r x y.
      Mem r y IN (store2heap s) ==>
      store2heap (LUPDATE x r s) = Mem r x INSERT ((store2heap s) DELETE Mem r y)``,
  Induct \\
  fs [store2heap_def, store2heap_aux_def] \\
  Cases_on `r` \\ qx_genl_tac [`v`, `x`, `y`] \\
  qspecl_then [`s`, `1`, `0`, `y`] assume_tac store2heap_aux_IN_bound \\
  fs [LUPDATE_def, INSERT_DEF, DELETE_DEF, EXTENSION, store2heap_aux_def]
  THEN1 (metis_tac []) \\
  strip_tac \\ qx_gen_tac `u` \\
  Cases_on `u = Mem 0 v` \\ fs [] \\ Cases_on `u`
  \\ fs [FFI_part_NOT_IN_store2heap_aux]
  THEN1 (
    rename1 `m <> 0n` \\ Cases_on `m` \\ fs [] \\
    qpat_assum `_ IN _` mp_tac \\
    rewrite_tac [ONE, GSYM store2heap_aux_suc] \\ rpt strip_tac \\
    first_assum drule \\
    disch_then (qspecl_then [`x`, `Mem n' s'`] assume_tac) \\ fs [])
  THEN1 (
    Cases_on `n'` \\ fs []
    THEN1 (eq_tac \\ rw [] \\ imp_res_tac store2heap_aux_IN_bound \\ fs []) \\
    qpat_assum `_ IN _` mp_tac \\
    rewrite_tac [ONE, GSYM store2heap_aux_suc] \\ rpt strip_tac \\
    first_assum drule \\
    disch_then (qspecl_then [`x`, `Mem n'' s'`] assume_tac) \\ fs []))

val _ = export_theory ()
