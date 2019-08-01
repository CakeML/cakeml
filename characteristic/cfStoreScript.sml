(*
  Conversion from semantic stores to heaps.
*)
open preamble
open set_sepTheory helperLib ConseqConv
open semanticPrimitivesTheory ml_translatorTheory
open cfHeapsTheory cfHeapsBaseLib

val _ = new_theory "cfStore"


(* Definitions *)

val store2heap_aux_def = Define `
  store2heap_aux n [] = ({}: heap) /\
  store2heap_aux n (v :: t) = (Mem n v) INSERT (store2heap_aux (n+1: num) t)`

(* store2heap: v store -> heap *)
val store2heap_def = Define `store2heap l = store2heap_aux (0: num) l`

val ffi_has_index_in_def = Define `
  ffi_has_index_in ns (IO_event i args newargs outcome) = (MEM i ns)`;

val parts_ok_def = Define `
  parts_ok st ((proj,parts):'ffi ffi_proj) <=>
    ALL_DISTINCT (MAP (λx. x.mlname) (FLAT (MAP FST parts))) /\
    EVERY (ffi_has_index_in (MAP (λx. x.mlname) (FLAT (MAP FST parts)))) st.io_events /\
    (!sigs u.
       MEM (sigs,u) parts ==> !sig. MEM sig sigs ==>
       FIND (λx. x.mlname = sig.mlname) st.signatures = SOME sig
       ) /\
    (!sigs u.
       MEM (sigs,u) parts ==>
       ?s. !sig. MEM sig sigs ==> FLOOKUP (proj st.ffi_state) sig.mlname = SOME(s,sig)) /\
    (!x args als sig sigs u.
       MEM (sigs,u) parts /\ MEM sig sigs /\ args_ok sig.args args /\
       u sig.mlname args als (FST(proj x ' sig.mlname)) = SOME FFIdiverge ==>
        st.oracle sig.mlname x args als = Oracle_final(FFI_diverged)) /\
    !x args als w new_bytes retv sig sigs u.
      MEM (sigs,u) parts /\ MEM sig sigs /\ args_ok sig.args args /\
      u sig.mlname args als (FST(proj x ' sig.mlname)) = SOME(FFIreturn new_bytes retv w) ==>
      mut_len sig.args args = MAP LENGTH new_bytes /\ ret_ok sig.retty retv /\ als_ok new_bytes als /\
      ?y.
        st.oracle sig.mlname x args als = Oracle_return y new_bytes retv /\
        proj x |++ (MAP (\sig. (sig.mlname,(w,sig))) sigs) = proj y`

val ffi2heap_def = Define `
  ffi2heap ((proj,parts):'ffi ffi_proj) st =
    if parts_ok st (proj,parts) then
      FFI_split INSERT
      { FFI_part s u sigs ts |
        MEM (sigs,u) parts /\ sigs <> [] /\
        ts = FILTER (ffi_has_index_in (MAP (λx. x.mlname) sigs)) st.io_events /\
        !sig. MEM sig sigs ==> FLOOKUP (proj st.ffi_state) sig.mlname = SOME(s,sig) }
    else
      { FFI_full st.signatures st.io_events }`;

(* st2heap: 'ffi state -> heap *)
val st2heap_def = Define `
  st2heap (f:'ffi ffi_proj) (st: 'ffi semanticPrimitives$state) =
    store2heap st.refs UNION ffi2heap f st.ffi`

(* Lemmas *)

Theorem store2heap_aux_append:
   !s n x.
      store2heap_aux n (s ++ [x]) =
      (Mem (LENGTH s + n) x) INSERT store2heap_aux n s
Proof
  Induct THENL [all_tac, Cases] \\ fs [store2heap_aux_def, INSERT_COMM]
  \\ fs [DECIDE ``(LENGTH s + 1) = SUC (LENGTH s)``]
QED

Theorem store2heap_append:
   !s x. store2heap (s ++ [x]) = Mem (LENGTH s) x INSERT store2heap s
Proof
  fs [store2heap_def, store2heap_aux_append]
QED

Theorem store2heap_aux_suc:
   !s n u v.
      (Mem u v IN store2heap_aux n s) =
      (Mem (SUC u) v IN store2heap_aux (SUC n) s)
Proof
  Induct
  THEN1 (strip_tac \\ fs [store2heap_def, store2heap_aux_def])
  THEN1 (
    Cases \\
    once_rewrite_tac [store2heap_aux_def] \\ rpt strip_tac \\
    pop_assum (qspecl_then [`n+1`, `u`, `v`] assume_tac) \\
    fs [DECIDE ``SUC n + 1 = SUC (n + 1)``]
  )
QED

Theorem store2heap_aux_IN_bound:
   !s n u v. Mem u v IN store2heap_aux n s ==> (u >= n)
Proof
  Induct THENL [all_tac, Cases] \\ fs [store2heap_aux_def] \\
  rpt strip_tac \\ fs [] \\ first_assum (qspecl_then [`n+1`, `u`, `v`] drule) \\
  rw_tac arith_ss []
QED

Theorem store2heap_alloc_disjoint:
   !s x. ~ (Mem (LENGTH s) x IN (store2heap s))
Proof
  Induct
  THEN1 (strip_tac \\ fs [store2heap_def, store2heap_aux_def])
  THEN1 (
    Cases \\ fs [store2heap_def, store2heap_aux_def] \\
    rewrite_tac [ONE] \\
    fs [GSYM store2heap_aux_suc]
  )
QED

Theorem store2heap_IN_LENGTH:
   !s r x. Mem r x IN (store2heap s) ==> r < LENGTH s
Proof
  Induct THENL [all_tac, Cases] \\
  fs [store2heap_def, store2heap_aux_def] \\
  Cases_on `r` \\ fs [] \\ rewrite_tac [ONE] \\
  rpt strip_tac \\ fs [GSYM store2heap_aux_suc] \\ metis_tac []
QED

val tac_store2heap_IN =
  Induct THENL [all_tac, Cases] \\ fs [store2heap_def, store2heap_aux_def] \\
  Cases_on `r` \\ fs [] \\
  rewrite_tac [ONE] \\ rpt strip_tac \\
  fs [GSYM store2heap_aux_suc] \\ TRY (metis_tac []) \\
  qspecl_then [`s`, `1`, `0`, `x'`] drule store2heap_aux_IN_bound \\
  rw_tac arith_ss []

Theorem store2heap_IN_EL:
   !s r x. Mem r x IN (store2heap s) ==> EL r s = x
Proof
  tac_store2heap_IN
QED

Theorem store2heap_IN_unique_key:
   !s r x.
      Mem r x IN (store2heap s) ==>
      !x'. Mem r x' IN (store2heap s) ==> x = x'
Proof
  tac_store2heap_IN
QED

Theorem Mem_NOT_IN_ffi2heap:
   ~(Mem rv x IN ffi2heap (p:'ffi ffi_proj) f)
Proof
  PairCases_on `p` \\ fs [ffi2heap_def] \\ rw []
QED

Theorem FFI_split_NOT_IN_store2heap_aux:
   ∀n s. FFI_split ∉ store2heap_aux n s
Proof
  Induct_on `s` \\ fs [store2heap_aux_def]
QED

Theorem FFI_part_NOT_IN_store2heap_aux:
   ∀n s. FFI_part x1 x2 x3 x4 ∉ store2heap_aux n s
Proof
  Induct_on `s` \\ fs [store2heap_aux_def]
QED

Theorem FFI_full_NOT_IN_store2heap_aux:
   ∀n s. FFI_full x1 x2 ∉ store2heap_aux n s
Proof
  Induct_on `s` \\ fs [store2heap_aux_def]
QED

Theorem FFI_part_NOT_IN_store2heap:
   !s. ~(FFI_split ∈ store2heap s) /\
        ~(FFI_part x1 x2 x3 x4 ∈ store2heap s) /\
        ~(FFI_full y1 y2 ∈ store2heap s)
Proof
  fs [store2heap_def,FFI_part_NOT_IN_store2heap_aux,
      FFI_full_NOT_IN_store2heap_aux,FFI_split_NOT_IN_store2heap_aux]
QED

Theorem store2heap_LUPDATE:
   !s r x y.
      Mem r y IN (store2heap s) ==>
      store2heap (LUPDATE x r s) = Mem r x INSERT ((store2heap s) DELETE Mem r y)
Proof
  Induct \\
  fs [store2heap_def, store2heap_aux_def] \\
  Cases_on `r` \\ qx_genl_tac [`v`, `x`, `y`] \\
  qspecl_then [`s`, `1`, `0`, `y`] assume_tac store2heap_aux_IN_bound \\
  fs [LUPDATE_def, INSERT_DEF, DELETE_DEF, EXTENSION, store2heap_aux_def]
  THEN1 (metis_tac []) \\
  strip_tac \\ qx_gen_tac `u` \\
  Cases_on `u = Mem 0 v` \\ fs [] \\ Cases_on `u`
  \\ fs [FFI_split_NOT_IN_store2heap_aux,
         FFI_part_NOT_IN_store2heap_aux,
         FFI_full_NOT_IN_store2heap_aux]
  THEN1 (
    rename1 `m <> 0n` \\ Cases_on `m` \\ fs [] \\
    qpat_x_assum `_ IN _` mp_tac \\
    rewrite_tac [ONE, GSYM store2heap_aux_suc] \\ rpt strip_tac \\
    first_assum drule \\
    disch_then (qspecl_then [`x`, `Mem n' s'`] assume_tac) \\ fs [])
  THEN1 (
    Cases_on `n'` \\ fs []
    THEN1 (eq_tac \\ rw [] \\ imp_res_tac store2heap_aux_IN_bound \\ fs []) \\
    qpat_x_assum `_ IN _` mp_tac \\
    rewrite_tac [ONE, GSYM store2heap_aux_suc] \\ rpt strip_tac \\
    first_assum drule \\
    disch_then (qspecl_then [`x`, `Mem n'' s'`] assume_tac) \\ fs [])
QED

Theorem st2heap_clock:
   !st ck. st2heap (p:'ffi ffi_proj) (st with clock := ck) = st2heap p st
Proof
  fs [st2heap_def]
QED

val _ = export_theory ()
