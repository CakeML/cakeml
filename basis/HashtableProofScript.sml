(*
  Proofs about the Array module.
  load "cfLib";
  load "HashtableProgTheory";
  load "ArrayProofTheory";
*)

open preamble ml_translatorTheory ml_translatorLib cfLib
     mlbasicsProgTheory ArrayProgTheory ArrayProofTheory MapProgTheory HashtableProgTheory

val _ = new_theory"HashtableProof";

val _ = translation_extends "HashtableProg";

val hashtable_st = get_ml_prog_state();

(*  ----------------------------------- *)

(* the union of each bucket is the heap *)
(* the vlv list contains the buckets *)
(* each bucket only contains keys that hash there *)
val buckets_to_fmap_def = Define `
  buckets_to_fmap xs = alist_to_fmap (FLAT (MAP mlmap$toAscList xs))`;

(*
val buckets_to_fmap_def = Define `
  buckets_to_fmap [] = FEMPTY /\
  buckets_to_fmap (x::xs) = FUNION (mlmap$to_fmap x) (buckets_to_fmap xs)`;
  *)


val bucket_ok_def = Define `
  bucket_ok b idx hf length = !k v.
    mlmap$lookup b k = SOME v ==> (hf k) MOD length = idx`;

val buckets_ok_def = Define `
    buckets_ok bs hf = !i.
      i < LENGTH bs ==>
        bucket_ok (EL i bs) i hf (LENGTH bs)`;

val hashtable_inv_def = Define `
  hashtable_inv a b hf cmp (h:'a|->'b) vlv =
    ?buckets.
      h = buckets_to_fmap buckets /\
      buckets_ok buckets hf /\
      LIST_REL (MAP_TYPE a b) buckets vlv `;


Theorem buckets_ok_empty
  `buckets_ok (REPLICATE n (mlmap$empty cmp)) hf`
( rw[buckets_ok_def]
\\ fs[EL_REPLICATE]
\\ rw[bucket_ok_def]
\\ fs[mlmapTheory.lookup_def, mlmapTheory.empty_def,
      balanced_mapTheory.empty_def, balanced_mapTheory.lookup_def]);

val REF_NUM_def = Define `
  REF_NUM loc n =
    SEP_EXISTS v. REF loc v * & (NUM n v)`;

val REF_ARRAY_def = Define `
  REF_ARRAY loc arr content = REF loc arr * ARRAY arr content`;


val HASHTABLE_def = Define
 `HASHTABLE a b hf cmp (h:'a|->'b) v =
    SEP_EXISTS ur ar arr hfv cmpv vlv heuristic_size.
      &(v = (Conv (SOME (TypeStamp "Hashtable" 8)) [ur; ar; hfv; cmpv]) /\
        (a --> NUM) hf hfv /\
        (a --> a --> ORDERING_TYPE) cmp cmpv /\
        hashtable_inv a b hf cmp h vlv) *
      REF_NUM ur heuristic_size *
      REF_ARRAY ar arr vlv`;


Theorem hashtable_initBuckets_spec
 `!a b n nv cmp cmpv.
    (a --> a --> ORDERING_TYPE) cmp cmpv /\
    NUM n nv ==>
      app (p:'ffi ffi_proj) Hashtable_initBuckets_v [nv; cmpv]
      emp
      (POSTv ar. SEP_EXISTS mpv. &(MAP_TYPE a b (mlmap$empty cmp) mpv) * ARRAY ar (REPLICATE n mpv))`
(xcf_with_def "Hashtable.initBuckets" Hashtable_initBuckets_v_def
\\ xlet `POSTv r1. & (MAP_TYPE a b (mlmap$empty cmp) r1)`
    >-(xapp
    \\ simp[])
\\ xapp_spec array_alloc_spec
\\ xsimpl
\\ asm_exists_tac
\\ simp[]
\\ asm_exists_tac
\\ simp[]);

Theorem hashtable_empty_spec
  `!a b hf hfv cmp cmpv size sizev htv.
      (a --> NUM) hf hfv /\
      (a --> a --> ORDERING_TYPE) cmp cmpv /\
      (h = FEMPTY) /\
      NUM size sizev ==>
      app (p:'ffi ffi_proj) Hashtable_empty_v [sizev; hfv; cmpv]
        emp
        (POSTv htv. HASHTABLE a b hf cmp FEMPTY htv)`
(xcf_with_def "Hashtable.empty" Hashtable_empty_v_def
\\xlet_auto
   >-(xsimpl)
\\ xlet `POSTv v. &(NUM 1 v \/ (NUM size' v /\ BOOL F bv))`
  THEN1 (xif
  \\ xlit
  \\ xsimpl
  \\ fs[BOOL_def])
  (*size > 1*)
 THEN1 (xlet `POSTv ar. SEP_EXISTS mpv. &(MAP_TYPE a b (mlmap$empty cmp) mpv) * ARRAY ar (REPLICATE 1 mpv)`
   >-(xapp
  \\ simp[])
THEN1 (xlet `POSTv loc. SEP_EXISTS addr arr. &(addr = loc) * REF_ARRAY loc arr (REPLICATE 1 mpv)`
     >-(xref
      \\ fs[REF_ARRAY_def,REF_NUM_def]
      \\ xsimpl)
THEN1 (xlet `POSTv loc. SEP_EXISTS arr. REF_NUM loc 0 * REF_ARRAY addr arr (REPLICATE 1 mpv)`
     >-(xref
      \\ fs[REF_ARRAY_def, REF_NUM_def]
      \\ xsimpl)
\\ xcon
\\ fs[HASHTABLE_def]
\\ xsimpl
\\ qexists_tac `arr`
\\ qexists_tac `(REPLICATE 1 mpv)`
\\ qexists_tac `0`
\\ xsimpl
\\ fs[hashtable_inv_def]
\\ qexists_tac `(REPLICATE 1 (mlmap$empty cmp))`
\\ simp[LIST_REL_REPLICATE_same]
\\ conj_tac
>- (EVAL_TAC)
\\ fs[buckets_ok_empty])))
(*size > 1*)
THEN1 (xlet `POSTv ar. SEP_EXISTS mpv. &(MAP_TYPE a b (mlmap$empty cmp) mpv) * ARRAY ar (REPLICATE size' mpv)`
   >-(xapp
  \\ simp[])
THEN1 (xlet `POSTv loc. SEP_EXISTS addr arr. &(addr = loc) * REF_ARRAY loc arr (REPLICATE size' mpv)`
     >-(xref
      \\fs[REF_ARRAY_def,REF_NUM_def]
      \\ xsimpl)
THEN1 (xlet `POSTv loc. SEP_EXISTS arr. REF_NUM loc 0 * REF_ARRAY addr arr (REPLICATE size' mpv)`
     >-(xref
    \\ fs[REF_ARRAY_def, REF_NUM_def]
    \\ xsimpl)
\\ xcon
\\ fs[HASHTABLE_def]
\\ xsimpl
\\ qexists_tac `arr`
\\ qexists_tac `(REPLICATE size' mpv)`
\\ qexists_tac `0`
\\ xsimpl
\\ fs[hashtable_inv_def]
\\ qexists_tac `(REPLICATE size' (empty cmp))`
\\ conj_tac
\\ fs[buckets_to_fmap_def]
\\ fs[map_replicate]
>- (EVAL_TAC \\
  fs[FLAT_REPLICATE_NIL])
\\ conj_tac
\\ fs[buckets_ok_empty]
\\ simp[LIST_REL_REPLICATE_same]))));

Theorem hashtable_staticInsert_spec
  `!a b hf hfv cmp cmpv k kv v vv htv.
      (a --> NUM) hf hfv /\
      (a --> a --> ORDERING_TYPE) cmp cmpv /\
      a k kv /\
      b v vv ==>
      app (p:'ffi ffi_proj) Hashtable_staticInsert_v [htv; kv; vv]
        (HASHTABLE a b hf cmp h htv)
        (POSTv uv. &(UNIT_TYPE () uv) * HASHTABLE a b hf cmp (h|+(k,v)) htv)`
(xcf_with_def "Hashtable.staticInsert" Hashtable_staticInsert_v_def
\\ fs[HASHTABLE_def]
\\ xpull
\\ xmatch
\\ xlet `POSTv v. HASHTABLE a b hf cmp h htv`
  >-(xapp
    \\ fs[HASHTABLE_def]
    \\qexists_tac `ARRAY arr vlv * REF_NUM ur heuristic_size`
    \\qexists_tac `arr`
    \\fs[REF_ARRAY_def]
    \\xsimpl
    \\qexists_tac `heuristic_size`
    \\xsimpl)



val _ = export_theory();
