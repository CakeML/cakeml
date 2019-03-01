(*
  Proofs about the Array module.
  load "cfLib";
  load "HashtableProgTheory";

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

val buckets_to_fmap = Define `
  buckets_to_fmap xs = alist_to_fmap (FLAT (MAP mlmap$toAscList xs))`;

val hashtable_inv_def = Define `
  hashtable_inv a b hf cmp (h:'a|->'b) vlv =
    ?buckets.
      h = buckets_to_fmap buckets /\
      LIST_REL (MAP_TYPE a b) buckets vlv `;

val REF_NUM_def = Define `
  REF_NUM loc n =
    SEP_EXISTS v. REF loc v * & (NUM n v)`;

val REF_ARRAY_def = Define `
  REF_ARRAY loc content =
    SEP_EXISTS v. REF loc v * ARRAY v content`;


val HASHTABLE_def = Define
 `HASHTABLE a b hf cmp (h:'a|->'b) v =
    SEP_EXISTS ur ar hfv cmpv vlv heuristic_size.
      &(v = (Conv (SOME (TypeStamp "Hashtable" 8)) [ur; ar; hfv; cmpv]) /\
        (a --> INT) hf hfv /\
        (a --> a --> ORDERING_TYPE) cmp cmpv /\
        hashtable_inv a b hf cmp h vlv) *
      REF_NUM ur heuristic_size *
      REF_ARRAY ar vlv`;




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
      (a --> INT) hf hfv /\
      (a --> a --> ORDERING_TYPE) cmp cmpv /\
      (h = FEMPTY) /\
      NUM size sizev ==>
      app (p:'ffi ffi_proj) Hashtable_empty_v [sizev; hfv; cmpv]
        emp
        (POSTv htv. HASHTABLE a b hf cmp FEMPTY htv)`
(xcf_with_def "Hashtable.empty" Hashtable_empty_v_def
\\ xlet_auto
   >-(xsimpl)
\\ xlet `POSTv v. &(NUM 1 v \/ (NUM size' v /\ BOOL F bv))`
  >-(xif
  \\ xlit
  \\ xsimpl
  \\ fs[]
  \\ xsimpl)
\\ xlet `POSTv ar. SEP_EXISTS mpv. &(MAP_TYPE a b (mlmap$empty cmp) mpv) * ARRAY ar (REPLICATE 1 mpv)`
   >-(xapp
  \\ simp[])
\\ xlet `POSTv loc. SEP_EXISTS addr. &(addr = loc) * REF_ARRAY loc (REPLICATE 1 mpv)`
     >-(xref
      \\fs[REF_ARRAY_def,REF_NUM_def]
      \\ xsimpl)
\\ xlet `POSTv loc. REF_NUM loc 0 * REF_ARRAY addr (REPLICATE 1 mpv)`
     >-(xref
    \\ fs[REF_ARRAY_def, REF_NUM_def]
    \\ xsimpl)
\\ xcon
\\ fs[HASHTABLE_def]
\\ xsimpl
\\ qexists_tac `(REPLICATE 1 mpv)`
\\ qexists_tac `0`
\\ xsimpl
\\ fs[hashtable_inv_def]
\\ qexists_tac `(REPLICATE 1 (mlmap$empty cmp))`
\\ simp[LIST_REL_REPLICATE_same]
\\ EVAL_TAC

\\ xlet `POSTv ar. SEP_EXISTS mpv. &(MAP_TYPE a b (mlmap$empty cmp) mpv) * ARRAY ar (REPLICATE size' mpv)`
   >-(xapp
  \\ simp[])
\\ xlet `POSTv loc. SEP_EXISTS addr. &(addr = loc) * REF_ARRAY loc (REPLICATE size' mpv)`
     >-(xref
      \\fs[REF_ARRAY_def,REF_NUM_def]
      \\ xsimpl)
\\ xlet `POSTv loc. REF_NUM loc 0 * REF_ARRAY addr (REPLICATE size' mpv)`
     >-(xref
    \\ fs[REF_ARRAY_def, REF_NUM_def]
    \\ xsimpl)
\\ xcon
\\ fs[HASHTABLE_def]
\\ xsimpl
\\ qexists_tac `(REPLICATE size' mpv)`
\\ qexists_tac `0`
\\ xsimpl
\\ fs[hashtable_inv_def]
\\ qexists_tac `(REPLICATE size' (empty cmp))`
\\ simp[LIST_REL_REPLICATE_same]
\\ fs[buckets_to_fmap]
\\ fs[map_replicate]
\\ EVAL_TAC
\\ fs[FLAT_REPLICATE_NIL]);


val _ = export_theory();
