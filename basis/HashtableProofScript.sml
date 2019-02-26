(*
  Proofs about the Array module.
  load "cfLib";
  load "HashtableProgTheory";

*)

open preamble ml_translatorTheory ml_translatorLib cfLib
     mlbasicsProgTheory ArrayProgTheory MapProgTheory HashtableProgTheory

val _ = new_theory"HashtableProof";

val _ = translation_extends "HashtableProg";

val hashtable_st = get_ml_prog_state();

(*  ----------------------------------- *)

(* the union of each bucket is the heap *)
(* the vlv list contains the buckets *)
(* each bucket only contains keys that hash there *)

val list_union_def = Define `
  list_union [x] = x /\
  list_union (x::xs) = mlmap$union x (list_union xs)`

val hashtable_inv_def = Define `
  hashtable_inv a b hf cmp (h:'a|->'b) vlv =
    ?buckets.
      h = to_fmap (list_union buckets) /\
      LIST_REL (MAP_TYPE a b) buckets vlv /\
      ARB`;

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


val _ = export_theory();
