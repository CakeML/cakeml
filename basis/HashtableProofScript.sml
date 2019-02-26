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
\\ xapp
\\ simp[]
\\ xapp_spec array_alloc_spec
\\ xsimpl
\\ qexists_tac `n`
\\ simp[]
\\ qexists_tac `r1`
\\ simp[]);

Theorem empty_test
  `!a b hf hfv cmp cmpv size sizev htv.
      (a --> INT) hf hfv /\
      (a --> a --> ORDERING_TYPE) cmp cmpv /\
      NUM size sizev ==>
        app (p:'ffi ffi_proj) Hashtable_empty_v [sizev; hfv; cmpv]
          emp
          (POSTv htv. HASHTABLE a b hf cmp h htv)`
          (* (POSTv v. HASHTABLE a b hf cmp h htv)` *)

          xlet `POSTv htv. HASHTABLE a b hf cmp h htv`

          INT 1 v \/
           xlet `POSTv v. &(?i. (NUM i sizev))`

           (xcf_with_def "Hashtable.empty" Hashtable_empty_v_def
           \\ xlet_auto
           \\ xsimpl
           \\ xlet `POSTv v. &(?i. (NUM i sizev))`
           \\ simp[]
           \\ xif
           \\ simp[]
           \\ xlit
           \\ xsimpl
           \\ qexists_tac `size'`
           \\ simp[]
           \\ xvar
           \\ xsimpl
           \\ qexists_tac `size'`
           \\ simp[]
           \\ xlet_auto
           \\ xlet `POSTv ar. !elmapo. & (MAP_TYPE a b elmapo (mlmap$empty cmp)) * ARRAY ar (REPLICATE n elmapo)`
           \\ xcf_with_def "Hashtable.initBuckets" Hashtable_empty_v_def)




(* Theorem size_test
  `!a b hf cmp hv.
    app (p:'ffi ffi_proj) Hashtable_size_v [hv]
      (HASHTABLE a b hf cmp h hv)
      (POSTv v.  & (NUM (fmap_size (\x. 1) (\y. 0) h) v) * HASHTABLE a b hf cmp h hv)`
  (xcf_with_def "Hashtable.size" Hashtable_size_v_def
  \\ simp[REF_NUM_def,HASHTABLE_def]
  \\ xpull
  \\ xmatch
  \\ xapp
  \\ xsimpl
  \\ asm_exists_tac
  \\ simp[]
  \\ asm_exists_tac
  \\ xsimpl); *)

(*  ----------------------------------- *)
val _ = export_theory();
