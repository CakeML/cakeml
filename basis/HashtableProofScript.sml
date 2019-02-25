(*
  Proofs about the Array module.
*)

open preamble ml_translatorTheory ml_translatorLib cfLib
     mlbasicsProgTheory HashtableProgTheory

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

Theorem size_test
  `!a b hf cmp hv.
    app (p:'ffi ffi_proj) Hashtable_size_v [hv]
      (HASHTABLE a b hf cmp h hv)
      (POSTv v. HASHTABLE a b hf cmp h hv)`
  (xcf_with_def "Hashtable.size" Hashtable_size_v_def
  \\ simp[REF_NUM_def,HASHTABLE_def]
  \\ xpull
  \\ xmatch
  \\ xapp
  \\ xsimpl
  \\ asm_exists_tac
  \\ simp[]
  \\ asm_exists_tac
  \\ xsimpl);

(*  ----------------------------------- *)
val _ = export_theory();
