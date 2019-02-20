(*
  Proofs about the Array module.
*)
open preamble ml_translatorTheory ml_translatorLib cfLib
     mlbasicsProgTheory HashtableProgTheory

val _ = new_theory"HashtableProof";

val _ = translation_extends "HashtableProg";

val hashtable_st = get_ml_prog_state();
(*  ----------------------------------- *)

(* Theorem hashtable_empty
  `!v.`

Theorem array_alloc_empty_spec
  `!v.
     UNIT_TYPE () v ⇒
     app (p:'ffi ffi_proj) ^(fetch_v "Hashtable.hashtableEmpty" array_st) [v]
       emp (POSTv av. ARRAY av [])`
  (prove_array_spec "Array.arrayEmpty"); *)



(*  ----------------------------------- *)
val _ = export_theory();
