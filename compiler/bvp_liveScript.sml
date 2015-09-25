open preamble bvpTheory;

val _ = new_theory "bvp_live";

(* This script defines an optimisation that minimises the live var
   annotations that are attached to MakeSpace, Assign and Call in BVP
   programs. *)

val compile_def = Define `
  (compile Skip live = (Skip,live)) /\
  (compile (Return n) live = (Return n, insert n () LN)) /\
  (compile (Raise n) live = (Raise n, insert n () LN)) /\
  (compile (Move n1 n2) live =
    (Move n1 n2, insert n2 () (delete n1 live))) /\
  (compile (Seq c1 c2) live =
     let (d2,l2) = compile c2 live in
     let (d1,l1) = compile c1 l2 in
       (Seq d1 d2, l1)) /\
  (compile Tick live = (Tick,live)) /\
  (compile (MakeSpace k names) live =
     let l1 = inter names live in (MakeSpace k l1,l1)) /\
  (compile (Assign v op vs NONE) live =
     let l1 = list_insert vs (delete v live) in
       (Assign v op vs NONE,l1)) /\
  (compile (Assign v op vs (SOME names)) live =
     let l1 = inter names (list_insert vs (delete v live)) in
       (Assign v op vs (SOME l1),l1)) /\
  (compile (If c1 n c2 c3) live =
     let (d3,l3) = compile c3 live in
     let (d2,l2) = compile c2 live in
     let (d1,l1) = compile c1 (insert n () (union l2 l3)) in
       (If d1 n d2 d3, l1)) /\
  (compile (Call NONE dest vs handler) live =
     (Call NONE dest vs handler,list_to_num_set vs)) /\
  (compile (Call (SOME (n,names)) dest vs NONE) live =
     let l1 = inter names (delete n live) in
     let l2 = list_insert vs l1 in
       (Call (SOME (n,l1)) dest vs NONE,l2)) /\
  (compile (Call (SOME (n,names)) dest vs (SOME (v,c))) live =
     let (d,l3) = compile c live in
     let l0 = union (delete n live) (delete v l3) in
     let l1 = inter names l0 in
     let l2 = list_insert vs l1 in
       (Call (SOME (n,l1)) dest vs (SOME (v,d)),l2))`;

val _ = export_theory();
