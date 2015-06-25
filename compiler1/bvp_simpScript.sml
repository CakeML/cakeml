open preamble bvpTheory;

val _ = new_theory "bvp_simp";

(* Simple clean up of BVP:

   The simp optimisation removes Skips and deletes some dead code
   created by Raise and Return, e.g.

     Seq (Seq Skip (Raise n)) anything_here

   translates into

     Raise n

   It also right-associates Seq, e.g.

     Seq (Seq x1 x2) x3 --> Seq x1 (Seq x2 x3)
*)

val pSeq_def = Define `
  pSeq c1 c2 =
    if c2 = Skip then c1 else Seq c1 c2`;

val simp_def = Define `
  (simp Skip c = c) /\
  (simp (Return n) c = Return n) /\
  (simp (Raise n) c = Raise n) /\
  (simp (Seq c1 c2) c = simp c1 (simp c2 c)) /\
  (simp (If c1 n c2 c3) c =
     pSeq (If (simp c1 Skip) n (simp c2 Skip) (simp c3 Skip)) c) /\
  (simp (Call ret dest args (SOME (v,handler))) c =
     pSeq (Call ret dest args (SOME (v,simp handler Skip))) c) /\
  (simp c1 c2 = pSeq c1 c2)`;

val _ = export_theory();
