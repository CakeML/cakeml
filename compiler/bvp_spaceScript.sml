open preamble bvpTheory;

val _ = new_theory "bvp_space";

(* BVP optimisation that lumps together MakeSpace operations. *)

val pMakeSpace_def = Define `
  (pMakeSpace (INL c) = c) /\
  (pMakeSpace (INR (k,names,c)) = Seq (MakeSpace k names) c)`;

val space_def = Define `
  (space (MakeSpace k names) = INR (k,names,Skip)) /\
  (space (Seq c1 c2) =
     let d1 = pMakeSpace (space c1) in
     let x2 = space c2 in
       case x2 of
       | INL c4 =>
          (case c1 of
           | MakeSpace k names => INR (k,names,c4)
           | Skip => INL c4
           | _ => INL (Seq d1 c4))
       | INR (k,names,c4) =>
          (case c1 of
           | Skip => INR (k,names,c4)
           | MakeSpace k2 names2 => INR (k+k2,inter names names2,c4)
           | Move dest src =>
               INR (k,insert src () (delete dest names),
                    Seq (Move dest src) c4)
           | Assign dest op args NONE =>
               INR (k,list_insert args (delete dest names),
                    Seq (Assign dest op args NONE) c4)
           | _ => INL (Seq d1 (pMakeSpace x2)))) /\
  (space (If c1 n c2 c3) =
     INL (If (pMakeSpace (space c1)) n (pMakeSpace (space c2))
                                       (pMakeSpace (space c3)))) /\
  (space c = INL c)`;

val compile_def = Define `
  compile c = pMakeSpace (space c)`;

val _ = export_theory();
