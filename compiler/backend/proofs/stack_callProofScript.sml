(*
  Kommentar som beskriver filen
*)

open preamble stackLangTheory stackSemTheory stack_callTheory;

val _ = new_theory("stack_callProof");

Theorem dest_StackFree_thm
  `dest_StackFree x = SOME  m <=> x = StackFree m`
   (EQ_TAC
     >- (Cases_on `x`
          >> (fs[dest_StackFree_def]))
     >> (fs[dest_StackFree_def]));

Theorem dest_StackFree2_thm
  `dest_StackFree x = NONE <=> !m. x <> StackFree m`
  (EQ_TAC
    >> (Cases_on `x`
         >> (fs[dest_StackFree_def])));



val _ = export_theory();
