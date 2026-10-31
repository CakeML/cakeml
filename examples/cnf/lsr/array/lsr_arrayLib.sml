(*
  Tactics shared by the array-layer theories of the LSR checker
*)
structure lsr_arrayLib =
struct

open preamble

(* Closes a separation-logic entailment whose two sides differ only by
  frame association and GC slack *)
val sep_triv =
  metis_tac[ccnf_parseProgTheory.SEP_IMP_REFL_gc,set_sepTheory.SEP_IMP_REFL,
    set_sepTheory.STAR_ASSOC,set_sepTheory.STAR_COMM];

end
