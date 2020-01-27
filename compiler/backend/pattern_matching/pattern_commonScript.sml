(*
  Types common to some different parts of the pattern match compiler.
*)

open preamble;
open numTheory listTheory arithmeticTheory;

val _ = new_theory "pattern_common";

(*
A position describes a path to a sub-term in a term
*)
Datatype:
  position =
    EmptyPos
  | Pos num position
End

(* Results of a pattern match or a multiple pattern match *)
Datatype:
  pmatchResult =
    PMatchSuccess
  | PMatchFailure
  | PTypeFailure
End

(*
  Pattern matching can return three results :
    - Success, with the number of the right hand side that succeeded
    - MatchFailure, when no branch has matched the value
    - TypeFailure, when there was a type mismatch between the value
      to be matched and the patterns
*)
Datatype:
  matchResult =
    MatchSuccess num
  | MatchFailure
End

val _ = export_theory();
