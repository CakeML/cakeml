(*
  The REPL type checks and modifies the decs given as input. This file
  defines the function that implements this and proves that the
  function will only produce type checked and allowed declarations.
*)
open preamble
open semanticsPropsTheory evaluateTheory semanticPrimitivesTheory
open inferTheory compilerTheory

val _ = new_theory "repl_check_and_tweak";

Definition decs_allowed_def:
  decs_allowed (s:ast$dec list) = T  (* TODO: fix *)
End

val read_next_dec =
  “[Dlet (Locs UNKNOWNpt UNKNOWNpt) Pany
       (App Opapp
          [App Opderef [Var (Long "REPL" (Short "readNextString"))];
           Con NONE []])]”

Definition check_and_tweak_def:
  check_and_tweak (decs, types, input_str) =
    let all_decs = decs ++ ^read_next_dec in
      case infertype_prog types all_decs of
      | Success new_types => INR (all_decs, new_types)
      | Failure (loc,msg) =>
          INL (concat [strlit "ERROR: "; msg; strlit " at ";
                       locs_to_string input_str loc])
End

Theorem check_and_tweak: (* used in replProof *)
  check_and_tweak (decs,types,input_str) = INR (safe_decs,new_types) ⇒
  infertype_prog types safe_decs = Success new_types ∧ decs_allowed safe_decs
Proof
  fs [check_and_tweak_def,AllCaseEqs()] \\ rw []
  \\ fs [decs_allowed_def]
QED

val _ = export_theory();
