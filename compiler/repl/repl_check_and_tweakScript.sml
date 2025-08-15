(*
  The REPL type checks and modifies the decs given as input. This file
  defines the function that implements this and proves that the
  function will only produce type checked and allowed declarations.
*)
open preamble
open semanticsPropsTheory evaluateTheory semanticPrimitivesTheory
open inferTheory compilerTheory repl_decs_allowedTheory printTweaksTheory

val _ = Parse.hide "types"

val _ = new_theory "repl_check_and_tweak";

Definition check_and_tweak_def:
  check_and_tweak (decs, types, input_str) =
    case add_print_then_read types decs of
    | Success (new_decs,new_types) =>
        if decs_allowed new_decs then INR (new_decs, new_types)
        else INL (strlit "ERROR: input contains reserved constructor/FFI names")
    | Failure (loc,msg) =>
        INL (concat [strlit "ERROR: "; msg; strlit " at ";
                     locs_to_string input_str loc])
End

(* main correctness result *)

Theorem check_and_tweak: (* used in replProof *)
  check_and_tweak (decs,types,input_str) = INR (safe_decs,new_types) ⇒
  infertype_prog_inc (SND types) safe_decs = Success (SND new_types) ∧
  decs_allowed safe_decs
Proof
  fs [check_and_tweak_def,AllCaseEqs()] \\ rw []
  \\ drule add_print_then_read_succ \\ rw []
  \\ fs [infertype_prog_inc_def]
QED

(* used in repl-function in compiler64Prog *)

Definition roll_back_def:
  roll_back ((old_tn:type_names, old_ienv:inf_env, old_next_id:num),
             (new_tn:type_names, new_ienv:inf_env, new_next_id:num)) =
    (old_tn, old_ienv, new_next_id)
End

val _ = export_theory();
