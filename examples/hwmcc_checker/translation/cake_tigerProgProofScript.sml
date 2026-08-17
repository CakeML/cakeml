(*
  Proofs for the top-level binary cake_tiger.
*)
Theory cake_tigerProgProof
Ancestors
  fsFFIProps  (* all_lines_file *)
  cake_tigerProg
Libs
  preamble

(* TODO Would be nice if we had also a record for the semantic representation
   of AIG (instead of passing around 6-tuples or so) *)

(** Top-Level Semantics *******************************************************)

(* Parses the model. *)
Definition parse_model_def:
  parse_model str =
    case parse_aiger str 0 of
    | error _ => NONE
    | return (maig, _) => SOME maig
End

(* Converts the parsed AIG into the semantic definition from aigScript. *)
Definition process_model_def:
  process_model m =
  let
    mcirc  = m.circuit;
    mreset = ALOOKUP m.reset;
    mnext  =
      (λl.
         case ALOOKUP m.next l of
         | SOME lit => lit
         | NONE => (Base Ff, F)  (* should not happen *));
    mpreds =
      MAP not
        (if m.counts.bad = 0 ∧ m.counts.justice = 0 then m.outputs
         else m.bad);
    mcnstrs = m.constraints;
    mfair = MAP not m.fairness;
    mlive = MAP (λsignals. mfair ++ (MAP not signals)) m.justice;
    mlatches =
      [m.counts.inputs + 1 .. m.counts.inputs + m.counts.latches];
  in
    (mcirc, mreset, mnext, mpreds, mcnstrs, mlive, mlatches)
End

(* Reads the model from a file in the file system.
   Part of the trusted computing base. *)
Definition get_model_def:
  get_model fs f =
  case file_content fs f of
  | NONE => NONE
  | SOME str =>
    case parse_model (implode str) of
    | NONE => NONE
    | SOME maig => SOME (process_model maig)
End

(* True if and only if the cnf-formula is unsatisfiable. *)
Definition is_unsat_def:
  is_unsat cnf = ¬satisfiable_cnf (set cnf)
End

(* TODO main_sem is not quite right; it's missing the command line/prefix
   information *)

(* 1. getting the model (parsing + processing) was successful
   2. there exist 9 CNF formulas, such that
     2.1 if they are all unsatisfiable, then the model is safe and live
     2.2 their string representations are saved in the file system *)
Definition main_sem_def:
  main_sem fs f1 out ⇔
    (out = «SUCCESS» ⇒
     ∃mcirc mreset mnext mpreds mcnstrs mlive mlatches
      (* TODO remove annotation once we have added "are saved in FS" *)
      (reset: num lit list list) transition property base step liveness decrease closure
      consistent.
       get_model fs f1 =
         SOME (mcirc, mreset, mnext, mpreds, mcnstrs, mlive, mlatches) ∧
       (* TODO are saved in FS *)
       (EVERY is_unsat
          [reset; transition; property; base; step;
           liveness; decrease; closure; consistent] ⇒
          is_safe
            mcirc mreset mnext (set mcnstrs) (set mlatches) (set mpreds) ∧
          is_live
            mcirc mreset mnext (set mcnstrs) (qleft mcirc) (qleft_live mlive)
            (set mlatches)))
End
