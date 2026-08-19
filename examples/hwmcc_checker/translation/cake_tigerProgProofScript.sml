(*
  Proofs for the top-level binary cake_tiger.
*)
Theory cake_tigerProgProof
Ancestors
  cake_tigerProg
Libs
  preamble
  basis

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

(* Asserts that cnf is saved in the file system. *)
Definition cnf_saved_def:
  cnf_saved fs pfx name cnf =
  ∃limit.
    lits_within limit cnf ∧
    get_file_content fs (make_fname pfx name) =
      SOME (explode (cnf_to_string (cnf, limit)))
End

(* Asserts that cnfs for the checker are saved in the file system. *)
Definition cnf_checks_saved_def:
  cnf_checks_saved fs pfx
    reset transition property base step liveness decrease closure consistent
  =
  LIST_REL (cnf_saved fs pfx)
    [«reset»; «transition»; «property»; «base»; «step»;
     «liveness»; «decrease»; «closure»; «consistent»]
    [reset; transition; property; base; step;
     liveness; decrease; closure; consistent]
End

(* Asserts that if SUCCESS was output, then:
   1. getting the model (parsing + processing) was successful
   2. there exist 9 CNF formulas, such that
     2.1 their string representations are saved in the file system
     2.2 if they are all unsatisfiable, then the model is safe and live *)
Definition make_cert_sem_def:
  make_cert_sem fs fs' fmodel out prefix ⇔
    (out = «SUCCESS» ⇒
     ∃mcirc mreset mnext mpreds mcnstrs mlive mlatches
      reset transition property base step liveness decrease closure consistent.
        get_model fs fmodel =
          SOME (mcirc, mreset, mnext, mpreds, mcnstrs, mlive, mlatches) ∧
        cnf_checks_saved fs' prefix
           reset transition property base step liveness decrease
           closure consistent ∧
        (EVERY is_unsat
           [reset; transition; property; base; step; liveness; decrease;
            closure; consistent]
         ⇒
          is_safe
            mcirc mreset mnext (set mcnstrs) (set mlatches) (set mpreds) ∧
          is_live
            mcirc mreset mnext (set mcnstrs) (qleft mcirc) (qleft_live mlive)
            (set mlatches)))
End

(* TODO Definition main_sem_def *)

(** CFCML *******************************************************************)

val _ = translation_extends "cake_tigerProg";

val prog = get_ml_prog_state ()

Theorem make_cert_spec:
  app (p:'ffi ffi_proj) ^(fetch_v "make_cert" prog)
    [fmodelv; fwitnessv; prefixv]
    (STDIO fs)
    (POSTv uv.
       &UNIT_TYPE () uv *
       SEP_EXISTS fs'. STDIO fs' * &(make_cert_sem fs fs' fmodel out prefix))
Proof
  xcf "make_cert" prog
  >> cheat
QED
