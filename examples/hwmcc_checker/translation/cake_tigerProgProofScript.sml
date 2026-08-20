(*
  Proofs for the top-level binary cake_tiger.
*)
Theory cake_tigerProgProof
Ancestors
  aig_parseProg  (* for ERRORMONAD_ERROR_TYPE_def *)
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

(* Asserts that if out = «SUCCESS», then:
   1. getting the model (parsing + processing) was successful
   2. there exist 9 CNF formulas, such that
     2.1 their string representations are saved in the file system
     2.2 if they are all unsatisfiable, then the model is safe and live
   Note that, on success, fs' is the file system right after the
   last certificate has been written to disk. In particular, it is before
   printing SUCCESS to stdout. The connection to printing SUCCESS to stdout is
   in the CFCML specification of make_cert. *)
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

Theorem make_cert_sem_out_nil[local]:
  make_cert_sem fs fs' fmodel «» prefix
Proof
  simp [make_cert_sem_def]
QED

(* TODO Definition main_sem_def *)

(** CFCML *******************************************************************)

val _ = translation_extends "cake_tigerProg";

val prog = get_ml_prog_state ()

val print_err_tac =
  xsimpl >> rw []
  >> qmatch_goalsub_abbrev_tac ‘add_stderr _ msg’
  >> qexistsl [‘add_stderr fs msg’, ‘«»’]
  >> conj_tac >- simp [make_cert_sem_out_nil]
  >> DEP_REWRITE_TAC [add_stdout_nil]
  >> conj_tac >- (irule STD_streams_add_stderr >> simp [])
  >> xsimpl

Theorem make_cert_spec:
  FILENAME fmodel fmodelv ∧
  FILENAME fwitness fwitnessv ∧
  OPTION_TYPE STRING_TYPE prefix prefixv ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v "make_cert" prog)
    [fmodelv; fwitnessv; prefixv]
    (STDIO fs)
    (POSTv uv.
       &UNIT_TYPE () uv *
       SEP_EXISTS fs' out.
         STDIO (add_stdout fs' out) *
         &(make_cert_sem fs fs' fmodel out prefix))
Proof
  rw []
  >> xcf "make_cert" prog
  >> reverse $ Cases_on ‘STD_streams fs’
  >- (fs [STDIO_def] >> xpull)
  >> xlet_auto >- (xcon >> xsimpl)
  (* next xlet slow: ~24s *)
  >> xlet ‘POSTv sv.
       &OPTION_TYPE STRING_TYPE
         (monad_bind (file_content fs fmodel) (SOME ∘ implode)) sv *
       STDIO fs’
  >- (xapp_spec inputAllFrom_SOME_spec >> simp [OPTION_TYPE_def])
  >> Cases_on ‘file_content fs fmodel’ >> gvs [OPTION_TYPE_def]
  >> xmatch
  >- (xapp >> xsimpl >> qexistsl [‘emp’, ‘fs’] >> print_err_tac)
  >> xlet_auto >- (xcon >> xsimpl)
  >> xlet ‘POSTv sv.
       &OPTION_TYPE STRING_TYPE
         (monad_bind (file_content fs fwitness) (SOME ∘ implode)) sv *
       STDIO fs’
  >- (xapp_spec inputAllFrom_SOME_spec >> simp [OPTION_TYPE_def])
  >> Cases_on ‘file_content fs fwitness’ >> gvs [OPTION_TYPE_def]
  >> xmatch
  >- (xapp >> xsimpl >> qexistsl [‘emp’, ‘fs’] >> print_err_tac)
  >> xlet_auto >- xsimpl
  >> qmatch_asmsub_abbrev_tac ‘parse model witness’
  >> reverse $ Cases_on ‘parse model witness’
  >- (
    qmatch_asmsub_rename_tac ‘error err’
    >> Cases_on ‘err’
    >> gvs [ERRORMONAD_ERROR_TYPE_def, PAIR_TYPE_def]
    >> xmatch >> xapp >> xsimpl
    >> first_assum $ irule_at (Pos hd) >> qexistsl [‘fs’, ‘emp’]
    >> print_err_tac
  )
  >> qmatch_asmsub_rename_tac ‘return res’
  >> PairCases_on ‘res’
  >> gvs [ERRORMONAD_ERROR_TYPE_def, PAIR_TYPE_def]
  >> xmatch
  >> xlet_auto >- xsimpl
  >> reverse $ Cases_on ‘process_and_check res0 res1 res2’
  >- (
    qmatch_asmsub_rename_tac ‘error err’
    >> Cases_on ‘err’
    >> gvs [ERRORMONAD_ERROR_TYPE_def, PAIR_TYPE_def]
    >> xmatch >> xapp >> xsimpl
    >> first_assum $ irule_at (Pos hd) >> qexistsl [‘fs’, ‘emp’]
    >> print_err_tac
  )
  >> qmatch_asmsub_rename_tac ‘return aigs’
  >> PairCases_on ‘aigs’
  >> gvs [ERRORMONAD_ERROR_TYPE_def, PAIR_TYPE_def]
  >> xmatch
  (* reset string *)
  >> xlet_auto >- xsimpl
  >> qmatch_asmsub_abbrev_tac ‘PAIR_TYPE STRING_TYPE STRING_TYPE reset_string’
  >> PairCases_on ‘reset_string’
  >> gvs [PAIR_TYPE_def]
  >> xmatch
  >> xlet_auto >- xsimpl
  (* outputFile *)
  >> cheat
QED
