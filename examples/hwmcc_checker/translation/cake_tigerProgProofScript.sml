(*
  Proofs for the top-level binary cake_tiger.
*)
Theory cake_tigerProgProof
Ancestors
  errorMonad (* for bind_def *)
  aig_to_cnf  (* for aig_to_cnf_def_correct *)
  aig_parseProg  (* for ERRORMONAD_ERROR_TYPE_def *)
  aig_cert_encode  (* for reset_encoding_is_unsat *)
  aig_cert_full  (* for make_reset_string_def *)
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

Theorem parse_imp_parse_model[local]:
  parse model witness = return (maig, waig, ms) ⇒
  parse_model model = SOME maig
Proof
  rw []
  >> gvs [parse_def, parse_model_def, oneline bind_def, AllCaseEqs()]
  >> rpt (pairarg_tac >> gvs [AllCaseEqs()])
QED

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

Theorem process_and_check_imp_process_model[local]:
  process_and_check maig waig ms =
    return
      (mcirc, mreset, mnext, mpreds, mcnstrs, mlive, mlatches, rest)
  ⇒
  process_model maig =
    (mcirc, mreset, mnext, mpreds, mcnstrs, mlive, mlatches)
Proof
  simp [process_and_check_def, process_model_def, process_mlatches_range_def,
        aig_cert_fullTheory.preprocess_def, guard_def, oneline bind_def,
        AllCaseEqs()]
  >> rpt (pairarg_tac >> gvs [AllCaseEqs()])
  >> rpt strip_tac >> gvs [lookup_fromAList, FUN_EQ_THM]
QED


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

(* Asserts that str is a string represnetation of cnf. *)
Definition is_cnf_str_def:
  is_cnf_str cnf str ⇔ ∃limit. str = explode (cnf_to_string (cnf, limit))
End

(* Asserts that cnf is saved in the file system. *)
Definition cnf_saved_def:
  cnf_saved fs name cnf =
    ∃content. get_file_content fs name = SOME content ∧ is_cnf_str cnf content
End

(* Asserts that if out = «SUCCESS» and the files to be written do not yet
   exist in the filesystem, then:
   1. getting the model (parsing + processing) was successful
   2. there exist 9 CNF formulas, such that
     2.1 their string representations are saved in the file system
     2.2 if they are all unsatisfiable, then the model is safe and live
   Note that, on success, fs' is the file system right after the
   last certificate has been written to disk. In particular, it is before
   printing SUCCESS to stdout. The connection to printing SUCCESS to stdout is
   in the CFCML specification of make_cert.
   The reason we assume that the files do not yet exist is because of
   hard links: suppose that all the files we write already exist and are
   pointing to the same inode. In that case, all files will have the same
   content, namely the content of the last write. *)
(* TODO Enable unlinking (requires additions to fsFFI + basis_ffi.c) to
   remove the precondition of the files to be written not yet existing *)
Definition make_cert_sem_def:
  make_cert_sem fs fs' fmodel out prefix ⇔
  let
    fnames =
      MAP (make_fname prefix)
        [«reset»; «transition»; «property»; «base»; «step»; «liveness»;
         «decrease»; «closure»; «consistent»]
  in
    (out = «SUCCESS» ∧ EVERY (λf. ALOOKUP fs.files f = NONE) fnames ⇒
     ∃mcirc mreset mnext mpreds mcnstrs mlive mlatches
      reset transition property base step liveness decrease closure consistent.
        get_model fs fmodel =
          SOME (mcirc, mreset, mnext, mpreds, mcnstrs, mlive, mlatches) ∧
        LIST_REL (cnf_saved fs') fnames
          [reset; transition; property; base; step; liveness; decrease;
           closure; consistent] ∧
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

Definition main_sem_def:
  main_sem cl fs fs' out =
  if LENGTH cl = 3 then
    make_cert_sem fs fs' cl❲1❳ out «»
  else if LENGTH cl = 4 then
    make_cert_sem fs fs' cl❲1❳ out cl❲3❳
  else out = «»
End

(** CFCML *********************************************************************)

val _ = translation_extends "cake_tigerProg";

val prog = get_ml_prog_state ()

(*** write_{reset,transition,...} *********************************************)

Overload "CIRCUIT_TYPE"[local] =
  “LIST_TYPE
     (PAIR_TYPE NUM (LIST_TYPE (PAIR_TYPE (AIG_VAR_TYPE NUM NUM NUM) BOOL)))”

Overload "LIT_TYPE"[local] = “PAIR_TYPE (AIG_VAR_TYPE NUM NUM NUM) BOOL”

Overload "LIT_LIST"[local] = “LIST_TYPE LIT_TYPE”

Overload "LATCH_LIT_TYPE"[local] = “NUM --> LIT_TYPE”

Overload "LATCH_OPTION_LIT_TYPE"[local] = “NUM --> OPTION_TYPE LIT_TYPE”

Overload "INTERV_TYPE"[local] =
  “AIG_VAR_TYPE NUM NUM NUM --> OPTION_TYPE (PAIR_TYPE NUM BOOL)”

Theorem write_reset_spec[local]:
  FILENAME prefix prefixv ∧
  strlen prefix + 9 < 65536 ∧
  CIRCUIT_TYPE mcirc mcircv ∧
  LATCH_OPTION_LIT_TYPE mreset mresetv ∧
  LIT_LIST mcnstrs mcnstrsv ∧
  LIST_TYPE NUM mlatches mlatchesv ∧
  CIRCUIT_TYPE wcirc wcircv ∧
  LATCH_OPTION_LIT_TYPE wreset wresetv ∧
  LIT_LIST wcnstrs wcnstrsv ∧
  LIST_TYPE NUM wlatches wlatchesv ∧
  LIST_TYPE NUM klatches klatchesv ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) write_reset_v
    [prefixv; mcircv; mresetv; mcnstrsv; mlatchesv;
     wcircv; wresetv; wcnstrsv; wlatchesv; klatchesv]
    (STDIO fs)
    (POSTv uv.
       &UNIT_TYPE () uv *
       SEP_EXISTS cnf content.
         &(is_cnf_str cnf content ∧
           (is_unsat cnf ⇔
            reset_encoding_is_unsat
              mcirc mreset mcnstrs mlatches
              wcirc wreset wcnstrs wlatches klatches)) *
         STDIO (write_file fs (make_fname prefix «reset») content))
Proof
  rw []
  >> xcf "write_reset" prog
  >> simp [Once STDIO_STD_streams] >> xpull
  >> xlet_autop
  >> qmatch_asmsub_abbrev_tac ‘PAIR_TYPE STRING_TYPE STRING_TYPE out_string’
  >> PairCases_on ‘out_string’
  >> gvs [PAIR_TYPE_def]
  >> xmatch
  >> xlet_autop
  >> xapp_spec outputFile_spec
  >> qexistsl [‘emp’, ‘make_fname prefix out_string0’, ‘fs’, ‘out_string1’]
  >> conj_tac
  >- (
    gvs [make_fname_def, concat_def]
    >> Cases_on ‘prefix’ >> Cases_on ‘out_string0’
    >> gvs [FILENAME_def, make_reset_string_def]
  )
  >> xsimpl
  >> rw []
  >> gvs [make_reset_string_def]
  >> qmatch_asmsub_abbrev_tac ‘cnf_to_string cnf_limit’
  >> namedCases_on ‘cnf_limit’ ["cnf limit"]
  >> qexistsl [‘cnf’, ‘explode (cnf_to_string (cnf, limit))’]
  >> xsimpl
  >> conj_tac >- (simp [is_cnf_str_def] >> qexists ‘limit’ >> simp [])
  >> gvs []
  >> drule_then assume_tac aig_to_cnf_def_correct
  >> simp [is_unsat_def, reset_encoding_is_unsat_def]
  >> metis_tac [PAIR]
QED

Theorem write_transition_spec[local]:
  FILENAME prefix prefixv ∧
  strlen prefix + 14 < 65536 ∧
  CIRCUIT_TYPE mcirc mcircv ∧
  LATCH_LIT_TYPE mnext mnextv ∧
  LIT_LIST mcnstrs mcnstrsv ∧
  LIST_TYPE NUM mlatches mlatchesv ∧
  CIRCUIT_TYPE wcirc wcircv ∧
  LATCH_LIT_TYPE wnext wnextv ∧
  LIT_LIST wcnstrs wcnstrsv ∧
  LIST_TYPE NUM wlatches wlatchesv ∧
  LIST_TYPE NUM klatches klatchesv ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) write_transition_v
    [prefixv; mcircv; mnextv; mcnstrsv; mlatchesv;
     wcircv; wnextv; wcnstrsv; wlatchesv; klatchesv]
    (STDIO fs)
    (POSTv uv.
       &UNIT_TYPE () uv *
       SEP_EXISTS cnf content.
         &(is_cnf_str cnf content ∧
           (is_unsat cnf ⇔
            transition_encoding_is_unsat
              mcirc mnext mcnstrs mlatches
              wcirc wnext wcnstrs wlatches klatches)) *
         STDIO (write_file fs (make_fname prefix «transition») content))
Proof
  rw []
  >> xcf "write_transition" prog
  >> simp [Once STDIO_STD_streams] >> xpull
  >> xlet_autop
  >> qmatch_asmsub_abbrev_tac ‘PAIR_TYPE STRING_TYPE STRING_TYPE out_string’
  >> PairCases_on ‘out_string’
  >> gvs [PAIR_TYPE_def]
  >> xmatch
  >> xlet_autop
  >> xapp_spec outputFile_spec
  >> qexistsl [‘emp’, ‘make_fname prefix out_string0’, ‘fs’, ‘out_string1’]
  >> conj_tac
  >- (
    gvs [make_fname_def, concat_def]
    >> Cases_on ‘prefix’ >> Cases_on ‘out_string0’
    >> gvs [FILENAME_def, make_transition_string_def]
  )
  >> xsimpl
  >> rw []
  >> gvs [make_transition_string_def]
  >> qmatch_asmsub_abbrev_tac ‘cnf_to_string cnf_limit’
  >> namedCases_on ‘cnf_limit’ ["cnf limit"]
  >> qexistsl [‘cnf’, ‘explode (cnf_to_string (cnf, limit))’]
  >> xsimpl
  >> conj_tac >- (simp [is_cnf_str_def] >> qexists ‘limit’ >> simp [])
  >> gvs []
  >> drule_then assume_tac aig_to_cnf_def_correct
  >> simp [is_unsat_def, transition_encoding_is_unsat_def]
  >> metis_tac [PAIR]
QED

Theorem write_property_spec[local]:
  FILENAME prefix prefixv ∧
  strlen prefix + 12 < 65536 ∧
  CIRCUIT_TYPE mcirc mcircv ∧
  LIT_LIST mcnstrs mcnstrsv ∧
  LIT_LIST mpreds mpredsv ∧
  CIRCUIT_TYPE wcirc wcircv ∧
  LIT_LIST wcnstrs wcnstrsv ∧
  LIT_LIST wpreds wpredsv ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) write_property_v
    [prefixv; mcircv; mcnstrsv; mpredsv; wcircv; wcnstrsv; wpredsv]
    (STDIO fs)
    (POSTv uv.
       &UNIT_TYPE () uv *
       SEP_EXISTS cnf content.
         &(is_cnf_str cnf content ∧
           (is_unsat cnf ⇔
            (property_encoding_is_unsat
               mcirc mcnstrs mpreds
               wcirc wcnstrs wpreds))) *
         STDIO (write_file fs (make_fname prefix «property») content))
Proof
  rw []
  >> xcf "write_property" prog
  >> simp [Once STDIO_STD_streams] >> xpull
  >> xlet_autop
  >> qmatch_asmsub_abbrev_tac ‘PAIR_TYPE STRING_TYPE STRING_TYPE out_string’
  >> PairCases_on ‘out_string’
  >> gvs [PAIR_TYPE_def]
  >> xmatch
  >> xlet_autop
  >> xapp_spec outputFile_spec
  >> qexistsl [‘emp’, ‘make_fname prefix out_string0’, ‘fs’, ‘out_string1’]
  >> conj_tac
  >- (
    gvs [make_fname_def, concat_def]
    >> Cases_on ‘prefix’ >> Cases_on ‘out_string0’
    >> gvs [FILENAME_def, make_property_string_def]
  )
  >> xsimpl
  >> rw []
  >> gvs [make_property_string_def]
  >> qmatch_asmsub_abbrev_tac ‘cnf_to_string cnf_limit’
  >> namedCases_on ‘cnf_limit’ ["cnf limit"]
  >> qexistsl [‘cnf’, ‘explode (cnf_to_string (cnf, limit))’]
  >> xsimpl
  >> conj_tac >- (simp [is_cnf_str_def] >> qexists ‘limit’ >> simp [])
  >> gvs []
  >> drule_then assume_tac aig_to_cnf_def_correct
  >> simp [is_unsat_def, property_encoding_is_unsat_def]
  >> metis_tac [PAIR]
QED

Theorem write_base_spec[local]:
  FILENAME prefix prefixv ∧
  strlen prefix + 8 < 65536 ∧
  CIRCUIT_TYPE wcirc wcircv ∧
  LATCH_OPTION_LIT_TYPE wreset wresetv ∧
  LIT_LIST wcnstrs wcnstrsv ∧
  LIT_LIST wpreds wpredsv ∧
  LIST_TYPE NUM wlatches wlatchesv ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) write_base_v
    [prefixv; wcircv; wresetv; wcnstrsv; wpredsv; wlatchesv]
    (STDIO fs)
    (POSTv uv.
       &UNIT_TYPE () uv *
       SEP_EXISTS cnf content.
         &(is_cnf_str cnf content ∧
           (is_unsat cnf ⇔
            (base_encoding_is_unsat
               wcirc wreset wcnstrs wpreds wlatches))) *
         STDIO (write_file fs (make_fname prefix «base») content))
Proof
  rw []
  >> xcf "write_base" prog
  >> simp [Once STDIO_STD_streams] >> xpull
  >> xlet_autop
  >> qmatch_asmsub_abbrev_tac ‘PAIR_TYPE STRING_TYPE STRING_TYPE out_string’
  >> PairCases_on ‘out_string’
  >> gvs [PAIR_TYPE_def]
  >> xmatch
  >> xlet_autop
  >> xapp_spec outputFile_spec
  >> qexistsl [‘emp’, ‘make_fname prefix out_string0’, ‘fs’, ‘out_string1’]
  >> conj_tac
  >- (
    gvs [make_fname_def, concat_def]
    >> Cases_on ‘prefix’ >> Cases_on ‘out_string0’
    >> gvs [FILENAME_def, make_base_string_def]
  )
  >> xsimpl
  >> rw []
  >> gvs [make_base_string_def]
  >> qmatch_asmsub_abbrev_tac ‘cnf_to_string cnf_limit’
  >> namedCases_on ‘cnf_limit’ ["cnf limit"]
  >> qexistsl [‘cnf’, ‘explode (cnf_to_string (cnf, limit))’]
  >> xsimpl
  >> conj_tac >- (simp [is_cnf_str_def] >> qexists ‘limit’ >> simp [])
  >> gvs []
  >> drule_then assume_tac aig_to_cnf_def_correct
  >> simp [is_unsat_def, base_encoding_is_unsat_def]
  >> metis_tac [PAIR]
QED

Theorem write_step_spec[local]:
  FILENAME prefix prefixv ∧
  strlen prefix + 8 < 65536 ∧
  CIRCUIT_TYPE wcirc wcircv ∧
  LATCH_LIT_TYPE wnext wnextv ∧
  LIT_LIST wcnstrs wcnstrsv ∧
  LIT_LIST wpreds wpredsv ∧
  LIST_TYPE NUM wlatches wlatchesv ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) write_step_v
    [prefixv; wcircv; wnextv; wcnstrsv; wpredsv; wlatchesv]
    (STDIO fs)
    (POSTv uv.
       &UNIT_TYPE () uv *
       SEP_EXISTS cnf content.
         &(is_cnf_str cnf content ∧
           (is_unsat cnf ⇔
            (step_encoding_is_unsat
               wcirc wnext wcnstrs wpreds wlatches))) *
         STDIO (write_file fs (make_fname prefix «step») content))
Proof
  rw []
  >> xcf "write_step" prog
  >> simp [Once STDIO_STD_streams] >> xpull
  >> xlet_autop
  >> qmatch_asmsub_abbrev_tac ‘PAIR_TYPE STRING_TYPE STRING_TYPE out_string’
  >> PairCases_on ‘out_string’
  >> gvs [PAIR_TYPE_def]
  >> xmatch
  >> xlet_autop
  >> xapp_spec outputFile_spec
  >> qexistsl [‘emp’, ‘make_fname prefix out_string0’, ‘fs’, ‘out_string1’]
  >> conj_tac
  >- (
    gvs [make_fname_def, concat_def]
    >> Cases_on ‘prefix’ >> Cases_on ‘out_string0’
    >> gvs [FILENAME_def, make_step_string_def]
  )
  >> xsimpl
  >> rw []
  >> gvs [make_step_string_def]
  >> qmatch_asmsub_abbrev_tac ‘cnf_to_string cnf_limit’
  >> namedCases_on ‘cnf_limit’ ["cnf limit"]
  >> qexistsl [‘cnf’, ‘explode (cnf_to_string (cnf, limit))’]
  >> xsimpl
  >> conj_tac >- (simp [is_cnf_str_def] >> qexists ‘limit’ >> simp [])
  >> gvs []
  >> drule_then assume_tac aig_to_cnf_def_correct
  >> simp [is_unsat_def, step_encoding_is_unsat_def]
  >> metis_tac [PAIR]
QED

Theorem write_liveness_spec[local]:
  FILENAME prefix prefixv ∧
  strlen prefix + 12 < 65536 ∧
  CIRCUIT_TYPE mcirc mcircv ∧
  LIT_LIST mcnstrs mcnstrsv ∧
  LIST_TYPE LIT_LIST mlive mlivev ∧
  CIRCUIT_TYPE wcirc wcircv ∧
  LATCH_LIT_TYPE wnext wnextv ∧
  LIT_LIST wcnstrs wcnstrsv ∧
  LIT_LIST wpreds wpredsv ∧
  LIST_TYPE LIT_LIST wlive wlivev ∧
  LIST_TYPE NUM wlatches wlatchesv ∧
  INTERV_TYPE interv intervv ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) write_liveness_v
    [prefixv; mcircv; mcnstrsv; mlivev;
     wcircv; wnextv; wcnstrsv; wpredsv; wlivev; wlatchesv; intervv]
    (STDIO fs)
    (POSTv uv.
       &UNIT_TYPE () uv *
       SEP_EXISTS cnf content.
         &(is_cnf_str cnf content ∧
           (is_unsat cnf ⇔
            (liveness_encoding_is_unsat
               mcirc mcnstrs mlive
               wcirc wnext wcnstrs wpreds wlive wlatches interv))) *
         STDIO (write_file fs (make_fname prefix «liveness») content))
Proof
  rw []
  >> xcf "write_liveness" prog
  >> simp [Once STDIO_STD_streams] >> xpull
  >> xlet_autop
  >> qmatch_asmsub_abbrev_tac ‘PAIR_TYPE STRING_TYPE STRING_TYPE out_string’
  >> PairCases_on ‘out_string’
  >> gvs [PAIR_TYPE_def]
  >> xmatch
  >> xlet_autop
  >> xapp_spec outputFile_spec
  >> qexistsl [‘emp’, ‘make_fname prefix out_string0’, ‘fs’, ‘out_string1’]
  >> conj_tac
  >- (
    gvs [make_fname_def, concat_def]
    >> Cases_on ‘prefix’ >> Cases_on ‘out_string0’
    >> gvs [FILENAME_def, make_liveness_string_def]
  )
  >> xsimpl
  >> rw []
  >> gvs [make_liveness_string_def]
  >> qmatch_asmsub_abbrev_tac ‘cnf_to_string cnf_limit’
  >> namedCases_on ‘cnf_limit’ ["cnf limit"]
  >> qexistsl [‘cnf’, ‘explode (cnf_to_string (cnf, limit))’]
  >> xsimpl
  >> conj_tac >- (simp [is_cnf_str_def] >> qexists ‘limit’ >> simp [])
  >> gvs []
  >> drule_then assume_tac aig_to_cnf_def_correct
  >> simp [is_unsat_def, liveness_encoding_is_unsat_def]
  >> metis_tac [PAIR]
QED

Theorem write_decrease_spec[local]:
  FILENAME prefix prefixv ∧
  strlen prefix + 12 < 65536 ∧
  CIRCUIT_TYPE wcirc wcircv ∧
  LATCH_LIT_TYPE wnext wnextv ∧
  LIT_LIST wcnstrs wcnstrsv ∧
  LIT_LIST wpreds wpredsv ∧
  LIST_TYPE LIT_LIST wlive wlivev ∧
  LIST_TYPE NUM wlatches wlatchesv ∧
  INTERV_TYPE interv intervv ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) write_decrease_v
    [prefixv; wcircv; wnextv; wcnstrsv; wpredsv; wlivev; wlatchesv; intervv]
    (STDIO fs)
    (POSTv uv.
       &UNIT_TYPE () uv *
       SEP_EXISTS cnf content.
         &(is_cnf_str cnf content ∧
           (is_unsat cnf ⇔
            (decrease_encoding_is_unsat
               wcirc wnext wcnstrs wpreds wlive wlatches interv))) *
         STDIO (write_file fs (make_fname prefix «decrease») content))
Proof
  rw []
  >> xcf "write_decrease" prog
  >> simp [Once STDIO_STD_streams] >> xpull
  >> xlet_autop
  >> qmatch_asmsub_abbrev_tac ‘PAIR_TYPE STRING_TYPE STRING_TYPE out_string’
  >> PairCases_on ‘out_string’
  >> gvs [PAIR_TYPE_def]
  >> xmatch
  >> xlet_autop
  >> xapp_spec outputFile_spec
  >> qexistsl [‘emp’, ‘make_fname prefix out_string0’, ‘fs’, ‘out_string1’]
  >> conj_tac
  >- (
    gvs [make_fname_def, concat_def]
    >> Cases_on ‘prefix’ >> Cases_on ‘out_string0’
    >> gvs [FILENAME_def, make_decrease_string_def]
  )
  >> xsimpl
  >> rw []
  >> gvs [make_decrease_string_def]
  >> qmatch_asmsub_abbrev_tac ‘cnf_to_string cnf_limit’
  >> namedCases_on ‘cnf_limit’ ["cnf limit"]
  >> qexistsl [‘cnf’, ‘explode (cnf_to_string (cnf, limit))’]
  >> xsimpl
  >> conj_tac >- (simp [is_cnf_str_def] >> qexists ‘limit’ >> simp [])
  >> gvs []
  >> drule_then assume_tac aig_to_cnf_def_correct
  >> simp [is_unsat_def, decrease_encoding_is_unsat_def]
  >> metis_tac [PAIR]
QED

Theorem write_closure_spec[local]:
  FILENAME prefix prefixv ∧
  strlen prefix + 11 < 65536 ∧
  CIRCUIT_TYPE wcirc wcircv ∧
  LATCH_LIT_TYPE wnext wnextv ∧
  LIT_LIST wcnstrs wcnstrsv ∧
  LIT_LIST wpreds wpredsv ∧
  LIST_TYPE LIT_LIST wlive wlivev ∧
  LIST_TYPE NUM wlatches wlatchesv ∧
  INTERV_TYPE interv intervv ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) write_closure_v
    [prefixv; wcircv; wnextv; wcnstrsv; wpredsv; wlivev; wlatchesv; intervv]
    (STDIO fs)
    (POSTv uv.
       &UNIT_TYPE () uv *
       SEP_EXISTS cnf content.
         &(is_cnf_str cnf content ∧
           (is_unsat cnf ⇔
            (closure_encoding_is_unsat
               wcirc wnext wcnstrs wpreds wlive wlatches interv))) *
         STDIO (write_file fs (make_fname prefix «closure») content))
Proof
  rw []
  >> xcf "write_closure" prog
  >> simp [Once STDIO_STD_streams] >> xpull
  >> xlet_autop
  >> qmatch_asmsub_abbrev_tac ‘PAIR_TYPE STRING_TYPE STRING_TYPE out_string’
  >> PairCases_on ‘out_string’
  >> gvs [PAIR_TYPE_def]
  >> xmatch
  >> xlet_autop
  >> xapp_spec outputFile_spec
  >> qexistsl [‘emp’, ‘make_fname prefix out_string0’, ‘fs’, ‘out_string1’]
  >> conj_tac
  >- (
    gvs [make_fname_def, concat_def]
    >> Cases_on ‘prefix’ >> Cases_on ‘out_string0’
    >> gvs [FILENAME_def, make_closure_string_def]
  )
  >> xsimpl
  >> rw []
  >> gvs [make_closure_string_def]
  >> qmatch_asmsub_abbrev_tac ‘cnf_to_string cnf_limit’
  >> namedCases_on ‘cnf_limit’ ["cnf limit"]
  >> qexistsl [‘cnf’, ‘explode (cnf_to_string (cnf, limit))’]
  >> xsimpl
  >> conj_tac >- (simp [is_cnf_str_def] >> qexists ‘limit’ >> simp [])
  >> gvs []
  >> drule_then assume_tac aig_to_cnf_def_correct
  >> simp [is_unsat_def, closure_encoding_is_unsat_def]
  >> metis_tac [PAIR]
QED

Theorem write_consistent_spec[local]:
  FILENAME prefix prefixv ∧
  strlen prefix + 14 < 65536 ∧
  CIRCUIT_TYPE wcirc wcircv ∧
  LATCH_LIT_TYPE wnext wnextv ∧
  LIT_LIST wcnstrs wcnstrsv ∧
  LIT_LIST wpreds wpredsv ∧
  LIST_TYPE LIT_LIST wlive wlivev ∧
  LIST_TYPE NUM wlatches wlatchesv ∧
  INTERV_TYPE interv intervv ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) write_consistent_v
    [prefixv; wcircv; wnextv; wcnstrsv; wpredsv; wlivev; wlatchesv; intervv]
    (STDIO fs)
    (POSTv uv.
       &UNIT_TYPE () uv *
       SEP_EXISTS cnf content.
         &(is_cnf_str cnf content ∧
           (is_unsat cnf ⇔
            (consistent_encoding_is_unsat
               wcirc wnext wcnstrs wpreds wlive wlatches interv))) *
         STDIO (write_file fs (make_fname prefix «consistent») content))
Proof
  rw []
  >> xcf "write_consistent" prog
  >> simp [Once STDIO_STD_streams] >> xpull
  >> xlet_autop
  >> qmatch_asmsub_abbrev_tac ‘PAIR_TYPE STRING_TYPE STRING_TYPE out_string’
  >> PairCases_on ‘out_string’
  >> gvs [PAIR_TYPE_def]
  >> xmatch
  >> xlet_autop
  >> xapp_spec outputFile_spec
  >> qexistsl [‘emp’, ‘make_fname prefix out_string0’, ‘fs’, ‘out_string1’]
  >> conj_tac
  >- (
    gvs [make_fname_def, concat_def]
    >> Cases_on ‘prefix’ >> Cases_on ‘out_string0’
    >> gvs [FILENAME_def, make_consistent_string_def]
  )
  >> xsimpl
  >> rw []
  >> gvs [make_consistent_string_def]
  >> qmatch_asmsub_abbrev_tac ‘cnf_to_string cnf_limit’
  >> namedCases_on ‘cnf_limit’ ["cnf limit"]
  >> qexistsl [‘cnf’, ‘explode (cnf_to_string (cnf, limit))’]
  >> xsimpl
  >> conj_tac >- (simp [is_cnf_str_def] >> qexists ‘limit’ >> simp [])
  >> gvs []
  >> drule_then assume_tac aig_to_cnf_def_correct
  >> simp [is_unsat_def, consistent_encoding_is_unsat_def]
  >> metis_tac [PAIR]
QED

(*** make_cert ****************************************************************)

(* Tactic to close goals after printing an error. *)
val print_err_tac =
  xsimpl >> rw []
  >> qmatch_goalsub_abbrev_tac ‘add_stderr _ msg’
  >> qexistsl [‘add_stderr fs msg’, ‘«»’]
  >> conj_tac >- simp [make_cert_sem_out_nil]
  >> DEP_REWRITE_TAC [add_stdout_nil]
  >> conj_tac >- (irule STD_streams_add_stderr >> simp [])
  >> xsimpl

(* Tactic to dispatch the sideconditions of the write_{reset,transition,...}
   functions. *)
val write_side_tac : tactic =
  xsimpl
  >> rw []
  >> qpat_assum ‘is_cnf_str _ _’ $ irule_at Any
  >> simp [] >> xsimpl

Theorem make_fname_name_neq[local,simp]:
  make_fname pfx s' ≠ make_fname pfx s ⇔ s' ≠ s
Proof
  simp [make_fname_def, concat_def]
  >> rpt (CASE_TAC >> simp [])
QED

Theorem ALOOKUP_write_file_files_neq[local]:
  n' ≠ n ⇒ (ALOOKUP (write_file fs n' str).files n = ALOOKUP fs.files n)
Proof
  rw [write_file_def] >> CASE_TAC >> gvs []
QED

Theorem cnf_saved_write_file_files_neq[local]:
  n' ≠ n ∧ ALOOKUP fs.files n' = NONE ⇒
  (cnf_saved (write_file fs n' content') n cnf ⇔ cnf_saved fs n cnf)
Proof
  rw [cnf_saved_def, get_file_content_def, write_file_def]
  >> CASE_TAC >> gvs []
  >> metis_tac [fresh_iname_spec]
QED

Theorem cnf_saved_write_file_files_eq[local]:
  consistentFS fs ⇒
  (cnf_saved (write_file fs n content) n cnf ⇔ is_cnf_str cnf content)
Proof
  rw [cnf_saved_def, get_file_content_def, write_file_def]
  >> CASE_TAC >> gvs [AFUPDKEY_ALOOKUP]
  >> CASE_TAC >> gvs [consistentFS_def, ALOOKUP_NONE]
  >> metis_tac []
QED

Theorem make_cert_spec:
  FILENAME fmodel fmodelv ∧
  FILENAME fwitness fwitnessv ∧
  FILENAME prefix prefixv ∧
  (* 14 = max length of property name + file extension
     TODO Factor out the string constants and compute their length here *)
  strlen prefix + 14 < 65536 ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) make_cert_v
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
  >> simp [Once STDIO_STD_streams, Once STDIO_consistentFS] >> xpull
  >> xlet_autop
  >> xlet ‘POSTv sv.
       &OPTION_TYPE STRING_TYPE
         (monad_bind (file_content fs fmodel) (SOME ∘ implode)) sv *
       STDIO fs’
  >- (xapp_spec inputAllFrom_SOME_spec >> simp [OPTION_TYPE_def])
  >> Cases_on ‘file_content fs fmodel’ >> gvs [OPTION_TYPE_def]
  >> xmatch
  >- (xapp >> xsimpl >> qexistsl [‘emp’, ‘fs’] >> print_err_tac)
  >> xlet_autop
  >> xlet ‘POSTv sv.
       &OPTION_TYPE STRING_TYPE
         (monad_bind (file_content fs fwitness) (SOME ∘ implode)) sv *
       STDIO fs’
  >- (xapp_spec inputAllFrom_SOME_spec >> simp [OPTION_TYPE_def])
  >> Cases_on ‘file_content fs fwitness’ >> gvs [OPTION_TYPE_def]
  >> xmatch
  >- (xapp >> xsimpl >> qexistsl [‘emp’, ‘fs’] >> print_err_tac)
  >> xlet_autop
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
  >> xlet_autop
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
  >> ntac 9 (xlet_auto >- write_side_tac)
  >> xapp >> xsimpl
  >> qmatch_goalsub_abbrev_tac ‘STDIO fs'’
  >> qexistsl [‘emp’, ‘fs'’]
  >> conj_tac >- xsimpl
  >> rw []
  >> qexistsl [‘fs'’, ‘«SUCCESS»’]
  >> conj_tac
  >- (
    rw [make_cert_sem_def]
    (* Showing get_model is successful *)
    >> simp [get_model_def]
    >> drule_then assume_tac parse_imp_parse_model >> simp []
    >> drule_then assume_tac process_and_check_imp_process_model >> simp []
    (* Showing cnf_saved *)
    >> simp [Abbr ‘fs'’, Req0 cnf_saved_write_file_files_eq,
             cnf_saved_write_file_files_neq, ALOOKUP_write_file_files_neq]
    (* Showing is_cnf_str *)
    >> rpt (qpat_assum ‘is_cnf_str _ _’ $ irule_at Any)
    (* Showing unsat ⇒ safe + live *)
    >> drule process_and_check_return
    >> simp [GSYM encodings_unsat_def]
  )
  >> xsimpl
QED

(*** main *********************************************************************)

val wrong_arg_count_tac =
  xmatch >> xapp
  >> qmatch_goalsub_abbrev_tac ‘COMMANDLINE cl’
  >> qexistsl [‘COMMANDLINE cl’, ‘usage_string’, ‘fs’]
  >> simp [usage_string_v_thm] >> xsimpl
  >> rw []
  >> simp [Abbr ‘cl’, main_sem_def]
  >> qexists ‘add_stderr fs usage_string’
  >> simp [Req0 add_stdout_nil, STD_streams_add_stderr]
  >> xsimpl

Theorem main_spec:
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) main_v
    [Conv NONE []]
    (COMMANDLINE cl * STDIO fs)
    (POSTv uv.
       &UNIT_TYPE () uv * COMMANDLINE cl *
       SEP_EXISTS fs' out.
         STDIO (add_stdout fs' out) * &(main_sem cl fs fs' out))
Proof
  simp [Once STDIO_STD_streams, Once COMMANDLINE_wfcl] >> xpull
  >> xcf "main" prog
  >> xmatch
  >> xlet_autop
  >> xlet_auto >- (qexistsl [‘STDIO fs’] >> xsimpl)
  >> namedCases_on ‘cl’ ["", "arg₀ rest"] >> gvs [LIST_TYPE_def]
  >- wrong_arg_count_tac
  >> namedCases_on ‘rest’ ["", "arg₁ rest₁"] >> gvs [LIST_TYPE_def]
  >- wrong_arg_count_tac
  >> namedCases_on ‘rest₁’ ["", "arg₂ rest₂"] >> gvs [LIST_TYPE_def]
  >- wrong_arg_count_tac
  >> namedCases_on ‘rest₂’ ["", "arg₂ rest₃"] >> gvs [LIST_TYPE_def]
  (* no prefix passed in *)
  >- (
    xmatch >> xapp
    >> simp []
    >> qpat_assum ‘CARD _ < _’ $ irule_at Any
    >> qexists ‘«»’  (* instantiate prefix *)
    >> fs [FILENAME_def, wfcl_def, validArg_def]
    >> ntac 2 $ qpat_assum ‘STRING_TYPE _ _’ $ irule_at Any
    >> simp []
    >> xsimpl
    >> rw []
    >> simp [main_sem_def]
    >> qpat_assum ‘make_cert_sem _ _ _ _ _’ $ irule_at Any
    >> xsimpl
  )
  >> namedCases_on ‘rest₃’ ["", "arg₃ rest₄"] >> gvs [LIST_TYPE_def]
  (* prefix passed in *)
  >- (
    xmatch
    >> xlet_autop
    >> xlet_autop
    >> xif
    >- (
      (* prefix too long *)
      xapp
      >> qmatch_goalsub_abbrev_tac ‘COMMANDLINE cl’
      >> xsimpl
      >> qexistsl [‘COMMANDLINE cl’, ‘fs’]
      >> xsimpl
      >> rw [Abbr ‘cl’, main_sem_def]
      >> qexistsl [‘add_stderr fs «prefix too long»’, ‘«»’]
      >> simp [make_cert_sem_out_nil, add_stdout_nil, STD_streams_add_stderr]
      >> xsimpl
    )
    >> xapp
    >> simp []
    >> qpat_assum ‘CARD _ < _’ $ irule_at Any
    >> fs [FILENAME_def, wfcl_def, validArg_def]
    >> ntac 3 $ qpat_assum ‘STRING_TYPE _ _’ $ irule_at Any
    >> simp []
    >> xsimpl
    >> rw [main_sem_def]
    >> qpat_assum ‘make_cert_sem _ _ _ _ _’ $ irule_at Any
    >> xsimpl
  )
  >> wrong_arg_count_tac
QED
