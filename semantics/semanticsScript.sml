open HolKernel boolLib bossLib Parse;
open lexer_funTheory cmlPtreeConversionTheory initialProgramTheory; (* TODO: should be included in termination *)
open terminationTheory;

val _ = new_theory "semantics";

val parse_def = Define`
parse toks =
  case some pt. valid_ptree cmlG pt ∧ ptree_head pt = NT (mkNT nTopLevelDecs) ∧
                ptree_fringe pt = MAP TOK toks
  of
     NONE => NONE
   | SOME p => ptree_TopLevelDecs p`;

val _ = hide "state";

val can_type_prog_def = Define `
can_type_prog state prog =
  ∃tdecs' tenvT' tenvM' tenvC' tenv'.
    type_prog T state.tdecs state.tenvT state.tenvM state.tenvC state.tenv
        prog
        tdecs' tenvT' tenvM' tenvC' tenv'`;

val evaluate_prog_with_clock_def = Define`
  evaluate_prog_with_clock st k =
    evaluate_prog (st.sem_st with clock := k) st.sem_env`;

val semantics_prog_def = Define `
(semantics_prog state prog (Terminate io_list) ⇔
  can_type_prog state prog ∧
  (* there is a clock for which evaluation does not time out and the
     accumulated io events match the given io_list *)
  ?k state' r envC.
    r ≠ Rerr (Rabort Rtimeout_error) ∧
    evaluate_prog_with_clock state k prog = (state', envC, r) ∧
    ¬state'.ffi.ffi_failed ∧
    REVERSE state'.ffi.io_events = io_list) ∧
(semantics_prog state prog (Diverge io_trace) ⇔
  can_type_prog state prog ∧
  (* for all clocks, evaluation times out and the accumulated io events
     match some prefix of the given io_trace *)
  (!k. ?state' envC n.
    (evaluate_prog_with_clock state k prog =
        (state', envC, Rerr (Rabort Rtimeout_error))) ∧
     ¬state'.ffi.ffi_failed ∧
     LTAKE n io_trace = SOME (REVERSE state'.ffi.io_events)) ∧
  (* furthermore, the whole io_trace is necessary:
     for every prefix of the io_trace, there is a clock
     for which evaluation produces that prefix  *)
   (!n io_list. LTAKE n io_trace = SOME io_list ⇒
      ?k. REVERSE (FST (evaluate_prog_with_clock state k prog)).ffi.io_events = io_list)) ∧
(semantics_prog state prog Fail ⇔
  ¬(can_type_prog state prog))`;

(* Top-level semantics of a string is an optional set of behaviours. There are
   no behaviours if the string cannot be parsed. Otherwise, the set of behaviours
   is according to semantics_prog. (We can prove the set is always a singleton.) *)
val semantics_def = Define`
  semantics state =
  OPTION_MAP (semantics_prog state) o parse o lexer_fun`;

val _ = export_theory();
