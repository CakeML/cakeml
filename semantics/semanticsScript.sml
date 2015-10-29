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
can_type_prog state prog ⇔
  no_dup_mods prog state.sem_st.defined_mods ∧
  no_dup_top_types prog state.sem_st.defined_types ∧
  ∃tdecs' tenvT' tenvM' tenvC' tenv'.
    type_prog T state.tdecs state.tenvT state.tenvM state.tenvC state.tenv
        prog
        tdecs' tenvT' tenvM' tenvC' tenv'`;

val evaluate_prog_with_clock_def = Define`
  evaluate_prog_with_clock st k prog =
    let (st',envC,r) =
      evaluate_prog (st.sem_st with clock := k) st.sem_env prog
    in (st'.ffi,r)`;

val semantics_prog_def = Define `
(semantics_prog state prog (Terminate outcome io_list) ⇔
  (* there is a clock for which evaluation terminates, either internally or via
     FFI, and the accumulated io events match the given io_list *)
  ?k ffi r.
    evaluate_prog_with_clock state k prog = (ffi,r) ∧
    (if ffi.final_event = NONE then
       (∀a. r ≠ Rerr (Rabort a)) ∧ outcome = Success
     else outcome = FFI_outcome (THE ffi.final_event)) ∧
    (io_list = ffi.io_events)) ∧
(semantics_prog state prog (Diverge io_trace) ⇔
  (* for all clocks, evaluation times out *)
  (!k. ?ffi.
    (evaluate_prog_with_clock state k prog =
        (ffi, Rerr (Rabort Rtimeout_error))) ∧
     ffi.final_event = NONE) ∧
  (* the io_trace is the least upper bound of the set of traces
     produced for each clock *)
   lprefix_lub
     (IMAGE
       (λk. fromList (FST (evaluate_prog_with_clock state k prog)).io_events)
       UNIV)
     io_trace) ∧
(semantics_prog state prog Fail ⇔
  (* there is a clock for which evaluation produces a runtime type error *)
  ∃k.
    SND(evaluate_prog_with_clock state k prog) = Rerr (Rabort Rtype_error))`;

val _ = Datatype`semantics = CannotParse | IllTyped | Execute (behaviour set)`;

val semantics_def = Define`
  semantics state prelude input =
  case parse (lexer_fun input) of
  | NONE => CannotParse
  | SOME prog =>
    if can_type_prog state (prelude ++ prog)
    then Execute (semantics_prog state (prelude ++ prog))
    else IllTyped`;

val _ = export_theory();
