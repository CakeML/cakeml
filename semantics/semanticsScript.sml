open preamble;
open lexer_funTheory cmlPtreeConversionTheory; (* TODO: should be included in termination *)
open terminationTheory;

val _ = new_theory "semantics";

val parse_def = Define`
parse toks =
  case some pt. valid_ptree cmlG pt ∧ ptree_head pt = NT (mkNT nTopLevelDecs) ∧
                ptree_fringe pt = MAP TOK toks
  of
     NONE => NONE
   | SOME p => ptree_TopLevelDecs p`;

val _ = Datatype`
  state = <| (* Type system state *)
            tdecs : decls;
            tenv : type_environment;
            (* Semantics state *)
            sem_st : 'ffi semanticPrimitives$state;
            sem_env : v environment |>`;

val _ = hide "state";

val can_type_prog_def = Define `
can_type_prog state prog ⇔
  ∃tdecs' new_tenv. type_prog T state.tdecs state.tenv prog tdecs' new_tenv`;

val evaluate_prog_with_clock_def = Define`
  evaluate_prog_with_clock st env k prog =
    let (st',envC,r) =
      evaluate_prog (st with clock := k) env prog
    in (st'.ffi,r)`;

val semantics_prog_def = Define `
(semantics_prog st env prog (Terminate outcome io_list) ⇔
  (* there is a clock for which evaluation terminates, either internally or via
     FFI, and the accumulated io events match the given io_list *)
  (?k ffi r.
    evaluate_prog_with_clock st env k prog = (ffi,r) ∧
    (if ffi.final_event = NONE then
       (r ≠ Rerr (Rabort Rtimeout_error)) ∧ outcome = Success
     else outcome = FFI_outcome (THE ffi.final_event)) ∧
    (io_list = ffi.io_events)) ∧
  (!k ffi.
    evaluate_prog_with_clock st env k prog ≠ (ffi, Rerr (Rabort Rtype_error)))) ∧
(semantics_prog st env prog (Diverge io_trace) ⇔
  (* for all clocks, evaluation times out *)
  (!k. ?ffi.
    (evaluate_prog_with_clock st env k prog =
        (ffi, Rerr (Rabort Rtimeout_error))) ∧
     ffi.final_event = NONE) ∧
  (* the io_trace is the least upper bound of the set of traces
     produced for each clock *)
   lprefix_lub
     (IMAGE
       (λk. fromList (FST (evaluate_prog_with_clock st env k prog)).io_events)
       UNIV)
     io_trace) ∧
(semantics_prog st env prog Fail ⇔
  (* there is a clock for which evaluation produces a runtime type error *)
  ∃k.
    SND(evaluate_prog_with_clock st env k prog) = Rerr (Rabort Rtype_error))`;

val _ = Datatype`semantics = CannotParse | IllTyped | Execute (behaviour set)`;

val semantics_def = Define`
  semantics state prelude input =
  case parse (lexer_fun input) of
  | NONE => CannotParse
  | SOME prog =>
    if can_type_prog state (prelude ++ prog)
    then Execute (semantics_prog state.sem_st state.sem_env (prelude ++ prog))
    else IllTyped`;

val _ = export_theory();
