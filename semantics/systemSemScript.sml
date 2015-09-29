open HolKernel boolLib bossLib Parse;
open lexer_funTheory printTheory initialProgramTheory gramTheory cmlPtreeConversionTheory;
open ffiTheory;
open terminationTheory;
open pathTheory;

val _ = new_theory "systemSem";

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

val evaluate_prog_with_io_def = Define `
evaluate_prog_with_io state k prog =
  evaluate_prog
    <| clock := k
     ; refs := state.sem_st.refs
     ; ffi := <| oracle := add_trace state.sem_st.ffi.oracle;
                 ffi_state := OPTION_MAP (λffi. (ffi,[])) state.sem_st.ffi.ffi_state
               |>
     ; defined_types := state.sem_st.defined_types
     ; defined_mods := state.sem_st.defined_mods
     |>
    state.sem_env
    prog`;

val sem_def = Define `
(sem state prog (Terminate io_list) ⇔
  can_type_prog state prog ∧
  (* there is a clock for which evaluation does not time out and the
     accumulated io events match the given io_list *)
  ?k state' r envC ffi'.
    r ≠ Rerr (Rabort Rtimeout_error) ∧
    evaluate_prog_with_io state k prog = (state', envC, r) ∧
    state'.ffi.ffi_state = SOME (ffi',REVERSE io_list)) ∧
(sem state prog (Diverge io_trace) ⇔
  can_type_prog state prog ∧
  (* for all clocks, evaluation times out and the accumulated io events
     match some prefix of the given io_trace *)
  (!k. ?state' envC ffi' n io_list.
    (evaluate_prog_with_io state k prog =
        (state', envC, Rerr (Rabort Rtimeout_error))) ∧
     LTAKE n io_trace = SOME io_list ∧
     state'.ffi.ffi_state = SOME (ffi', REVERSE io_list)) ∧
  (* furthermore, the whole io_trace is necessary:
     for every prefix of the io_trace, there is a clock
     for which evaluation produces that prefix  *)
   (!n io_list. LTAKE n io_trace = SOME io_list ⇒
      ?k ffi'. (FST (evaluate_prog_with_io state k prog)).ffi.ffi_state = SOME (ffi', REVERSE io_list))) ∧
(sem state prog Fail ⇔
  ¬(can_type_prog state prog))`;

(* attempt to do composed semantics for the simpleIO instantation of the oracle
open simpleIOTheory

val compose_system_sem_def = Define `
(compose_system_sem path (Terminate io_list) (Terminate io_list') ⇔
  io_list = io_list' ∧
  fromList io_list = labels path) ∧
(compose_system_sem path (Diverge io_trace) (Terminate io_list') ⇔
  io_trace = fromList io_list' ∧
  fromList io_list' = labels path ∧
  (last path).has_exited) ∧
(compose_system_sem path (Diverge io_trace) (Diverge io_trace') ⇔
  io_trace = io_trace' ∧
  io_trace = labels path ∧
  (LFINITE io_trace ⇒ ¬(last path).has_exited)) ∧
(compose_system_sem path Fail Fail ⇔ T) ∧
(compose_system_sem path _ _ ⇔ F)`;

val system_sem_def = Define `
system_sem init_state toks res =
  case parse toks of
  | NONE => res = Fail
  | SOME prog =>
      ?res' p.
        sem init_state prog res' ∧
        okpath system_step p ∧
        compose_system_sem p res' res`;
*)

val _ = export_theory();
