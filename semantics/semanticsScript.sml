(*
  The top-level semantics of CakeML programs.
*)
Theory semantics
Ancestors
  lexer_fun cmlPtreeConversion primTypes
Libs
  preamble

Definition parse_def:
  parse toks =
    case some pt. valid_lptree cmlG pt ∧ ptree_head pt = NT (mkNT nTopLevelDecs) ∧
                  real_fringe pt = MAP (TOK ## I) toks
    of
     | NONE => NONE
     | SOME p => ptree_TopLevelDecs p
End

Datatype:
  state = <| (* Type system state *)
             tenv : type_env;
             type_ids : type_ident set;
             (* Semantics state *)
             sem_st : 'ffi semanticPrimitives$state;
             sem_env : v sem_env |>
End

val _ = hide "state";

Definition can_type_prog_def:
  can_type_prog state prog ⇔
    ∃new_tids new_tenv.
      DISJOINT state.type_ids new_tids ∧
      type_ds T state.tenv prog new_tids new_tenv
End

Definition evaluate_prog_with_clock_def:
  evaluate_prog_with_clock st env k prog =
    let (st',r) =
      evaluate_decs (st with clock := k) env prog
    in (st'.ffi,r)
End

Definition semantics_prog_def:
  (semantics_prog st env prog (Terminate outcome io_list) ⇔
    (* there is a clock for which evaluation terminates, either internally or via
       FFI, and the accumulated io events match the given io_list *)
    (?k ffi r.
      evaluate_prog_with_clock st env k prog = (ffi,r) ∧
      (case r of
       | Rerr (Rabort (Rffi_error outcome')) =>
         outcome = FFI_outcome (outcome')
       | r => r ≠ Rerr (Rabort Rtimeout_error) ∧ outcome = Success) ∧
      (io_list = ffi.io_events) ∧
      (r ≠ Rerr (Rabort Rtype_error)))) ∧
  (semantics_prog st env prog (Diverge io_trace) ⇔
    (* for all clocks, evaluation times out *)
    (!k. ?ffi.
      (evaluate_prog_with_clock st env k prog =
          (ffi, Rerr (Rabort Rtimeout_error)))) ∧
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
      SND(evaluate_prog_with_clock st env k prog) = Rerr (Rabort Rtype_error))
End

Datatype:
  semantics = CannotParse | IllTyped | Execute (behaviour set)
End

Definition semantics_def:
  semantics state prelude input =
    case parse (lexer_fun input) of
    | NONE => CannotParse
    | SOME prog =>
      if can_type_prog state (prelude ++ prog)
      then Execute (semantics_prog state.sem_st state.sem_env (prelude ++ prog))
      else IllTyped
End

Definition semantics_init_def:
  semantics_init ffi =
    semantics <| sem_st := FST (THE (prim_sem_env ffi));
                 sem_env := SND(THE (prim_sem_env ffi));
                 tenv := prim_tenv;
                 type_ids := prim_type_ids |>
End

