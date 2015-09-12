open HolKernel boolLib bossLib Parse;
open lexer_funTheory printTheory initialProgramTheory gramTheory cmlPtreeConversionTheory;
open ffiTheory simpleIOTheory;
open terminationTheory;
open pathTheory;

val _ = new_theory "standalone";

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
evaluate_prog_with_io prog state io k =
  evaluate_prog prog 
                (state.sem_env.sem_envM, state.sem_env.sem_envC, state.sem_env.sem_envE)
                ((<| clock := k; 
                     refs := FST (SND (FST state.sem_env.sem_store)); 
                     io := io |>,
                  FST (SND state.sem_env.sem_store)),
                 SND (SND state.sem_env.sem_store))`;

val sem_def = Define `
(sem state prog (Terminate io_list) ⇔
  can_type_prog state prog ∧
  ?k state' r envC.
    r ≠ Rerr (Rabort Rtimeout_error) ∧
    evaluate_prog_with_io prog state (SOME (fromList io_list)) k = (r, envC, state') ∧
    (FST (FST state')).io = SOME LNIL) ∧
(sem state prog (Diverge io_trace) ⇔
  can_type_prog state prog ∧
  (!k. ?state' envC.
    (evaluate_prog_with_io prog state (SOME io_trace) k = 
        (Rerr (Rabort Rtimeout_error), envC, state')) ∧
     IS_SOME (FST (FST state')).io) ∧
     (* for every proper prefix of the I/O trace: evaluate causes the
        I/O component to disagree with the given I/O trace prefix *)
   (!io. LPREFIX io io_trace ∧ io ≠ io_trace ⇒
      ?k. ((FST (FST (SND (SND (evaluate_prog_with_io prog state (SOME io) k))))).io = NONE))) ∧
(sem state prog Fail ⇔
  ¬(can_type_prog state prog))`;

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

val _ = export_theory();
