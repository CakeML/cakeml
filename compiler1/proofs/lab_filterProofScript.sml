open preamble labSemTheory labPropsTheory lab_filterTheory;

val _ = new_theory "lab_filterProof";

val adjust_pc_def = Define `
  adjust_pc p xs =
    if p = 0n then 0n else
      case xs of
      | [] => 0
      | (Section n [] :: rest) => adjust_pc p rest
      | (Section n (l::lines) :: rest) =>
          if is_Label l then
            adjust_pc p (Section n lines :: rest)
          else if not_skip l then
            adjust_pc (p-1) (Section n lines :: rest) + 1
          else adjust_pc (p-1) (Section n lines :: rest)`

val state_rel_def = Define `
  state_rel (s1:'a labSem$state) t1 =
    (s1 = t1 with <| code := filter_skip t1.code ;
                     pc := adjust_pc t1.pc t1.code |>)`

val filter_correct = prove(
  ``!(s1:'a labSem$state) t1 res s2.
      (evaluate s1 = (res,s2)) /\ state_rel s1 t1 ==>
      ?t2 k.
        (evaluate (t1 with clock := s1.clock + k) = (res,t2)) /\
        (s2.io_events = t2.io_events)``,
  cheat);

val state_rel_IMP_sem_EQ_sem = prove(
  ``!s t. state_rel s t ==> sem s = sem t``,
  fs [labSemTheory.sem_def] \\ rpt strip_tac
  \\ fs [FUN_EQ_THM] \\ reverse Cases
  \\ fs [labSemTheory.sem_def,evaluate_with_io_def]
  \\ rpt strip_tac
  THEN1 (* Fail *)
   (eq_tac \\ rpt strip_tac THEN1
     (Cases_on `evaluate (s with <|io_events := SOME io; clock := k|>)`
      \\ fs [] \\ rw []
      \\ `state_rel (s with <|io_events := SOME io; clock := k|>)
           (t with <|io_events := SOME io; clock := k|>)` by
            (fs [state_rel_def,state_component_equality])
      \\ imp_res_tac filter_correct \\ fs [] \\ rfs[]
      \\ Q.LIST_EXISTS_TAC [`k+k'`,`io`] \\ fs [])
    \\ Cases_on `evaluate (t with <|io_events := SOME io; clock := k|>)`
    \\ fs [] \\ rw [] \\ CCONTR_TAC \\ fs []
    \\ pop_assum (mp_tac o Q.SPECL [`k`,`io`]) \\ rpt strip_tac
    \\ Cases_on `evaluate (s with <|io_events := SOME io; clock := k|>)`
    \\ fs []
    \\ `state_rel (s with <|io_events := SOME io; clock := k|>)
         (t with <|io_events := SOME io; clock := k|>)` by
          (fs [state_rel_def,state_component_equality])
    \\ imp_res_tac filter_correct \\ fs [] \\ rfs[]
    \\ imp_res_tac evaluate_ADD_clock \\ fs [])
  THEN1 (* Terminate *)
   (qabbrev_tac `io = llist$fromList (l:io_event list)`
    \\ eq_tac \\ rpt strip_tac
    THEN1
     (Cases_on `evaluate (s with <|io_events := SOME io; clock := k|>)`
      \\ fs [] \\ rw []
      \\ `state_rel (s with <|io_events := SOME io; clock := k|>)
           (t with <|io_events := SOME io; clock := k|>)` by
            (fs [state_rel_def,state_component_equality])
      \\ imp_res_tac filter_correct \\ fs [] \\ rw [] \\ fs []
      \\ Q.LIST_EXISTS_TAC [`k+k'`] \\ fs [])
    \\ CCONTR_TAC \\ fs []
    \\ pop_assum (mp_tac o Q.SPECL [`k`]) \\ rpt strip_tac
    \\ `state_rel (s with <|io_events := SOME io; clock := k|>)
         (t with <|io_events := SOME io; clock := k|>)` by
            (fs [state_rel_def,state_component_equality])
    \\ Cases_on `evaluate (s with <|io_events := SOME io; clock := k|>)`
    \\ fs [] \\ imp_res_tac filter_correct \\ fs [] \\ rfs[]
    \\ imp_res_tac evaluate_ADD_clock \\ fs [])
  THEN1 (* Diverge *) cheat);

val filter_skip_sem = store_thm("filter_skip_sem",
  ``!s. (s.pc = 0) ==> sem (s with code := filter_skip s.code) = sem s``,
  rpt strip_tac \\ match_mp_tac state_rel_IMP_sem_EQ_sem
  \\ fs [state_rel_def,state_component_equality,Once adjust_pc_def]);

val _ = export_theory();
