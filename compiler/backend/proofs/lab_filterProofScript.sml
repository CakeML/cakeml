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
  state_rel (s1:('a,'ffi) labSem$state) t1 =
    (s1 = t1 with <| code := filter_skip t1.code ;
                     pc := adjust_pc t1.pc t1.code |>)`

val filter_correct = prove(
  ``!(s1:('a,'ffi) labSem$state) t1 res s2.
      (evaluate s1 = (res,s2)) /\ state_rel s1 t1 ==>
      ?t2 k.
        (evaluate (t1 with clock := s1.clock + k) = (res,t2)) /\
        (s2.ffi = t2.ffi)``,
  cheat);

val state_rel_IMP_sem_EQ_sem = prove(
  ``!s t. state_rel s t ==> semantics s = semantics t``,
  rw[] >> simp[FUN_EQ_THM]
  \\ reverse Cases
  \\ fs [labSemTheory.semantics_def]
  \\ rpt strip_tac
  THEN1 (* Fail *)
   (eq_tac \\ rpt strip_tac THEN1
     (Cases_on `evaluate (s with clock := k)`
      \\ fs [] \\ rw []
      \\ `state_rel (s with clock := k) (t with clock := k)` by
            (fs [state_rel_def,state_component_equality])
      \\ imp_res_tac filter_correct \\ fs [] \\ rfs[]
      \\ Q.LIST_EXISTS_TAC [`k+k'`] \\ fs [])
    \\ Cases_on `evaluate (t with clock := k)`
    \\ fs [] \\ rw [] \\ CCONTR_TAC \\ fs []
    \\ pop_assum (mp_tac o Q.SPECL [`k`]) \\ rpt strip_tac
    \\ Cases_on `evaluate (s with clock := k)`
    \\ fs []
    \\ `state_rel (s with clock := k) (t with clock := k)` by
          (fs [state_rel_def,state_component_equality])
    \\ imp_res_tac filter_correct \\ fs [] \\ rfs[]
    \\ imp_res_tac evaluate_ADD_clock \\ fs [])
  THEN1 (* Terminate *)
   (eq_tac \\ rpt strip_tac
    THEN1
     (Cases_on `evaluate (s with clock := k)`
      \\ fs [] \\ rw []
      \\ `state_rel (s with clock := k) (t with clock := k)` by
            (fs [state_rel_def,state_component_equality])
      \\ imp_res_tac filter_correct \\ fs [] \\ rw [] \\ fs []
      \\ Q.LIST_EXISTS_TAC [`k+k'`] \\ fs []
      \\ BasicProvers.CASE_TAC >> fs[]
      \\ cheat)
    \\ CCONTR_TAC \\ fs []
    \\ pop_assum (mp_tac o Q.SPECL [`k`]) \\ rpt strip_tac
    \\ `state_rel (s with <| clock := k|>) (t with <| clock := k|>)` by
            (fs [state_rel_def,state_component_equality])
    \\ Cases_on `evaluate (s with <| clock := k|>)`
    \\ fs [] \\ imp_res_tac filter_correct \\ fs [] \\ rfs[]
    \\ imp_res_tac evaluate_ADD_clock \\ fs []
    \\ every_case_tac >> fs[] >> rw[] >> fs[]
    \\ cheat)
  THEN1 (* Diverge *) cheat);

val filter_skip_semantics = store_thm("filter_skip_semantics",
  ``!s. (s.pc = 0) ==> semantics (s with code := filter_skip s.code) = semantics s``,
  rpt strip_tac \\ match_mp_tac state_rel_IMP_sem_EQ_sem
  \\ fs [state_rel_def,state_component_equality,Once adjust_pc_def]);

val _ = export_theory();
