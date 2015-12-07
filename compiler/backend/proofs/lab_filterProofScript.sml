open preamble labSemTheory labPropsTheory lab_filterTheory;
open BasicProvers

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

(*All skips for the next k*)
val all_skips_def = Define`
  all_skips pc code k ⇔
  ∀i. i < k ⇒
    ∃x y.
    asm_fetch_aux (pc+i) code = SOME(Asm (Inst Skip) x y)`

val is_Label_not_skip = prove(``
  is_Label y ⇒ not_skip y``,
  Cases_on`y`>>fs[is_Label_def,not_skip_def])

(*
Proof plan:
1)
For any pc, code,
there exists a k such that
asmfetch (pc+k) code = asmfetch (adjust pc) (adjust code)
and
for all i < k
  asmfetch (pc+i) code = Skip

2)
for all i < k.
  asmfetch(pc+i) code = Skip
⇒
evaluate pc code with k for a clock = evaluate (pc+k) code

*)

(* 1)
There is probably a neater way to prove this*)
val asm_fetch_aux_eq = prove(``
  ∀pc code.
  ∃k.
    asm_fetch_aux (pc+k) code = asm_fetch_aux (adjust_pc pc code) (filter_skip code) ∧
    all_skips pc code k``,
  Induct_on`code`
  >-
    (simp[Once adjust_pc_def,filter_skip_def,asm_fetch_aux_def,all_skips_def]>>
    qexists_tac`0`>>DECIDE_TAC)
  >>
  Induct_on`h`>>Induct_on`l`>>fs[]>>rw[]
  >-
    (Cases_on`pc=0`>>simp[asm_fetch_aux_def,Once adjust_pc_def,filter_skip_def]
    >-
      (first_x_assum(qspec_then`0`assume_tac)>>
      fs[all_skips_def,asm_fetch_aux_def]>>
      qexists_tac`k`>>fs[Once adjust_pc_def])
    >>
      fs[all_skips_def]>>simp[Once asm_fetch_aux_def]>>
      metis_tac[DECIDE``A +B = B+A:num``])
  >>
  Cases_on`pc=0`
  >-
    (Cases_on`h`>>fs[asm_fetch_aux_def,is_Label_def,filter_skip_def,not_skip_def,all_skips_def]
    >-
      (first_x_assum(qspecl_then[`n`,`0`] assume_tac)>>
      fs[]>>
      qexists_tac`k`>>ntac 2 (simp[Once adjust_pc_def]))
    >-
      (first_x_assum(qspecl_then[`n`,`0`] assume_tac)>>
      fs[]>>
      EVERY_CASE_TAC>>fs[]
      >-
        (qexists_tac`k+1`>>ntac 2 (simp[Once adjust_pc_def])>>
        rw[]>>
        `i-1<k` by DECIDE_TAC>>
        metis_tac[])
      >>
      qexists_tac`0`>>fs[]>>
      simp[Once adjust_pc_def]>>
      simp[Once asm_fetch_aux_def,SimpRHS,is_Label_def])
    >-
      (qexists_tac`0`>>fs[]>>
      simp[Once adjust_pc_def]))
  >>
  Cases_on`h`>>
  simp[Once adjust_pc_def]>>
  fs[asm_fetch_aux_def,is_Label_def,filter_skip_def,not_skip_def,all_skips_def]
  >-
    metis_tac[DECIDE``A+B = B+A:num``]
  >>
    (EVERY_CASE_TAC>>fs[]>>
    simp[Once asm_fetch_aux_def,SimpRHS,is_Label_def]>>
    first_x_assum(qspecl_then[`n`,`pc-1`] assume_tac)>>fs[]>>
    `∀x. pc - 1 + x = pc + x -1` by DECIDE_TAC>>
    `∀x. pc - 1 + x = x + pc -1` by DECIDE_TAC>>
    metis_tac[]))

(*For any adjusted fetch, the original fetch is either equal or is a skip
This is probably the wrong direction*)
val asm_fetch_not_skip_adjust_pc = prove(
  ``∀pc code inst.
  (∀x y.asm_fetch_aux pc code ≠ SOME (Asm (Inst Skip) x y)) ⇒
  asm_fetch_aux pc code = asm_fetch_aux (adjust_pc pc code) (filter_skip code)``,
  ho_match_mp_tac asm_fetch_aux_ind>>rw[]
  >-
    simp[asm_fetch_aux_def,filter_skip_def]
  >-
    (fs[asm_fetch_aux_def,filter_skip_def]>>
    simp[Once adjust_pc_def,SimpRHS]>>
    IF_CASES_TAC>>
    metis_tac[adjust_pc_def])
  >>
  Cases_on`is_Label y`>>fs[]
  >-
    (fs[asm_fetch_aux_def,filter_skip_def]>>
    simp[Once adjust_pc_def,SimpRHS]>>
    simp[is_Label_not_skip]>>
    IF_CASES_TAC>>
    res_tac>>fs[]>>
    simp[asm_fetch_aux_def]>>
    simp[Once adjust_pc_def])
  >>
  reverse(Cases_on`pc ≠ 0`>>fs[])
  >-
    (fs[asm_fetch_aux_def,Once adjust_pc_def,filter_skip_def,not_skip_def]>>
    EVERY_CASE_TAC>>
    fs[asm_fetch_aux_def,is_Label_def])
  >>
    fs[Once asm_fetch_aux_def]>>
    simp[Once adjust_pc_def,SimpRHS]>>
    IF_CASES_TAC>>fs[filter_skip_def]>>
    simp[asm_fetch_aux_def])

val state_rw = prove(``
  s with clock := s.clock = s ∧
  s with pc := s.pc = s``,
  fs[state_component_equality])

(* 2) all_skips allow swapping pc for clock*)
val all_skips_evaluate = prove(``
  ∀k s.
  all_skips s.pc s.code k ⇒
  evaluate (s with clock:= s.clock +k) =
  evaluate (s with pc := s.pc +k)``,
  Induct>>fs[all_skips_def]
  >-
    metis_tac[state_rw]
  >>
    rw[]>>first_assum(qspec_then`0` mp_tac)>>
    discharge_hyps>-
      fs[]>>
    strip_tac>>fs[]>>
    simp[Once evaluate_def,asm_fetch_def,asm_inst_def]>>
    (*?*)
    `¬s.failed` by cheat >>
    fs[inc_pc_def,dec_clock_def]>>
    fs[arithmeticTheory.ADD1]>>
    `k+1 + s.clock -1 = s.clock+k` by DECIDE_TAC>>
    fs[]>>
    first_x_assum(qspec_then `s with <|pc:=s.pc+1|>` mp_tac)>>
    discharge_hyps>-
      (rw[]>>first_x_assum(qspec_then`1+i` assume_tac)>>rfs[]>>
      fs[arithmeticTheory.ADD_ASSOC])
    >>
    fs[]>>
    `s.pc +1 + k = k +1 + s.pc` by DECIDE_TAC>>
    fs[])

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
  ho_match_mp_tac evaluate_ind>>rw[]>>
  qpat_assum`evaluate s1 = A` mp_tac>>
  simp[Once evaluate_def]>>
  IF_CASES_TAC>-
    (simp[Once evaluate_def]>>
    strip_tac>>qexists_tac`t1 with clock:=0`>>
    qexists_tac`0`>>
    fs[state_rel_def])>>
  Cases_on`asm_fetch s1`>>fs[]>-
    (*t1 must not be fetched either*)
    cheat
  >>
 cheat);

(*Broken*)
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
     (`state_rel (s with clock := k) (t with clock := k)` by
            (fs [state_rel_def,state_component_equality])
      \\ imp_res_tac filter_correct \\ fs [] \\ rw [] \\ fs []
      \\ Q.LIST_EXISTS_TAC [`k+k'`] \\ fs [])
    \\ CCONTR_TAC \\ fs []
    \\ pop_assum (mp_tac o Q.SPECL [`k`]) \\ rpt strip_tac
    \\ `state_rel (s with <| clock := k|>) (t with <| clock := k|>)` by
            (fs [state_rel_def,state_component_equality])
    \\ fs [] \\ imp_res_tac filter_correct \\ fs [] \\ rfs[]
    \\ Cases_on `evaluate (s with clock := k)` \\ fs []
    \\ imp_res_tac evaluate_ADD_clock \\ fs []
    \\ Cases_on `o'` \\ fs [] \\ rw [] \\ fs []
    \\ cheat)
  THEN1 (* Diverge *) cheat);

val filter_skip_semantics = store_thm("filter_skip_semantics",
  ``!s. (s.pc = 0) ==>
        semantics (s with code := filter_skip s.code) = semantics s``,
  rpt strip_tac \\ match_mp_tac state_rel_IMP_sem_EQ_sem
  \\ fs [state_rel_def,state_component_equality,Once adjust_pc_def]);

val _ = export_theory();
