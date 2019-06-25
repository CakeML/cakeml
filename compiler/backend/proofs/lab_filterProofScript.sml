(*
  Correctness proof for lab_filter
*)
open preamble labSemTheory labPropsTheory lab_filterTheory;

val _ = new_theory "lab_filterProof";

val adjust_pc_def = Define `
  adjust_pc p xs =
    if p = 0n then 0n else
      case xs of
      | [] => p
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
  (∀x y. asm_fetch_aux (pc+k) code ≠ SOME(Asm (Asmi(Inst Skip)) x y)) ∧
  ∀i. i < k ⇒
    ∃x y.
    asm_fetch_aux (pc+i) code = SOME(Asm (Asmi(Inst Skip)) x y)`

val is_Label_not_skip = Q.prove(`
  is_Label y ⇒ not_skip y`,
  Cases_on`y`>>full_simp_tac(srw_ss())[is_Label_def,not_skip_def])

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
val asm_fetch_aux_eq = Q.prove(`
  ∀pc code.
  ∃k.
    asm_fetch_aux (pc+k) code = asm_fetch_aux (adjust_pc pc code) (filter_skip code) ∧
    all_skips pc code k`,
  Induct_on`code`
  >-
    (simp[Once adjust_pc_def,filter_skip_def,asm_fetch_aux_def,all_skips_def]>>
    qexists_tac`0`>>DECIDE_TAC)
  >>
  Induct_on`h`>>Induct_on`l`>>full_simp_tac(srw_ss())[]>>srw_tac[][]
  >-
    (Cases_on`pc=0`>>simp[asm_fetch_aux_def,Once adjust_pc_def,filter_skip_def]
    >-
      (first_x_assum(qspec_then`0`assume_tac)>>
      full_simp_tac(srw_ss())[all_skips_def,asm_fetch_aux_def]>>
      qexists_tac`k`>>full_simp_tac(srw_ss())[Once adjust_pc_def])
    >>
      full_simp_tac(srw_ss())[all_skips_def]>>full_simp_tac(srw_ss())[Once asm_fetch_aux_def]>>
      first_x_assum(qspec_then`pc` assume_tac)>>full_simp_tac(srw_ss())[]>>
      metis_tac[ADD_COMM,asm_fetch_aux_def])
  >>
  Cases_on`pc=0`
  >-
    (Cases_on`h`>>full_simp_tac(srw_ss())[asm_fetch_aux_def,is_Label_def,filter_skip_def,not_skip_def,all_skips_def]
    >-
      (first_x_assum(qspecl_then[`n`,`0`] assume_tac)>>
      full_simp_tac(srw_ss())[]>>
      qexists_tac`k`>>ntac 2 (simp[Once adjust_pc_def]))
    >-
      (first_x_assum(qspecl_then[`n`,`0`] assume_tac)>>
      full_simp_tac(srw_ss())[]>>
      EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
      full_simp_tac(srw_ss())[Once adjust_pc_def,asm_fetch_aux_def]
      >-
        (qexists_tac`k+1`>>rev_full_simp_tac(srw_ss())[]>>srw_tac[][]>>
        `i-1<k` by DECIDE_TAC>>
        metis_tac[])
      >>
      qexists_tac`0`>>full_simp_tac(srw_ss())[]>>
      simp[Once adjust_pc_def]>>
      simp[Once asm_fetch_aux_def,SimpRHS,is_Label_def])
    >-
      (qexists_tac`0`>>full_simp_tac(srw_ss())[is_Label_def]>>
      simp[Once adjust_pc_def]))
  >>
  Cases_on`h`>>
  simp[Once adjust_pc_def]>>
  full_simp_tac(srw_ss())[asm_fetch_aux_def,is_Label_def,filter_skip_def,not_skip_def,all_skips_def]
  >-
    metis_tac[ADD_COMM]
  >>
    (EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
    simp[Once asm_fetch_aux_def,SimpRHS,is_Label_def]>>
    first_x_assum(qspecl_then[`n`,`pc-1`] assume_tac)>>full_simp_tac(srw_ss())[]>>
    `∀x. pc - 1 + x = pc + x -1` by DECIDE_TAC>>
    `∀x. pc - 1 + x = x + pc -1` by DECIDE_TAC>>
    metis_tac[]))

(*For any adjusted fetch, the original fetch is either equal or is a skip
This is probably the wrong direction*)
val asm_fetch_not_skip_adjust_pc = Q.prove(
  `∀pc code inst.
  (∀x y.asm_fetch_aux pc code ≠ SOME (Asm (Asmi(Inst Skip)) x y)) ⇒
  asm_fetch_aux pc code = asm_fetch_aux (adjust_pc pc code) (filter_skip code)`,
  ho_match_mp_tac asm_fetch_aux_ind>>srw_tac[][]
  >-
    simp[asm_fetch_aux_def,filter_skip_def]
  >-
    (full_simp_tac(srw_ss())[asm_fetch_aux_def,filter_skip_def]>>
    simp[Once adjust_pc_def,SimpRHS]>>
    IF_CASES_TAC>>
    metis_tac[adjust_pc_def])
  >>
  Cases_on`is_Label y`>>full_simp_tac(srw_ss())[]
  >-
    (full_simp_tac(srw_ss())[asm_fetch_aux_def,filter_skip_def]>>
    simp[Once adjust_pc_def,SimpRHS]>>
    simp[is_Label_not_skip]>>
    IF_CASES_TAC>>
    res_tac>>full_simp_tac(srw_ss())[]>>
    simp[asm_fetch_aux_def]>>
    simp[Once adjust_pc_def])
  >>
  reverse(Cases_on`pc ≠ 0`>>full_simp_tac(srw_ss())[])
  >-
    (full_simp_tac(srw_ss())[asm_fetch_aux_def,Once adjust_pc_def,filter_skip_def,not_skip_def]>>
    EVERY_CASE_TAC>>
    full_simp_tac(srw_ss())[asm_fetch_aux_def,is_Label_def])
  >>
    full_simp_tac(srw_ss())[Once asm_fetch_aux_def]>>
    simp[Once adjust_pc_def,SimpRHS]>>
    IF_CASES_TAC>>full_simp_tac(srw_ss())[filter_skip_def]>>
    simp[asm_fetch_aux_def]);

val state_rw = Q.prove(`
  s with clock := s.clock = s ∧
  s with pc := s.pc = s ∧
  s with <|pc := s.pc; clock:= s.clock+k'|> = s with clock:=s.clock+k'`,
  full_simp_tac(srw_ss())[state_component_equality])

(* 2) all_skips allow swapping pc for clock*)
val all_skips_evaluate = Q.prove(`
  ∀k s.
  all_skips s.pc s.code k ∧
  ¬s.failed ⇒
  ∀k'.
  evaluate (s with clock:= s.clock +k' + k) =
  evaluate (s with <|pc := s.pc +k; clock:= s.clock +k'|>)`,
  Induct>>full_simp_tac(srw_ss())[all_skips_def]
  >-
    metis_tac[state_rw]
  >>
    srw_tac[][]>>first_assum(qspec_then`0` mp_tac)>>
    impl_tac>-
      full_simp_tac(srw_ss())[]>>
    strip_tac>>full_simp_tac(srw_ss())[]>>
    simp[Once evaluate_def,asm_fetch_def,asm_inst_def]>>
    full_simp_tac(srw_ss())[inc_pc_def,dec_clock_def]>>
    full_simp_tac(srw_ss())[arithmeticTheory.ADD1]>>
    `k' + (k+1 + s.clock) -1 = k' + s.clock+k` by DECIDE_TAC>>
    full_simp_tac(srw_ss())[]>>
    first_x_assum(qspec_then `s with <|pc:=s.pc+1;clock:=k'+s.clock|>` mp_tac)>>
    impl_tac>-
      (srw_tac[][]>>first_x_assum(qspec_then`i+1` assume_tac)>>rev_full_simp_tac(srw_ss())[]>>
      metis_tac[arithmeticTheory.ADD_COMM,ADD_ASSOC])>>
    srw_tac[][]>>first_x_assum(qspec_then`0` assume_tac)>>rev_full_simp_tac(srw_ss())[]>>
    metis_tac[arithmeticTheory.ADD_COMM,ADD_ASSOC])

val state_rel_def = Define `
  state_rel (s1:('a,'c,'ffi) labSem$state) t1 ⇔
    (∃s1compile.
     s1 = t1 with <| code := filter_skip t1.code ;
                     pc := adjust_pc t1.pc t1.code ;
                     compile_oracle := λn. (λ(a,b).(a,filter_skip b)) (t1.compile_oracle n);
                     compile := s1compile
                     |> ∧
    t1.compile = λc p. s1compile c (filter_skip p)  ) ∧
    ¬t1.failed`

val adjust_pc_all_skips = Q.prove(`
  ∀k pc code.
  all_skips pc code k ⇒
  adjust_pc pc code +1 = adjust_pc (pc+k+1) code`,
  Induct>>full_simp_tac(srw_ss())[all_skips_def]>>simp[]>>
  ho_match_mp_tac asm_fetch_aux_ind
  >>
  full_simp_tac(srw_ss())[asm_fetch_aux_def]>>srw_tac[][]>>simp[Once adjust_pc_def,SimpRHS]>>
  simp[Once adjust_pc_def]>>
  TRY (IF_CASES_TAC>>full_simp_tac(srw_ss())[not_skip_def]>>
      full_simp_tac(srw_ss())[Once adjust_pc_def]>>
      pop_assum mp_tac >> EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>NO_TAC)
  >-
    (IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
    `pc - 1 + 1 = pc` by DECIDE_TAC>>
    full_simp_tac(srw_ss())[])
  >-
    (pop_assum(qspec_then`k` mp_tac)>>full_simp_tac(srw_ss())[])
  >>
    full_simp_tac(srw_ss())[arithmeticTheory.ADD1]>>Cases_on`pc=0`
    >-
      (first_assum(qspec_then`0` mp_tac)>>
      full_simp_tac(srw_ss())[]>>impl_tac>-DECIDE_TAC>>strip_tac>>
      full_simp_tac(srw_ss())[not_skip_def]>>
      first_x_assum(qspecl_then[`0`,`Section k' ys::xs`]mp_tac)>>impl_tac>-
      (full_simp_tac(srw_ss())[]>>srw_tac[][]>>
      first_x_assum(qspec_then`i+1` mp_tac)>>impl_tac>-DECIDE_TAC>>
      srw_tac[][])>>
      full_simp_tac(srw_ss())[Once adjust_pc_def])
    >>
    full_simp_tac(srw_ss())[]>>IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
    `pc -1 + (k+1 +1) = pc +(k+1)` by DECIDE_TAC>>
    `pc -1 + (k+1) = pc + k` by DECIDE_TAC>>
    `pc  + (k+1) -1 = pc + k` by DECIDE_TAC>>
    `!i. i+(pc-1) = i+pc -1` by DECIDE_TAC>>
    full_simp_tac(srw_ss())[]>>
    first_assum match_mp_tac>>full_simp_tac(srw_ss())[]>>
    full_simp_tac(srw_ss())[]);

val asm_fetch_aux_eq2 = Q.prove(
`asm_fetch_aux (adjust_pc pc code) (filter_skip code) = x ⇒
  ∃k.
  asm_fetch_aux (pc+k) code = x ∧
  all_skips pc code k`,
  metis_tac[asm_fetch_aux_eq]);

val all_skips_evaluate_0 = all_skips_evaluate |>SIMP_RULE std_ss [PULL_FORALL]|>(Q.SPECL[`k`,`s`,`0`])|>GEN_ALL|>SIMP_RULE std_ss[]

val all_skips_evaluate_rw = Q.prove(`
  all_skips s.pc s.code k ∧ ¬s.failed ∧
  s.clock = clk + k ∧
  t = s with <| pc:= s.pc +k ; clock := clk |> ⇒
  evaluate s = evaluate t`,
  srw_tac[][]>>
  qabbrev_tac`s' = s with clock := clk`>>
  `s = s' with clock := s'.clock +k` by
    full_simp_tac(srw_ss())[Abbr`s'`,state_component_equality]>>
  `s' with pc := s.pc +k =
   s' with <| pc := s'.pc +k ; clock := s'.clock|>` by full_simp_tac(srw_ss())[state_component_equality]>>
   ntac 2 (pop_assum SUBST_ALL_TAC)>>
   match_mp_tac all_skips_evaluate_0>>
   full_simp_tac(srw_ss())[state_component_equality])

(*For all initial code there is some all_skips*)
val all_skips_initial_adjust = Q.prove(`
  ∀code.
  ∃k. all_skips 0 code k ∧ adjust_pc k code = 0`,
  Induct>>full_simp_tac(srw_ss())[all_skips_def]
  >-
    (qexists_tac`0`>>full_simp_tac(srw_ss())[adjust_pc_def,asm_fetch_aux_def])
  >>
  Induct>>Induct_on`l`>>srw_tac[][]
  >-
    (simp[Once adjust_pc_def]>>
    qexists_tac`k`>>full_simp_tac(srw_ss())[asm_fetch_aux_def])
  >>
    pop_assum(qspec_then`n` assume_tac)>>full_simp_tac(srw_ss())[]>>
    Cases_on`h`>>
    simp[Once adjust_pc_def,asm_fetch_aux_def,is_Label_def,not_skip_def]
    >-
      (qexists_tac`k'`>>full_simp_tac(srw_ss())[])
    >-
      (Cases_on`a=Asmi(Inst Skip)`>>full_simp_tac(srw_ss())[]
      >-
        (qexists_tac`k'+1`>>srw_tac[][]>>
        `i-1 < k'` by DECIDE_TAC>>
        metis_tac[])
      >> (qexists_tac`0`>>full_simp_tac(srw_ss())[]))
    >> (qexists_tac`0`>>full_simp_tac(srw_ss())[]));

(*May need strengthening*)
val loc_to_pc_eq_NONE = Q.prove(`
  ∀n1 n2 code.
  loc_to_pc n1 n2 (filter_skip code) = NONE ⇒
  loc_to_pc n1 n2 code = NONE`,
  ho_match_mp_tac loc_to_pc_ind>>srw_tac[][]>>
  full_simp_tac(srw_ss())[filter_skip_def]>>
  full_simp_tac(srw_ss())[Once loc_to_pc_def]>>IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
  FULL_CASE_TAC>>full_simp_tac(srw_ss())[]>>rev_full_simp_tac(srw_ss())[]>>
  IF_CASES_TAC>>
  full_simp_tac(srw_ss())[]>>
  TRY
    (qpat_x_assum`_=NONE` mp_tac>>
    IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
    IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
    simp[Once loc_to_pc_def]>>
    EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>NO_TAC)>>
  full_simp_tac(srw_ss())[not_skip_def])

val loc_to_pc_eq_SOME = Q.prove(`
  ∀n1 n2 code pc.
  loc_to_pc n1 n2 (filter_skip code) = SOME pc ⇒
  ∃pc'.
  loc_to_pc n1 n2 code = SOME pc' ∧
  adjust_pc pc' code = pc`,
  ho_match_mp_tac loc_to_pc_ind>>srw_tac[][]
  >-
    (full_simp_tac(srw_ss())[filter_skip_def,adjust_pc_def]>>
    IF_CASES_TAC>>full_simp_tac(srw_ss())[])
  >>
  full_simp_tac(srw_ss())[Once loc_to_pc_def]>>IF_CASES_TAC>>full_simp_tac(srw_ss())[]
  >-
    (full_simp_tac(srw_ss())[filter_skip_def,Once loc_to_pc_def]>>
    full_simp_tac(srw_ss())[Once adjust_pc_def])
  >>
    (FULL_CASE_TAC>>full_simp_tac(srw_ss())[filter_skip_def,Once loc_to_pc_def]>>rev_full_simp_tac(srw_ss())[]
    >-
      (full_simp_tac(srw_ss())[Once adjust_pc_def]>>
      IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
      simp[Once adjust_pc_def])
    >>
    IF_CASES_TAC>>full_simp_tac(srw_ss())[]
    >-
      (full_simp_tac(srw_ss())[not_skip_def]>>
      qpat_x_assum`_=pc` sym_sub_tac>>
      full_simp_tac(srw_ss())[Once adjust_pc_def])
    >>
      (IF_CASES_TAC>>full_simp_tac(srw_ss())[]
      >-
        (Cases_on`not_skip h`>>qpat_x_assum`_=SOME pc` mp_tac>>
        TRY(`not_skip h` by (full_simp_tac(srw_ss())[]>>NO_TAC)>>
          simp[Once loc_to_pc_def,SimpLHS])>>
        srw_tac[][]>>
        (last_x_assum(qspec_then`pc` mp_tac)>>
        impl_tac>-
          (EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
          DECIDE_TAC)>>
        srw_tac[][]>>
        simp[Once loc_to_pc_def]>>
        simp[Once adjust_pc_def]>>IF_CASES_TAC>>
        full_simp_tac(srw_ss())[]>>full_simp_tac(srw_ss())[Once adjust_pc_def]))
      >>
      Cases_on`not_skip h`>>qpat_x_assum`_=SOME pc` mp_tac
      >-
        (simp[]>>simp[Once loc_to_pc_def,SimpLHS]>>
        srw_tac[][]>>
        last_x_assum(qspec_then`pc-1` mp_tac)>>
        impl_tac>-
          (EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
          DECIDE_TAC)>>
        srw_tac[][]>>
        simp[Once loc_to_pc_def]>>
        `pc ≠ 0` by
          (qpat_x_assum`_=SOME pc` mp_tac>>
          EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
          srw_tac[][]>>
          DECIDE_TAC)>>
        simp[Once adjust_pc_def]>>DECIDE_TAC)
      >>
        simp[]>>srw_tac[][]>>
        last_x_assum (qspec_then`pc` mp_tac)>>
        impl_tac>-
         (EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
          DECIDE_TAC)>>
        srw_tac[][]>>
        simp[Once loc_to_pc_def]>>
        simp[Once adjust_pc_def])));

val next_label_filter_skip = Q.prove(`
  ∀code.
  next_label code = next_label (filter_skip code)`,
  ho_match_mp_tac next_label_ind>>srw_tac[][]>>
  full_simp_tac(srw_ss())[next_label_def,filter_skip_def,not_skip_def]>>
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[next_label_def])

val all_skips_get_lab_after = Q.prove(`
  ∀code k.
  all_skips 0 code k ⇒
  get_lab_after k code =
  get_lab_after 0 (filter_skip code)`,
  Induct>>full_simp_tac(srw_ss())[get_lab_after_def,filter_skip_def]>>
  Induct>>Induct_on`l`>>srw_tac[][]>>full_simp_tac(srw_ss())[filter_skip_def,get_lab_after_def]
  >-
    (first_assum match_mp_tac>>full_simp_tac(srw_ss())[all_skips_def,asm_fetch_aux_def])
  >>
  IF_CASES_TAC>>full_simp_tac(srw_ss())[is_Label_not_skip]
  >-
    (simp[get_lab_after_def]>>
    first_assum match_mp_tac>>
    full_simp_tac(srw_ss())[all_skips_def,asm_fetch_aux_def])
  >>
  IF_CASES_TAC>>full_simp_tac(srw_ss())[]
  >-
    (`not_skip h` by
      (full_simp_tac(srw_ss())[all_skips_def,asm_fetch_aux_def]>>
      Cases_on`h`>>fs[not_skip_def]>>
      Cases_on`a`>>fs[]>>
      Cases_on`a'`>>fs[]>>
      Cases_on`i`>>fs[])>>
    full_simp_tac(srw_ss())[get_lab_after_def]>>
    mp_tac next_label_filter_skip>>
    disch_then(qspec_then`Section n l::code` assume_tac)>>
    full_simp_tac(srw_ss())[filter_skip_def])
  >>
    `¬not_skip h` by
      (full_simp_tac(srw_ss())[all_skips_def,asm_fetch_aux_def]>>
      first_x_assum(qspec_then`0` mp_tac)>>impl_tac>-
        DECIDE_TAC>>
      srw_tac[][]>>
      full_simp_tac(srw_ss())[not_skip_def])>>
    full_simp_tac(srw_ss())[]>>first_assum match_mp_tac>>
    full_simp_tac(srw_ss())[all_skips_def,asm_fetch_aux_def]>>srw_tac[][]>>
    `i+1 < k` by DECIDE_TAC>>
    res_tac>>
    full_simp_tac(srw_ss())[]);

val get_lab_after_adjust = Q.prove(`
  ∀pc code k.
  all_skips pc code k ⇒
  get_lab_after (pc+k) code = get_lab_after (adjust_pc pc code) (filter_skip code)`,
  ho_match_mp_tac get_lab_after_ind>>
  srw_tac[][]
  >-
    (simp[Once adjust_pc_def,filter_skip_def]>>
    IF_CASES_TAC>>full_simp_tac(srw_ss())[get_lab_after_def])
  >-
    (full_simp_tac(srw_ss())[filter_skip_def,get_lab_after_def]>>simp[Once adjust_pc_def]>>
    IF_CASES_TAC
    >-
      (full_simp_tac(srw_ss())[Once adjust_pc_def]>>
      first_assum match_mp_tac>>
      full_simp_tac(srw_ss())[all_skips_def,asm_fetch_aux_def])
    >>
      first_assum(qspec_then`k'` mp_tac)>>
      impl_tac>-
        full_simp_tac(srw_ss())[all_skips_def,asm_fetch_aux_def]
      >> simp[])
  >>
    Cases_on`is_Label y`>>full_simp_tac(srw_ss())[]
    >-
      (simp[get_lab_after_def,Once adjust_pc_def]>>
      `not_skip y` by
        (Cases_on`y`>>full_simp_tac(srw_ss())[is_Label_def,not_skip_def])>>
      full_simp_tac(srw_ss())[filter_skip_def,get_lab_after_def]>>
      IF_CASES_TAC
      >-
        (full_simp_tac(srw_ss())[Once adjust_pc_def]>>
        first_assum match_mp_tac>>
        full_simp_tac(srw_ss())[all_skips_def,asm_fetch_aux_def])
      >>
        first_assum(qspec_then`k'` mp_tac)>>
        impl_tac>-
          full_simp_tac(srw_ss())[all_skips_def,asm_fetch_aux_def]>>
        simp[])
    >>
      simp[Once adjust_pc_def]>>IF_CASES_TAC>>full_simp_tac(srw_ss())[]
      >-
        metis_tac[all_skips_get_lab_after]
      >>
      full_simp_tac(srw_ss())[get_lab_after_def]>>
      IF_CASES_TAC>>
      full_simp_tac(srw_ss())[filter_skip_def,get_lab_after_def]>>
      `∀x. x + pc -1 = pc -1 + x` by DECIDE_TAC>>
      full_simp_tac(srw_ss())[]>>
      first_assum match_mp_tac>>
      `∀x. pc + x -1 = pc -1 +x` by DECIDE_TAC>>
      full_simp_tac(srw_ss())[all_skips_def,asm_fetch_aux_def]);

val loc_to_pc_adjust_pc_append = Q.prove(`
  ∀n1 n2 code pc ls.
  loc_to_pc n1 n2 code = SOME pc ==>
  adjust_pc pc code = adjust_pc pc (code++ls)`,
  ho_match_mp_tac loc_to_pc_ind>>rw[]>>
  pop_assum mp_tac>>
  simp[Once loc_to_pc_def]>>
  IF_CASES_TAC>>fs[]
  >-
    (rw[Once adjust_pc_def]>>
    rw[Once adjust_pc_def])>>
  (TOP_CASE_TAC>>fs[]
  >-
    (simp[Once adjust_pc_def]>>
    simp[Once adjust_pc_def,SimpRHS]>>
    metis_tac[]))>>
  (IF_CASES_TAC>>fs[]
  >-
    (simp[Once adjust_pc_def]>>
    simp[Once adjust_pc_def,SimpRHS]>>
    metis_tac[]))>>
  (IF_CASES_TAC>>fs[]
  >-
    (simp[Once adjust_pc_def]>>
    simp[Once adjust_pc_def,SimpRHS]>>
    metis_tac[]))>>
  TOP_CASE_TAC>>
  fs[]>>
  simp[Once adjust_pc_def]>>
  simp[Once adjust_pc_def,SimpRHS]>>
  IF_CASES_TAC>>rw[]>>simp[])

val same_inst_tac =
  full_simp_tac(srw_ss())[asm_fetch_def,state_rel_def,state_component_equality]>>
  rev_full_simp_tac(srw_ss())[]>>
  imp_res_tac asm_fetch_aux_eq2>>
  imp_res_tac all_skips_evaluate_0>>
  srw_tac[][]>>qexists_tac`k`>>full_simp_tac(srw_ss())[]>>
  rev_full_simp_tac(srw_ss())[ADD_COMM]>>
  simp[Once evaluate_def,asm_fetch_def];

val upd_pc_tac =
  first_assum(qspec_then`0` assume_tac)>>full_simp_tac(srw_ss())[]>>
  qmatch_assum_abbrev_tac`evaluate aa = evaluate bb`>>
  first_x_assum(qspec_then`bb` mp_tac)>>
  impl_tac>-
  (simp[inc_pc_def,dec_clock_def,Abbr`bb`,state_component_equality])>>
  srw_tac[][Abbr`bb`]>>
  qexists_tac`k+k'`>>qexists_tac`t2`>>full_simp_tac(srw_ss())[]>>
  first_x_assum(qspec_then`k'` assume_tac)>>
  `k'+t1.clock-1 = k'+(t1.clock -1)` by DECIDE_TAC>>
  full_simp_tac(srw_ss())[]>>rev_full_simp_tac(srw_ss())[]>>
  metis_tac[arithmeticTheory.ADD_COMM,arithmeticTheory.ADD_ASSOC];

Theorem filter_correct:
   !(s1:('a,'c,'ffi) labSem$state) t1 res s2.
      (evaluate s1 = (res,s2)) /\ state_rel s1 t1 /\ ~t1.failed ==>
      ?k t2.
        (evaluate (t1 with clock := s1.clock + k) = (res,t2)) /\
        (s2.ffi = t2.ffi)
Proof
  ho_match_mp_tac evaluate_ind>>srw_tac[][]>>
  qpat_x_assum`evaluate s1 = _` mp_tac>>
  simp[Once evaluate_def]>>
  IF_CASES_TAC>-
    (simp[Once evaluate_def]>>
    strip_tac>>
    qexists_tac`0`>>
    qexists_tac`t1 with clock:=0`>>
    full_simp_tac(srw_ss())[state_rel_def])>>
  Cases_on`asm_fetch s1`>>full_simp_tac(srw_ss())[]>- same_inst_tac>>
  Cases_on`x`>>full_simp_tac(srw_ss())[] >- same_inst_tac
  >-
    (Cases_on`a`>>TRY(Cases_on`a'`)>>full_simp_tac(srw_ss())[]>>TRY(same_inst_tac>>NO_TAC)>>
    full_simp_tac(srw_ss())[asm_fetch_def,state_rel_def]>>rev_full_simp_tac(srw_ss())[]>>
    imp_res_tac asm_fetch_aux_eq2>>
    imp_res_tac all_skips_evaluate>>
    pop_assum mp_tac>>simp[Once evaluate_def,SimpRHS,asm_fetch_def]>>
    fs[ADD_COMM]
    >-
      (Cases_on`i`>>full_simp_tac(srw_ss())[asm_inst_def,upd_reg_def,arith_upd_def,mem_op_def]
      >-
        (full_simp_tac(srw_ss())[all_skips_def]>>
        metis_tac[arithmeticTheory.ADD_COMM])
      >-
        (rw[]>>
        fs[inc_pc_def,dec_clock_def]>>
        qmatch_asmsub_abbrev_tac`evaluate tt = (res,s2)`>>
        first_x_assum(qspec_then `tt with <|pc:= t1.pc+k+1; code:=t1.code; compile:= t1.compile; compile_oracle := t1.compile_oracle|>` mp_tac)>>
        simp[Abbr`tt`,state_component_equality]>>
        impl_tac>-
          metis_tac[adjust_pc_all_skips,ADD_COMM,ADD_ASSOC]>>
        strip_tac>>
        first_x_assum(qspec_then`k'` assume_tac)>>
        qmatch_asmsub_abbrev_tac`evaluate tt = (res,t2)`>>
        qmatch_asmsub_abbrev_tac`evaluate _ = evaluate ss`>>
        `ss = tt` by (unabbrev_all_tac>>fs[state_component_equality])>>
        unabbrev_all_tac>>fs[]>>
        metis_tac[ADD_ASSOC])
      >-
        (* arith upd*)
        (Cases_on`a`>>fs[arith_upd_def]>>
        TRY(Cases_on`r`>>Cases_on`b`)>>full_simp_tac(srw_ss())[]>>
        EVERY_CASE_TAC>>full_simp_tac(srw_ss())[binop_upd_def,LET_THM]>>
        fs[upd_reg_def,inc_pc_def,dec_clock_def,assert_def]>>
        rw[]>> fs[]>>
        (* Error cases *)
        TRY(first_x_assum(qspec_then`0` mp_tac)>>
          srw_tac[][]>>
          qexists_tac`k`>>qexists_tac`t1 with pc:=k+t1.pc`>>full_simp_tac(srw_ss())[]>>NO_TAC)>>
        (* normal cases *)
        (qmatch_asmsub_abbrev_tac`evaluate tt = (res,s2)`>>
        first_x_assum(qspec_then `tt with <|pc:= t1.pc+k+1; code:=t1.code; compile:= t1.compile; compile_oracle := t1.compile_oracle|>` mp_tac)>>
        simp[Abbr`tt`,state_component_equality]>>
        impl_tac>-
          metis_tac[adjust_pc_all_skips,ADD_COMM,ADD_ASSOC]>>
        strip_tac>>
        first_x_assum(qspec_then`k'` assume_tac)>>
        qmatch_asmsub_abbrev_tac`evaluate tt = (res,t2)`>>
        qmatch_asmsub_abbrev_tac`evaluate _ = evaluate ss`>>
        `ss = tt` by (unabbrev_all_tac>>fs[state_component_equality])>>
        unabbrev_all_tac>>fs[]>>
        metis_tac[ADD_ASSOC]))
      >-
        (Cases_on`a`>>Cases_on`m`>>
        fs[mem_op_def,mem_load_def,addr_def,mem_load_byte_def,mem_store_def,upd_mem_def,mem_store_byte_def]>>
        EVERY_CASE_TAC>>
        fs[upd_reg_def,inc_pc_def,dec_clock_def,assert_def]>>
        rw[]>>fs[]>>
        rfs[]>>
        (* Error cases *)
        TRY(first_x_assum(qspec_then`0` mp_tac)>>
          srw_tac[][]>>
          qexists_tac`k`>>qexists_tac`t1 with pc:=k+t1.pc`>>full_simp_tac(srw_ss())[]>>NO_TAC)>>
        (* everything else*)
        (qmatch_asmsub_abbrev_tac`evaluate tt = (res,s2)`>>
        first_x_assum(qspec_then `tt with <|pc:= t1.pc+k+1; code:=t1.code; compile:= t1.compile; compile_oracle := t1.compile_oracle|>` mp_tac)>>
        simp[Abbr`tt`,state_component_equality]>>
        impl_tac>-
          metis_tac[adjust_pc_all_skips,ADD_COMM,ADD_ASSOC]>>
        strip_tac>>
        first_x_assum(qspec_then`k'` assume_tac)>>
        qmatch_asmsub_abbrev_tac`evaluate tt = (res,t2)`>>
        qmatch_asmsub_abbrev_tac`evaluate _ = evaluate ss`>>
        `ss = tt` by (unabbrev_all_tac>>fs[state_component_equality])>>
        unabbrev_all_tac>>fs[]>>
        metis_tac[ADD_ASSOC]))
      >>
        (* FP *)
        Cases_on`f`>>fs[fp_upd_def]>> every_case_tac >>
        fs[upd_reg_def,inc_pc_def,dec_clock_def,assert_def,read_fp_reg_def,upd_fp_reg_def]>>
        rw[]>>fs[]>>
        (* Error cases *)
        TRY(
          qmatch_goalsub_rename_tac`Error` >>
          first_x_assum(qspec_then`0` mp_tac)>>
          srw_tac[][]>>
          qexists_tac`k`>>qexists_tac`t1 with pc:=k+t1.pc`>>full_simp_tac(srw_ss())[]>>NO_TAC)>>
        (qmatch_asmsub_abbrev_tac`evaluate tt = (res,s2)`>>
        last_x_assum(qspec_then `tt with <|pc:= t1.pc+k+1; code:=t1.code; compile:=t1.compile;
          compile_oracle := t1.compile_oracle|>` mp_tac)>>
        simp[Abbr`tt`,state_component_equality]>>
        impl_tac>-
          metis_tac[adjust_pc_all_skips,ADD_COMM,ADD_ASSOC]>>
        strip_tac>>
        first_x_assum(qspec_then`k'` assume_tac)>>
        qmatch_asmsub_abbrev_tac`evaluate tt = (res,t2)`>> rfs[] >>
        qmatch_asmsub_abbrev_tac`evaluate _ = evaluate ss`>>
        `ss = tt` by (unabbrev_all_tac>>fs[state_component_equality])>>
        unabbrev_all_tac>>fs[]>>
        metis_tac[ADD_ASSOC])
      )
    >- (*JumpReg*)
      (FULL_CASE_TAC>>full_simp_tac(srw_ss())[]>-same_inst_tac>>
      Cases_on`loc_to_pc n'' n0 (filter_skip t1.code)`>>full_simp_tac(srw_ss())[]
      >-
        (imp_res_tac loc_to_pc_eq_NONE>>same_inst_tac)
      >>
        imp_res_tac loc_to_pc_eq_SOME>>
        full_simp_tac(srw_ss())[get_pc_value_def,upd_pc_def,dec_clock_def]>>srw_tac[][]>>
        upd_pc_tac)
    >- (*CBW*)
      (reverse(simp[case_eq_thms]>>rw[]>>fs[inc_pc_def,dec_clock_def])
      >> TRY (
        rename1`code_buffer_write _ _ _ = SOME _`>>
        qmatch_asmsub_abbrev_tac`evaluate tt = (res,s2)`>>
        first_x_assum(qspec_then `tt with <|pc:= t1.pc+k+1; code:=t1.code; compile:= t1.compile; compile_oracle := t1.compile_oracle|>` mp_tac)>>
        simp[Abbr`tt`,state_component_equality]>>
        impl_tac>-
          metis_tac[adjust_pc_all_skips,ADD_COMM,ADD_ASSOC]>>
        strip_tac>>
        first_x_assum(qspec_then`k'` assume_tac)>>
        qmatch_asmsub_abbrev_tac`evaluate tt = (res,t2)`>>
        qmatch_asmsub_abbrev_tac`evaluate ss = evaluate _`>>
        `ss = tt` by (
          unabbrev_all_tac>>fs[state_component_equality])>>
        unabbrev_all_tac>>fs[]>>
        metis_tac[ADD_ASSOC])
      >>
        (first_x_assum(qspec_then`0` (assume_tac o SYM))>>
        fs[]>>qexists_tac`k`>>fs[])))
  >>
    Cases_on`a`>>
    full_simp_tac(srw_ss())[asm_fetch_def,state_rel_def]>>rev_full_simp_tac(srw_ss())[]>>
    imp_res_tac asm_fetch_aux_eq2>>
    imp_res_tac all_skips_evaluate>>
    pop_assum mp_tac>>simp[Once evaluate_def,SimpRHS,asm_fetch_def]>>
    fs[ADD_COMM]
    >-
      (full_simp_tac(srw_ss())[get_pc_value_def]>>Cases_on`l'`>>full_simp_tac(srw_ss())[]>>
      Cases_on`loc_to_pc n' n0 (filter_skip t1.code)`>>full_simp_tac(srw_ss())[]
      >-
        (imp_res_tac loc_to_pc_eq_NONE>>full_simp_tac(srw_ss())[]>>
        same_inst_tac>>full_simp_tac(srw_ss())[get_pc_value_def])
      >>
        imp_res_tac loc_to_pc_eq_SOME>>full_simp_tac(srw_ss())[]>>
        full_simp_tac(srw_ss())[get_pc_value_def,upd_pc_def,dec_clock_def]>>
        srw_tac[][]>>
        upd_pc_tac)
    >-
      (Cases_on`r`>>full_simp_tac(srw_ss())[reg_imm_def]>>
      (FULL_CASE_TAC>-same_inst_tac>>
      IF_CASES_TAC>-
        (full_simp_tac(srw_ss())[get_pc_value_def]>>Cases_on`l'`>>full_simp_tac(srw_ss())[]>>
        TRY(qabbrev_tac`n'''=n''`)>>
        Cases_on`loc_to_pc n''' n0 (filter_skip t1.code)`>>full_simp_tac(srw_ss())[]
        >-
          (imp_res_tac loc_to_pc_eq_NONE>>full_simp_tac(srw_ss())[]>>
          same_inst_tac>>full_simp_tac(srw_ss())[get_pc_value_def])
        >>
          imp_res_tac loc_to_pc_eq_SOME>>full_simp_tac(srw_ss())[]>>
          full_simp_tac(srw_ss())[get_pc_value_def,upd_pc_def,dec_clock_def]>>
          srw_tac[][]>>
          upd_pc_tac)
      >>
        (fs[inc_pc_def,dec_clock_def]>>rw[]>>
        fs[]>>
        qmatch_asmsub_abbrev_tac`evaluate tt = (res,s2)`>>
        first_x_assum(qspec_then `tt with <|pc:= t1.pc+k+1; code:=t1.code; compile:= t1.compile; compile_oracle := t1.compile_oracle|>` mp_tac)>>
        simp[Abbr`tt`,state_component_equality]>>
        impl_tac>-
          metis_tac[adjust_pc_all_skips,ADD_COMM,ADD_ASSOC]>>
        strip_tac>>
        first_x_assum(qspec_then`k'` assume_tac)>>
        qmatch_asmsub_abbrev_tac`evaluate tt = (res,t2)`>>
        qmatch_asmsub_abbrev_tac`evaluate _ = evaluate ss`>>
        `ss = tt` by (unabbrev_all_tac>>fs[state_component_equality])>>
        unabbrev_all_tac>>fs[]>>
        metis_tac[ADD_ASSOC])))
    >-
      (*get_lab_after*)
      (full_simp_tac(srw_ss())[get_pc_value_def]>>Cases_on`l'`>>full_simp_tac(srw_ss())[]>>
      Cases_on`loc_to_pc n' n0 (filter_skip t1.code)`>>full_simp_tac(srw_ss())[]
      >-
        (imp_res_tac loc_to_pc_eq_NONE>>full_simp_tac(srw_ss())[]>>
        same_inst_tac>>full_simp_tac(srw_ss())[get_pc_value_def])
      >>
        imp_res_tac loc_to_pc_eq_SOME>>
        full_simp_tac(srw_ss())[get_ret_Loc_def]>>
        qpat_abbrev_tac`aa = get_lab_after _ _`>>
        qpat_abbrev_tac`aaa = get_lab_after _ _`>>
        `aa = aaa` by
          (imp_res_tac (INST_TYPE[beta|->alpha]get_lab_after_adjust)>>
          rev_full_simp_tac(srw_ss())[]>>
          metis_tac[arithmeticTheory.ADD_COMM])>>
        Cases_on`aaa`>>full_simp_tac(srw_ss())[]
        >-
          (same_inst_tac>>
          full_simp_tac(srw_ss())[get_pc_value_def,get_ret_Loc_def])
        >>
          fs[upd_pc_def,dec_clock_def,upd_reg_def]>>rw[]>>fs[]>>
          qmatch_asmsub_abbrev_tac`evaluate tt = (res,s2)`>>
          first_x_assum(qspec_then `tt with <|pc:= pc'; code:=t1.code; compile:= t1.compile; compile_oracle := t1.compile_oracle|>` mp_tac)>>
          simp[Abbr`tt`,state_component_equality]>>
          strip_tac>>
          first_x_assum(qspec_then`k'` assume_tac)>>
          qmatch_asmsub_abbrev_tac`evaluate tt = (res,t2)`>>
          qmatch_asmsub_abbrev_tac`evaluate _ = evaluate ss`>>
          `ss = tt` by (unabbrev_all_tac>>fs[state_component_equality])>>
          unabbrev_all_tac>>fs[]>>
          metis_tac[ADD_ASSOC])
    >-
      (full_simp_tac(srw_ss())[inc_pc_def,dec_clock_def,upd_reg_def,get_pc_value_def]>>
      Cases_on`l'`>>fs[]>>
      Cases_on`loc_to_pc n'' n0 (filter_skip t1.code)`>>fs[]
      >-
        (imp_res_tac loc_to_pc_eq_NONE>>fs[]>>
        disch_then(qspec_then`0` assume_tac)>>rw[]>>
        fs[]>>qexists_tac`k`>>fs[])
      >>
      imp_res_tac loc_to_pc_eq_SOME>>
      fs[]>>rw[]>>
      first_assum(qspec_then`0` assume_tac)>>full_simp_tac(srw_ss())[]>>
      qmatch_assum_abbrev_tac`evaluate aa = evaluate bb`>>
      first_x_assum(qspec_then`bb` mp_tac)>>
      impl_tac>-
        (simp[inc_pc_def,dec_clock_def,Abbr`bb`,state_component_equality]>>
        `k + (t1.pc +1) = (t1.pc + k + 1)` by DECIDE_TAC>>full_simp_tac(srw_ss())[]>>
        metis_tac[adjust_pc_all_skips])>>
      srw_tac[][Abbr`bb`]>>
      qexists_tac`k+k'`>>qexists_tac`t2`>>full_simp_tac(srw_ss())[]>>
      qpat_x_assum`Z=(res,t2)` sym_sub_tac>>
      first_x_assum(qspec_then`k'` assume_tac)>>
      `∀x.x + t1.clock -1 = x + (t1.clock -1)` by DECIDE_TAC>>rev_full_simp_tac(srw_ss())[]>>
      metis_tac[arithmeticTheory.ADD_COMM,arithmeticTheory.ADD_ASSOC])
    >-
      (reverse(Cases_on`t1.regs t1.len_reg`>>full_simp_tac(srw_ss())[])>-same_inst_tac>>
      reverse(Cases_on`t1.regs t1.ptr_reg`>>full_simp_tac(srw_ss())[])>-same_inst_tac>>
      reverse(Cases_on`t1.regs t1.len2_reg`>>full_simp_tac(srw_ss())[])>-same_inst_tac>>
      (Cases_on`t1.regs t1.link_reg`>>full_simp_tac(srw_ss())[])>-same_inst_tac>>
      reverse(Cases_on`t1.regs t1.ptr2_reg`>>full_simp_tac(srw_ss())[])>-same_inst_tac>>
      Cases_on`read_bytearray c'' (w2n c') (mem_load_byte_aux t1.mem t1.mem_domain t1.be)`>>full_simp_tac(srw_ss())[]
      >- same_inst_tac>>
      Cases_on`read_bytearray c'''' (w2n c''') (mem_load_byte_aux t1.mem t1.mem_domain t1.be)`>>full_simp_tac(srw_ss())[]
      >- same_inst_tac>>
      Cases_on`loc_to_pc n' n0 (filter_skip t1.code)`>>full_simp_tac(srw_ss())[]
      >-
        (imp_res_tac loc_to_pc_eq_NONE>>full_simp_tac(srw_ss())[]>>
        same_inst_tac)
      >>
        imp_res_tac loc_to_pc_eq_SOME>>full_simp_tac(srw_ss())[]>>
        full_simp_tac(srw_ss())[]>>
        srw_tac[][]>>Cases_on`call_FFI t1.ffi s x x'`>>fs[]>-upd_pc_tac>>
        same_inst_tac)
    >- (*oracle case *)
      (reverse(Cases_on`t1.regs t1.ptr_reg`) \\ fs[] >- same_inst_tac \\
      (Cases_on`t1.regs t1.link_reg`) \\ fs[] >- same_inst_tac \\
      reverse(Cases_on`t1.regs t1.len_reg`) \\ fs[] >- same_inst_tac \\
      TOP_CASE_TAC >- same_inst_tac \\
      strip_tac \\
      TOP_CASE_TAC >- (
        fs[loc_to_pc_eq_NONE] \\ rw[]
        \\ first_x_assum(qspec_then`0`mp_tac) \\ rw[]
        \\ qexists_tac`k` \\ simp[] ) \\
      split_pair_case_tac \\ fs[] \\
      pairarg_tac>>fs[] \\
      imp_res_tac loc_to_pc_eq_SOME \\ fs[] \\
      TOP_CASE_TAC >- (
        rw[]>>pairarg_tac>>fs[]>>
        Cases_on`b`>>fs[filter_skip_MAP]>>
        same_inst_tac)>>
      TOP_CASE_TAC>-(
        rw[]>>pairarg_tac>>fs[]>>
        Cases_on`b`>>Cases_on`h`>>fs[filter_skip_MAP]>>
        same_inst_tac)>>
      split_pair_case_tac \\ fs[] \\
      TOP_CASE_TAC >> fs[] >>
      reverse IF_CASES_TAC >- (
        rw[]>>pairarg_tac>>fs[]>>
        Cases_on`b`>>fs[filter_skip_MAP]>>
        Cases_on`h`>>same_inst_tac>>
        fs[shift_seq_def]>>
        pairarg_tac>>fs[])>>
      strip_tac>>
      pairarg_tac>>fs[shift_seq_def]>>
      pairarg_tac>>fs[]>>
      fs[]>>rfs[]>>
      rw[]>>
      first_x_assum(qspec_then `t1 with <|
        regs := (t1.ptr_reg =+ Loc n'' 0) (λa. get_reg_value (t1.cc_regs 0 a) (read_reg a t1) Word);
        pc := pc';
        code := t1.code ++ SND(t1.compile_oracle 0);
        compile_oracle := shift_seq 1 t1.compile_oracle;
        code_buffer := cb; clock:=t1.clock-1 ; cc_regs:= shift_seq 1 t1.cc_regs|>` mp_tac)>>
      simp[state_component_equality]>>
      impl_tac>- (
        rw[filter_skip_MAP,shift_seq_def]
        >-
          metis_tac[loc_to_pc_adjust_pc_append]
        >>
          metis_tac[FUN_EQ_THM,filter_skip_MAP])>>
      rw[]>>
      first_x_assum(qspec_then`k''` assume_tac)>>rfs[]>>
      Cases_on`b`>>fs[filter_skip_MAP]>>
      Cases_on`h`>>fs[shift_seq_def]>>
      metis_tac[ADD_ASSOC])
    >>
      EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>srw_tac[][]>>
      same_inst_tac
QED

val state_rel_IMP_sem_EQ_sem = Q.prove(
  `!s t. state_rel s t ==> semantics s = semantics t`,
  srw_tac[][labSemTheory.semantics_def] >- (
    DEEP_INTRO_TAC some_intro >>
    full_simp_tac(srw_ss())[FST_EQ_EQUIV] >>
    `state_rel (s with clock := k) (t with clock := k)` by
      fs[state_rel_def,state_component_equality]>>
    `¬(t with clock := k).failed` by full_simp_tac(srw_ss())[state_rel_def] >>
    imp_res_tac filter_correct >> full_simp_tac(srw_ss())[] >>
    metis_tac[] )
  >- (
    DEEP_INTRO_TAC some_intro >> full_simp_tac(srw_ss())[] >>
    `state_rel (s with clock := k) (t with clock := k)` by
      fs[state_rel_def,state_component_equality]>>
    drule (REWRITE_RULE[GSYM CONJ_ASSOC](ONCE_REWRITE_RULE[CONJ_COMM]filter_correct)) >>
    simp_tac(srw_ss()++QUANT_INST_ss[pair_default_qp])[] >>
    impl_tac >- full_simp_tac(srw_ss())[state_rel_def] >>
    simp[FST_EQ_EQUIV,PULL_EXISTS] >>
    rpt gen_tac >> strip_tac >>
    full_simp_tac(srw_ss())[FST_EQ_EQUIV] >>
    imp_res_tac evaluate_ADD_clock >> full_simp_tac(srw_ss())[] >>
    metis_tac[FST,PAIR] )
  >- (
    DEEP_INTRO_TAC some_intro >> full_simp_tac(srw_ss())[] >>
    conj_tac >- (
      srw_tac[][] >>
      DEEP_INTRO_TAC some_intro >> full_simp_tac(srw_ss())[] >>
      conj_tac >- (
        srw_tac[][] >>
        qhdtm_x_assum`evaluate`mp_tac >>
        drule filter_correct >>
        disch_then(qspec_then`t with clock := k`mp_tac) >>
        impl_tac >-
          fs[state_rel_def,state_component_equality] >>
        strip_tac >> full_simp_tac(srw_ss())[] >> strip_tac >>
        rename1`t with clock := a + b`>>
        rename1`t with clock := c`>>
        qabbrev_tac`d = a+b` >>
        qspecl_then[`c`,`d`]mp_tac LESS_EQ_CASES >>
        simp[LESS_EQ_EXISTS] >> strip_tac >>
        qmatch_assum_rename_tac`k = y + p` >>
        qspecl_then[`p`,`t with clock := y`]mp_tac(GEN_ALL evaluate_add_clock_io_events_mono) >>
        simp[] >> fsrw_tac[ARITH_ss][] >>
        every_case_tac >> full_simp_tac(srw_ss())[] >>
        imp_res_tac evaluate_ADD_clock >> full_simp_tac(srw_ss())[] >>
        srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >>
        rpt(first_x_assum(qspec_then`p`mp_tac))>>simp[]>>
        srw_tac[][] >> full_simp_tac(srw_ss())[] ) >>
      drule filter_correct >>
      disch_then(qspec_then`t with clock := k`mp_tac) >>
      impl_tac >-
        fs[state_rel_def,state_component_equality] >>
      strip_tac >> full_simp_tac(srw_ss())[] >>
      qexists_tac`k+k'`>>simp[] >>
      every_case_tac >> full_simp_tac(srw_ss())[] ) >>
    srw_tac[][] >>
    DEEP_INTRO_TAC some_intro >> full_simp_tac(srw_ss())[] >>
    conj_tac >- (
      srw_tac[][] >>
      Q.ISPEC_THEN`s with clock := k`mp_tac filter_correct >>
      simp[] >>
      qexists_tac`t with clock := k` >>
      simp_tac(srw_ss()++QUANT_INST_ss[pair_default_qp])[] >>
      conj_tac >-
        fs[state_rel_def,state_component_equality] >>
      conj_tac >-
        fs[state_rel_def,state_component_equality] >>
      srw_tac[][] >>
      first_x_assum(qspec_then`k`mp_tac) >>
      srw_tac[QUANT_INST_ss[pair_default_qp]][] >>
      qspecl_then[`k'`,`t with clock := k`]mp_tac(GEN_ALL evaluate_add_clock_io_events_mono) >>
      simp[] >> strip_tac >>
      every_case_tac >> full_simp_tac(srw_ss())[] >>
      imp_res_tac evaluate_ADD_clock >> full_simp_tac(srw_ss())[] >>
      full_simp_tac(srw_ss())[ffiTheory.ffi_state_component_equality] ) >>
    strip_tac >>
    qmatch_abbrev_tac`build_lprefix_lub l1 = build_lprefix_lub l2` >>
    `lprefix_chain l1 ∧ lprefix_chain l2` by (
      unabbrev_all_tac >>
      conj_tac >>
      Ho_Rewrite.ONCE_REWRITE_TAC[GSYM o_DEF] >>
      REWRITE_TAC[IMAGE_COMPOSE] >>
      match_mp_tac prefix_chain_lprefix_chain >>
      simp[prefix_chain_def,PULL_EXISTS] >>
      qx_genl_tac[`k1`,`k2`] >>
      qspecl_then[`k1`,`k2`]mp_tac LESS_EQ_CASES >>
      metis_tac[
        labPropsTheory.evaluate_add_clock_io_events_mono
        |> Q.SPEC`s with clock := k` |> SIMP_RULE (srw_ss())[],
        LESS_EQ_EXISTS]) >>
    `equiv_lprefix_chain l1 l2` by (
      simp[equiv_lprefix_chain_thm] >>
      unabbrev_all_tac >> simp[PULL_EXISTS] >>
      ntac 2 (pop_assum kall_tac) >>
      simp[LNTH_fromList,PULL_EXISTS] >>
      simp[GSYM FORALL_AND_THM] >>
      rpt gen_tac >>
      Q.ISPEC_THEN `s with clock := k` mp_tac filter_correct >>
      Cases_on`evaluate (s with clock := k)`>>full_simp_tac(srw_ss())[] >>
      disch_then(qspec_then`t with clock := k`mp_tac) >>
      impl_tac >-
        fs[state_rel_def,state_component_equality]>>
      simp[] >> strip_tac >>
      conj_tac >> strip_tac >- (
        rev_full_simp_tac(srw_ss())[] >> qexists_tac`k+k'`>>simp[] ) >>
      qspecl_then[`k'`,`s with clock := k`]mp_tac(GEN_ALL evaluate_add_clock_io_events_mono) >>
      simp[] >> strip_tac >>
      qspecl_then[`k'`,`t with clock := k`]mp_tac(GEN_ALL evaluate_add_clock_io_events_mono) >>
      simp[] >> strip_tac >>
      full_simp_tac(srw_ss())[IS_PREFIX_APPEND] >> full_simp_tac(srw_ss())[] >>
      qexists_tac`k+k'`>>simp[EL_APPEND1] ) >>
    metis_tac[build_lprefix_lub_thm,unique_lprefix_lub,lprefix_lub_new_chain]));

Theorem filter_skip_semantics:
   !s t. (t.pc = 0) ∧ ¬t.failed /\
   (∃scompile.
     s = t with <| code := filter_skip t.code ;
                   compile_oracle := (λ(a,b).(a,filter_skip b)) o t.compile_oracle;
                   compile := scompile
                 |> ∧
    t.compile = λc p. scompile c (filter_skip p)) ∧
    ¬t.failed  ==>
  semantics s = semantics t
Proof
  srw_tac[][] \\ match_mp_tac state_rel_IMP_sem_EQ_sem
  \\ full_simp_tac(srw_ss())[state_rel_def,state_component_equality,Once adjust_pc_def,o_DEF]
QED

Theorem sec_ends_with_label_filter_skip:
   ∀code.
   EVERY sec_ends_with_label code ⇒
   EVERY sec_ends_with_label (filter_skip code)
Proof
  Induct \\ simp[filter_skip_def]
  \\ Cases \\ fs[filter_skip_def,sec_ends_with_label_def]
  \\ Induct_on`l` \\ fs[NULL_EQ]
  \\ Cases \\ fs[LAST_CONS_cond,not_skip_def]
  \\ TOP_CASE_TAC \\ fs[]
  \\ TOP_CASE_TAC \\ fs[]
  \\ fs[LAST_CONS_cond]
QED

val _ = export_theory();
