open preamble BasicProvers
     wordLangTheory wordPropsTheory word_instTheory wordSemTheory
     asmTheory

val _ = new_theory "word_instProof";

val sym_sub_tac = SUBST_ALL_TAC o SYM;

val inst_select_exp_thm = prove(``
  ∀s exp tar temp w.
  word_exp s exp = SOME w ∧
  (∀x. x ∈ domain s.locals ⇒ x < temp) ⇒ 
  let (res,s') = evaluate ((inst_select_exp tar temp exp),s) in
    res = NONE ∧
    s' = s with locals:=s'.locals ∧ 
    ∀x. 
    if x = tar then lookup x s'.locals = SOME (Word w)
    else 
      x ∈ domain s.locals ⇒ (lookup x s.locals = lookup x s'.locals)``,
  ho_match_mp_tac word_exp_ind>>rpt strip_tac>>
  fs[LET_THM,inst_select_exp_def,evaluate_def,word_exp_def,inst_def,assign_def,set_var_def,lookup_insert,get_vars_def,set_vars_def,get_var_def]
  >-
    (EVERY_CASE_TAC>>fs[alist_insert_def,lookup_insert])
  >-
    (EVERY_CASE_TAC>>fs[lookup_insert])
  >-
    (EVERY_CASE_TAC>>fs[]>>
    first_x_assum(qspecl_then[`temp`,`temp+1`] mp_tac)>>
    discharge_hyps_keep>-
      (rw[]>>res_tac>>DECIDE_TAC)
    >>
    strip_tac>>fs[]>>
    qpat_abbrev_tac`A = evaluate (B,C)`>>
    Cases_on`A`>>fs[]>>
    `lookup temp r.locals = SOME (Word x)` by metis_tac[]>>
    fs[word_op_def,mem_load_def,state_component_equality,lookup_insert]>>
    rw[]>>Cases_on`x'=tar`>>fs[]>>
    rw[]>>first_x_assum(qspec_then `x'` assume_tac)>>
    `x' ≠ temp` by 
      (res_tac>>DECIDE_TAC)>>
    metis_tac[])
  >-
    (*hard case where Op order optimizations come in*)
    cheat
  >>
    (EVERY_CASE_TAC>>fs[]>>
    first_x_assum(qspecl_then[`temp`,`temp+1`] mp_tac)>>
    discharge_hyps_keep>-
      (rw[]>>res_tac>>DECIDE_TAC)
    >>
    strip_tac>>fs[]>>
    qpat_abbrev_tac`A = evaluate (B,C)`>>
    Cases_on`A`>>fs[]>>
    `lookup temp r.locals = SOME (Word x)` by metis_tac[]>>
    fs[word_op_def,mem_load_def,state_component_equality,lookup_insert,Once num_exp_def]>>
    (*Some weird type error??*)
    cheat))

val inst_select_thm = prove(``
  ∀prog st res rst temp.
  evaluate (prog,st) = (res,rst) ∧
  res ≠ SOME Error ∧ 
  (∀x. x ∈ domain st.locals ⇒ x < temp) ⇒ 
  let (res',rst') = evaluate (inst_select temp prog,st) in
    res = res' ∧
    rst' = rst with locals:=rst'.locals ∧ 
    ∀x. 
    x ∈ domain rst.locals ⇒ (lookup x rst.locals = lookup x rst'.locals)``,
  completeInduct_on`prog_size (K 0) prog`>>
  rpt strip_tac>>
  Cases_on`prog`>>
  fs[inst_select_def,evaluate_def,LET_THM,state_component_equality]
  >-
    (Cases_on`word_exp st e`>>fs[]>>
    imp_res_tac inst_select_exp_thm>>
    pop_assum(qspec_then`n` assume_tac)>>
    pop_assum mp_tac>>LET_ELIM_TAC>>
    fs[]>>qpat_assum`A=rst` sym_sub_tac>>fs[set_var_def,state_component_equality,lookup_insert]>>
    metis_tac[])
  >-
    (Cases_on`word_exp st e`>>fs[]>>
    `∀x. x ∈ domain st.locals ⇒ x < temp+1` by 
      (rw[]>>res_tac>>DECIDE_TAC) >>
    imp_res_tac inst_select_exp_thm>>
    pop_assum kall_tac>>pop_assum(qspec_then`temp` assume_tac)>>
    pop_assum mp_tac>>LET_ELIM_TAC>>
    fs[]>>qpat_assum`A=rst` sym_sub_tac>>fs[set_store_def,state_component_equality,lookup_insert,word_exp_def]>>
    `lookup temp s'.locals = SOME(Word x)` by metis_tac[]>>
    fs[]>>
    rw[]>>  `x' ≠ temp` by 
      (res_tac>>DECIDE_TAC)>>
    metis_tac[])
  >-
    (EVERY_CASE_TAC>>fs[inst_def]>>
    `∀x. x ∈ domain st.locals ⇒ x < temp+1` by 
      (rw[]>>res_tac>>DECIDE_TAC) >>
    imp_res_tac inst_select_exp_thm>>
    pop_assum kall_tac>>pop_assum(qspec_then`temp` assume_tac)>>
    pop_assum mp_tac>>LET_ELIM_TAC>>
    `lookup temp s'.locals = SOME(Word x')` by metis_tac[]>>
    fs[word_exp_def,LET_THM,word_op_def,get_var_def,mem_store_def]>>
    `n ≠ temp` by 
      (`n ∈ domain st.locals` by fs[domain_lookup]>>
      res_tac>>DECIDE_TAC)>>
    `lookup n s'.locals = SOME x` by 
      (first_x_assum(qspec_then`n` assume_tac)>>rfs[]>>
      metis_tac[domain_lookup])>>
    fs[state_component_equality]>>
    rw[]>>`x''' ≠ temp` by (res_tac>>DECIDE_TAC)>>
    metis_tac[])
  (*Induction -- IH must be strengthened so that temp 
    does not occur anywhere in the program as well*)
  >> cheat)
    
    
(*No expressions nesting*)
val flat_exp_conventions_def = Define`
  (*These should be converted to Insts*)
  (flat_exp_conventions (Assign v exp) = F) ∧
  (flat_exp_conventions (Store exp num) = F) ∧ 
  (*Only top level vars allowed*)
  (flat_exp_conventions (Set store_name (Var r)) = T) ∧ 
  (flat_exp_conventions (Set store_name _) = F) ∧
  (flat_exp_conventions (Seq p1 p2) =
    (flat_exp_conventions p1 ∧ flat_exp_conventions p2)) ∧
  (flat_exp_conventions (If cmp r1 ri e2 e3) =
    (flat_exp_conventions e2 ∧ 
    flat_exp_conventions e3)) ∧ 
  (flat_exp_conventions (Call ret dest args h) =
    ((case ret of
      NONE => T
    | SOME (v,cutset,ret_handler,l1,l2) => 
        flat_exp_conventions ret_handler) ∧ 
    (case h of 
      NONE => T
    | SOME (v,prog,l1,l2) => flat_exp_conventions prog))) ∧ 
  (flat_exp_conventions _ = T)`

val inst_select_exp_conventions = prove(``
  ∀tar temp exp.
  flat_exp_conventions (inst_select_exp tar temp exp)``,
  ho_match_mp_tac inst_select_exp_ind>>rw[]>>fs[inst_select_exp_def,flat_exp_conventions_def,LET_THM]>>
  ho_match_mp_tac FOLDL_invariant>>fs[flat_exp_conventions_def])

val inst_select_conventions = prove(``
  ∀temp prog.
  flat_exp_conventions (inst_select temp prog)``,
  ho_match_mp_tac inst_select_ind >>rw[]>>
  fs[flat_exp_conventions_def,inst_select_def,LET_THM]>>
  EVERY_CASE_TAC>>
  metis_tac[inst_select_exp_conventions])

val _ = export_theory ();
