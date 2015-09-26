open preamble BasicProvers
     wordLangTheory wordPropsTheory word_instTheory wordSemTheory
     asmTheory word_allocTheory

val _ = new_theory "word_instProof";

val sym_sub_tac = SUBST_ALL_TAC o SYM;

(*First step: Make op expressions have exactly 2 args*)
(*Semantics*)
val flatten_exp_ok = prove(``
  ∀exp s.
  word_exp s exp = word_exp s (flatten_exp exp)``,
  ho_match_mp_tac flatten_exp_ind>>rw[]>>
  fs[flatten_exp_def]
  >-
    (fs[flatten_exp_def,word_exp_def]>>LET_ELIM_TAC>>
    `ws = ws'` by 
      (match_mp_tac LIST_EQ>>unabbrev_all_tac>>fs[EL_MAP,EL_MEM])>>
    metis_tac[])
  >>
    fs[word_exp_def,LET_THM,word_op_def]>>IF_CASES_TAC>>fs[]>>
    TRY(first_x_assum(qspec_then `s` assume_tac)>>rfs[]>>
    pop_assum sym_sub_tac>>fs[])>>metis_tac[option_CLAUSES])

(*All ops are 2 args. Technically, we should probably check that Sub has 2 args. However, the semantics already checks that and it will get removed later*)
val binary_branch_exp_def = tDefine "binary_branch_exp" `
  (binary_branch_exp (Op Sub exps) = EVERY (binary_branch_exp) exps) ∧ 
  (binary_branch_exp (Op op xs) = (LENGTH xs = 2 ∧ EVERY (binary_branch_exp) xs)) ∧
  (binary_branch_exp (Load exp) = binary_branch_exp exp) ∧ 
  (binary_branch_exp (Shift shift exp nexp) = binary_branch_exp exp) ∧  
  (binary_branch_exp exp = T)`
  (WF_REL_TAC `measure (exp_size ARB)`
   \\ REPEAT STRIP_TAC \\ IMP_RES_TAC MEM_IMP_exp_size
   \\ TRY (FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `ARB`))
   \\ fs[exp_size_def]
   \\ TRY (DECIDE_TAC))

(*Syntax*)
val flatten_exp_binary_branch_exp = prove(``
  ∀exp.
  binary_branch_exp (flatten_exp exp)``,
  ho_match_mp_tac flatten_exp_ind>>fs[flatten_exp_def,binary_branch_exp_def,EVERY_MEM,EVERY_MAP])

val num_exp_equiv = prove(``
  word_inst$num_exp = wordSem$num_exp``,
  fs[FUN_EQ_THM]>>Induct>>
  fs[wordSemTheory.num_exp_def,word_instTheory.num_exp_def])

(*2nd step: Convert expressions to insts*)
val inst_select_exp_thm = prove(``
  ∀tar temp exp s w.
  binary_branch_exp exp ∧ 
  word_exp s exp = SOME w ⇒ 
  let (res,s') = evaluate ((inst_select_exp tar temp exp),s) in
    res = NONE ∧
    s' = s with locals:= s'.locals ∧ 
    ∀x. 
    if x = tar then lookup x s'.locals = SOME (Word w)
    else if x < temp then lookup x s'.locals = lookup x s.locals
    else T``,
  ho_match_mp_tac inst_select_exp_ind>>
  rpt strip_tac>>
  fs[LET_THM,inst_select_exp_def,evaluate_def,word_exp_def,inst_def,assign_def,set_var_def,lookup_insert,get_vars_def,set_vars_def,get_var_def,binary_branch_exp_def,binary_branch_exp_def]
  >-(EVERY_CASE_TAC>>fs[alist_insert_def,lookup_insert])
  >-(EVERY_CASE_TAC>>fs[alist_insert_def,lookup_insert])
  >-
    (EVERY_CASE_TAC>>fs[binary_branch_exp_def]>>
    res_tac>>
    qpat_abbrev_tac`A = evaluate (B,C)`>>
    Cases_on`A`>>fs[]>>
    `lookup temp r.locals = SOME (Word x)` by metis_tac[]>>
    fs[word_op_def,mem_load_def,state_component_equality,lookup_insert]>>
    rw[]>>Cases_on`x'=tar`>>fs[]>>
    rw[]>>first_x_assum(qspec_then `x'` assume_tac)>>
    `x' ≠ temp` by 
      (res_tac>>DECIDE_TAC)>>
    `x' < temp+1` by DECIDE_TAC>>
    metis_tac[])
  >-
    cheat
    (*Cases_on`op`>>fs[binary_branch_exp_def,IS_SOME_EXISTS]>>
    EVERY_CASE_TAC>>res_tac>>
    qpat_abbrev_tac`A=evaluate(B,C)`>>
    Cases_on`A`>>fs[]>>
    (*TODO: Strengthen IH so that this is true*)
    `word_exp r exp' = SOME x'` by cheat>>
    res_tac>>
    qpat_abbrev_tac`A=evaluate(B,C)`>>
    Cases_on`A`>>fs[]>>
    cheat*)
  >-
    (EVERY_CASE_TAC>>fs[binary_branch_exp_def]>>
    res_tac>>
    qpat_abbrev_tac`A = evaluate (B,C)`>>
    Cases_on`A`>>fs[]>>
    `lookup temp r.locals = SOME (Word x)` by metis_tac[]>>
    fs[word_op_def,mem_load_def,state_component_equality,lookup_insert,Once num_exp_def,num_exp_equiv]>>
    rw[]>>Cases_on`x'=tar`>>fs[]>>
    rw[]>>first_x_assum(qspec_then `x'` assume_tac)>>
    `x' ≠ temp` by 
      (res_tac>>DECIDE_TAC)>>
    `x' < temp+1` by DECIDE_TAC>>
    metis_tac[])
  >>
    Cases_on`v11`>>fs[binary_branch_exp_def,word_op_def])

val locals_rel_def = Define`
  locals_rel s t ⇔ (∀x v. lookup x s = SOME v ⇒ lookup x t = SOME v)` 

val locals_rel_get_vars  = prove(``
  ∀ls vs.
  get_vars ls st = SOME vs ∧ 
  locals_rel st.locals loc ⇒ 
  get_vars ls (st with locals:= loc) = SOME vs``,
  Induct>>fs[get_vars_def]>>rw[]>>
  EVERY_CASE_TAC>>fs[locals_rel_def,get_var_def]>>
  metis_tac[option_CLAUSES])

val locals_rel_alist_insert = prove(``
  ∀ls vs s t.
  locals_rel s t ⇒ 
  locals_rel (alist_insert ls vs s) (alist_insert ls vs t)``,
  ho_match_mp_tac alist_insert_ind>>fs[alist_insert_def,locals_rel_def]>>
  rw[]>>
  Cases_on`x'=ls`>>fs[lookup_insert])

(*Simple thm for cases where we do not change the program
Note: This can be directly proved by instantiating evaluate_apply_colour
but the form of the theorem isn't nice (because of permutations)
*)
val locals_rel_eval_thm = prove(``
  ∀prog st res rst loc.
  evaluate (prog,st) = (res,rst) ∧
  res ≠ SOME Error ∧
  locals_rel st.locals loc ⇒
  ∃loc'.
  evaluate (prog,st with locals:=loc) = (res,rst with locals:=loc') ∧
  locals_rel rst.locals loc'``,
  completeInduct_on`prog_size (K 0) prog`>>
  rpt strip_tac>>
  Cases_on`prog`>>
  fs[evaluate_def,LET_THM]
  >-
    metis_tac[]
  >-
    (qpat_assum `A = (res,rst)` mp_tac>> ntac 2 FULL_CASE_TAC>>fs[]>>
    imp_res_tac locals_rel_get_vars>>
    fs[set_vars_def]>>imp_res_tac locals_rel_alist_insert>>
    fs[state_component_equality]>>
    rw[]>>metis_tac[])
  >>
    cheat)

val locals_rel_get_var = prove(``
  get_var r st = SOME x ∧ 
  locals_rel st.locals loc ⇒ 
  get_var r (st with locals:=loc) = SOME x``,
  fs[get_var_def,locals_rel_def])

val locals_rel_get_var_imm = prove(``
  get_var_imm r st = SOME x ∧ 
  locals_rel st.locals loc ⇒ 
  get_var_imm r (st with locals:=loc) = SOME x``,
  Cases_on`r`>>fs[get_var_imm_def]>>
  metis_tac[locals_rel_get_var])

val inst_select_thm = prove(``
  ∀c temp prog st res rst loc.
  evaluate (prog,st) = (res,rst) ∧
  every_var (λx. x < temp) prog ∧   
  res ≠ SOME Error ∧
  locals_rel st.locals loc ⇒
  ∃loc'. 
  evaluate (inst_select c temp prog,st with locals:=loc) = (res,rst with locals:=loc') ∧
  locals_rel rst.locals loc'``,
  ho_match_mp_tac inst_select_ind>>rw[]>>
  fs[inst_select_def,locals_rel_eval_thm]
  >-
    (*Assign*)
    cheat
  >-
    (*Set*)
    cheat
  >-
    (*Store*)
    cheat
  >- 
    (*Seq*)
    (fs[evaluate_def,LET_THM]>>Cases_on`evaluate(prog,st)`>>
    fs[every_var_def,GSYM AND_IMP_INTRO]>>
    `q ≠ SOME Error` by (EVERY_CASE_TAC>>fs[])>>
    first_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th)) >>
    fs[]>> disch_then (qspec_then`loc` assume_tac)>>rfs[]>>
    IF_CASES_TAC>>fs[]>>
    metis_tac[])
  >-
    (fs[evaluate_def]>>ntac 4 (pop_assum mp_tac)>>ntac 4 FULL_CASE_TAC>>fs[]>>
    rw[]>> imp_res_tac locals_rel_get_var>>
    imp_res_tac locals_rel_get_var_imm>>fs[GSYM AND_IMP_INTRO,every_var_def])
  >>
    cheat)

(*No expressions nesting*)
val flat_exp_conventions_def = Define`
  (*These should be converted to Insts*)
  (flat_exp_conventions (Assign v exp) = F) ∧
  (flat_exp_conventions (Store exp num) = F) ∧ 
  (*The only place where top level (expression) vars are allowed*)
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

(*3rd step: 3 to 2 reg if necessary*)

val distinct_tar_reg_def = Define`
  (distinct_tar_reg (Arith (Binop bop r1 r2 ri)) 
    ⇔ (r1 ≠ r2 ∧ case ri of (Reg r3) => r1 ≠ r3 | _ => T)) ∧ 
  (distinct_tar_reg  (Arith (Shift l r1 r2 n))
    ⇔ r1 ≠ r2) ∧ 
  (distinct_tar_reg _ ⇔ T)`

(*Instructions are 2 register code for arith ok*)
val two_reg_inst_def = Define`
  (two_reg_inst (Arith (Binop bop r1 r2 ri)) 
    ⇔ (r1 = r2)) ∧ 
  (two_reg_inst (Arith (Shift l r1 r2 n))
    ⇔ (r1 = r2)) ∧ 
  (two_reg_inst _ ⇔ T)`

(*TODO: move to HOL*)
val insert_shadow = prove(``
  ∀t a b c.
  insert a b (insert a c t) = insert a b t``,
  completeInduct_on`a`>>
  Induct>>
  simp[Once insert_def]>>
  rw[]>>
  simp[Once insert_def]>>
  simp[Once insert_def,SimpRHS]>>
  `(a-1) DIV 2 < a` by 
    (`0 < (2:num)` by fs[] >>
    imp_res_tac DIV_LT_X>>
    first_x_assum match_mp_tac>>
    DECIDE_TAC)>>
  metis_tac[])
 
(*Semantics preservation*)
val three_to_two_reg_correct = prove(``
  ∀prog s res s'.
  every_inst distinct_tar_reg prog ∧ 
  evaluate (prog,s) = (res,s') ∧ res ≠ SOME Error
  ⇒ 
  evaluate(three_to_two_reg prog,s) = (res,s')``,
  ho_match_mp_tac three_to_two_reg_ind>>
  rw[]>>fs[three_to_two_reg_def,evaluate_def,state_component_equality]>>
  TRY
    (ntac 2 (pop_assum mp_tac)>>fs[inst_def,assign_def,word_exp_def,get_vars_def,get_var_def,set_vars_def,alist_insert_def]>>
    EVERY_CASE_TAC >>
    fs[LET_THM,alist_insert_def,every_inst_def,distinct_tar_reg_def,word_exp_def,lookup_insert,set_var_def,insert_shadow]>>NO_TAC)
  >-
    (ntac 2 (pop_assum mp_tac)>>LET_ELIM_TAC>>fs[every_inst_def]>>
    Cases_on`res'' = SOME Error`>>fs[]>>res_tac>>
    EVERY_CASE_TAC>>fs[]>>
    metis_tac[])
  >-
    (ntac 2 (pop_assum mp_tac)>>LET_ELIM_TAC>>fs[every_inst_def]>>
    unabbrev_all_tac>>
    Cases_on`ret`>>Cases_on`handler`>>fs[evaluate_def]
    >-
      (EVERY_CASE_TAC>>fs[])
    >-
      (EVERY_CASE_TAC>>fs[]>>
      res_tac>>fs[]>>
      rfs[])
    >>
      PairCases_on`x`>>PairCases_on`x'`>>fs[]>>
      Cases_on`get_vars args s`>>fs[]>>
      Cases_on`find_code dest x s.code`>>fs[]>>
      Cases_on`x'`>>Cases_on`cut_env x1 s.locals`>>fs[]>>
      IF_CASES_TAC>>fs[push_env_def,LET_THM]>>
      EVERY_CASE_TAC>>fs[]>>
      res_tac>>fs[]>>
      rfs[]))

(*Syntactic correctness*)
val three_to_two_reg_syn = prove(``
  ∀prog. every_inst two_reg_inst (three_to_two_reg prog)``,
  ho_match_mp_tac three_to_two_reg_ind>>rw[]>>fs[every_inst_def,two_reg_inst_def,three_to_two_reg_def,LET_THM]>>EVERY_CASE_TAC>>fs[])

(*word_alloc preserves all syntactic program convs*)
val word_alloc_two_reg_inst_lem = prove(``
  ∀f prog. 
  every_inst two_reg_inst prog ⇒ 
  every_inst two_reg_inst (apply_colour f prog)``,
  ho_match_mp_tac apply_colour_ind>>fs[every_inst_def]>>rw[]
  >-
    (Cases_on`i`>>TRY(Cases_on`a`)>>TRY(Cases_on`m`)>>
    fs[apply_colour_inst_def,two_reg_inst_def])
  >>
    EVERY_CASE_TAC>>unabbrev_all_tac>>fs[every_inst_def])

val word_alloc_two_reg_inst = prove(``
  ∀k prog.
  every_inst two_reg_inst prog ⇒ 
  every_inst two_reg_inst (word_alloc k prog)``,
  fs[word_alloc_two_reg_inst_lem,word_alloc_def,LET_THM])

val word_alloc_flat_exp_conventions_lem = prove(``
  ∀f prog. 
  flat_exp_conventions prog ⇒ 
  flat_exp_conventions (apply_colour f prog)``,
  ho_match_mp_tac apply_colour_ind>>fs[flat_exp_conventions_def]>>rw[]
  >-
    (EVERY_CASE_TAC>>unabbrev_all_tac>>fs[flat_exp_conventions_def])
  >>
    Cases_on`exp`>>fs[flat_exp_conventions_def])

val word_alloc_flat_exp_conventions = prove(``
  ∀k prog.
  flat_exp_conventions prog ⇒ 
  flat_exp_conventions (word_alloc k prog)``,
  fs[word_alloc_flat_exp_conventions_lem,word_alloc_def,LET_THM])

val fake_moves_flat_exp_conventions = prove(``
  ∀ls ssal ssar na l r a b c.
  fake_moves ls ssal ssar na = (l,r,a,b,c) ⇒ 
  flat_exp_conventions l ∧ 
  flat_exp_conventions r``,
  Induct>>fs[fake_moves_def]>>rw[]>>fs[flat_exp_conventions_def]>>
  pop_assum mp_tac>> LET_ELIM_TAC>> EVERY_CASE_TAC>> fs[LET_THM]>>unabbrev_all_tac>>
  metis_tac[flat_exp_conventions_def,fake_move_def])

(*ssa generates distinct regs and also preserves flattening*)
val ssa_cc_trans_flat_exp_conventions_lem = prove(``
  ∀prog ssa na.
  flat_exp_conventions prog ⇒
  flat_exp_conventions (FST (ssa_cc_trans prog ssa na))``,
  ho_match_mp_tac ssa_cc_trans_ind>>fs[ssa_cc_trans_def]>>rw[]>>
  unabbrev_all_tac>>
  fs[flat_exp_conventions_def]
  >-
    (pop_assum mp_tac>>fs[fix_inconsistencies_def,fake_moves_def]>>LET_ELIM_TAC>>fs[flat_exp_conventions_def]>>
    metis_tac[fake_moves_flat_exp_conventions,flat_exp_conventions_def])
  >-
    (fs[list_next_var_rename_move_def]>>rpt (pop_assum mp_tac)>>
    LET_ELIM_TAC>>fs[flat_exp_conventions_def,EQ_SYM_EQ])
  >-
    (Cases_on`exp`>>fs[ssa_cc_trans_exp_def,flat_exp_conventions_def])
  >>
    EVERY_CASE_TAC>>unabbrev_all_tac>>fs[flat_exp_conventions_def]
    >-
      (fs[list_next_var_rename_move_def]>>rpt (pop_assum mp_tac)>>
      LET_ELIM_TAC>>fs[flat_exp_conventions_def,EQ_SYM_EQ])
    >>
      LET_ELIM_TAC>>unabbrev_all_tac>>
      fs[list_next_var_rename_move_def,flat_exp_conventions_def]>>
      fs[fix_inconsistencies_def]>>
      rpt (pop_assum mp_tac)>> LET_ELIM_TAC>>fs[]>>
      metis_tac[fake_moves_flat_exp_conventions,flat_exp_conventions_def])

val _ = export_theory ();
