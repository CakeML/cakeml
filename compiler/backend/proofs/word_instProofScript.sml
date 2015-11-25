open preamble BasicProvers
     wordLangTheory wordPropsTheory word_instTheory wordSemTheory
     asmTheory word_allocTheory word_allocProofTheory

val _ = new_theory "word_instProof";

val convert_sub_ok = prove(``
  ∀ls.
  word_exp s (convert_sub ls) = word_exp s (Op Sub ls)``,
  ho_match_mp_tac convert_sub_ind>>rw[convert_sub_def,word_exp_def]>>unabbrev_all_tac>>
  fs[word_op_def]>>
  EVERY_CASE_TAC>>
  fs[WORD_NEG_MUL,WORD_NOT])

(*In general, any permutation works*)
val word_exp_op_permute_lem = prove(``
  op ≠ Sub ⇒
  ∀ls ls'.
  PERM ls ls' ⇒
  word_exp s (Op op ls) = word_exp s (Op op ls')``,
  strip_tac>>
  ho_match_mp_tac PERM_STRONG_IND>>rw[]>>
  fs[word_exp_def,LET_THM]>>
  qpat_abbrev_tac`A = MAP f ls`>>
  qpat_abbrev_tac`B = MAP f ls'`>>
  `PERM A B` by metis_tac[PERM_MAP]>>
  `EVERY IS_SOME A ⇔ EVERY IS_SOME B` by metis_tac[PERM_EVERY]>>
  Cases_on`EVERY IS_SOME A` >>
  (*Don't know why simplifier removes EVERY in a bad way here...*)
  TRY
  (`~EVERY IS_SOME B` by metis_tac[]>>
  simp[])>>fs[]>>IF_CASES_TAC>>fs[]>>
  Cases_on`op`>>fs[word_op_def])

(*Remove tail recursion to make proof easier...*)
val pull_ops_simp_def = Define`
  (pull_ops_simp op [] = [] ) ∧
  (pull_ops_simp op (x::xs) =
    case x of
    |  (Op op' ls) => if op = op' then ls ++ (pull_ops_simp op xs) else x::(pull_ops_simp op xs)
    |  _  => x::(pull_ops_simp op xs))`

val PERM_SWAP_SIMP = prove(``
  PERM (A ++ (B::C)) (B::(A++C))``,
  match_mp_tac APPEND_PERM_SYM>>fs[]>>
  metis_tac[PERM_APPEND])

val EL_FILTER = prove(``
  ∀ls x. x < LENGTH (FILTER P ls) ⇒ P (EL x (FILTER P ls))``,
  Induct>>rw[]>>
  Cases_on`x`>>fs[EL])

val PERM_SWAP = prove(``
  PERM (A ++ B ++ C) (B++(A++C))``,
  fs[PERM_DEF]>>rw[]>>
  match_mp_tac LIST_EQ>>CONJ_ASM1_TAC
  >-
    (fs[FILTER_APPEND]>>DECIDE_TAC)
  >>
  rw[]>>
  imp_res_tac EL_FILTER>>
  last_x_assum SUBST_ALL_TAC>>
  imp_res_tac EL_FILTER>>
  metis_tac[])

val pull_ops_simp_pull_ops_perm = prove(``
  ∀ls x.
  PERM (pull_ops op ls x) ((pull_ops_simp op ls)++x)``,
  Induct>>fs[pull_ops_def,pull_ops_simp_def]>>rw[]>>EVERY_CASE_TAC>>fs[]>>
  TRY(qpat_abbrev_tac`A = B::x`>>
  first_x_assum(qspec_then`A` assume_tac)>>fs[Abbr`A`])>>
  TRY(first_x_assum(qspec_then`l++x` assume_tac))>>
  metis_tac[PERM_SWAP,PERM_TRANS,PERM_SWAP_SIMP,PERM_SYM])

val pull_ops_simp_pull_ops_word_exp = prove(``
  op ≠ Sub ⇒
  word_exp s (Op op (pull_ops op ls [])) = word_exp s (Op op (pull_ops_simp op ls))``,
  strip_tac>> imp_res_tac word_exp_op_permute_lem>>
  pop_assum match_mp_tac>>
  assume_tac pull_ops_simp_pull_ops_perm>>
  pop_assum (qspecl_then [`ls`,`[]`] assume_tac)>>fs[])

val word_exp_op_mono = prove(``
  op ≠ Sub ⇒
  word_exp s (Op op ls) = word_exp s (Op op ls') ⇒
  word_exp s (Op op (x::ls)) =
  word_exp s (Op op (x::ls'))``,
  rw[word_exp_def,LET_THM]>>
  Cases_on`op`>>fs[word_op_def])

val word_exp_op_op = prove(``
  op ≠ Sub ⇒
  ∀ls ls'.
  word_exp s (Op op ls) = word_exp s (Op op ls') ⇒
  word_exp s (Op op (l ++ ls)) =
  word_exp s (Op op ((Op op l) :: ls'))``,
  rw[word_exp_def,LET_THM]>>
  qpat_abbrev_tac`A = MAP f ls`>>
  qpat_abbrev_tac`B = MAP f ls'`>>
  qpat_abbrev_tac`C = MAP f l`>>
  `EVERY IS_SOME A ⇔ EVERY IS_SOME B` by
    (Cases_on`op`>>fs[word_op_def]>>
    qpat_assum`C=D` mp_tac >>EVERY_CASE_TAC>>fs[])>>
  Cases_on`EVERY IS_SOME A` >>
  TRY
  (`~EVERY IS_SOME B` by metis_tac[]>>
  simp[])>>fs[]>>IF_CASES_TAC>>fs[]>>
  Cases_on`op`>>fs[word_op_def,FOLDR_APPEND]>>
  unabbrev_all_tac>>Induct_on`l`>>fs[])

val pull_ops_ok = prove(``
  op ≠ Sub ⇒
  ∀ls. word_exp s (Op op (pull_ops op ls [])) =
         word_exp s (Op op ls)``,
  strip_tac>>
  fs[pull_ops_simp_pull_ops_word_exp]>>
  Induct>>rw[pull_ops_simp_def]>>Cases_on`op`>>fs[]>>
  FULL_CASE_TAC>>fs[word_exp_op_mono]>>
  IF_CASES_TAC>>fs[word_exp_op_mono]>>
  `b ≠ Sub` by rw[]>>
  imp_res_tac word_exp_op_op>>
  pop_assum (qspec_then`l` assume_tac)>>fs[])

val word_exp_swap_head = prove(``
  ∀B.
  op ≠ Sub ⇒
  word_exp s (Op op A) = SOME w ⇒
  word_exp s (Op op (B++A)) = word_exp s (Op op (Const w::B))``,
  fs[word_exp_def,LET_THM,word_op_def]>>rw[]>>
  Cases_on`op`>>fs[FOLDR_APPEND]>>
  Induct_on`B`>>fs[])

val EVERY_is_const_word_exp = prove(``
  ∀ls. EVERY is_const ls ⇒
  EVERY IS_SOME (MAP (λa. word_exp s a) ls)``,
  Induct>>rw[]>>Cases_on`h`>>fs[is_const_def,word_exp_def])

val all_consts_simp = prove(``
  op ≠ Sub ⇒
  ∀ls.
  EVERY is_const ls ⇒
  word_exp s (Op op ls) =
  SOME( THE (word_op op (MAP rm_const ls)))``,
  strip_tac>>Induct>>fs[word_exp_def,LET_THM]
  >-
    (fs[word_op_def,word_instTheory.word_op_def]>>
    Cases_on`op`>>fs[])
  >>
  ntac 2 strip_tac>>
  Cases_on`h`>>fs[is_const_def,word_exp_def]>>
  fs[EVERY_is_const_word_exp]>>
  Cases_on`op`>>fs[word_op_def,rm_const_def,word_instTheory.word_op_def])

val optimize_consts_ok = prove(``
  op ≠ Sub ⇒
  ∀ls. word_exp s (optimize_consts op ls) =
       word_exp s (Op op ls)``,
  strip_tac>>rw[optimize_consts_def]>>
  Cases_on`const_ls`>>fs[]
  >-
    (imp_res_tac word_exp_op_permute_lem>>pop_assum match_mp_tac>>
    metis_tac[PERM_PARTITION,APPEND_NIL,PERM_SYM])
  >>
    LET_ELIM_TAC>>
    `EVERY is_const (h::t)` by
      (fs[PARTITION_DEF]>>
      imp_res_tac (GSYM PARTs_HAVE_PROP)>>fs[EVERY_MEM])>>
    imp_res_tac all_consts_simp>>
    `PERM ls ((h::t)++nconst_ls)` by metis_tac[PERM_PARTITION]>>
    imp_res_tac word_exp_op_permute_lem>>
    pop_assum(qspec_then`s` SUBST_ALL_TAC)>>
    Cases_on`nconst_ls`>>fs[]
    >-
      fs[word_exp_def,LET_THM]
    >>
    imp_res_tac word_exp_swap_head>>
    pop_assum(qspecl_then [`w`,`s`,`h::t`] assume_tac)>>
    rfs[]>>
    pop_assum(qspec_then`h'::t'` assume_tac)>>
    pop_assum sym_sub_tac>>
    pop_assum kall_tac>>imp_res_tac word_exp_op_permute_lem>>
    pop_assum match_mp_tac>>
    qpat_abbrev_tac`A = h'::t'`>>
    qpat_abbrev_tac`B = h::t`>>
    `h:: (t ++A) = B ++A` by fs[]>>pop_assum SUBST_ALL_TAC>>
    metis_tac[PERM_APPEND])

val pull_exp_ok = prove(``
  ∀exp s.
  word_exp s exp = word_exp s (pull_exp exp)``,
  ho_match_mp_tac pull_exp_ind>>rw[]>>
  fs[pull_exp_def,LET_THM]>>
  TRY(fs[op_consts_def,word_exp_def,LET_THM,word_op_def]>>NO_TAC)
  >-
    (simp[convert_sub_ok,word_exp_def,MAP_MAP_o]>>
    qpat_abbrev_tac`ws = MAP f ls`>>
    qpat_abbrev_tac`ws = MAP f ls`>>
    `ws = ws'` by
      (match_mp_tac LIST_EQ>>unabbrev_all_tac>>fs[EL_MAP,EL_MEM])>>
    fs[GSYM MAP_MAP_o])
  >>
  TRY(fs[pull_exp_def,word_exp_def,LET_THM,word_op_def]>>IF_CASES_TAC>>fs[]>>
  first_x_assum(qspec_then `s` assume_tac)>>rfs[]>>
  pop_assum sym_sub_tac>>fs[IS_SOME_EXISTS]>>NO_TAC)>>
  assume_tac binop_distinct>>
  fs[optimize_consts_ok,pull_ops_ok]>>
  qpat_abbrev_tac`ls = A::B::C`>>
  `MAP (λa. word_exp s a) ls = MAP (λa. word_exp s a) (MAP pull_exp ls)` by
    (match_mp_tac LIST_EQ>>unabbrev_all_tac>>rw[]>>
    Cases_on`x`>>fs[]>>
    Cases_on`n`>>fs[]>>
    fs[EL_MAP,EL_MEM])>>
  unabbrev_all_tac>>fs[word_exp_def,ETA_AX])

val convert_sub_every_var_exp = prove(``
  ∀ls.
  (∀x. MEM x ls ⇒ every_var_exp P x) ⇒
  every_var_exp P (convert_sub ls)``,
  ho_match_mp_tac convert_sub_ind>>rw[convert_sub_def]>>
  fs[every_var_exp_def,EVERY_MEM])

val optimize_consts_every_var_exp = prove(``
  ∀ls.
  (∀x. MEM x ls ⇒ every_var_exp P x) ⇒
  every_var_exp P (optimize_consts op ls)``,
  rw[optimize_consts_def]>>
  `PERM ls (const_ls++nconst_ls)` by metis_tac[PERM_PARTITION]>>fs[]>>
  imp_res_tac PERM_MEM_EQ>>
  EVERY_CASE_TAC>>fs[every_var_exp_def,LET_THM,EVERY_MEM])

val pull_ops_every_var_exp = prove(``
  ∀ls acc.
  EVERY (every_var_exp P) acc ∧ EVERY (every_var_exp P) ls ⇒
  EVERY (every_var_exp P) (pull_ops op ls acc)``,
  Induct>>fs[pull_ops_def]>>rw[]>>EVERY_CASE_TAC>>fs[every_var_exp_def]>>
  metis_tac[ETA_AX,EVERY_APPEND,every_var_exp_def]) |> REWRITE_RULE[EVERY_MEM]

val pull_exp_every_var_exp = prove(``
  ∀exp.
  every_var_exp P exp ⇒
  every_var_exp P (pull_exp exp)``,
  ho_match_mp_tac pull_exp_ind>>fs[op_consts_def,pull_exp_def,every_var_exp_def,EVERY_MEM,EVERY_MAP,LET_THM]>>rw[]
  >-
    metis_tac[convert_sub_every_var_exp,MEM_MAP,PULL_EXISTS]
  >>
    match_mp_tac optimize_consts_every_var_exp>>
    match_mp_tac pull_ops_every_var_exp>>rw[]>>
    metis_tac[MEM_MAP])

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
    fs[op_consts_def,word_exp_def,LET_THM,word_op_def]>>IF_CASES_TAC>>fs[]>>
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
  ho_match_mp_tac flatten_exp_ind>>fs[op_consts_def,flatten_exp_def,binary_branch_exp_def,EVERY_MEM,EVERY_MAP])

val flatten_exp_every_var_exp = prove(``
  ∀exp.
  every_var_exp P exp ⇒
  every_var_exp P (flatten_exp exp)``,
  ho_match_mp_tac flatten_exp_ind>>fs[op_consts_def,flatten_exp_def,every_var_exp_def,EVERY_MEM,EVERY_MAP])

val num_exp_equiv = prove(``
  word_inst$num_exp = wordSem$num_exp``,
  fs[FUN_EQ_THM]>>Induct>>
  fs[wordSemTheory.num_exp_def,word_instTheory.num_exp_def])

(*2nd step: Convert expressions to insts*)
val inst_select_exp_thm = prove(``
  ∀c tar temp exp s w loc.
  binary_branch_exp exp ∧
  every_var_exp (λx. x < temp) exp ∧
  locals_rel temp s.locals loc ∧
  word_exp s exp = SOME w
  ⇒
  ∃loc'.
  evaluate ((inst_select_exp c tar temp exp),s with locals:=loc) = (NONE:'a result option,s with locals:=loc') ∧
  ∀x.
    if x = tar then lookup x loc' = SOME (Word w)
    else if x < temp then lookup x loc' = lookup x s.locals
    else T``,
  completeInduct_on`exp_size (K 0) exp`>>
  rpt strip_tac>>
  Cases_on`exp`>>
  fs[evaluate_def,binary_branch_exp_def,every_var_exp_def]
  >-
    (simp[inst_select_exp_def]>>
    fs[LET_THM,evaluate_def,inst_def,assign_def,word_exp_def,set_var_def,mem_load_def,word_op_def]>>
    simp[state_component_equality,locals_rel_def,lookup_insert]>>
    fs[locals_rel_def])
  >-
    (simp[inst_select_exp_def]>>
    fs[LET_THM,evaluate_def,inst_def,assign_def,word_exp_def,set_var_def,mem_load_def,word_op_def,get_vars_def,set_vars_def,get_var_def]>>
    fs[locals_rel_def]>>pop_assum mp_tac>>ntac 2 FULL_CASE_TAC>>fs[]>>
    res_tac>>fs[alist_insert_def]>>rw[]>>
    simp[state_component_equality,lookup_insert])
  >-
    (simp[inst_select_exp_def]>>
    fs[LET_THM,evaluate_def,inst_def,assign_def,word_exp_def,set_var_def,mem_load_def,word_op_def,get_vars_def,set_vars_def,get_var_def]>>
    FULL_CASE_TAC>>fs[]>>pop_assum mp_tac>>FULL_CASE_TAC>>fs[locals_rel_def]>>
    simp[state_component_equality,lookup_insert])
  >-
    (*Load*)
    (Cases_on`∃exp' w'. e = Op Add[exp';Const w']` >>fs[]
    >-
      (simp[Once inst_select_exp_def]>>IF_CASES_TAC
      >-
        (fs[binary_branch_exp_def,every_var_exp_def,word_exp_def,LET_THM]>>EVERY_CASE_TAC>>fs[IS_SOME_EXISTS]>>rfs[]>>
        last_x_assum mp_tac>>simp[Once PULL_FORALL]>>disch_then (qspec_then`exp'` mp_tac)>>simp[exp_size_def]>>strip_tac>>res_tac>>
        pop_assum(qspecl_then[`temp`,`c`] assume_tac)>>fs[evaluate_def,LET_THM]>>
        simp[evaluate_def,LET_THM,inst_def,assign_def,word_exp_def]>>
        `lookup temp loc'' = SOME (Word x')` by metis_tac[]>>fs[mem_load_def]>>
        fs[state_component_equality,set_var_def,lookup_insert]>>rw[]>>
        DISJ2_TAC>>strip_tac>>`x'' ≠ temp` by DECIDE_TAC>>metis_tac[])
      >>
        (last_x_assum mp_tac>>simp[Once PULL_FORALL]>>
        disch_then (qspec_then`e`mp_tac)>>
        discharge_hyps>-(fs[exp_size_def]>>DECIDE_TAC)>>
        fs[binary_branch_exp_def,every_var_exp_def,LET_THM]>>EVERY_CASE_TAC>>fs[IS_SOME_EXISTS]>>rfs[]>>
        qpat_assum`A=SOME w` mp_tac>>simp[Once word_exp_def]>>FULL_CASE_TAC>>
        rw[]>>res_tac>>
        pop_assum(qspecl_then[`temp`,`c`] assume_tac)>>fs[evaluate_def,LET_THM]>>
        simp[evaluate_def,LET_THM,inst_def,assign_def,word_exp_def]>>
        `lookup temp loc'' = SOME (Word x)` by metis_tac[]>>fs[mem_load_def]>>
        fs[state_component_equality,set_var_def,lookup_insert]>>rw[]>>
        simp[state_component_equality,set_var_def,lookup_insert,word_op_def]>>
        rw[]>>
        DISJ2_TAC>>strip_tac>>`x' ≠ temp` by DECIDE_TAC>>metis_tac[]))
    >>
      `inst_select_exp c tar temp (Load e) =
        let prog = inst_select_exp c temp temp e in
          Seq prog (Inst (Mem Load tar (Addr temp (0w))))` by
      (fs[inst_select_exp_def,LET_THM]>>EVERY_CASE_TAC>>fs[])>>
      last_x_assum mp_tac>>simp[Once PULL_FORALL]>>
      disch_then (qspec_then`e`mp_tac)>>
      discharge_hyps>-(fs[exp_size_def]>>DECIDE_TAC)>>
      strip_tac>>fs[word_exp_def]>>EVERY_CASE_TAC>>fs[]>>
      res_tac>>
      pop_assum(qspecl_then[`temp`,`c`] assume_tac)>>fs[evaluate_def,LET_THM]>>
      `lookup temp loc'' = SOME (Word x)` by metis_tac[]>>
      simp[inst_def,assign_def,word_exp_def,word_op_def]>>fs[mem_load_def]>>
      simp[state_component_equality,set_var_def,lookup_insert]>>
      rw[]>>DISJ2_TAC>>strip_tac>>
      `x' ≠ temp` by DECIDE_TAC>>metis_tac[])
  >-
    (*Op*)
    (Cases_on`∃e1 e2. l = [e1;e2]`>>fs[inst_select_exp_def]
    >-
      (`binary_branch_exp e1` by
        (Cases_on`b`>>fs[binary_branch_exp_def])>>
      fs[word_exp_def,LET_THM,IS_SOME_EXISTS]>>
      last_x_assum mp_tac>>simp[Once PULL_FORALL]>>
      disch_then assume_tac>> first_assum mp_tac>>
      disch_then (qspec_then`e1`mp_tac)>>
        discharge_hyps>-(fs[exp_size_def]>>DECIDE_TAC)>>
      strip_tac>>res_tac>>
      pop_assum(qspecl_then[`temp`,`c`] assume_tac)>>fs[]>>
      Cases_on`∃w. e2 = Const w`
      >-
        (fs[]>>IF_CASES_TAC
        >-
          (fs[evaluate_def]>>
          simp[LET_THM,inst_def,word_exp_def,assign_def]>>
          `lookup temp loc'' = SOME (Word x)` by metis_tac[]>>
          fs[word_op_def]>>
          Cases_on`b`>>
          fs[set_var_def,state_component_equality,lookup_insert,word_exp_def]>>
          rw[]>>DISJ2_TAC>>strip_tac>>`x'' ≠ temp` by DECIDE_TAC>>metis_tac[])
        >> IF_CASES_TAC
        >-
          (simp[evaluate_def,LET_THM,inst_def,assign_def,word_exp_def,set_var_def,lookup_insert]>>
          `lookup temp loc'' = SOME (Word x)` by metis_tac[]>>
          fs[]>>rfs[word_exp_def,word_op_def]>>
          fs[state_component_equality,lookup_insert]>>rw[]>>
          DISJ2_TAC>>strip_tac>>
          `x'' ≠ temp` by DECIDE_TAC>>
          metis_tac[])
        >>
          (simp[evaluate_def,LET_THM,inst_def,assign_def,word_exp_def,set_var_def,lookup_insert]>>
          `lookup temp loc'' = SOME (Word x)` by metis_tac[]>>
          fs[]>>rfs[word_exp_def]>>
          fs[state_component_equality,lookup_insert]>>
          rw[]>>
          DISJ2_TAC>>strip_tac>-`F` by DECIDE_TAC>>
          `x'' ≠ temp` by DECIDE_TAC>>
          `¬ (temp+1 < temp)` by DECIDE_TAC>>
          metis_tac[]))
      >>
        `inst_select_exp c tar temp (Op b [e1;e2]) =
        let p1 = inst_select_exp c temp temp e1 in
        let p2 = inst_select_exp c (temp+1) (temp+1) e2 in
        Seq p1 (Seq p2 (Inst (Arith (Binop b tar temp (Reg (temp+1))))))` by
        (fs[inst_select_exp_def,LET_THM]>>EVERY_CASE_TAC>>fs[])>>
        fs[inst_select_exp_def,LET_THM]>>pop_assum kall_tac>>
        fs[evaluate_def,LET_THM]>>
        first_x_assum(qspecl_then[`e2`] mp_tac)>>
        simp[exp_size_def]>>
        disch_then(qspecl_then [`c`,`temp+1`,`temp+1`,`s with locals:=loc''`,`x'`,`loc''`] mp_tac)>>
        discharge_hyps>-
          (rw[locals_rel_def]>-(Cases_on`b`>>fs[binary_branch_exp_def])
          >-
            (match_mp_tac every_var_exp_mono>>
            HINT_EXISTS_TAC>>fs[]>>DECIDE_TAC)
          >>
            (*word_exp invariant under extra locals*)
            match_mp_tac locals_rel_word_exp>>
            fs[locals_rel_def]>>
            rw[]>>`x'' ≠ temp` by DECIDE_TAC>>
            metis_tac[])>>
        strip_tac>>fs[word_exp_def]>>
        `lookup temp loc''' = SOME (Word x) ∧
         lookup (temp+1) loc''' = SOME (Word x')` by
         (first_assum(qspecl_then[`temp`] assume_tac)>>
         first_x_assum(qspecl_then[`temp+1`] assume_tac)>>
         `temp ≠ temp+1` by DECIDE_TAC>>
         fs[]>>metis_tac[])>>
        rfs[]>>
        simp[inst_def,assign_def,word_exp_def,LET_THM,state_component_equality,set_var_def,lookup_insert]>>
        rw[]>>DISJ2_TAC>>strip_tac>>
        `x''<temp+1 ∧ x'' ≠ temp ∧ x'' ≠ temp+1` by DECIDE_TAC>>
        metis_tac[])
    >>
      (Cases_on`b`>>fs[binary_branch_exp_def,word_exp_def,LET_THM,word_op_def]>>Cases_on`l`>>fs[]>>Cases_on`t`>>fs[]>>Cases_on`t'`>>fs[]))
  >-
    (simp[inst_select_exp_def]>>last_x_assum mp_tac>>simp[Once PULL_FORALL]>>disch_then (qspec_then`e`mp_tac)>>discharge_hyps>-(fs[exp_size_def]>>DECIDE_TAC)>>
    fs[LET_THM,word_exp_def]>>EVERY_CASE_TAC>>fs[]
    >-
      (`word_sh s' x (num_exp n) = SOME x` by
        (fs[word_sh_def]>>EVERY_CASE_TAC)>>
      rw[]>>res_tac>>
      first_assum(qspecl_then[`temp`,`c`] assume_tac)>>
      fs[evaluate_def,LET_THM,get_vars_def,get_var_def]>>
      `lookup temp loc'' = SOME (Word x)` by metis_tac[]>>
      fs[set_vars_def,alist_insert_def,state_component_equality,num_exp_equiv,lookup_insert]>>
      rw[]>>DISJ2_TAC>>strip_tac>>`x' ≠ temp` by DECIDE_TAC>>metis_tac[])
    >-
      (assume_tac DIMINDEX_GT_0>>
      `0 ≠ dimindex(:'a)` by DECIDE_TAC>>fs[])
    >-
      (
      rw[]>>res_tac>>
      first_assum(qspecl_then[`temp`,`c`] assume_tac)>>
      fs[evaluate_def,LET_THM,inst_def,assign_def,word_exp_def]>>
      `lookup temp loc'' = SOME (Word x)` by metis_tac[]>>
      fs[num_exp_def,num_exp_equiv,set_var_def,state_component_equality,lookup_insert]>>
      rw[]>>DISJ2_TAC>>strip_tac>>`x' ≠ temp` by DECIDE_TAC>>
      metis_tac[])
    >-
      (`num_exp n ≥ dimindex(:'a)` by DECIDE_TAC>>
      fs[word_sh_def,num_exp_equiv])))

val locals_rm = prove(``
  D with locals := D.locals = D``,
  fs[state_component_equality])

(*  Main semantics theorem for inst selection:
    The inst-selected program gives same result but
    with possibly more locals used
*)
val inst_select_thm = prove(``
  ∀c temp prog st res rst loc.
  evaluate (prog,st) = (res,rst) ∧
  every_var (λx. x < temp) prog ∧
  res ≠ SOME Error ∧
  locals_rel temp st.locals loc ⇒
  ∃loc'.
  evaluate (inst_select c temp prog,st with locals:=loc) = (res,rst with locals:=loc') ∧
  locals_rel temp rst.locals loc'``,
  ho_match_mp_tac inst_select_ind>>rw[]>>
  fs[inst_select_def,locals_rel_evaluate_thm]
  >-
    (fs[evaluate_def]>>last_x_assum mp_tac>>FULL_CASE_TAC>>rw[]>>
    fs[every_var_def]>>
    imp_res_tac pull_exp_every_var_exp>>
    imp_res_tac flatten_exp_every_var_exp>>
    fs[Once pull_exp_ok]>>
    fs[Once flatten_exp_ok]>>
    assume_tac flatten_exp_binary_branch_exp>>
    pop_assum(qspec_then`pull_exp exp` assume_tac)>>
    imp_res_tac inst_select_exp_thm>>rfs[]>>
    first_x_assum(qspecl_then[`c'`,`c`] assume_tac)>>fs[]>>
    simp[state_component_equality,set_var_def,locals_rel_def]>>
    rw[]>>fs[lookup_insert]>>Cases_on`x'=c'`>>fs[]>>
    metis_tac[])
  >-
    (fs[evaluate_def]>>last_x_assum mp_tac>>
    FULL_CASE_TAC>>fs[]>>strip_tac>>
    fs[every_var_def]>>
    imp_res_tac pull_exp_every_var_exp>>
    imp_res_tac flatten_exp_every_var_exp>>
    fs[Once pull_exp_ok]>>
    fs[Once flatten_exp_ok]>>
    assume_tac flatten_exp_binary_branch_exp>>
    pop_assum(qspec_then`pull_exp exp` assume_tac)>>
    imp_res_tac inst_select_exp_thm>>rfs[]>>
    first_x_assum(qspecl_then[`temp`,`c`] assume_tac)>>fs[]>>
    fs[LET_THM,evaluate_def,word_exp_def]>>
    first_assum(qspec_then`temp` assume_tac)>>fs[set_store_def]>>
    fs[state_component_equality,locals_rel_def]>>
    rw[]>>`x' ≠ temp` by DECIDE_TAC>>metis_tac[])
  >-
    (fs[evaluate_def]>>last_x_assum mp_tac>>
    ntac 3 FULL_CASE_TAC>>fs[]>>strip_tac>>
    qpat_abbrev_tac`expr = flatten_exp (pull_exp exp)`>>
    Cases_on`∃w exp'. expr = Op Add [exp';Const w]`>>
    fs[LET_THM]
    >-
      (IF_CASES_TAC
      >-
        (fs[Abbr`expr`,every_var_def]>>
        imp_res_tac pull_exp_every_var_exp>>
        fs[Once pull_exp_ok]>>
        fs[Once flatten_exp_ok,word_exp_def,LET_THM,IS_SOME_EXISTS]>>
        imp_res_tac flatten_exp_every_var_exp>>rfs[every_var_exp_def]>>
        fs[]>>
        imp_res_tac inst_select_exp_thm>> ntac 5 (pop_assum kall_tac)>>
        pop_assum mp_tac>>discharge_hyps>-
          (assume_tac flatten_exp_binary_branch_exp>>
          pop_assum(qspec_then`pull_exp exp` mp_tac)>>simp[binary_branch_exp_def])>>
        rw[]>>
        fs[evaluate_def,LET_THM]>>first_x_assum(qspecl_then [`temp`,`c`] assume_tac)>>
        fs[inst_def,word_exp_def]>>
        `lookup temp loc' = SOME(Word x''')` by metis_tac[]>>
        simp[LET_THM]>>
        `get_var var (st with locals := loc') = SOME x` by
          (fs[get_var_def]>>
          `var ≠ temp` by DECIDE_TAC>>metis_tac[])>>
        fs[mem_store_def]>>
        fs[state_component_equality,locals_rel_def]>>
        rw[]>>`x'' ≠ temp` by DECIDE_TAC>>metis_tac[])
      >>
        qpat_assum`expr =A` sym_sub_tac>>
        fs[Once pull_exp_ok]>>
        fs[Once flatten_exp_ok]>>
        imp_res_tac inst_select_exp_thm>>
        fs[AND_IMP_INTRO]>> pop_assum mp_tac>>
        discharge_hyps
        >-
          (fs[every_var_def,Abbr`expr`]>>
          metis_tac[flatten_exp_every_var_exp,flatten_exp_binary_branch_exp,pull_exp_every_var_exp])
        >>
        disch_then (qspecl_then [`temp`,`c`] assume_tac)>>
        fs[evaluate_def,LET_THM,inst_def,word_exp_def]>>
        `lookup temp loc' = SOME (Word x')` by metis_tac[]>>
        fs[word_op_def]>>
        `get_var var (st with locals := loc') = SOME x` by
          (fs[get_var_def,every_var_def]>>
          `var ≠ temp` by DECIDE_TAC>>
          metis_tac[])>>
        fs[mem_store_def]>>
        fs[state_component_equality,locals_rel_def]>>
        rw[]>>`x''' ≠ temp` by DECIDE_TAC>>metis_tac[])
    >>
      `inst_select c temp (Store exp var) =
        Seq(inst_select_exp c temp temp expr)
        (Inst (Mem Store var (Addr temp 0w)))` by
        (fs[inst_select_def,LET_THM]>>
        EVERY_CASE_TAC>>fs[])>>
      fs[inst_select_def,LET_THM,Abbr`expr`]>>
      fs[Once pull_exp_ok]>>
      fs[Once flatten_exp_ok]>>
      imp_res_tac inst_select_exp_thm>>
      fs[AND_IMP_INTRO]>> pop_assum mp_tac>>
      discharge_hyps
      >-
        (fs[every_var_def]>>
        metis_tac[pull_exp_every_var_exp,flatten_exp_every_var_exp,flatten_exp_binary_branch_exp])
      >>
      disch_then(qspecl_then [`temp`,`c`] assume_tac)>>
      fs[evaluate_def,LET_THM,inst_def,word_exp_def]>>
      `lookup temp loc' = SOME (Word x')` by metis_tac[]>>
      fs[word_op_def,every_var_def]>>
      `get_var var (st with locals := loc') = SOME x` by
        (fs[get_var_def]>>`var ≠ temp` by DECIDE_TAC>>
        metis_tac[])>>
      fs[mem_store_def]>>
      fs[state_component_equality,locals_rel_def]>>rw[]>>
      `x''' ≠ temp` by DECIDE_TAC>>metis_tac[])
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
    (fs[evaluate_def]>>ntac 4 (pop_assum mp_tac)>>ntac 4 FULL_CASE_TAC>>
    fs[every_var_def]>>
    rw[]>> imp_res_tac locals_rel_get_var>>
    imp_res_tac locals_rel_get_var_imm>>fs[GSYM AND_IMP_INTRO,every_var_def])
  >>
    imp_res_tac locals_rel_evaluate_thm>>
    ntac 20 (pop_assum kall_tac)>>
    fs[LET_THM,evaluate_def,every_var_def]>>
    qpat_abbrev_tac `stt = st with locals := A`>>
    Cases_on`get_vars args stt`>>fs[]>>
    Cases_on`ret`>>fs[add_ret_loc_def]
    >-(*Tail Call*)
      (Cases_on`find_code dest x st.code`>>Cases_on`handler`>>
      TRY(PairCases_on`x'`)>>fs[]>>
      fs[call_env_def,dec_clock_def,state_component_equality,locals_rel_def])
    >>
      PairCases_on`x'`>>fs[add_ret_loc_def]>>
      Cases_on `find_code dest (Loc x'3 x'4::x) st.code`>>fs []>>
      PairCases_on`x'`>>fs[]>>
      Cases_on`cut_env x'1 loc`>>fs[]>>
      IF_CASES_TAC>-
        fs[call_env_def,state_component_equality,locals_rel_def]
      >>
      fs[]>>
      qpat_assum`A=(res,rst with locals:=loc')` mp_tac>>
      qpat_abbrev_tac`st = call_env B C`>>
      qpat_abbrev_tac`st' = call_env B C`>>
      `st' = st''` by
        (unabbrev_all_tac>>
        Cases_on`handler`>>TRY(PairCases_on`x''`)>>
        fs[call_env_def,push_env_def,dec_clock_def,push_env_def,LET_THM,env_to_list_def,state_component_equality])>>
      Cases_on`evaluate(x'1',st'')`>>Cases_on`q`>>fs[]>>
      Cases_on`x''`>>fs[]
      >-
        (IF_CASES_TAC>>fs[]>>
        FULL_CASE_TAC>>fs[]>>
        IF_CASES_TAC>>fs[]>>
        ntac 2 (FULL_CASE_TAC>>fs[])>>rw[]>>
        res_tac>>fs[]>>
        qpat_abbrev_tac`D = set_var A B C`>>
        first_x_assum(qspec_then`D.locals` assume_tac)>>fs[locals_rel_def]>>
        fs[locals_rm,state_component_equality])
      >-
        (Cases_on`handler`>>fs[state_component_equality]>>
        PairCases_on`x''`>>fs[]>>
        IF_CASES_TAC>>fs[]>>
        IF_CASES_TAC>>fs[]>>
        rw[]>>
        res_tac>>
        qpat_abbrev_tac`D = set_var A B C`>>
        first_x_assum(qspec_then`D.locals` assume_tac)>>fs[locals_rel_def]>>
        fs[locals_rm,state_component_equality])
      >>
        fs[state_component_equality])

(*No expressions occur except in Set, where it must be a Var expr*)
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

val inst_select_exp_flat_exp_conventions = prove(``
  ∀c tar temp exp.
  flat_exp_conventions (inst_select_exp c tar temp exp)``,
  ho_match_mp_tac inst_select_exp_ind>>rw[]>>fs[inst_select_exp_def,flat_exp_conventions_def,LET_THM]>>
  EVERY_CASE_TAC>>fs[flat_exp_conventions_def,inst_select_exp_def,LET_THM])

val inst_select_flat_exp_conventions = prove(``
  ∀c temp prog.
  flat_exp_conventions (inst_select c temp prog)``,
  ho_match_mp_tac inst_select_ind >>rw[]>>
  fs[flat_exp_conventions_def,inst_select_def,LET_THM]>>
  EVERY_CASE_TAC>>
  fs[flat_exp_conventions_def]>>
  metis_tac[inst_select_exp_flat_exp_conventions])

(*Less restrictive version of inst_ok guaranteed by inst_select*)
(*Note: We carry the assumption that 0 addr offsets are allowed by the config*)

val inst_ok_less_def = Define`
  (inst_ok_less (c:'a asm_config) (Arith (Binop b r1 r2 (Imm w)))=
    c.valid_imm (INL b) w) ∧
  (inst_ok_less c (Arith (Shift l r1 r2 n)) =
    (((n = 0) ==> (l = Lsl)) ∧ n < dimindex(:'a))) ∧
  (inst_ok_less c (Mem m r (Addr r' w)) =
    addr_offset_ok w c) ∧
  (inst_ok_less _ _ = T)`

val inst_select_exp_inst_ok_less = prove(``
  ∀c tar temp exp.
  addr_offset_ok 0w c ⇒
  every_inst (inst_ok_less c) (inst_select_exp c tar temp exp)``,
  ho_match_mp_tac inst_select_exp_ind>>rw[]>>fs[inst_select_exp_def,every_inst_def,LET_THM,inst_ok_less_def]>>
  every_case_tac>>fs[every_inst_def,inst_ok_less_def,inst_select_exp_def,LET_THM] )

val inst_select_inst_ok_less = prove(``
  ∀c temp prog.
  addr_offset_ok 0w c ∧
  every_inst (inst_ok_less c) prog
  ⇒
  every_inst (inst_ok_less c) (inst_select c temp prog)``,
  ho_match_mp_tac inst_select_ind>>rw[inst_select_def,every_inst_def]>>
  fs[LET_THM]>>unabbrev_all_tac>>EVERY_CASE_TAC>>fs[every_inst_def,inst_ok_less_def]>>
  metis_tac[inst_select_exp_inst_ok_less])

(*3rd step: 3 to 2 reg if necessary*)

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
  >>
    ntac 2 (pop_assum mp_tac)>>LET_ELIM_TAC>>fs[every_inst_def]>>
    unabbrev_all_tac>>
    Cases_on`ret`>>Cases_on`handler`>>fs[evaluate_def]
    >-
      (EVERY_CASE_TAC>>fs[])
    >-
      (ntac 5 (EVERY_CASE_TAC>>fs[add_ret_loc_def]>>
      res_tac>>fs[add_ret_loc_def]>>
      rfs[add_ret_loc_def]>>rw[]>>fs[]))
    >>
      PairCases_on`x`>>PairCases_on`x'`>>fs[]>>
      Cases_on`get_vars args s`>>fs[add_ret_loc_def]>>
      Cases_on`find_code dest (Loc x3 x4::x) s.code`>>fs[]>>
      Cases_on`x'`>>Cases_on`cut_env x1 s.locals`>>fs[]>>
      IF_CASES_TAC>>fs[push_env_def,LET_THM]>>
      EVERY_CASE_TAC>>fs[]>>
      res_tac>>fs[]>>
      rfs[])

(*Syntactic correctness*)
val three_to_two_reg_syn = prove(``
  ∀prog. every_inst two_reg_inst (three_to_two_reg prog)``,
  ho_match_mp_tac three_to_two_reg_ind>>rw[]>>fs[every_inst_def,two_reg_inst_def,three_to_two_reg_def,LET_THM]>>EVERY_CASE_TAC>>fs[])

(*word_alloc preserves syntactic conventions*)
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

val word_alloc_inst_ok_less_lem = prove(``
  ∀f prog c.
  every_inst (inst_ok_less c) prog ⇒
  every_inst (inst_ok_less c) (apply_colour f prog)``,
  ho_match_mp_tac apply_colour_ind>>fs[every_inst_def]>>rw[]
  >-
    (Cases_on`i`>>TRY(Cases_on`a`)>>TRY(Cases_on`m`)>>TRY(Cases_on`r`)>>
    fs[apply_colour_inst_def,inst_ok_less_def])
  >>
    EVERY_CASE_TAC>>unabbrev_all_tac>>fs[every_inst_def])

val word_alloc_inst_ok_less = prove(``
  ∀k prog c.
  every_inst (inst_ok_less c) prog ⇒
  every_inst (inst_ok_less c) (word_alloc k prog)``,
  fs[word_alloc_inst_ok_less_lem,word_alloc_def,LET_THM])

(*ssa preserves all syntactic conventions
  Note: only flat_exp and inst_ok_less are needed since 3-to-2 reg comes after SSA (if required)
  SLOW PROOF
*)
val fake_moves_conventions = prove(``
  ∀ls ssal ssar na l r a b c conf.
  fake_moves ls ssal ssar na = (l,r,a,b,c) ⇒
  flat_exp_conventions l ∧
  flat_exp_conventions r ∧
  every_inst (inst_ok_less conf) l ∧
  every_inst (inst_ok_less conf) r ∧
  every_inst distinct_tar_reg l ∧
  every_inst distinct_tar_reg r``,
  Induct>>fs[fake_moves_def]>>rw[]>>fs[flat_exp_conventions_def,every_inst_def]>>
  pop_assum mp_tac>> LET_ELIM_TAC>> EVERY_CASE_TAC>> fs[LET_THM]>>
  unabbrev_all_tac>>
  metis_tac[flat_exp_conventions_def,fake_move_def,inst_ok_less_def,every_inst_def,distinct_tar_reg_def])

(*ssa generates distinct regs and also preserves flattening*)
val ssa_cc_trans_flat_exp_conventions = prove(``
  ∀prog ssa na.
  flat_exp_conventions prog ⇒
  flat_exp_conventions (FST (ssa_cc_trans prog ssa na))``,
  ho_match_mp_tac ssa_cc_trans_ind>>fs[ssa_cc_trans_def]>>rw[]>>
  unabbrev_all_tac>>
  fs[flat_exp_conventions_def]
  >-
    (pop_assum mp_tac>>fs[fix_inconsistencies_def,fake_moves_def]>>LET_ELIM_TAC>>fs[flat_exp_conventions_def]>>
    metis_tac[fake_moves_conventions,flat_exp_conventions_def])
  >-
    (fs[list_next_var_rename_move_def]>>rpt (pop_assum mp_tac)>>
    LET_ELIM_TAC>>fs[flat_exp_conventions_def,EQ_SYM_EQ])
  >-
    (Cases_on`exp`>>fs[ssa_cc_trans_exp_def,flat_exp_conventions_def])
  >-
    (fs[list_next_var_rename_move_def]>>rpt (pop_assum mp_tac)>>
    LET_ELIM_TAC>>fs[flat_exp_conventions_def,EQ_SYM_EQ])
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
      metis_tac[fake_moves_conventions,flat_exp_conventions_def])

val full_ssa_cc_trans_flat_exp_conventions = prove(``
  ∀prog n.
  flat_exp_conventions prog ⇒
  flat_exp_conventions (full_ssa_cc_trans n prog)``,
  fs[full_ssa_cc_trans_def,setup_ssa_def,list_next_var_rename_move_def]>>
  LET_ELIM_TAC>>unabbrev_all_tac>>fs[flat_exp_conventions_def,EQ_SYM_EQ]>>
  metis_tac[ssa_cc_trans_flat_exp_conventions,FST])

val ssa_cc_trans_inst_ok_less = prove(``
  ∀prog ssa na c.
  every_inst (inst_ok_less c) prog ⇒
  every_inst (inst_ok_less c) (FST (ssa_cc_trans prog ssa na))``,
  ho_match_mp_tac ssa_cc_trans_ind>>fs[ssa_cc_trans_def]>>rw[]>>
  unabbrev_all_tac>>
  fs[every_inst_def]
  >-
    (Cases_on`i`>>TRY(Cases_on`a`)>>TRY(Cases_on`m`)>>TRY(Cases_on`r`)>>
    fs[ssa_cc_trans_inst_def,LET_THM,next_var_rename_def]>>
    fs[EQ_SYM_EQ,inst_ok_less_def])
  >-
    (pop_assum mp_tac>>fs[fix_inconsistencies_def,fake_moves_def]>>LET_ELIM_TAC>>
    fs[every_inst_def,EQ_SYM_EQ]>>
    metis_tac[fake_moves_conventions])
  >>TRY
    (fs[list_next_var_rename_move_def]>>rpt (pop_assum mp_tac)>>
    LET_ELIM_TAC>>fs[every_inst_def,EQ_SYM_EQ])
  >>
    EVERY_CASE_TAC>>unabbrev_all_tac>>fs[every_inst_def]>>
    LET_ELIM_TAC>>
    unabbrev_all_tac>>fs[every_inst_def]>>
    fs[fix_inconsistencies_def]>>
    rpt (pop_assum mp_tac)>> LET_ELIM_TAC>>fs[]>>
    metis_tac[fake_moves_conventions,every_inst_def])

val full_ssa_cc_trans_inst_ok_less = prove(``
  ∀prog n c.
  every_inst (inst_ok_less c) prog ⇒
  every_inst (inst_ok_less c) (full_ssa_cc_trans n prog)``,
  fs[full_ssa_cc_trans_def,setup_ssa_def,list_next_var_rename_move_def]>>
  LET_ELIM_TAC>>unabbrev_all_tac>>fs[every_inst_def,EQ_SYM_EQ]>>
  metis_tac[ssa_cc_trans_inst_ok_less,FST])


val _ = export_theory ();
