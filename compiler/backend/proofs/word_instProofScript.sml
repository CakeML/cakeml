open preamble BasicProvers
     wordLangTheory wordPropsTheory word_instTheory wordSemTheory
     asmTheory word_allocTheory word_allocProofTheory

val _ = new_theory "word_instProof";

val convert_sub_ok = prove(``
  ∀ls.
  word_exp s (convert_sub ls) = word_exp s (Op Sub ls)``,
  ho_match_mp_tac convert_sub_ind>>srw_tac[][convert_sub_def,word_exp_def]>>unabbrev_all_tac>>
  full_simp_tac(srw_ss())[word_op_def,the_words_def]>>
  EVERY_CASE_TAC>>
  simp[])

(*In general, any permutation works*)
val word_exp_op_permute_lem = prove(``
  op ≠ Sub ⇒
  ∀ls ls'.
  PERM ls ls' ⇒
  word_exp s (Op op ls) = word_exp s (Op op ls')``,
  strip_tac>>
  ho_match_mp_tac PERM_STRONG_IND>>srw_tac[][]>>
  full_simp_tac(srw_ss())[word_exp_def,LET_THM,the_words_def]>>
  qpat_abbrev_tac`A = MAP f ls`>>
  qpat_abbrev_tac`B = MAP f ls'`>>
  `PERM A B` by metis_tac[PERM_MAP]>>
  TRY(Cases_on`word_exp s y`>>fs[])>>
  Cases_on`word_exp s x`>>fs[]>>
  Cases_on`x'`>>fs[]>>
  TRY(Cases_on`x''`>>fs[])>>
  rpt(qpat_assum`C=D:'a word_loc option` mp_tac)>>
  Cases_on`the_words A`>>
  Cases_on`the_words B`>>
  fs[word_op_def]>>
  Cases_on`op`>>fs[])

(*Remove tail recursion to make proof easier...*)
val pull_ops_simp_def = Define`
  (pull_ops_simp op [] = [] ) ∧
  (pull_ops_simp op (x::xs) =
    case x of
    |  (Op op' ls) => if op = op' then ls ++ (pull_ops_simp op xs) else x::(pull_ops_simp op xs)
    |  _  => x::(pull_ops_simp op xs))`

val PERM_SWAP_SIMP = prove(``
  PERM (A ++ (B::C)) (B::(A++C))``,
  match_mp_tac APPEND_PERM_SYM>>full_simp_tac(srw_ss())[]>>
  metis_tac[PERM_APPEND])

val EL_FILTER = prove(``
  ∀ls x. x < LENGTH (FILTER P ls) ⇒ P (EL x (FILTER P ls))``,
  Induct>>srw_tac[][]>>
  Cases_on`x`>>full_simp_tac(srw_ss())[EL])

val PERM_SWAP = prove(``
  PERM (A ++ B ++ C) (B++(A++C))``,
  full_simp_tac(srw_ss())[PERM_DEF]>>srw_tac[][]>>
  match_mp_tac LIST_EQ>>CONJ_ASM1_TAC
  >-
    (full_simp_tac(srw_ss())[FILTER_APPEND]>>DECIDE_TAC)
  >>
  srw_tac[][]>>
  imp_res_tac EL_FILTER>>
  last_x_assum SUBST_ALL_TAC>>
  imp_res_tac EL_FILTER>>
  metis_tac[])

val pull_ops_simp_pull_ops_perm = prove(``
  ∀ls x.
  PERM (pull_ops op ls x) ((pull_ops_simp op ls)++x)``,
  Induct>>full_simp_tac(srw_ss())[pull_ops_def,pull_ops_simp_def]>>srw_tac[][]>>EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
  TRY(qpat_abbrev_tac`A = B::x`>>
  first_x_assum(qspec_then`A` assume_tac)>>full_simp_tac(srw_ss())[Abbr`A`])>>
  TRY(first_x_assum(qspec_then`l++x` assume_tac))>>
  metis_tac[PERM_SWAP,PERM_TRANS,PERM_SWAP_SIMP,PERM_SYM])

val pull_ops_simp_pull_ops_word_exp = prove(``
  op ≠ Sub ⇒
  word_exp s (Op op (pull_ops op ls [])) = word_exp s (Op op (pull_ops_simp op ls))``,
  strip_tac>> imp_res_tac word_exp_op_permute_lem>>
  pop_assum match_mp_tac>>
  assume_tac pull_ops_simp_pull_ops_perm>>
  pop_assum (qspecl_then [`ls`,`[]`] assume_tac)>>full_simp_tac(srw_ss())[])

val word_exp_op_mono = prove(``
  op ≠ Sub ⇒
  word_exp s (Op op ls) = word_exp s (Op op ls') ⇒
  word_exp s (Op op (x::ls)) =
  word_exp s (Op op (x::ls'))``,
  srw_tac[][word_exp_def,LET_THM]>>
  fs[the_words_def]>>Cases_on`word_exp s x`>>fs[]>>
  Cases_on`x'`>>fs[]>>
  rpt(qpat_assum`A=B` mp_tac)>>ntac 2 (TOP_CASE_TAC>>fs[])>>
  Cases_on`op`>>full_simp_tac(srw_ss())[word_op_def])

val the_words_append = prove(``
  ∀ls ls'.
  the_words (ls ++ ls') =
  case the_words ls of
    NONE => NONE
  | SOME w =>
    (case the_words ls' of
      NONE => NONE
    | SOME w' => SOME(w ++ w'))``,
  Induct>>fs[the_words_def]>>rw[]>>
  TOP_CASE_TAC>>fs[]>>
  TOP_CASE_TAC>>fs[]>>
  Cases_on`the_words ls`>>fs[]>>
  Cases_on`the_words ls'`>>fs[])

val word_exp_op_op = prove(``
  op ≠ Sub ⇒
  ∀ls ls'.
  word_exp s (Op op ls) = word_exp s (Op op ls') ⇒
  word_exp s (Op op (l ++ ls)) =
  word_exp s (Op op ((Op op l) :: ls'))``,
  srw_tac[][word_exp_def,LET_THM]>>
  fs[the_words_append]>>
  qpat_abbrev_tac`C = MAP f l`>>
  Cases_on`the_words C'`>>fs[the_words_def]>>
  rpt(qpat_assum`A=B` mp_tac)>>
  ntac 2 (TOP_CASE_TAC)>>fs[]>>
  Cases_on`op`>> fs[word_op_def,FOLDR_APPEND]>>
  rw[Abbr`C'`]>>
  rpt(pop_assum kall_tac)>>
  Induct_on`x`>>fs[])

val pull_ops_ok = prove(``
  op ≠ Sub ⇒
  ∀ls. word_exp s (Op op (pull_ops op ls [])) =
         word_exp s (Op op ls)``,
  strip_tac>>
  full_simp_tac(srw_ss())[pull_ops_simp_pull_ops_word_exp]>>
  Induct>>srw_tac[][pull_ops_simp_def]>>Cases_on`op`>>full_simp_tac(srw_ss())[]>>
  FULL_CASE_TAC>>full_simp_tac(srw_ss())[word_exp_op_mono]>>
  IF_CASES_TAC>>full_simp_tac(srw_ss())[word_exp_op_mono]>>
  `b ≠ Sub` by srw_tac[][]>>
  imp_res_tac word_exp_op_op>>
  pop_assum (qspec_then`l` assume_tac)>>full_simp_tac(srw_ss())[])

val word_exp_swap_head = prove(``
  ∀B.
  op ≠ Sub ⇒
  word_exp s (Op op A) = SOME (Word w) ⇒
  word_exp s (Op op (B++A)) = word_exp s (Op op (Const w::B))``,
  fs[word_exp_def,the_words_append,the_words_def]>>rw[]>>
  FULL_CASE_TAC>>fs[]>>
  FULL_CASE_TAC>>fs[word_op_def]>>
  Cases_on`op`>>fs[FOLDR_APPEND]>>
  rpt(pop_assum kall_tac)>>
  Induct_on`x'`>>full_simp_tac(srw_ss())[])

val EVERY_is_const_word_exp = prove(``
  ∀ls. EVERY is_const ls ⇒
  EVERY IS_SOME (MAP (λa. word_exp s a) ls)``,
  Induct>>srw_tac[][]>>Cases_on`h`>>full_simp_tac(srw_ss())[is_const_def,word_exp_def])

val all_consts_simp = prove(``
  op ≠ Sub ⇒
  ∀ls.
  EVERY is_const ls ⇒
  word_exp s (Op op ls) =
  SOME( Word(THE (word_op op (MAP rm_const ls))))``,
  strip_tac>>Induct>>full_simp_tac(srw_ss())[word_exp_def,the_words_def]
  >-
    (full_simp_tac(srw_ss())[word_op_def]>>
    Cases_on`op`>>full_simp_tac(srw_ss())[])
  >>
  ntac 2 strip_tac>>
  Cases_on`h`>>full_simp_tac(srw_ss())[is_const_def,word_exp_def]>>
  FULL_CASE_TAC>>fs[EVERY_is_const_word_exp]>>
  Cases_on`op`>>full_simp_tac(srw_ss())[word_op_def,rm_const_def])

val optimize_consts_ok = prove(``
  op ≠ Sub ⇒
  ∀ls. word_exp s (optimize_consts op ls) =
       word_exp s (Op op ls)``,
  strip_tac>>srw_tac[][optimize_consts_def]>>
  Cases_on`const_ls`>>full_simp_tac(srw_ss())[]
  >-
    (imp_res_tac word_exp_op_permute_lem>>pop_assum match_mp_tac>>
    metis_tac[PERM_PARTITION,APPEND_NIL,PERM_SYM])
  >>
    LET_ELIM_TAC>>
    `EVERY is_const (h::t)` by
      (full_simp_tac(srw_ss())[PARTITION_DEF]>>
      imp_res_tac (GSYM PARTs_HAVE_PROP)>>full_simp_tac(srw_ss())[EVERY_MEM])>>
    imp_res_tac all_consts_simp>>
    `PERM ls ((h::t)++nconst_ls)` by metis_tac[PERM_PARTITION]>>
    imp_res_tac word_exp_op_permute_lem>>
    pop_assum(qspec_then`s` SUBST_ALL_TAC)>>
    Cases_on`nconst_ls`>>full_simp_tac(srw_ss())[]
    >-
      full_simp_tac(srw_ss())[word_exp_def,LET_THM]
    >>
    imp_res_tac word_exp_swap_head>>
    pop_assum(qspecl_then [`w`,`s`,`h::t`] assume_tac)>>
    rev_full_simp_tac(srw_ss())[]>>
    pop_assum(qspec_then`h'::t'` assume_tac)>>
    pop_assum sym_sub_tac>>
    pop_assum kall_tac>>imp_res_tac word_exp_op_permute_lem>>
    pop_assum match_mp_tac>>
    qpat_abbrev_tac`A = h'::t'`>>
    qpat_abbrev_tac`B = h::t`>>
    `h:: (t ++A) = B ++A` by full_simp_tac(srw_ss())[]>>pop_assum SUBST_ALL_TAC>>
    metis_tac[PERM_APPEND])

val pull_exp_ok = prove(``
  ∀exp s x.
  word_exp s exp = SOME x ⇒
  word_exp s (pull_exp exp) = SOME x``,
  ho_match_mp_tac pull_exp_ind>>srw_tac[][]>>
  full_simp_tac(srw_ss())[pull_exp_def,LET_THM]>>
  TRY(full_simp_tac(srw_ss())[op_consts_def,word_exp_def,LET_THM,word_op_def,the_words_def]>>
    FULL_CASE_TAC>>fs[]>>
    FULL_CASE_TAC>>fs[]>>NO_TAC)
  >-
    (fs[convert_sub_ok,word_exp_def,MAP_MAP_o]>>
    pop_assum mp_tac>>
    qpat_abbrev_tac`ws = MAP f ls`>>
    qpat_abbrev_tac`ws = MAP f ls`>>
    TOP_CASE_TAC>>fs[]>>
    `ws = ws'` by
      (imp_res_tac the_words_EVERY_IS_SOME>>
      unabbrev_all_tac>>fs[MAP_EQ_f,MAP_MAP_o]>>
      fs[EVERY_MAP,EVERY_MEM]>>
      rw[]>>res_tac>>
      fs[IS_SOME_EXISTS])>>
    fs[])
  >>
  fs[optimize_consts_ok,pull_ops_ok]>>
  fs[word_exp_def,the_words_def]>>
  (*4 goals*)
  TRY(pop_assum mp_tac>>
    ntac 5(FULL_CASE_TAC>>fs[])>>
    rw[]>>
    fs[DISJ_IMP_THM,FORALL_AND_THM]>>
    res_tac>>fs[]>>
    qpat_assum`A=SOME x'` mp_tac>>
    qpat_abbrev_tac`ws = MAP f ls`>>
    qpat_abbrev_tac`ws = MAP f ls`>>
    strip_tac>>
    `ws = ws'` by
     (imp_res_tac the_words_EVERY_IS_SOME>>
      unabbrev_all_tac>>fs[MAP_EQ_f,MAP_MAP_o]>>
      fs[EVERY_MAP,EVERY_MEM]>>
      rw[]>>res_tac>>
      fs[IS_SOME_EXISTS])>>
    fs[])>>
  EVERY_CASE_TAC>>fs[]>>
  res_tac>>fs[]>>
  rfs[])

val convert_sub_every_var_exp = prove(``
  ∀ls.
  (∀x. MEM x ls ⇒ every_var_exp P x) ⇒
  every_var_exp P (convert_sub ls)``,
  ho_match_mp_tac convert_sub_ind>>srw_tac[][convert_sub_def]>>
  full_simp_tac(srw_ss())[every_var_exp_def,EVERY_MEM])

val optimize_consts_every_var_exp = prove(``
  ∀ls.
  (∀x. MEM x ls ⇒ every_var_exp P x) ⇒
  every_var_exp P (optimize_consts op ls)``,
  srw_tac[][optimize_consts_def]>>
  `PERM ls (const_ls++nconst_ls)` by metis_tac[PERM_PARTITION]>>full_simp_tac(srw_ss())[]>>
  imp_res_tac PERM_MEM_EQ>>
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[every_var_exp_def,LET_THM,EVERY_MEM])

val pull_ops_every_var_exp = prove(``
  ∀ls acc.
  EVERY (every_var_exp P) acc ∧ EVERY (every_var_exp P) ls ⇒
  EVERY (every_var_exp P) (pull_ops op ls acc)``,
  Induct>>full_simp_tac(srw_ss())[pull_ops_def]>>srw_tac[][]>>EVERY_CASE_TAC>>full_simp_tac(srw_ss())[every_var_exp_def]>>
  metis_tac[ETA_AX,EVERY_APPEND,every_var_exp_def]) |> REWRITE_RULE[EVERY_MEM]

val pull_exp_every_var_exp = prove(``
  ∀exp.
  every_var_exp P exp ⇒
  every_var_exp P (pull_exp exp)``,
  ho_match_mp_tac pull_exp_ind>>full_simp_tac(srw_ss())[op_consts_def,pull_exp_def,every_var_exp_def,EVERY_MEM,EVERY_MAP,LET_THM]>>srw_tac[][]
  >-
    metis_tac[convert_sub_every_var_exp,MEM_MAP,PULL_EXISTS]
  >>
    match_mp_tac optimize_consts_every_var_exp>>
    match_mp_tac pull_ops_every_var_exp>>srw_tac[][]>>
    metis_tac[MEM_MAP])

(*First step: Make op expressions have exactly 2 args*)
(*Semantics*)
val flatten_exp_ok = prove(``
  ∀exp s x.
  word_exp s exp = SOME x ⇒
  word_exp s (flatten_exp exp) = SOME x``,
  ho_match_mp_tac flatten_exp_ind>>srw_tac[][]>>
  fs[word_exp_def,flatten_exp_def]
  >-
    (pop_assum mp_tac>>
    TOP_CASE_TAC>>fs[]>>
    pop_assum mp_tac>>
    qpat_abbrev_tac`ls = MAP A B`>>
    qpat_abbrev_tac`ls' = MAP A B`>>
    rw[]>>
    `ls = ls'` by
      (imp_res_tac the_words_EVERY_IS_SOME>>
      unabbrev_all_tac>>fs[MAP_EQ_f,MAP_MAP_o]>>
      fs[EVERY_MAP,EVERY_MEM]>>
      rw[]>>res_tac>>
      fs[IS_SOME_EXISTS])>>
    fs[])
  >>
    fs[op_consts_def,word_exp_def,LET_THM,word_op_def,the_words_def]>>
    Cases_on`word_exp s exp`>>fs[]>>Cases_on`x'`>>fs[]>>
    (*4 cases*)
    TRY(qpat_assum`A=SOME x` mp_tac>>qcase_tac`word_exp s exp'`>>
    Cases_on`word_exp s exp'`>>fs[]>>Cases_on`x'`>>fs[]>>
    FULL_CASE_TAC>>fs[]>>
    first_x_assum(qspec_then`s` assume_tac)>>rfs[]>>
    first_x_assum(qspec_then`s` assume_tac)>>rfs[])>>
    res_tac>>fs[])

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
   \\ full_simp_tac(srw_ss())[exp_size_def]
   \\ TRY (DECIDE_TAC))

(*Syntax*)
val flatten_exp_binary_branch_exp = prove(``
  ∀exp.
  binary_branch_exp (flatten_exp exp)``,
  ho_match_mp_tac flatten_exp_ind>>full_simp_tac(srw_ss())[op_consts_def,flatten_exp_def,binary_branch_exp_def,EVERY_MEM,EVERY_MAP])

val flatten_exp_every_var_exp = prove(``
  ∀exp.
  every_var_exp P exp ⇒
  every_var_exp P (flatten_exp exp)``,
  ho_match_mp_tac flatten_exp_ind>>full_simp_tac(srw_ss())[op_consts_def,flatten_exp_def,every_var_exp_def,EVERY_MEM,EVERY_MAP])

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
    if x = tar then lookup x loc' = SOME w
    else if x < temp then lookup x loc' = lookup x s.locals
    else T``,
  completeInduct_on`exp_size (K 0) exp`>>
  rpt strip_tac>>
  Cases_on`exp`>>
  full_simp_tac(srw_ss())[evaluate_def,binary_branch_exp_def,every_var_exp_def]
  >-
    (simp[inst_select_exp_def]>>
    full_simp_tac(srw_ss())[LET_THM,evaluate_def,inst_def,mem_load_def,assign_def,word_exp_def,set_var_def,mem_load_def,word_op_def]>>
    simp[state_component_equality,locals_rel_def,lookup_insert]>>
    full_simp_tac(srw_ss())[locals_rel_def])
  >-
    (simp[inst_select_exp_def]>>
    full_simp_tac(srw_ss())[LET_THM,evaluate_def,inst_def,mem_load_def,assign_def,word_exp_def,set_var_def,mem_load_def,word_op_def,get_vars_def,set_vars_def,get_var_def]>>
    full_simp_tac(srw_ss())[locals_rel_def]>>
    res_tac>>fs[alist_insert_def]>>
    simp[state_component_equality,lookup_insert])
  >-
    (simp[inst_select_exp_def]>>
    full_simp_tac(srw_ss())[LET_THM,evaluate_def,inst_def,mem_load_def,assign_def,word_exp_def,set_var_def,mem_load_def,word_op_def,get_vars_def,set_vars_def,get_var_def]>>
    fs[locals_rel_def,state_component_equality,lookup_insert])
  >-
    (*Load*)
    (Cases_on`∃exp' w'. e = Op Add[exp';Const w']` >>full_simp_tac(srw_ss())[]
    >-
      (simp[Once inst_select_exp_def]>>IF_CASES_TAC
      >-
        (fs[binary_branch_exp_def,every_var_exp_def,word_exp_def,the_words_def]>>EVERY_CASE_TAC>>full_simp_tac(srw_ss())[IS_SOME_EXISTS]>>rev_full_simp_tac(srw_ss())[]>>
        last_x_assum mp_tac>>simp[Once PULL_FORALL]>>disch_then (qspec_then`exp'` mp_tac)>>simp[exp_size_def]>>strip_tac>>res_tac>>
        pop_assum(qspecl_then[`temp`,`c`] assume_tac)>>full_simp_tac(srw_ss())[evaluate_def,LET_THM]>>
        simp[evaluate_def,LET_THM,inst_def,mem_load_def,assign_def,word_exp_def,the_words_def]>>
        `lookup temp loc'' = SOME (Word c')` by metis_tac[]>>full_simp_tac(srw_ss())[mem_load_def]>>
        full_simp_tac(srw_ss())[state_component_equality,set_var_def,lookup_insert]>>srw_tac[][]>>
        DISJ2_TAC>>strip_tac>>`x' ≠ temp` by DECIDE_TAC>>metis_tac[])
      >>
        (last_x_assum mp_tac>>simp[Once PULL_FORALL]>>
        disch_then (qspec_then`e`mp_tac)>>
        discharge_hyps>-(full_simp_tac(srw_ss())[exp_size_def]>>DECIDE_TAC)>>
        full_simp_tac(srw_ss())[binary_branch_exp_def,every_var_exp_def,the_words_def]>>EVERY_CASE_TAC>>full_simp_tac(srw_ss())[IS_SOME_EXISTS]>>rev_full_simp_tac(srw_ss())[]>>
        qpat_assum`A=SOME w` mp_tac>>simp[Once word_exp_def]>>FULL_CASE_TAC>>
        FULL_CASE_TAC>>fs[]>>
        srw_tac[][]>>res_tac>>
        pop_assum(qspecl_then[`temp`,`c`] assume_tac)>>full_simp_tac(srw_ss())[evaluate_def,LET_THM]>>
        simp[evaluate_def,LET_THM,inst_def,mem_load_def,assign_def,word_exp_def,the_words_def]>>
        `lookup temp loc'' = SOME (Word c')` by metis_tac[]>>full_simp_tac(srw_ss())[mem_load_def]>>
        full_simp_tac(srw_ss())[state_component_equality,set_var_def,lookup_insert]>>srw_tac[][]>>
        simp[state_component_equality,set_var_def,lookup_insert,word_op_def]>>
        rw[]>>DISJ2_TAC>>rw[]>>
        `x ≠ temp` by DECIDE_TAC>>metis_tac[]))
    >>
      `inst_select_exp c tar temp (Load e) =
        let prog = inst_select_exp c temp temp e in
          Seq prog (Inst (Mem Load tar (Addr temp (0w))))` by
      (full_simp_tac(srw_ss())[inst_select_exp_def,LET_THM]>>EVERY_CASE_TAC>>full_simp_tac(srw_ss())[])>>
      last_x_assum mp_tac>>simp[Once PULL_FORALL]>>
      disch_then (qspec_then`e`mp_tac)>>
      discharge_hyps>-(full_simp_tac(srw_ss())[exp_size_def]>>DECIDE_TAC)>>
      strip_tac>>full_simp_tac(srw_ss())[word_exp_def]>>EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
      res_tac>>
      pop_assum(qspecl_then[`temp`,`c`] assume_tac)>>full_simp_tac(srw_ss())[evaluate_def,LET_THM]>>
      `lookup temp loc'' = SOME (Word c')` by metis_tac[]>>
      simp[inst_def,assign_def,word_exp_def,word_op_def]>>full_simp_tac(srw_ss())[mem_load_def,the_words_def]>>
      simp[state_component_equality,set_var_def,lookup_insert]>>
      srw_tac[][]>>DISJ2_TAC>>strip_tac>>
      `x ≠ temp` by DECIDE_TAC>>metis_tac[])
  >-
    (*Op*)
    (Cases_on`∃e1 e2. l = [e1;e2]`>>full_simp_tac(srw_ss())[inst_select_exp_def]
    >-
      (`binary_branch_exp e1` by
        (Cases_on`b`>>full_simp_tac(srw_ss())[binary_branch_exp_def])>>
      full_simp_tac(srw_ss())[word_exp_def,the_words_def,IS_SOME_EXISTS]>>
      last_x_assum mp_tac>>simp[Once PULL_FORALL]>>
      disch_then assume_tac>> first_assum mp_tac>>
      disch_then (qspec_then`e1`mp_tac)>>
        discharge_hyps>-(full_simp_tac(srw_ss())[exp_size_def]>>DECIDE_TAC)>>
      Cases_on`word_exp s e1`>>fs[]>>Cases_on`x`>>
      Cases_on`word_exp s e2`>>fs[]>>Cases_on`x`>>fs[]>>
      strip_tac>>res_tac>>
      pop_assum(qspecl_then[`temp`,`c`] assume_tac)>>full_simp_tac(srw_ss())[]>>
      Cases_on`∃w. e2 = Const w`
      >-
        (full_simp_tac(srw_ss())[]>>IF_CASES_TAC
        >-
          (full_simp_tac(srw_ss())[evaluate_def]>>
          simp[LET_THM,inst_def,mem_load_def,word_exp_def,assign_def,the_words_def]>>
          `lookup temp loc'' = SOME (Word c')` by metis_tac[]>>
          full_simp_tac(srw_ss())[word_op_def]>>
          Cases_on`b`>>
          full_simp_tac(srw_ss())[set_var_def,state_component_equality,lookup_insert,word_exp_def]>>
          srw_tac[][]>>DISJ2_TAC>>strip_tac>>`x ≠ temp` by DECIDE_TAC>>metis_tac[])
        >> IF_CASES_TAC
        >-
          (simp[evaluate_def,LET_THM,inst_def,mem_load_def,assign_def,word_exp_def,set_var_def,lookup_insert,the_words_def]>>
          `lookup temp loc'' = SOME (Word c')` by metis_tac[]>>
          full_simp_tac(srw_ss())[]>>rev_full_simp_tac(srw_ss())[word_exp_def,word_op_def]>>
          full_simp_tac(srw_ss())[state_component_equality,lookup_insert]>>srw_tac[][]>>
          DISJ2_TAC>>strip_tac>>
          `x ≠ temp` by DECIDE_TAC>>
          metis_tac[])
        >>
          (simp[evaluate_def,LET_THM,inst_def,mem_load_def,assign_def,word_exp_def,set_var_def,lookup_insert,the_words_def]>>
          `lookup temp loc'' = SOME (Word c')` by metis_tac[]>>
          full_simp_tac(srw_ss())[]>>rev_full_simp_tac(srw_ss())[word_exp_def]>>
          full_simp_tac(srw_ss())[state_component_equality,lookup_insert]>>
          srw_tac[][]>>
          DISJ2_TAC>>strip_tac>-`F` by DECIDE_TAC>>
          `x ≠ temp` by DECIDE_TAC>>
          `¬ (temp+1 < temp)` by DECIDE_TAC>>
          metis_tac[]))
      >>
        `inst_select_exp c tar temp (Op b [e1;e2]) =
        let p1 = inst_select_exp c temp temp e1 in
        let p2 = inst_select_exp c (temp+1) (temp+1) e2 in
        Seq p1 (Seq p2 (Inst (Arith (Binop b tar temp (Reg (temp+1))))))` by
        (full_simp_tac(srw_ss())[inst_select_exp_def,LET_THM]>>EVERY_CASE_TAC>>full_simp_tac(srw_ss())[])>>
        full_simp_tac(srw_ss())[inst_select_exp_def,LET_THM]>>pop_assum kall_tac>>
        full_simp_tac(srw_ss())[evaluate_def,LET_THM]>>
        first_x_assum(qspecl_then[`e2`] mp_tac)>>
        simp[exp_size_def]>>
        disch_then(qspecl_then [`c`,`temp+1`,`temp+1`,`s with locals:=loc''`,`Word c''`,`loc''`] mp_tac)>>
        discharge_hyps>-
          (srw_tac[][locals_rel_def]>-(Cases_on`b`>>full_simp_tac(srw_ss())[binary_branch_exp_def])
          >-
            (match_mp_tac every_var_exp_mono>>
            HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[]>>DECIDE_TAC)
          >>
            (*word_exp invariant under extra locals*)
            match_mp_tac locals_rel_word_exp>>
            full_simp_tac(srw_ss())[locals_rel_def]>>
            srw_tac[][]>>`x ≠ temp` by DECIDE_TAC>>
            metis_tac[])>>
        strip_tac>>full_simp_tac(srw_ss())[word_exp_def]>>
        `lookup temp loc''' = SOME (Word c') ∧
         lookup (temp+1) loc''' = SOME (Word c'')` by
         (first_assum(qspecl_then[`temp`] assume_tac)>>
         first_x_assum(qspecl_then[`temp+1`] assume_tac)>>
         `temp ≠ temp+1` by DECIDE_TAC>>
         full_simp_tac(srw_ss())[]>>metis_tac[])>>
        rev_full_simp_tac(srw_ss())[]>>
        simp[inst_def,assign_def,word_exp_def,LET_THM,state_component_equality,set_var_def,lookup_insert,the_words_def]>>
        srw_tac[][]>>DISJ2_TAC>>strip_tac>>
        `x<temp+1 ∧ x ≠ temp ∧ x≠ temp+1` by DECIDE_TAC>>
        metis_tac[])
    >>
      (Cases_on`b`>>full_simp_tac(srw_ss())[binary_branch_exp_def,word_exp_def,the_words_def,word_op_def]>>
      Cases_on`l`>>fs[the_words_def]>>
      TRY(Cases_on`t`>>full_simp_tac(srw_ss())[]>>Cases_on`t'`>>full_simp_tac(srw_ss())[])>>
      qpat_assum`A=SOME w` mp_tac>>
      Cases_on`word_exp s h`>>fs[]>>
      Cases_on`x`>>fs[]>>
      Cases_on`t`>>fs[the_words_def]>>
      Cases_on`word_exp s h'`>>fs[]>>
      Cases_on`x`>>fs[]>>
      Cases_on`t'`>>fs[the_words_def]>>
      EVERY_CASE_TAC>>fs[]))
  >-
    (*Shift*)
    (simp[inst_select_exp_def]>>last_x_assum mp_tac>>simp[Once PULL_FORALL]>>disch_then (qspec_then`e`mp_tac)>>discharge_hyps>-(full_simp_tac(srw_ss())[exp_size_def]>>DECIDE_TAC)>>
    full_simp_tac(srw_ss())[LET_THM,word_exp_def]>>EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]
    >-
      (`word_sh s' c' (num_exp n) = SOME c'` by
        (full_simp_tac(srw_ss())[word_sh_def]>>EVERY_CASE_TAC>>
        fs[])>>
      srw_tac[][]>>res_tac>>
      first_assum(qspecl_then[`temp`,`c`] assume_tac)>>
      full_simp_tac(srw_ss())[evaluate_def,LET_THM,get_vars_def,get_var_def]>>
      `lookup temp loc'' = SOME (Word c')` by metis_tac[]>>
      full_simp_tac(srw_ss())[set_vars_def,alist_insert_def,state_component_equality,lookup_insert]>>
      srw_tac[][]>>rev_full_simp_tac(srw_ss())[]>>
      `x ≠ temp` by DECIDE_TAC>>metis_tac[])
    >-
      (assume_tac DIMINDEX_GT_0>>
      `0 ≠ dimindex(:'a)` by DECIDE_TAC>>full_simp_tac(srw_ss())[])
    >-
      (srw_tac[][]>>res_tac>>
      first_assum(qspecl_then[`temp`,`c`] assume_tac)>>
      full_simp_tac(srw_ss())[evaluate_def,LET_THM,inst_def,mem_load_def,assign_def,word_exp_def]>>
      `lookup temp loc'' = SOME (Word c')` by metis_tac[]>>
      full_simp_tac(srw_ss())[num_exp_def,set_var_def,state_component_equality,lookup_insert]>>
      srw_tac[][]>>DISJ2_TAC>>strip_tac>>`x ≠ temp` by DECIDE_TAC>>
      metis_tac[])
    >-
      (`num_exp n ≥ dimindex(:'a)` by DECIDE_TAC>>
      full_simp_tac(srw_ss())[word_sh_def])))

val locals_rm = prove(``
  D with locals := D.locals = D``,
  full_simp_tac(srw_ss())[state_component_equality])

(*  Main semantics theorem for inst selection:
    The inst-selected program gives same result but
    with possibly more locals used
*)
val inst_select_thm = store_thm("inst_select_thm",``
  ∀c temp prog st res rst loc.
  evaluate (prog,st) = (res,rst) ∧
  every_var (λx. x < temp) prog ∧
  res ≠ SOME Error ∧
  locals_rel temp st.locals loc ⇒
  ∃loc'.
  evaluate (inst_select c temp prog,st with locals:=loc) = (res,rst with locals:=loc') ∧
  case res of
    NONE => locals_rel temp rst.locals loc'
  | SOME _ => rst.locals = loc'``,
  ho_match_mp_tac inst_select_ind>>srw_tac[][]>>
  full_simp_tac(srw_ss())[inst_select_def,locals_rel_evaluate_thm]
  >-
    (full_simp_tac(srw_ss())[evaluate_def]>>last_x_assum mp_tac>>FULL_CASE_TAC>>srw_tac[][]>>
    full_simp_tac(srw_ss())[every_var_def]>>
    imp_res_tac pull_exp_every_var_exp>>
    imp_res_tac flatten_exp_every_var_exp>>
    imp_res_tac pull_exp_ok>>
    imp_res_tac flatten_exp_ok>>
    fs[]>>
    assume_tac flatten_exp_binary_branch_exp>>
    pop_assum(qspec_then`pull_exp exp` assume_tac)>>
    imp_res_tac inst_select_exp_thm>>rev_full_simp_tac(srw_ss())[]>>
    first_x_assum(qspecl_then[`c'`,`c`] assume_tac)>>full_simp_tac(srw_ss())[]>>
    simp[state_component_equality,set_var_def,locals_rel_def]>>
    srw_tac[][]>>full_simp_tac(srw_ss())[lookup_insert]>>
    IF_CASES_TAC>>fs[]>>
    metis_tac[])
  >-
    (full_simp_tac(srw_ss())[evaluate_def]>>last_x_assum mp_tac>>
    ntac 2 FULL_CASE_TAC>>full_simp_tac(srw_ss())[]>>strip_tac>>
    full_simp_tac(srw_ss())[every_var_def]>>
    imp_res_tac pull_exp_every_var_exp>>
    imp_res_tac flatten_exp_every_var_exp>>
    imp_res_tac pull_exp_ok>>
    imp_res_tac flatten_exp_ok>>
    fs[]>>
    assume_tac flatten_exp_binary_branch_exp>>
    pop_assum(qspec_then`pull_exp exp` assume_tac)>>
    imp_res_tac inst_select_exp_thm>>rev_full_simp_tac(srw_ss())[]>>
    first_x_assum(qspecl_then[`temp`,`c`] assume_tac)>>full_simp_tac(srw_ss())[]>>
    full_simp_tac(srw_ss())[LET_THM,evaluate_def,word_exp_def]>>
    first_assum(qspec_then`temp` assume_tac)>>full_simp_tac(srw_ss())[set_store_def]>>
    full_simp_tac(srw_ss())[state_component_equality,locals_rel_def]>>
    srw_tac[][]>>`x' ≠ temp` by DECIDE_TAC>>metis_tac[])
  >-(*Set has optimizations*)
    (full_simp_tac(srw_ss())[evaluate_def]>>last_x_assum mp_tac>>
    ntac 3 FULL_CASE_TAC>>full_simp_tac(srw_ss())[]>>strip_tac>>
    qpat_abbrev_tac`expr = flatten_exp (pull_exp exp)`>>
    Cases_on`∃w exp'. expr = Op Add [exp';Const w]`>>
    full_simp_tac(srw_ss())[LET_THM]
    >-
      (IF_CASES_TAC
      >-
        (full_simp_tac(srw_ss())[Abbr`expr`,every_var_def]>>
        imp_res_tac pull_exp_every_var_exp>>
        imp_res_tac pull_exp_ok>>
        imp_res_tac flatten_exp_ok>>
        rfs[word_exp_def,the_words_def]>>
        Cases_on`word_exp st exp'`>>fs[]>>Cases_on`x'`>>fs[]>>
        imp_res_tac inst_select_exp_thm>>
        pop_assum kall_tac>>
        fs[AND_IMP_INTRO]>>
        pop_assum mp_tac>>discharge_hyps>-
          (assume_tac flatten_exp_binary_branch_exp>>
          pop_assum(qspec_then`pull_exp exp` mp_tac)>>simp[binary_branch_exp_def]>>
          imp_res_tac flatten_exp_every_var_exp>>
          rfs[every_var_exp_def])>>
        srw_tac[][]>>
        full_simp_tac(srw_ss())[evaluate_def,LET_THM]>>first_x_assum(qspecl_then [`temp`,`c`] assume_tac)>>
        fs[inst_def,word_exp_def,the_words_def]>>
        `lookup temp loc' = SOME(Word c'')` by metis_tac[]>>
        `get_var var (st with locals := loc') = SOME x` by
          (full_simp_tac(srw_ss())[get_var_def]>>
          `var ≠ temp` by DECIDE_TAC>>metis_tac[])>>
        fs[mem_store_def]>>
        IF_CASES_TAC>>fs[state_component_equality]>>
        TOP_CASE_TAC>>fs[locals_rel_def]>>
        rw[]>>
        `x' ≠ temp` by DECIDE_TAC>>metis_tac[])
      >>
        qpat_assum`expr =A` sym_sub_tac>>
        imp_res_tac pull_exp_ok>>
        imp_res_tac flatten_exp_ok>>
        imp_res_tac inst_select_exp_thm>>
        full_simp_tac(srw_ss())[AND_IMP_INTRO]>>
        ntac 2 (pop_assum kall_tac)>>
        pop_assum mp_tac>>
        discharge_hyps>-
          (full_simp_tac(srw_ss())[every_var_def,Abbr`expr`]>>
          metis_tac[flatten_exp_every_var_exp,flatten_exp_binary_branch_exp,pull_exp_every_var_exp])>>
        disch_then (qspecl_then [`temp`,`c`] assume_tac)>>
        full_simp_tac(srw_ss())[evaluate_def,LET_THM,inst_def,word_exp_def]>>
        full_simp_tac(srw_ss())[word_op_def,the_words_def,Abbr`expr`]>>
        `lookup temp loc' = SOME (Word c')` by metis_tac[]>>
        `get_var var (st with locals := loc') = SOME x` by
          (full_simp_tac(srw_ss())[get_var_def,every_var_def]>>
          `var ≠ temp` by DECIDE_TAC>>
          metis_tac[])>>
        fs[mem_store_def]>>
        IF_CASES_TAC>>fs[state_component_equality,locals_rel_def]>>
        TOP_CASE_TAC>>rw[]>>
        `x' ≠ temp` by DECIDE_TAC>>metis_tac[])
    >>
      `inst_select c temp (Store exp var) =
        Seq(inst_select_exp c temp temp expr)
        (Inst (Mem Store var (Addr temp 0w)))` by
        (full_simp_tac(srw_ss())[inst_select_def,LET_THM]>>
        EVERY_CASE_TAC>>full_simp_tac(srw_ss())[])>>
      full_simp_tac(srw_ss())[inst_select_def,LET_THM,Abbr`expr`]>>
      imp_res_tac pull_exp_ok>>
      imp_res_tac flatten_exp_ok>>
      imp_res_tac inst_select_exp_thm>>
      full_simp_tac(srw_ss())[AND_IMP_INTRO]>>
      ntac 2 (pop_assum kall_tac)>>
      pop_assum mp_tac>>
      discharge_hyps
      >-
        (full_simp_tac(srw_ss())[every_var_def]>>
        metis_tac[pull_exp_every_var_exp,flatten_exp_every_var_exp,flatten_exp_binary_branch_exp])
      >>
      disch_then(qspecl_then [`temp`,`c`] assume_tac)>>
      fs[evaluate_def,inst_def,word_exp_def,the_words_def]>>
      `lookup temp loc' = SOME (Word c')` by metis_tac[]>>
      full_simp_tac(srw_ss())[word_op_def,every_var_def]>>
      `get_var var (st with locals := loc') = SOME x` by
        (full_simp_tac(srw_ss())[get_var_def]>>`var ≠ temp` by DECIDE_TAC>>
        metis_tac[])>>
      full_simp_tac(srw_ss())[mem_store_def]>>
      IF_CASES_TAC>>fs[state_component_equality]>>
      FULL_CASE_TAC>>fs[locals_rel_def]>>rw[]>>
      `x' ≠ temp` by DECIDE_TAC>>metis_tac[])
  >-
    (*Seq*)
    (full_simp_tac(srw_ss())[evaluate_def,LET_THM]>>Cases_on`evaluate(prog,st)`>>
    full_simp_tac(srw_ss())[every_var_def,GSYM AND_IMP_INTRO]>>
    `q ≠ SOME Error` by (EVERY_CASE_TAC>>full_simp_tac(srw_ss())[])>>
    first_assum(fn th => first_x_assum(mp_tac o C MATCH_MP th)) >>
    full_simp_tac(srw_ss())[]>> disch_then (qspec_then`loc` assume_tac)>>rev_full_simp_tac(srw_ss())[]>>
    IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
    metis_tac[])
  >-
    (full_simp_tac(srw_ss())[evaluate_def,LET_THM,every_var_def]>>
    IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
    ntac 2 (split_pair_tac>>full_simp_tac(srw_ss())[])>>
    Cases_on`res' = SOME TimeOut`>>full_simp_tac(srw_ss())[]>>
    rveq>>
    res_tac>>
    last_x_assum kall_tac>>
    ntac 2 (pop_assum kall_tac)>>
    pop_assum(qspec_then`loc` assume_tac)>>rev_full_simp_tac(srw_ss())[]>>
    simp[state_component_equality])
  >-
    (full_simp_tac(srw_ss())[evaluate_def]>>ntac 4 (pop_assum mp_tac)>>ntac 4 FULL_CASE_TAC>>
    full_simp_tac(srw_ss())[every_var_def]>>
    srw_tac[][]>> imp_res_tac locals_rel_get_var>>
    imp_res_tac locals_rel_get_var_imm>>full_simp_tac(srw_ss())[GSYM AND_IMP_INTRO,every_var_def])
  >>
    imp_res_tac locals_rel_evaluate_thm>>
    ntac 14 (pop_assum kall_tac)>>
    full_simp_tac(srw_ss())[LET_THM,evaluate_def,every_var_def]>>
    qpat_abbrev_tac `stt = st with locals := A`>>
    Cases_on`get_vars args stt`>>full_simp_tac(srw_ss())[]>>
    IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
    Cases_on`ret`>>full_simp_tac(srw_ss())[add_ret_loc_def]
    >-(*Tail Call*)
      (Cases_on`find_code dest x st.code`>>Cases_on`handler`>>
      TRY(PairCases_on`x'`)>>full_simp_tac(srw_ss())[]>>
      full_simp_tac(srw_ss())[call_env_def,dec_clock_def,state_component_equality,locals_rel_def])
    >>
      PairCases_on`x'`>>full_simp_tac(srw_ss())[add_ret_loc_def]>>
      ntac 5 (TOP_CASE_TAC>>full_simp_tac(srw_ss())[])>-
        full_simp_tac(srw_ss())[call_env_def,state_component_equality,locals_rel_def]
      >>
      full_simp_tac(srw_ss())[]>>
      qpat_assum`A=(res,rst with locals:=loc')` mp_tac>>
      qpat_abbrev_tac`st = call_env B C`>>
      qpat_abbrev_tac`st' = call_env B C`>>
      `st' = st''` by
        (unabbrev_all_tac>>
        Cases_on`handler`>>TRY(PairCases_on`x''`)>>
        full_simp_tac(srw_ss())[call_env_def,push_env_def,dec_clock_def,push_env_def,LET_THM,env_to_list_def,state_component_equality])>>
      Cases_on`evaluate(r,st'')`>>Cases_on`q'`>>full_simp_tac(srw_ss())[]>>
      Cases_on`x''`>>full_simp_tac(srw_ss())[]
      >-
        (IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
        FULL_CASE_TAC>>full_simp_tac(srw_ss())[]>>
        IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
        ntac 2 (FULL_CASE_TAC>>full_simp_tac(srw_ss())[])>>srw_tac[][]>>
        res_tac>>full_simp_tac(srw_ss())[]>>
        qpat_abbrev_tac`D = set_var A B C`>>
        first_x_assum(qspec_then`D.locals` assume_tac)>>full_simp_tac(srw_ss())[locals_rel_def]>>
        full_simp_tac(srw_ss())[locals_rm,state_component_equality])
      >-
        (Cases_on`handler`>>full_simp_tac(srw_ss())[state_component_equality]>>
        PairCases_on`x''`>>full_simp_tac(srw_ss())[]>>
        IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
        IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
        srw_tac[][]>>
        res_tac>>
        qpat_abbrev_tac`D = set_var A B C`>>
        first_x_assum(qspec_then`D.locals` assume_tac)>>full_simp_tac(srw_ss())[locals_rel_def]>>
        full_simp_tac(srw_ss())[locals_rm,state_component_equality]>>
        Cases_on`res`>>full_simp_tac(srw_ss())[]>>
        qexists_tac`loc''`>>metis_tac[])
      >>
        full_simp_tac(srw_ss())[state_component_equality])

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
  (flat_exp_conventions (MustTerminate n p) =
    flat_exp_conventions p) ∧
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
  ho_match_mp_tac inst_select_exp_ind>>srw_tac[][]>>full_simp_tac(srw_ss())[inst_select_exp_def,flat_exp_conventions_def,LET_THM]>>
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[flat_exp_conventions_def,inst_select_exp_def,LET_THM])

val inst_select_flat_exp_conventions = prove(``
  ∀c temp prog.
  flat_exp_conventions (inst_select c temp prog)``,
  ho_match_mp_tac inst_select_ind >>srw_tac[][]>>
  full_simp_tac(srw_ss())[flat_exp_conventions_def,inst_select_def,LET_THM]>>
  EVERY_CASE_TAC>>
  full_simp_tac(srw_ss())[flat_exp_conventions_def]>>
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
  ho_match_mp_tac inst_select_exp_ind>>srw_tac[][]>>full_simp_tac(srw_ss())[inst_select_exp_def,every_inst_def,LET_THM,inst_ok_less_def]>>
  every_case_tac>>full_simp_tac(srw_ss())[every_inst_def,inst_ok_less_def,inst_select_exp_def,LET_THM] )

val inst_select_inst_ok_less = prove(``
  ∀c temp prog.
  addr_offset_ok 0w c ∧
  every_inst (inst_ok_less c) prog
  ⇒
  every_inst (inst_ok_less c) (inst_select c temp prog)``,
  ho_match_mp_tac inst_select_ind>>srw_tac[][inst_select_def,every_inst_def]>>
  full_simp_tac(srw_ss())[LET_THM]>>unabbrev_all_tac>>EVERY_CASE_TAC>>full_simp_tac(srw_ss())[every_inst_def,inst_ok_less_def]>>
  metis_tac[inst_select_exp_inst_ok_less])

(*3rd step: 3 to 2 reg if necessary*)

(*Instructions are 2 register code for arith ok*)
val two_reg_inst_def = Define`
  (two_reg_inst (Arith (Binop bop r1 r2 ri))
    ⇔ (r1 = r2)) ∧
  (two_reg_inst (Arith (Shift l r1 r2 n))
    ⇔ (r1 = r2)) ∧
  (two_reg_inst _ ⇔ T)`

(*Semantics preservation*)
val three_to_two_reg_correct = store_thm("three_to_two_reg_correct",``
  ∀prog s res s'.
  every_inst distinct_tar_reg prog ∧
  evaluate (prog,s) = (res,s') ∧ res ≠ SOME Error
  ⇒
  evaluate(three_to_two_reg prog,s) = (res,s')``,
  ho_match_mp_tac three_to_two_reg_ind>>
  srw_tac[][]>>full_simp_tac(srw_ss())[three_to_two_reg_def,evaluate_def,state_component_equality]>>
  TRY
    (ntac 2 (pop_assum mp_tac)>>full_simp_tac(srw_ss())[inst_def,assign_def,word_exp_def,get_vars_def,get_var_def,set_vars_def,alist_insert_def,the_words_def]>>
    EVERY_CASE_TAC >>
    full_simp_tac(srw_ss())[LET_THM,alist_insert_def,every_inst_def,distinct_tar_reg_def,word_exp_def,lookup_insert,set_var_def,insert_shadow]>>NO_TAC)
  >-
    (ntac 2 (pop_assum mp_tac)>>LET_ELIM_TAC>>full_simp_tac(srw_ss())[every_inst_def]>>
    Cases_on`res'' = SOME Error`>>full_simp_tac(srw_ss())[]>>res_tac>>
    EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
    metis_tac[])
  >-
    (IF_CASES_TAC>>full_simp_tac(srw_ss())[LET_THM,every_inst_def]>>
    ntac 2(split_pair_tac>>full_simp_tac(srw_ss())[])>>
    Cases_on`res' = SOME TimeOut`>>full_simp_tac(srw_ss())[]>>rveq>>
    res_tac>>
    full_simp_tac(srw_ss())[]>>rveq>>
    full_simp_tac(srw_ss())[])
  >>
    ntac 2 (pop_assum mp_tac)>>LET_ELIM_TAC>>full_simp_tac(srw_ss())[every_inst_def]>>
    unabbrev_all_tac>>
    Cases_on`ret`>>Cases_on`handler`>>full_simp_tac(srw_ss())[evaluate_def]
    >-
      (EVERY_CASE_TAC>>full_simp_tac(srw_ss())[])
    >-
      (ntac 5 (EVERY_CASE_TAC>>full_simp_tac(srw_ss())[add_ret_loc_def]>>
      res_tac>>full_simp_tac(srw_ss())[add_ret_loc_def]>>
      rev_full_simp_tac(srw_ss())[add_ret_loc_def]>>srw_tac[][]>>full_simp_tac(srw_ss())[]))
    >>
      PairCases_on`x`>>PairCases_on`x'`>>full_simp_tac(srw_ss())[]>>
      TOP_CASE_TAC>>full_simp_tac(srw_ss())[add_ret_loc_def]>>
      ntac 6 (TOP_CASE_TAC>>full_simp_tac(srw_ss())[])>>
      full_simp_tac(srw_ss())[push_env_def,LET_THM]>>
      EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
      res_tac>>full_simp_tac(srw_ss())[]>>
      rev_full_simp_tac(srw_ss())[])

(*Syntactic correctness*)
val three_to_two_reg_two_reg_inst = store_thm("three_to_two_reg_two_reg_inst",``
  ∀prog. every_inst two_reg_inst (three_to_two_reg prog)``,
  ho_match_mp_tac three_to_two_reg_ind>>srw_tac[][]>>full_simp_tac(srw_ss())[every_inst_def,two_reg_inst_def,three_to_two_reg_def,LET_THM]>>EVERY_CASE_TAC>>full_simp_tac(srw_ss())[])

val three_to_two_reg_wf_cutsets = store_thm("three_to_two_reg_wf_cutsets",
  ``∀prog. wf_cutsets prog ⇒ wf_cutsets (three_to_two_reg prog)``,
  ho_match_mp_tac three_to_two_reg_ind>>srw_tac[][]>>
  full_simp_tac(srw_ss())[wf_cutsets_def,three_to_two_reg_def,LET_THM]>>EVERY_CASE_TAC>>full_simp_tac(srw_ss())[])

val three_to_two_reg_pre_alloc_conventions = store_thm("three_to_two_reg_pre_alloc_conventions",
  ``∀prog. pre_alloc_conventions prog ⇒ pre_alloc_conventions (three_to_two_reg prog)``,
  ho_match_mp_tac three_to_two_reg_ind>>srw_tac[][]>>
  full_simp_tac(srw_ss())[pre_alloc_conventions_def,every_stack_var_def,call_arg_convention_def,three_to_two_reg_def,LET_THM]>>
  FULL_CASE_TAC>>fs[]>>
  PairCases_on`x`>>fs[]>>
  FULL_CASE_TAC>>fs[]>>
  PairCases_on`x`>>fs[])

val three_to_two_reg_flat_exp_conventions = store_thm("three_to_two_reg_flat_exp_conventions",
  ``∀prog. flat_exp_conventions prog ⇒ flat_exp_conventions (three_to_two_reg prog)``,
  ho_match_mp_tac three_to_two_reg_ind>>srw_tac[][]>>
  full_simp_tac(srw_ss())[flat_exp_conventions_def,three_to_two_reg_def,LET_THM]>>EVERY_CASE_TAC>>full_simp_tac(srw_ss())[])

val three_to_two_reg_inst_ok_less = store_thm("three_to_two_reg_inst_ok_less",
  ``∀prog. every_inst (inst_ok_less c) prog ⇒
  every_inst (inst_ok_less c) (three_to_two_reg prog)``,
  ho_match_mp_tac three_to_two_reg_ind>>srw_tac[][]>>
  full_simp_tac(srw_ss())[every_inst_def,three_to_two_reg_def,LET_THM]>>EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]
  >-
    (Cases_on`bop`>>Cases_on`ri`>>fs[inst_ok_less_def])
  >>
    Cases_on`n`>>fs[inst_ok_less_def])
(*word_alloc preserves syntactic conventions*)
val word_alloc_two_reg_inst_lem = prove(``
  ∀f prog.
  every_inst two_reg_inst prog ⇒
  every_inst two_reg_inst (apply_colour f prog)``,
  ho_match_mp_tac apply_colour_ind>>full_simp_tac(srw_ss())[every_inst_def]>>srw_tac[][]
  >-
    (Cases_on`i`>>TRY(Cases_on`a`)>>TRY(Cases_on`m`)>>
    full_simp_tac(srw_ss())[apply_colour_inst_def,two_reg_inst_def])
  >>
    EVERY_CASE_TAC>>unabbrev_all_tac>>full_simp_tac(srw_ss())[every_inst_def])

val word_alloc_two_reg_inst = store_thm("word_alloc_two_reg_inst",``
  ∀alg k prog col_opt.
  every_inst two_reg_inst prog ⇒
  every_inst two_reg_inst (word_alloc alg k prog col_opt)``,
  full_simp_tac(srw_ss())[word_alloc_def,oracle_colour_ok_def]>>
  srw_tac[][]>>EVERY_CASE_TAC>>full_simp_tac(srw_ss())[LET_THM]>>
  metis_tac[word_alloc_two_reg_inst_lem])

val word_alloc_flat_exp_conventions_lem = prove(``
  ∀f prog.
  flat_exp_conventions prog ⇒
  flat_exp_conventions (apply_colour f prog)``,
  ho_match_mp_tac apply_colour_ind>>full_simp_tac(srw_ss())[flat_exp_conventions_def]>>srw_tac[][]
  >-
    (EVERY_CASE_TAC>>unabbrev_all_tac>>full_simp_tac(srw_ss())[flat_exp_conventions_def])
  >>
    Cases_on`exp`>>full_simp_tac(srw_ss())[flat_exp_conventions_def])

val word_alloc_flat_exp_conventions = store_thm("word_alloc_flat_exp_conventions",``
  ∀alg k prog col_opt.
  flat_exp_conventions prog ⇒
  flat_exp_conventions (word_alloc alg k prog col_opt)``,
  full_simp_tac(srw_ss())[word_alloc_def,oracle_colour_ok_def]>>
  srw_tac[][]>>EVERY_CASE_TAC>>full_simp_tac(srw_ss())[LET_THM]>>
  metis_tac[word_alloc_flat_exp_conventions_lem])

val word_alloc_inst_ok_less_lem = prove(``
  ∀f prog c.
  every_inst (inst_ok_less c) prog ⇒
  every_inst (inst_ok_less c) (apply_colour f prog)``,
  ho_match_mp_tac apply_colour_ind>>full_simp_tac(srw_ss())[every_inst_def]>>srw_tac[][]
  >-
    (Cases_on`i`>>TRY(Cases_on`a`)>>TRY(Cases_on`m`)>>TRY(Cases_on`r`)>>
    full_simp_tac(srw_ss())[apply_colour_inst_def,inst_ok_less_def])
  >>
    EVERY_CASE_TAC>>unabbrev_all_tac>>full_simp_tac(srw_ss())[every_inst_def])

val word_alloc_inst_ok_less = store_thm("word_alloc_inst_ok_less",``
  ∀alg k prog col_opt c.
  every_inst (inst_ok_less c) prog ⇒
  every_inst (inst_ok_less c) (word_alloc alg k prog col_opt)``,
  full_simp_tac(srw_ss())[word_alloc_def,oracle_colour_ok_def]>>
  srw_tac[][]>>EVERY_CASE_TAC>>full_simp_tac(srw_ss())[LET_THM]>>
  metis_tac[word_alloc_inst_ok_less_lem])

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
  Induct>>full_simp_tac(srw_ss())[fake_moves_def]>>srw_tac[][]>>full_simp_tac(srw_ss())[flat_exp_conventions_def,every_inst_def]>>
  pop_assum mp_tac>> LET_ELIM_TAC>> EVERY_CASE_TAC>> full_simp_tac(srw_ss())[LET_THM]>>
  unabbrev_all_tac>>
  metis_tac[flat_exp_conventions_def,fake_move_def,inst_ok_less_def,every_inst_def,distinct_tar_reg_def])

(*ssa generates distinct regs and also preserves flattening*)
val ssa_cc_trans_flat_exp_conventions = prove(``
  ∀prog ssa na.
  flat_exp_conventions prog ⇒
  flat_exp_conventions (FST (ssa_cc_trans prog ssa na))``,
  ho_match_mp_tac ssa_cc_trans_ind>>full_simp_tac(srw_ss())[ssa_cc_trans_def]>>srw_tac[][]>>
  unabbrev_all_tac>>
  full_simp_tac(srw_ss())[flat_exp_conventions_def]
  >-
    (pop_assum mp_tac>>full_simp_tac(srw_ss())[fix_inconsistencies_def,fake_moves_def]>>LET_ELIM_TAC>>full_simp_tac(srw_ss())[flat_exp_conventions_def]>>
    metis_tac[fake_moves_conventions,flat_exp_conventions_def])
  >-
    (full_simp_tac(srw_ss())[list_next_var_rename_move_def]>>rpt (pop_assum mp_tac)>>
    LET_ELIM_TAC>>full_simp_tac(srw_ss())[flat_exp_conventions_def,EQ_SYM_EQ])
  >-
    (Cases_on`exp`>>full_simp_tac(srw_ss())[ssa_cc_trans_exp_def,flat_exp_conventions_def])
  >-
    (full_simp_tac(srw_ss())[list_next_var_rename_move_def]>>rpt (pop_assum mp_tac)>>
    LET_ELIM_TAC>>full_simp_tac(srw_ss())[flat_exp_conventions_def,EQ_SYM_EQ])
  >>
    EVERY_CASE_TAC>>unabbrev_all_tac>>full_simp_tac(srw_ss())[flat_exp_conventions_def]
    >-
      (full_simp_tac(srw_ss())[list_next_var_rename_move_def]>>rpt (pop_assum mp_tac)>>
      LET_ELIM_TAC>>full_simp_tac(srw_ss())[flat_exp_conventions_def,EQ_SYM_EQ])
    >>
      LET_ELIM_TAC>>unabbrev_all_tac>>
      full_simp_tac(srw_ss())[list_next_var_rename_move_def,flat_exp_conventions_def]>>
      full_simp_tac(srw_ss())[fix_inconsistencies_def]>>
      rpt (pop_assum mp_tac)>> LET_ELIM_TAC>>full_simp_tac(srw_ss())[]>>
      metis_tac[fake_moves_conventions,flat_exp_conventions_def])

val full_ssa_cc_trans_flat_exp_conventions = store_thm("full_ssa_cc_trans_flat_exp_conventions",``
  ∀prog n.
  flat_exp_conventions prog ⇒
  flat_exp_conventions (full_ssa_cc_trans n prog)``,
  full_simp_tac(srw_ss())[full_ssa_cc_trans_def,setup_ssa_def,list_next_var_rename_move_def]>>
  LET_ELIM_TAC>>unabbrev_all_tac>>full_simp_tac(srw_ss())[flat_exp_conventions_def,EQ_SYM_EQ]>>
  metis_tac[ssa_cc_trans_flat_exp_conventions,FST])

val ssa_cc_trans_inst_ok_less = prove(``
  ∀prog ssa na c.
  every_inst (inst_ok_less c) prog ⇒
  every_inst (inst_ok_less c) (FST (ssa_cc_trans prog ssa na))``,
  ho_match_mp_tac ssa_cc_trans_ind>>full_simp_tac(srw_ss())[ssa_cc_trans_def]>>srw_tac[][]>>
  unabbrev_all_tac>>
  full_simp_tac(srw_ss())[every_inst_def]
  >-
    (Cases_on`i`>>TRY(Cases_on`a`)>>TRY(Cases_on`m`)>>TRY(Cases_on`r`)>>
    full_simp_tac(srw_ss())[ssa_cc_trans_inst_def,LET_THM,next_var_rename_def]>>
    full_simp_tac(srw_ss())[EQ_SYM_EQ,inst_ok_less_def])
  >-
    (pop_assum mp_tac>>full_simp_tac(srw_ss())[fix_inconsistencies_def,fake_moves_def]>>LET_ELIM_TAC>>
    full_simp_tac(srw_ss())[every_inst_def,EQ_SYM_EQ]>>
    metis_tac[fake_moves_conventions])
  >>TRY
    (full_simp_tac(srw_ss())[list_next_var_rename_move_def]>>rpt (pop_assum mp_tac)>>
    LET_ELIM_TAC>>full_simp_tac(srw_ss())[every_inst_def,EQ_SYM_EQ])
  >>
    EVERY_CASE_TAC>>unabbrev_all_tac>>full_simp_tac(srw_ss())[every_inst_def]>>
    LET_ELIM_TAC>>
    unabbrev_all_tac>>full_simp_tac(srw_ss())[every_inst_def]>>
    full_simp_tac(srw_ss())[fix_inconsistencies_def]>>
    rpt (pop_assum mp_tac)>> LET_ELIM_TAC>>full_simp_tac(srw_ss())[]>>
    metis_tac[fake_moves_conventions,every_inst_def])

val full_ssa_cc_trans_inst_ok_less = store_thm("full_ssa_cc_trans_inst_ok_less",``
  ∀prog n c.
  every_inst (inst_ok_less c) prog ⇒
  every_inst (inst_ok_less c) (full_ssa_cc_trans n prog)``,
  full_simp_tac(srw_ss())[full_ssa_cc_trans_def,setup_ssa_def,list_next_var_rename_move_def]>>
  LET_ELIM_TAC>>unabbrev_all_tac>>full_simp_tac(srw_ss())[every_inst_def,EQ_SYM_EQ]>>
  metis_tac[ssa_cc_trans_inst_ok_less,FST])

val _ = export_theory ();
