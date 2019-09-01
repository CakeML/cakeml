(*
  Correctness proof for word_inst
*)
open preamble
     wordLangTheory wordPropsTheory word_instTheory wordSemTheory
     asmTheory

val _ = new_theory "word_instProof";

val _ = set_grammar_ancestry ["wordLang", "wordProps", "word_inst", "wordSem"];

(* TODO: Move, but some of these are specific instantiations *)
val PERM_SWAP_SIMP = Q.prove(`
  PERM (A ++ (B::C)) (B::(A++C))`,
  match_mp_tac APPEND_PERM_SYM>>full_simp_tac(srw_ss())[]>>
  metis_tac[PERM_APPEND]);

val EL_FILTER = Q.prove(`
  ∀ls x. x < LENGTH (FILTER P ls) ⇒ P (EL x (FILTER P ls))`,
  Induct>>srw_tac[][]>>
  Cases_on`x`>>full_simp_tac(srw_ss())[EL]);

val PERM_SWAP = Q.prove(`
  PERM (A ++ B ++ C) (B++(A++C))`,
  full_simp_tac(srw_ss())[PERM_DEF]>>srw_tac[][]>>
  match_mp_tac LIST_EQ>>CONJ_ASM1_TAC
  >-
    (full_simp_tac(srw_ss())[FILTER_APPEND]>>DECIDE_TAC)
  >>
  srw_tac[][]>>
  imp_res_tac EL_FILTER>>
  last_x_assum SUBST_ALL_TAC>>
  imp_res_tac EL_FILTER>>
  metis_tac[]);

(* Instruction selection and assorted optimisation correctness
0) pull_exp correctness -- this does pull_ops and optimize_consts
1) pull_exp syntax
2) flatten_exp correctness -- makes stuff into binary branching trees
3) flatten_exp syntax -- prove the above property (binary_branch_exp -- not counted as a "global" syntactic convention since it is only used locally here)
4) inst_select_exp and inst_select correctness
5) inst_select syntax -- flat_exp_conventions and full_inst_ok_less
6) three_to_two_reg correctness
7) three_to_two_reg syntax -- two_reg_insts and some preservation ones
*)

(* pull_exp correctness *)
val convert_sub_ok = Q.prove(`
  ∀ls.
  word_exp s (convert_sub ls) = word_exp s (Op Sub ls)`,
  ho_match_mp_tac convert_sub_ind>>srw_tac[][convert_sub_def,word_exp_def]>>unabbrev_all_tac>>
  full_simp_tac(srw_ss())[word_op_def,the_words_def]>>
  EVERY_CASE_TAC>>
  simp[]);

(*In general, any permutation works*)
val word_exp_op_permute_lem = Q.prove(`
  op ≠ Sub ⇒
  ∀ls ls'.
  PERM ls ls' ⇒
  word_exp s (Op op ls) = word_exp s (Op op ls')`,
  strip_tac>>
  ho_match_mp_tac PERM_STRONG_IND>>srw_tac[][]>>
  full_simp_tac(srw_ss())[word_exp_def,LET_THM,the_words_def]>>
  qpat_abbrev_tac`A = MAP f ls`>>
  qpat_abbrev_tac`Z = MAP f ls'`>>
  `PERM A Z` by metis_tac[PERM_MAP]>>
  TRY(Cases_on`word_exp s y`>>fs[])>>
  Cases_on`word_exp s x`>>fs[]>>
  Cases_on`x'`>>fs[]>>
  TRY(Cases_on`x''`>>fs[])>>
  rpt(qpat_x_assum`C=D:'a word_loc option` mp_tac)>>
  Cases_on`the_words A`>>
  Cases_on`the_words Z`>>
  fs[word_op_def]>>
  Cases_on`op`>>fs[]);

(*Remove tail recursion to make proof easier...*)
val pull_ops_simp_def = Define`
  (pull_ops_simp op [] = [] ) ∧
  (pull_ops_simp op (x::xs) =
    case x of
    |  (Op op' ls) => if op = op' then ls ++ (pull_ops_simp op xs) else x::(pull_ops_simp op xs)
    |  _  => x::(pull_ops_simp op xs))`;

val pull_ops_simp_pull_ops_perm = Q.prove(`
  ∀ls x.
  PERM (pull_ops op ls x) ((pull_ops_simp op ls)++x)`,
  Induct>>full_simp_tac(srw_ss())[pull_ops_def,pull_ops_simp_def]>>srw_tac[][]>>EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
  TRY(qpat_abbrev_tac`A = B::x`>>
  first_x_assum(qspec_then`A` assume_tac)>>full_simp_tac(srw_ss())[Abbr`A`])>>
  TRY(first_x_assum(qspec_then`l++x` assume_tac))>>
  metis_tac[PERM_SWAP,PERM_TRANS,PERM_SWAP_SIMP,PERM_SYM]);

val pull_ops_simp_pull_ops_word_exp = Q.prove(`
  op ≠ Sub ⇒
  word_exp s (Op op (pull_ops op ls [])) = word_exp s (Op op (pull_ops_simp op ls))`,
  strip_tac>> imp_res_tac word_exp_op_permute_lem>>
  pop_assum match_mp_tac>>
  assume_tac pull_ops_simp_pull_ops_perm>>
  pop_assum (qspecl_then [`ls`,`[]`] assume_tac)>>full_simp_tac(srw_ss())[]);

(* TODO: Maybe move to props, if these are needed elsewhere *)

val word_exp_op_mono = Q.prove(`
  op ≠ Sub ⇒
  word_exp s (Op op ls) = word_exp s (Op op ls') ⇒
  word_exp s (Op op (x::ls)) =
  word_exp s (Op op (x::ls'))`,
  srw_tac[][word_exp_def,LET_THM]>>
  fs[the_words_def]>>Cases_on`word_exp s x`>>fs[]>>
  Cases_on`x'`>>fs[]>>
  rpt(qpat_x_assum`A=B` mp_tac)>>ntac 2 (TOP_CASE_TAC>>fs[])>>
  Cases_on`op`>>full_simp_tac(srw_ss())[word_op_def]);

val the_words_append = Q.prove(`
  ∀ls ls'.
  the_words (ls ++ ls') =
  case the_words ls of
    NONE => NONE
  | SOME w =>
    (case the_words ls' of
      NONE => NONE
    | SOME w' => SOME(w ++ w'))`,
  Induct>>fs[the_words_def]>>rw[]>>
  TOP_CASE_TAC>>fs[]>>
  TOP_CASE_TAC>>fs[]>>
  Cases_on`the_words ls`>>fs[]>>
  Cases_on`the_words ls'`>>fs[]);

val word_exp_op_op = Q.prove(`
  op ≠ Sub ⇒
  ∀ls ls'.
  word_exp s (Op op ls) = word_exp s (Op op ls') ⇒
  word_exp s (Op op (l ++ ls)) =
  word_exp s (Op op ((Op op l) :: ls'))`,
  srw_tac[][word_exp_def,LET_THM]>>
  fs[the_words_append]>>
  qpat_abbrev_tac`xx = MAP f l`>>
  Cases_on`the_words xx`>>fs[the_words_def]>>
  rpt(qpat_x_assum`_=_` mp_tac)>>
  ntac 2 (TOP_CASE_TAC)>>fs[]>>
  Cases_on`op`>> fs[word_op_def,FOLDR_APPEND]>>
  rw[Abbr`xx`]>>
  rpt(pop_assum kall_tac)>>
  Induct_on`x`>>fs[]);

val pull_ops_ok = Q.prove(`
  op ≠ Sub ⇒
  ∀ls. word_exp s (Op op (pull_ops op ls [])) =
         word_exp s (Op op ls)`,
  strip_tac>>
  full_simp_tac(srw_ss())[pull_ops_simp_pull_ops_word_exp]>>
  Induct>>srw_tac[][pull_ops_simp_def]>>Cases_on`op`>>full_simp_tac(srw_ss())[]>>
  FULL_CASE_TAC>>full_simp_tac(srw_ss())[word_exp_op_mono]>>
  IF_CASES_TAC>>full_simp_tac(srw_ss())[word_exp_op_mono]>>
  `b ≠ Sub` by srw_tac[][]>>
  imp_res_tac word_exp_op_op>>
  pop_assum (qspec_then`l` assume_tac)>>full_simp_tac(srw_ss())[]);

(* Done with pull_ops, next is optimize_consts *)

val word_exp_swap_head = Q.prove(`
  ∀B.
  op ≠ Sub ⇒
  word_exp s (Op op A) = SOME (Word w) ⇒
  word_exp s (Op op (B++A)) = word_exp s (Op op (Const w::B))`,
  fs[word_exp_def,the_words_append,the_words_def]>>rw[]>>
  FULL_CASE_TAC>>fs[]>>
  FULL_CASE_TAC>>fs[word_op_def]>>
  Cases_on`op`>>fs[FOLDR_APPEND]>>
  rpt(pop_assum kall_tac)>>
  Induct_on`x'`>>full_simp_tac(srw_ss())[]);

val EVERY_is_const_word_exp = Q.prove(`
  ∀ls. EVERY is_const ls ⇒
  EVERY IS_SOME (MAP (λa. word_exp s a) ls)`,
  Induct>>srw_tac[][]>>Cases_on`h`>>full_simp_tac(srw_ss())[is_const_def,word_exp_def]);

val all_consts_simp = Q.prove(`
  op ≠ Sub ⇒
  ∀ls.
  EVERY is_const ls ⇒
  word_exp s (Op op ls) =
  SOME( Word(THE (word_op op (MAP rm_const ls))))`,
  strip_tac>>Induct>>full_simp_tac(srw_ss())[word_exp_def,the_words_def]
  >-
    (full_simp_tac(srw_ss())[word_op_def]>>
    Cases_on`op`>>full_simp_tac(srw_ss())[])
  >>
  ntac 2 strip_tac>>
  Cases_on`h`>>full_simp_tac(srw_ss())[is_const_def,word_exp_def]>>
  FULL_CASE_TAC>>fs[EVERY_is_const_word_exp]>>
  Cases_on`op`>>full_simp_tac(srw_ss())[word_op_def,rm_const_def]);

val optimize_consts_ok = Q.prove(`
  op ≠ Sub ⇒
  ∀ls. word_exp s (optimize_consts op ls) =
       word_exp s (Op op ls)`,
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
    qpat_abbrev_tac`Z = h::t`>>
    `h:: (t ++A) = Z ++A` by full_simp_tac(srw_ss())[]>>pop_assum SUBST_ALL_TAC>>
    metis_tac[PERM_APPEND]);

val pull_exp_ok = Q.prove(`
  ∀exp s x.
  word_exp s exp = SOME x ⇒
  word_exp s (pull_exp exp) = SOME x`,
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
    qpat_x_assum`A=SOME x'` mp_tac>>
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
  rfs[]);

(* pull_exp syntax *)
val convert_sub_every_var_exp = Q.prove(`
  ∀ls.
  (∀x. MEM x ls ⇒ every_var_exp P x) ⇒
  every_var_exp P (convert_sub ls)`,
  ho_match_mp_tac convert_sub_ind>>srw_tac[][convert_sub_def]>>
  full_simp_tac(srw_ss())[every_var_exp_def,EVERY_MEM]);

val optimize_consts_every_var_exp = Q.prove(`
  ∀ls.
  (∀x. MEM x ls ⇒ every_var_exp P x) ⇒
  every_var_exp P (optimize_consts op ls)`,
  srw_tac[][optimize_consts_def]>>
  `PERM ls (const_ls++nconst_ls)` by metis_tac[PERM_PARTITION]>>full_simp_tac(srw_ss())[]>>
  imp_res_tac PERM_MEM_EQ>>
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[every_var_exp_def,LET_THM,EVERY_MEM]);

val pull_ops_every_var_exp = Q.prove(`
  ∀ls acc.
  EVERY (every_var_exp P) acc ∧ EVERY (every_var_exp P) ls ⇒
  EVERY (every_var_exp P) (pull_ops op ls acc)`,
  Induct>>full_simp_tac(srw_ss())[pull_ops_def]>>srw_tac[][]>>EVERY_CASE_TAC>>full_simp_tac(srw_ss())[every_var_exp_def]>>
  metis_tac[ETA_AX,EVERY_APPEND,every_var_exp_def]) |> REWRITE_RULE[EVERY_MEM];

val pull_exp_every_var_exp = Q.prove(`
  ∀exp.
  every_var_exp P exp ⇒
  every_var_exp P (pull_exp exp)`,
  ho_match_mp_tac pull_exp_ind>>full_simp_tac(srw_ss())[op_consts_def,pull_exp_def,every_var_exp_def,EVERY_MEM,EVERY_MAP,LET_THM]>>srw_tac[][]
  >-
    metis_tac[convert_sub_every_var_exp,MEM_MAP,PULL_EXISTS]
  >>
    match_mp_tac optimize_consts_every_var_exp>>
    match_mp_tac pull_ops_every_var_exp>>srw_tac[][]>>
    metis_tac[MEM_MAP]);

(* flatten_exp correctness *)
val flatten_exp_ok = Q.prove(`
  ∀exp s x.
  word_exp s exp = SOME x ⇒
  word_exp s (flatten_exp exp) = SOME x`,
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
    TRY(qpat_x_assum`A=SOME x` mp_tac>>rename1`word_exp s exp'`>>
    Cases_on`word_exp s exp'`>>fs[]>>Cases_on`x'`>>fs[]>>
    FULL_CASE_TAC>>fs[]>>
    first_x_assum(qspec_then`s` assume_tac)>>rfs[]>>
    first_x_assum(qspec_then`s` assume_tac)>>rfs[])>>
    res_tac>>fs[]);

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
   \\ TRY (DECIDE_TAC));

(* flatten_exp syntax *)
val flatten_exp_binary_branch_exp = Q.prove(`
  ∀exp.
  binary_branch_exp (flatten_exp exp)`,
  ho_match_mp_tac flatten_exp_ind>>full_simp_tac(srw_ss())[op_consts_def,flatten_exp_def,binary_branch_exp_def,EVERY_MEM,EVERY_MAP]);

val flatten_exp_every_var_exp = Q.prove(`
  ∀exp.
  every_var_exp P exp ⇒
  every_var_exp P (flatten_exp exp)`,
  ho_match_mp_tac flatten_exp_ind>>full_simp_tac(srw_ss())[op_consts_def,flatten_exp_def,every_var_exp_def,EVERY_MEM,EVERY_MAP]);

(* inst_select correctness
  Main difficulty: Dealing with multiple choice of optimizations, depending on whether we are allowed to use them w.r.t. to the asm configuration
*)
val inst_select_exp_thm = Q.prove(`
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
    else T`,
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
        impl_tac>-(full_simp_tac(srw_ss())[exp_size_def]>>DECIDE_TAC)>>
        full_simp_tac(srw_ss())[binary_branch_exp_def,every_var_exp_def,the_words_def]>>EVERY_CASE_TAC>>full_simp_tac(srw_ss())[IS_SOME_EXISTS]>>rev_full_simp_tac(srw_ss())[]>>
        qpat_x_assum`A=SOME w` mp_tac>>simp[Once word_exp_def]>>FULL_CASE_TAC>>
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
      impl_tac>-(full_simp_tac(srw_ss())[exp_size_def]>>DECIDE_TAC)>>
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
        impl_tac>-(full_simp_tac(srw_ss())[exp_size_def]>>DECIDE_TAC)>>
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
        impl_tac>-
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
      qpat_x_assum`A=SOME w` mp_tac>>
      Cases_on`word_exp s h`>>fs[]>>
      Cases_on`x`>>fs[]>>
      Cases_on`t`>>fs[the_words_def]>>
      Cases_on`word_exp s h'`>>fs[]>>
      Cases_on`x`>>fs[]>>
      Cases_on`t'`>>fs[the_words_def]>>
      EVERY_CASE_TAC>>fs[]))
  >-
    (*Shift*)
    (simp[inst_select_exp_def]>>last_x_assum mp_tac>>simp[Once PULL_FORALL]>>disch_then (qspec_then`e`mp_tac)>>impl_tac>-(full_simp_tac(srw_ss())[exp_size_def]>>DECIDE_TAC)>>
    full_simp_tac(srw_ss())[LET_THM,word_exp_def]>>EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]
    >-
      (`word_sh s' c' n = SOME c'` by
        (full_simp_tac(srw_ss())[word_sh_def]>>EVERY_CASE_TAC>>
        fs[])>>
      srw_tac[][]>>res_tac>>
      first_assum(qspecl_then[`temp`,`c`] assume_tac)>>
      full_simp_tac(srw_ss())[evaluate_def,LET_THM,get_vars_def,get_var_def]>>
      `lookup temp loc'' = SOME (Word c')` by metis_tac[]>>
      full_simp_tac(srw_ss())[set_vars_def,alist_insert_def,state_component_equality,lookup_insert]>>
      srw_tac[][]>>rev_full_simp_tac(srw_ss())[]>>
      Cases_on `x = temp`>>fs[]>>metis_tac[])
    >-
      (assume_tac DIMINDEX_GT_0>>
      `0 ≠ dimindex(:'a)` by DECIDE_TAC>>full_simp_tac(srw_ss())[])
    >-
      (srw_tac[][]>>res_tac>>
      first_assum(qspecl_then[`temp`,`c`] assume_tac)>>
      full_simp_tac(srw_ss())[evaluate_def,LET_THM,inst_def,mem_load_def,assign_def,word_exp_def]>>
      `lookup temp loc'' = SOME (Word c')` by metis_tac[]>>
      full_simp_tac(srw_ss())[set_var_def,state_component_equality,lookup_insert]>>
      srw_tac[][]>>DISJ2_TAC>>strip_tac>>`x ≠ temp` by DECIDE_TAC>>
      metis_tac[])
    >-
      (`n ≥ dimindex(:'a)` by DECIDE_TAC>>
      full_simp_tac(srw_ss())[word_sh_def])));

val locals_rm = Q.prove(`
  D with locals := D.locals = D`,
  full_simp_tac(srw_ss())[state_component_equality]);

(*  Main semantics theorem for inst selection:
    The inst-selected program gives same result but
    with possibly more locals used
*)
Theorem inst_select_thm:
    ∀c temp prog st res rst loc.
  evaluate (prog,st) = (res,rst) ∧
  every_var (λx. x < temp) prog ∧
  res ≠ SOME Error ∧
  locals_rel temp st.locals loc ⇒
  ∃loc'.
  evaluate (inst_select c temp prog,st with locals:=loc) = (res,rst with locals:=loc') ∧
  case res of
    NONE => locals_rel temp rst.locals loc'
  | SOME _ => rst.locals = loc'
Proof
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
        pop_assum mp_tac>>impl_tac>-
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
        qpat_x_assum`expr =A` sym_sub_tac>>
        imp_res_tac pull_exp_ok>>
        imp_res_tac flatten_exp_ok>>
        imp_res_tac inst_select_exp_thm>>
        full_simp_tac(srw_ss())[AND_IMP_INTRO]>>
        ntac 2 (pop_assum kall_tac)>>
        pop_assum mp_tac>>
        impl_tac>-
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
      impl_tac
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
    ntac 2 (pairarg_tac>>full_simp_tac(srw_ss())[])>>
    Cases_on`res'' = SOME TimeOut`>>full_simp_tac(srw_ss())[]>>
    rveq>>
    res_tac>>
    last_x_assum kall_tac>>
    ntac 2 (pop_assum kall_tac)>>
    pop_assum(qspec_then`loc` assume_tac)>>rev_full_simp_tac(srw_ss())[]>>
    simp[state_component_equality])
  >-
    (TOP_CASE_TAC>>TRY(IF_CASES_TAC)>>fs[evaluate_def]>>
    qpat_x_assum`A=(res,rst)` mp_tac>>
    fs[get_var_imm_def]
    >-
      (ntac 4(TOP_CASE_TAC>>fs[])>>
      fs[every_var_def,every_var_imm_def]>>
      srw_tac[][]>> imp_res_tac locals_rel_get_var>>
      fs[GSYM AND_IMP_INTRO,every_var_def])
    >-
      (ntac 3(TOP_CASE_TAC>>fs[])>>
      fs[every_var_def,every_var_imm_def]>>
      srw_tac[][]>> imp_res_tac locals_rel_get_var>>
      fs[GSYM AND_IMP_INTRO,every_var_def])
    >-
      (ntac 2(TOP_CASE_TAC>>fs[])>>
      fs[inst_def,assign_def,word_exp_def]>>
      imp_res_tac locals_rel_get_var>>fs[every_var_def,every_var_imm_def]>>
      rfs[get_var_def,set_var_def,lookup_insert]>>
      rw[]>>
      fs[AND_IMP_INTRO,every_var_def]>>
      first_assum match_mp_tac>>
      fs[locals_rel_def,lookup_insert]))
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
      qpat_x_assum`A=(res,rst with locals:=loc')` mp_tac>>
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
        full_simp_tac(srw_ss())[state_component_equality]
QED

(* inst_select syntax *)
val inst_select_exp_flat_exp_conventions = Q.prove(`
  ∀c tar temp exp.
  flat_exp_conventions (inst_select_exp c tar temp exp)`,
  ho_match_mp_tac inst_select_exp_ind>>srw_tac[][]>>full_simp_tac(srw_ss())[inst_select_exp_def,flat_exp_conventions_def,LET_THM]>>
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[flat_exp_conventions_def,inst_select_exp_def,LET_THM]);

Theorem inst_select_flat_exp_conventions:
    ∀c temp prog.
  flat_exp_conventions (inst_select c temp prog)
Proof
  ho_match_mp_tac inst_select_ind >>srw_tac[][]>>
  full_simp_tac(srw_ss())[flat_exp_conventions_def,inst_select_def,LET_THM]>>
  EVERY_CASE_TAC>>
  full_simp_tac(srw_ss())[flat_exp_conventions_def]>>
  metis_tac[inst_select_exp_flat_exp_conventions]
QED

(*Less restrictive version of inst_ok guaranteed by inst_select*)
val inst_select_exp_full_inst_ok_less = Q.prove(`
  ∀c tar temp exp.
  addr_offset_ok c 0w ⇒
  full_inst_ok_less c (inst_select_exp c tar temp exp)`,
  ho_match_mp_tac inst_select_exp_ind>>rw[]>>
  fs[inst_select_exp_def,LET_THM,inst_ok_less_def,full_inst_ok_less_def]>>
  every_case_tac>>fs[full_inst_ok_less_def,inst_ok_less_def,inst_select_exp_def,LET_THM]
  );

Theorem inst_select_full_inst_ok_less:
    ∀c temp prog.
  addr_offset_ok c 0w ∧
  every_inst (inst_ok_less c) prog
  ⇒
  full_inst_ok_less c (inst_select c temp prog)
Proof
  ho_match_mp_tac inst_select_ind>>
  rw[inst_select_def,full_inst_ok_less_def,every_inst_def]>>
  EVERY_CASE_TAC>>
  fs[inst_select_def,full_inst_ok_less_def,inst_ok_less_def,every_inst_def]>>
  metis_tac[inst_select_exp_full_inst_ok_less]
QED

(* three_to_two_reg semantics *)

(*Semantics preservation*)
Theorem three_to_two_reg_correct:
    ∀prog s res s'.
  every_inst distinct_tar_reg prog ∧
  evaluate (prog,s) = (res,s') ∧ res ≠ SOME Error
  ⇒
  evaluate(three_to_two_reg prog,s) = (res,s')
Proof
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
    ntac 2(pairarg_tac>>full_simp_tac(srw_ss())[])>>
    Cases_on`res'' = SOME TimeOut`>>full_simp_tac(srw_ss())[]>>rveq>>
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
      rev_full_simp_tac(srw_ss())[]
QED

(* Syntactic three_to_two_reg *)
Theorem three_to_two_reg_two_reg_inst:
    ∀prog. every_inst two_reg_inst (three_to_two_reg prog)
Proof
  ho_match_mp_tac three_to_two_reg_ind>>srw_tac[][]>>full_simp_tac(srw_ss())[every_inst_def,two_reg_inst_def,three_to_two_reg_def,LET_THM]>>EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]
QED

Theorem three_to_two_reg_wf_cutsets:
   ∀prog. wf_cutsets prog ⇒ wf_cutsets (three_to_two_reg prog)
Proof
  ho_match_mp_tac three_to_two_reg_ind>>srw_tac[][]>>
  full_simp_tac(srw_ss())[wf_cutsets_def,three_to_two_reg_def,LET_THM]>>EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]
QED

Theorem three_to_two_reg_pre_alloc_conventions:
   ∀prog. pre_alloc_conventions prog ⇒ pre_alloc_conventions (three_to_two_reg prog)
Proof
  ho_match_mp_tac three_to_two_reg_ind>>srw_tac[][]>>
  full_simp_tac(srw_ss())[pre_alloc_conventions_def,every_stack_var_def,three_to_two_reg_def,LET_THM,call_arg_convention_def,inst_arg_convention_def]>>
  FULL_CASE_TAC>>fs[]>>
  PairCases_on`x`>>fs[]>>
  FULL_CASE_TAC>>fs[]>>
  PairCases_on`x`>>fs[]
QED

Theorem three_to_two_reg_flat_exp_conventions:
   ∀prog. flat_exp_conventions prog ⇒ flat_exp_conventions (three_to_two_reg prog)
Proof
  ho_match_mp_tac three_to_two_reg_ind>>srw_tac[][]>>
  full_simp_tac(srw_ss())[flat_exp_conventions_def,three_to_two_reg_def,LET_THM]>>EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]
QED

Theorem three_to_two_reg_full_inst_ok_less:
   ∀prog. full_inst_ok_less c prog ⇒
  full_inst_ok_less c (three_to_two_reg prog)
Proof
  ho_match_mp_tac three_to_two_reg_ind>>srw_tac[][]>>
  full_simp_tac(srw_ss())[three_to_two_reg_def,LET_THM]>>EVERY_CASE_TAC>>fs[full_inst_ok_less_def]
  >-
    (Cases_on`bop`>>Cases_on`ri`>>fs[full_inst_ok_less_def,inst_ok_less_def,every_inst_def])
  >-
    (Cases_on`n`>>fs[inst_ok_less_def])
  >>
    metis_tac[inst_ok_less_def]
QED

(* label preservation stuff *)
val inst_select_exp_no_lab = Q.prove(`
  ∀c temp temp' exp.
  extract_labels (inst_select_exp c temp temp' exp) = []`,
  ho_match_mp_tac inst_select_exp_ind>>rw[inst_select_exp_def]>>fs[extract_labels_def]>>
  rpt(TOP_CASE_TAC>>fs[extract_labels_def,inst_select_exp_def]))

Theorem inst_select_lab_pres:
    ∀c temp prog.
  extract_labels prog = extract_labels (inst_select c temp prog)
Proof
  ho_match_mp_tac inst_select_ind>>rw[inst_select_def,extract_labels_def]>>
  TRY(metis_tac[inst_select_exp_no_lab])>>
  EVERY_CASE_TAC>>fs[extract_labels_def]>>
  TRY(metis_tac[inst_select_exp_no_lab])
QED

Theorem three_to_two_reg_lab_pres:
    ∀prog.
  extract_labels prog = extract_labels (three_to_two_reg prog)
Proof
  ho_match_mp_tac three_to_two_reg_ind>>rw[three_to_two_reg_def,extract_labels_def]>>EVERY_CASE_TAC>>fs[]
QED

val _ = export_theory ();
