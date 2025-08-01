(*
  Correctness proof for word_inst
*)
open preamble
     wordLangTheory wordPropsTheory wordConvsTheory
     word_instTheory wordSemTheory
     asmTheory;

val _ = temp_delsimps ["NORMEQ_CONV"]

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]

val _ = new_theory "word_instProof";

val _ = set_grammar_ancestry ["wordLang", "wordProps", "word_inst", "wordSem"];

(* resolve ambiguity between semanticsPrimitives$result and wordSem$result
   in latter's favour
*)
Type result[pp] = “:'a wordSem$result”

(* TODO: Move, but some of these are specific instantiations *)
Theorem PERM_SWAP_SIMP[local]:
  PERM (A ++ (B::C)) (B::(A++C))
Proof
  match_mp_tac APPEND_PERM_SYM>>full_simp_tac(srw_ss())[]>>
  metis_tac[PERM_APPEND]
QED

Triviality EL_FILTER:
  ∀ls x. x < LENGTH (FILTER P ls) ⇒ P (EL x (FILTER P ls))
Proof
  Induct>>srw_tac[][]>>
  Cases_on`x`>>full_simp_tac(srw_ss())[EL]
QED

Triviality PERM_SWAP:
  PERM (A ++ B ++ C) (B++(A++C))
Proof
  full_simp_tac(srw_ss())[PERM_DEF]>>srw_tac[][]>>
  match_mp_tac LIST_EQ>>CONJ_ASM1_TAC
  >-
    (full_simp_tac(srw_ss())[FILTER_APPEND]>>DECIDE_TAC)
  >>
  srw_tac[][]>>
  imp_res_tac EL_FILTER>>
  last_x_assum SUBST_ALL_TAC>>
  imp_res_tac EL_FILTER>>
  metis_tac[]
QED

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
Triviality convert_sub_ok:
  ∀ls.
  word_exp s (convert_sub ls) = word_exp s (Op Sub ls)
Proof
  ho_match_mp_tac convert_sub_ind>>srw_tac[][convert_sub_def,word_exp_def]>>unabbrev_all_tac>>
  full_simp_tac(srw_ss())[word_op_def,the_words_def]>>
  EVERY_CASE_TAC>>
  simp[]
QED

(*In general, any permutation works*)
Triviality word_exp_op_permute_lem:
  op ≠ Sub ⇒
  ∀ls ls'.
  PERM ls ls' ⇒
  word_exp s (Op op ls) = word_exp s (Op op ls')
Proof
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
  Cases_on`op`>>fs[]
QED

(*Remove tail recursion to make proof easier...*)
Definition pull_ops_simp_def:
  (pull_ops_simp op [] = [] ) ∧
  (pull_ops_simp op (x::xs) =
    case x of
    |  (Op op' ls) => if op = op' then ls ++ (pull_ops_simp op xs) else x::(pull_ops_simp op xs)
    |  _  => x::(pull_ops_simp op xs))
End

Triviality pull_ops_simp_pull_ops_perm:
  ∀ls x.
  PERM (pull_ops op ls x) ((pull_ops_simp op ls)++x)
Proof
  Induct>>full_simp_tac(srw_ss())[pull_ops_def,pull_ops_simp_def]>>srw_tac[][]>>EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
  TRY(qpat_abbrev_tac`A = B::x`>>
  first_x_assum(qspec_then`A` assume_tac)>>full_simp_tac(srw_ss())[Abbr`A`])>>
  TRY(first_x_assum(qspec_then`l++x` assume_tac))>>
  metis_tac[PERM_SWAP,PERM_TRANS,PERM_SWAP_SIMP,PERM_SYM]
QED

Triviality pull_ops_simp_pull_ops_word_exp:
  op ≠ Sub ⇒
  word_exp s (Op op (pull_ops op ls [])) = word_exp s (Op op (pull_ops_simp op ls))
Proof
  strip_tac>> imp_res_tac word_exp_op_permute_lem>>
  pop_assum match_mp_tac>>
  assume_tac pull_ops_simp_pull_ops_perm>>
  pop_assum (qspecl_then [`ls`,`[]`] assume_tac)>>full_simp_tac(srw_ss())[]
QED

(* TODO: Maybe move to props, if these are needed elsewhere *)

Triviality word_exp_op_mono:
  op ≠ Sub ⇒
  word_exp s (Op op ls) = word_exp s (Op op ls') ⇒
  word_exp s (Op op (x::ls)) =
  word_exp s (Op op (x::ls'))
Proof
  srw_tac[][word_exp_def,LET_THM]>>
  fs[the_words_def]>>Cases_on`word_exp s x`>>fs[]>>
  Cases_on`x'`>>fs[]>>
  rpt(qpat_x_assum`A=B` mp_tac)>>ntac 2 (TOP_CASE_TAC>>fs[])>>
  Cases_on`op`>>full_simp_tac(srw_ss())[word_op_def]
QED

Triviality the_words_append:
  ∀ls ls'.
  the_words (ls ++ ls') =
  case the_words ls of
    NONE => NONE
  | SOME w =>
    (case the_words ls' of
      NONE => NONE
    | SOME w' => SOME(w ++ w'))
Proof
  Induct>>fs[the_words_def]>>rw[]>>
  TOP_CASE_TAC>>fs[]>>
  TOP_CASE_TAC>>fs[]>>
  Cases_on`the_words ls`>>fs[]>>
  Cases_on`the_words ls'`>>fs[]
QED

Triviality word_exp_op_op:
  op ≠ Sub ⇒
  ∀ls ls'.
  word_exp s (Op op ls) = word_exp s (Op op ls') ⇒
  word_exp s (Op op (l ++ ls)) =
  word_exp s (Op op ((Op op l) :: ls'))
Proof
  srw_tac[][word_exp_def,LET_THM]>>
  fs[the_words_append]>>
  qpat_abbrev_tac`xx = MAP f l`>>
  Cases_on`the_words xx`>>fs[the_words_def]>>
  rpt(qpat_x_assum`_=_` mp_tac)>>
  ntac 2 (TOP_CASE_TAC)>>fs[]>>
  Cases_on`op`>> fs[word_op_def,FOLDR_APPEND]>>
  rw[Abbr`xx`]>>
  rpt(pop_assum kall_tac)>>
  Induct_on`x`>>fs[]
QED

Triviality pull_ops_ok:
  op ≠ Sub ⇒
  ∀ls. word_exp s (Op op (pull_ops op ls [])) =
         word_exp s (Op op ls)
Proof
  strip_tac>>
  full_simp_tac(srw_ss())[pull_ops_simp_pull_ops_word_exp]>>
  Induct>>srw_tac[][pull_ops_simp_def]>>Cases_on`op`>>full_simp_tac(srw_ss())[]>>
  FULL_CASE_TAC>>full_simp_tac(srw_ss())[word_exp_op_mono]>>
  IF_CASES_TAC>>full_simp_tac(srw_ss())[word_exp_op_mono]>>
  `b ≠ Sub` by srw_tac[][]>>
  imp_res_tac word_exp_op_op>>
  pop_assum (qspec_then`l` assume_tac)>>full_simp_tac(srw_ss())[]
QED

(* Done with pull_ops, next is optimize_consts *)

Triviality word_exp_swap_head:
  ∀B.
  op ≠ Sub ⇒
  word_exp s (Op op A) = SOME (Word w) ⇒
  word_exp s (Op op (B++A)) = word_exp s (Op op (Const w::B))
Proof
  fs[word_exp_def,the_words_append,the_words_def]>>rw[]>>
  FULL_CASE_TAC>>fs[]>>
  FULL_CASE_TAC>>fs[word_op_def]>>
  Cases_on`op`>>fs[FOLDR_APPEND]>>
  rpt(pop_assum kall_tac)>>
  Induct_on`x'`>>full_simp_tac(srw_ss())[]
QED

Triviality EVERY_is_const_word_exp:
  ∀ls. EVERY is_const ls ⇒
  EVERY IS_SOME (MAP (λa. word_exp s a) ls)
Proof
  Induct>>srw_tac[][]>>Cases_on`h`>>full_simp_tac(srw_ss())[is_const_def,word_exp_def]
QED

Triviality all_consts_simp:
  op ≠ Sub ⇒
  ∀ls.
  EVERY is_const ls ⇒
  word_exp s (Op op ls) =
  SOME( Word(THE (word_op op (MAP rm_const ls))))
Proof
  strip_tac>>Induct>>
  fs[word_exp_def,the_words_def]
  >-
    (fs[word_op_def]>>
    Cases_on`op`>>full_simp_tac(srw_ss())[])
  >>
  rw[]>>
  Cases_on`h`>>
  gvs[is_const_def,word_exp_def,AllCaseEqs()]>>
  drule EVERY_is_const_word_exp>>rw[]>>
  Cases_on`op`>>fs[word_op_def,rm_const_def]
QED

Triviality word_exp_reduce_const:
  word_exp s (Op op (Const w :: rest)) = SOME x ⇒
  word_exp s (reduce_const op w rest) = SOME x
Proof
  rw[reduce_const_def,word_exp_def]>>
  every_case_tac>>
  gvs[the_words_def,word_exp_def,word_op_def,AllCaseEqs()]
QED

Triviality optimize_consts_ok:
  op ≠ Sub ∧ word_exp s (Op op ls) = SOME x ⇒
  word_exp s (optimize_consts op ls) = SOME x
Proof
  rw[optimize_consts_def]>>
  pairarg_tac>>gvs[]>>
  Cases_on`const_ls`>>gvs[]
  >- (
    imp_res_tac word_exp_op_permute_lem>>
    qpat_x_assum` _ = SOME _` sym_sub_tac>>
    pop_assum match_mp_tac>>
    metis_tac[PERM_PARTITION,APPEND_NIL,PERM_SYM])>>
  `EVERY is_const (h::t)` by (
    gvs[PARTITION_DEF]>>
    drule (GSYM PARTs_HAVE_PROP)>>
    simp[EVERY_MEM])>>
  drule all_consts_simp>>
  disch_then drule>>
  disch_then (qspec_then`s` assume_tac)>>
  `PERM ls ((h::t)++nconst_ls)` by metis_tac[PERM_PARTITION]>>
  imp_res_tac word_exp_op_permute_lem>>
  pop_assum(qspec_then`s` SUBST_ALL_TAC)>>
  match_mp_tac word_exp_reduce_const>>
  drule_all word_exp_swap_head>>
  simp[]>>
  disch_then (qspec_then `nconst_ls` sym_sub_tac)>>
  metis_tac[word_exp_op_permute_lem,PERM_APPEND]
QED

Triviality pull_exp_ok:
  ∀exp s x.
  word_exp s exp = SOME x ⇒
  word_exp s (pull_exp exp) = SOME x
Proof
  ho_match_mp_tac pull_exp_ind>>srw_tac[][]>>
  full_simp_tac(srw_ss())[pull_exp_def,LET_THM]>>
  TRY(full_simp_tac(srw_ss())[op_consts_def,word_exp_def,LET_THM,word_op_def,the_words_def]>>
    FULL_CASE_TAC>>fs[]>>
    FULL_CASE_TAC>>fs[]>>NO_TAC)
  >- (fs[convert_sub_ok,word_exp_def,MAP_MAP_o]>>
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
    fs[]) >>
  TRY(irule optimize_consts_ok)>>
  simp[pull_ops_ok]>>
  fs[word_exp_def,the_words_def]>>
  (* 6 goals *)
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
  rfs[]
QED

(* pull_exp syntax *)
Triviality convert_sub_every_var_exp:
  ∀ls.
  (∀x. MEM x ls ⇒ every_var_exp P x) ⇒
  every_var_exp P (convert_sub ls)
Proof
  ho_match_mp_tac convert_sub_ind>>srw_tac[][convert_sub_def]>>
  full_simp_tac(srw_ss())[every_var_exp_def,EVERY_MEM]
QED

Triviality optimize_consts_every_var_exp:
  ∀ls.
  (∀x. MEM x ls ⇒ every_var_exp P x) ⇒
  every_var_exp P (optimize_consts op ls)
Proof
  srw_tac[][optimize_consts_def]>>
  `PERM ls (const_ls++nconst_ls)` by metis_tac[PERM_PARTITION]>>full_simp_tac(srw_ss())[]>>
  imp_res_tac PERM_MEM_EQ>>
  rw[reduce_const_def]>>
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[every_var_exp_def,LET_THM,EVERY_MEM]
QED

val pull_ops_every_var_exp = Q.prove(`
  ∀ls acc.
  EVERY (every_var_exp P) acc ∧ EVERY (every_var_exp P) ls ⇒
  EVERY (every_var_exp P) (pull_ops op ls acc)`,
  Induct>>full_simp_tac(srw_ss())[pull_ops_def]>>srw_tac[][]>>EVERY_CASE_TAC>>full_simp_tac(srw_ss())[every_var_exp_def]>>
  metis_tac[ETA_AX,EVERY_APPEND,every_var_exp_def]) |> REWRITE_RULE[EVERY_MEM];

Triviality pull_exp_every_var_exp:
  ∀exp.
  every_var_exp P exp ⇒
  every_var_exp P (pull_exp exp)
Proof
  ho_match_mp_tac pull_exp_ind>>full_simp_tac(srw_ss())[op_consts_def,pull_exp_def,every_var_exp_def,EVERY_MEM,EVERY_MAP,LET_THM]>>srw_tac[][]
  >-
    metis_tac[convert_sub_every_var_exp,MEM_MAP,PULL_EXISTS]
  >>
    match_mp_tac optimize_consts_every_var_exp>>
    match_mp_tac pull_ops_every_var_exp>>srw_tac[][]>>
    metis_tac[MEM_MAP]
QED

(* flatten_exp correctness *)
Triviality flatten_exp_ok:
  ∀exp s x.
  word_exp s exp = SOME x ⇒
  word_exp s (flatten_exp exp) = SOME x
Proof
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
    res_tac>>fs[]
QED

(*All ops are 2 args. Technically, we should probably check that Sub has 2 args. However, the semantics already checks that and it will get removed later*)
Definition binary_branch_exp_def:
  (binary_branch_exp (Op Sub exps) = EVERY (binary_branch_exp) exps) ∧
  (binary_branch_exp (Op op xs) = (LENGTH xs = 2 ∧ EVERY (binary_branch_exp) xs)) ∧
  (binary_branch_exp (Load exp) = binary_branch_exp exp) ∧
  (binary_branch_exp (Shift shift exp nexp) = binary_branch_exp exp) ∧
  (binary_branch_exp exp = T)
Termination
  WF_REL_TAC `measure (exp_size ARB)`
   \\ REPEAT STRIP_TAC \\ IMP_RES_TAC MEM_IMP_exp_size
   \\ TRY (FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `ARB`))
   \\ full_simp_tac(srw_ss())[exp_size_def]
   \\ TRY (DECIDE_TAC)
End

(* flatten_exp syntax *)
Triviality flatten_exp_binary_branch_exp:
  ∀exp.
  binary_branch_exp (flatten_exp exp)
Proof
  ho_match_mp_tac flatten_exp_ind>>full_simp_tac(srw_ss())[op_consts_def,flatten_exp_def,binary_branch_exp_def,EVERY_MEM,EVERY_MAP]
QED

Theorem flatten_exp_every_var_exp[local]:
  ∀exp.
  every_var_exp P exp ⇒
  every_var_exp P (flatten_exp exp)
Proof
  ho_match_mp_tac flatten_exp_ind>>full_simp_tac(srw_ss())[op_consts_def,flatten_exp_def,every_var_exp_def,EVERY_MEM,EVERY_MAP]
QED

(* inst_select correctness
  Main difficulty: Dealing with multiple choice of optimizations, depending on whether we are allowed to use them w.r.t. to the asm configuration
*)
Theorem inst_select_exp_thm[local]:
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
    else T
Proof
  completeInduct_on`exp_size (K 0) exp`>>
  rpt strip_tac>>
  Cases_on`exp`>>
  full_simp_tac(srw_ss())[evaluate_def,binary_branch_exp_def,every_var_exp_def]
  >-
    (rename [‘Const’]>>
    simp[inst_select_exp_def]>>
    full_simp_tac(srw_ss())[LET_THM,evaluate_def,inst_def,mem_load_def,assign_def,word_exp_def,set_var_def,mem_load_def,word_op_def]>>
    simp[state_component_equality,locals_rel_def,lookup_insert]>>
    full_simp_tac(srw_ss())[locals_rel_def]>>
    gvs[AllCaseEqs()])
  >-
    (rename [‘Var’] >>
    simp[inst_select_exp_def]>>
    full_simp_tac(srw_ss())[LET_THM,evaluate_def,inst_def,mem_load_def,assign_def,word_exp_def,set_var_def,mem_load_def,word_op_def,get_vars_def,set_vars_def,get_var_def]>>
    full_simp_tac(srw_ss())[locals_rel_def]>>
    res_tac>>fs[alist_insert_def]>>
    simp[state_component_equality,lookup_insert]>>
    gvs[AllCaseEqs()])
  >-
    (rename [‘Lookup’]>>
    simp[inst_select_exp_def]>>
    full_simp_tac(srw_ss())[LET_THM,evaluate_def,inst_def,mem_load_def,assign_def,word_exp_def,set_var_def,mem_load_def,word_op_def,get_vars_def,set_vars_def,get_var_def]>>
    fs[locals_rel_def,state_component_equality,lookup_insert]>>
    gvs[AllCaseEqs()])
  >-
    (rename [‘Load’]>>
    Cases_on`∃exp' w'. e = Op Add[exp';Const w']` >>full_simp_tac(srw_ss())[]
    >-
      (simp[Once inst_select_exp_def]>>IF_CASES_TAC
      >-
        (fs[binary_branch_exp_def,every_var_exp_def,word_exp_def,the_words_def]>>EVERY_CASE_TAC>>full_simp_tac(srw_ss())[IS_SOME_EXISTS]>>rev_full_simp_tac(srw_ss())[]>>
        last_x_assum mp_tac>>simp[Once PULL_FORALL]>>disch_then (qspec_then`exp'` mp_tac)>>simp[exp_size_def]>>strip_tac>>res_tac>>
        pop_assum(qspecl_then[`temp`,`c`] assume_tac)>>full_simp_tac(srw_ss())[evaluate_def,LET_THM]>>
        simp[evaluate_def,LET_THM,inst_def,mem_load_def,assign_def,word_exp_def,the_words_def]>>
        `lookup temp loc'' = SOME (Word c')` by metis_tac[]>>full_simp_tac(srw_ss())[mem_load_def]>>
        full_simp_tac(srw_ss())[state_component_equality,get_var_def,set_var_def,lookup_insert]>>srw_tac[][]>>
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
        simp[state_component_equality,set_var_def,get_var_def,lookup_insert,word_op_def]>>
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
      simp[state_component_equality,set_var_def,get_var_def,lookup_insert]>>
      srw_tac[][]>>DISJ2_TAC>>strip_tac>>
      `x ≠ temp` by DECIDE_TAC>>metis_tac[])
  >-
    (rename [‘Op’]>>
    Cases_on`∃e1 e2. l = [e1;e2]`>>full_simp_tac(srw_ss())[inst_select_exp_def]
    >-
      (IF_CASES_TAC THEN1
       (gvs[PULL_FORALL] >>
        first_x_assum (qspec_then ‘e1’ mp_tac) >>
        fs [exp_size_def,binary_branch_exp_def] >>
        ‘binary_branch_exp e1’ by
           (Cases_on ‘b’ \\ fs [binary_branch_exp_def]) >> fs [] >>
        disch_then drule >>
        gvs [word_exp_def,AllCaseEqs(),the_words_def,GSYM PULL_FORALL] >>
        disch_then (qspecl_then [‘c’,‘temp’] strip_assume_tac) >>
        pop_assum drule >> fs [] >> strip_tac >>
        gvs [evaluate_def,word_exp_def,the_words_def] >>
        first_assum (qspec_then ‘temp’ assume_tac) >> fs [] >>
        Cases_on ‘e2’ >> fs [is_Lookup_CurrHeap_def] >>
        rename [‘Lookup ss’] \\ Cases_on ‘ss’ >> fs [is_Lookup_CurrHeap_def] >>
        gvs [word_exp_def,set_var_def,get_var_def,state_component_equality,lookup_insert] >>
        rw [] >> metis_tac [prim_recTheory.LESS_REFL]) >>
      pop_assum mp_tac >>
      IF_CASES_TAC THEN1
       (gvs[PULL_FORALL] >>
        first_x_assum (qspec_then ‘e2’ mp_tac) >>
        fs [exp_size_def,binary_branch_exp_def] >>
        ‘binary_branch_exp e2’ by
           (Cases_on ‘b’ \\ fs [binary_branch_exp_def]) >> fs [] >>
        disch_then drule >>
        gvs [word_exp_def,AllCaseEqs(),the_words_def,GSYM PULL_FORALL] >>
        disch_then (qspecl_then [‘c’,‘temp’] strip_assume_tac) >>
        pop_assum drule >> fs [] >> strip_tac >>
        gvs [evaluate_def,word_exp_def,the_words_def] >>
        first_assum (qspec_then ‘temp’ assume_tac) >> fs [] >>
        Cases_on ‘e1’ >> fs [is_Lookup_CurrHeap_def] >>
        rename [‘Lookup ss’] \\ Cases_on ‘ss’ >> fs [is_Lookup_CurrHeap_def] >>
        rename [‘word_op b [x1; x2] = SOME x3’] >>
        ‘word_op b [x2; x1] = SOME x3’ by
          (Cases_on ‘b’ \\ fs [word_op_def,AllCaseEqs()]) >>
        gvs [word_exp_def,set_var_def,get_var_def,state_component_equality,lookup_insert] >>
        rw [] >> metis_tac [prim_recTheory.LESS_REFL]) >>
      pop_assum mp_tac>>
      `binary_branch_exp e1` by
        (Cases_on`b`>>full_simp_tac(srw_ss())[binary_branch_exp_def])>>
      fs[word_exp_def,the_words_def,IS_SOME_EXISTS]>>
      gvs[AllCaseEqs()]>>
      last_x_assum mp_tac>>simp[Once PULL_FORALL]>>
      disch_then assume_tac>>
      first_assum mp_tac>>
      disch_then (qspec_then`e1`mp_tac)>>
      impl_tac>- simp[]>>
      rpt (disch_then drule)>>
      disch_then (qspecl_then[`c`,`temp`] assume_tac)>>
      fs[]>>
      Cases_on`∃w. e2 = Const w`
      >- (
        rpt (disch_then kall_tac) >>fs[]>>
        IF_CASES_TAC
        >-
          (gvs[evaluate_def,inst_def,mem_load_def,word_exp_def,assign_def,the_words_def]>>
          gvs[COND_EXPAND_IMP,SF DNF_ss]>>
          full_simp_tac(srw_ss())[word_op_def]>>
          Cases_on`b`>>
          full_simp_tac(srw_ss())[set_var_def,get_var_def,
          state_component_equality,lookup_insert,word_exp_def]>>
          srw_tac[][]>>
          first_x_assum irule>>
          fs[])
        >> IF_CASES_TAC
        >-
          (fs[evaluate_def,LET_THM,inst_def,mem_load_def,assign_def,
          word_exp_def,set_var_def,lookup_insert,the_words_def]>>
          gvs[COND_EXPAND_IMP,SF DNF_ss]>>
          full_simp_tac(srw_ss())[]>>rev_full_simp_tac(srw_ss())[word_exp_def,word_op_def]>>
          full_simp_tac(srw_ss())[get_var_def,state_component_equality,lookup_insert]>>srw_tac[][]>>
          first_x_assum irule>>fs[])
        >- (
          full_simp_tac(srw_ss())[evaluate_def,LET_THM] >>
          gvs[COND_EXPAND_IMP,SF DNF_ss]>>
          simp[inst_def,assign_def,word_exp_def] >>
          simp[get_var_def,set_var_def,lookup_insert] >>
          simp[the_words_def] >>
          rev_full_simp_tac(srw_ss())[word_exp_def] >>
          simp[lookup_insert] >>
          srw_tac[][]))>>
      ntac 2 (disch_then assume_tac)
      >>
        `inst_select_exp c tar temp (Op b [e1;e2]) =
        let p1 = inst_select_exp c temp temp e1 in
        let p2 = inst_select_exp c (temp+1) (temp+1) e2 in
          Seq p1 (Seq p2 (Inst (Arith (Binop b tar temp (Reg (temp+1))))))` by
            (full_simp_tac(srw_ss())[inst_select_exp_def,LET_THM]>>
             EVERY_CASE_TAC>>full_simp_tac(srw_ss())[])>>
        pop_assum mp_tac >>
        pop_assum mp_tac >>
        pop_assum mp_tac >>
        full_simp_tac(srw_ss())[inst_select_exp_def,LET_THM]>>pop_assum kall_tac>>
        ntac 2 (disch_then assume_tac) >>
        IF_CASES_TAC THEN1 fs [] >>
        rpt (qpat_x_assum ‘~(_:bool)’ kall_tac) >>
        rpt (qpat_x_assum ‘_ ∨ _’ kall_tac) >>
        full_simp_tac(srw_ss())[evaluate_def,LET_THM]>>
        disch_then kall_tac >>
        first_x_assum(qspecl_then[`e2`] mp_tac)>>
        simp[exp_size_def]>>
        rename1`word_exp s e2 = SOME (Word cc)`>>
        disch_then(qspecl_then [`c`,`temp+1`,`temp+1`,`s with locals:=loc''`,`Word cc`,`loc''`] mp_tac)>>
        impl_tac>-
          (srw_tac[][locals_rel_def]>-(Cases_on`b`>>full_simp_tac(srw_ss())[binary_branch_exp_def])
          >-
            (match_mp_tac every_var_exp_mono>>
            HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[]>>DECIDE_TAC)
          >>
            (*word_exp invariant under extra locals*)
            irule locals_rel_word_exp>>
            fs[locals_rel_def]>>
            first_x_assum (irule_at Any)>>
            rw[]>>
            gvs[COND_EXPAND_IMP,SF DNF_ss])>>
        strip_tac>>full_simp_tac(srw_ss())[word_exp_def]>>
        gvs[COND_EXPAND_IMP,SF DNF_ss]>>
        simp[inst_def,assign_def,word_exp_def,LET_THM,state_component_equality,
        get_var_def,set_var_def,lookup_insert,the_words_def])
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
    (rename [‘Shift’]>>
    simp[inst_select_exp_def]>>last_x_assum mp_tac>>simp[Once PULL_FORALL]>>disch_then (qspec_then`e`mp_tac)>>impl_tac>-(full_simp_tac(srw_ss())[exp_size_def]>>DECIDE_TAC)>>
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
      (srw_tac[][]>>res_tac>>
      first_assum(qspecl_then[`temp`,`c`] assume_tac)>>
      full_simp_tac(srw_ss())[evaluate_def,LET_THM,inst_def,mem_load_def,assign_def,word_exp_def]>>
      `lookup temp loc'' = SOME (Word c')` by metis_tac[]>>
      full_simp_tac(srw_ss())[get_var_def,set_var_def,state_component_equality,lookup_insert]>>
      srw_tac[][]>>DISJ2_TAC>>strip_tac>>`x ≠ temp` by DECIDE_TAC>>
      metis_tac[])
    >-
      (`n ≥ dimindex(:'a)` by DECIDE_TAC>>
      full_simp_tac(srw_ss())[word_sh_def]))
QED

Triviality locals_rm:
  D with locals := D.locals = D
Proof
  full_simp_tac(srw_ss())[state_component_equality]
QED

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
  >- (* Assign *)
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
  >- (* Set *)
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
    full_simp_tac(srw_ss())[get_var_def,state_component_equality,locals_rel_def]>>
    srw_tac[][]>>`x' ≠ temp` by DECIDE_TAC>>metis_tac[])
  >-(*Store has optimizations*)
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
        simp[get_var_def] >>
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
        simp[get_var_def] >>
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
      simp[get_var_def] >>
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
  >- ( (* MustTerminate *)
    full_simp_tac(srw_ss())[evaluate_def,LET_THM,every_var_def]>>
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
    ( (* ShareInst *)
    gvs[evaluate_def,LET_THM,every_var_def,AllCaseEqs()] >>
    qpat_abbrev_tac`expr = flatten_exp (pull_exp exp)`>>
    Cases_on`∃w exp'. expr = Op Add [exp';Const w]` >>
    gvs[]
    >- (
      IF_CASES_TAC
      >- (
        imp_res_tac pull_exp_every_var_exp>>
        imp_res_tac pull_exp_ok>>
        imp_res_tac flatten_exp_ok>>
        imp_res_tac flatten_exp_every_var_exp>>
        qspec_then `pull_exp exp` assume_tac flatten_exp_binary_branch_exp >>
        gvs[binary_branch_exp_def] >>
        drule inst_select_exp_thm >>
        gvs[every_var_exp_def] >>
        ntac 2 (disch_then drule) >>
        gvs[word_exp_def,the_words_def,AllCaseEqs()] >>
        disch_then $ qspecl_then [`c`,`temp`] assume_tac >>
        gvs[AllCaseEqs(),evaluate_def,COND_EXPAND_IMP,FORALL_AND_THM] >>
        gvs[AllCaseEqs(),PULL_EXISTS,
          oneline share_inst_def,
          sh_mem_load_def,sh_mem_load_byte_def,sh_mem_store_def,sh_mem_store_byte_def,
          oneline sh_mem_set_var_def, sh_mem_load32_def, sh_mem_store32_def,
          set_var_def,locals_rel_def,word_exp_def,the_words_def,word_op_def,
          get_var_def,state_component_equality,lookup_insert,flush_state_def] >>
        metis_tac[lookup_insert]
      ) >>
      imp_res_tac pull_exp_every_var_exp>>
      imp_res_tac pull_exp_ok>>
      imp_res_tac flatten_exp_ok>>
      imp_res_tac flatten_exp_every_var_exp>>
      qspec_then `pull_exp exp` assume_tac flatten_exp_binary_branch_exp >>
      drule inst_select_exp_thm >>
      gvs[every_var_exp_def] >>
      ntac 3 (disch_then drule) >>
      disch_then $ qspecl_then [`c`,`temp`] assume_tac >>
      gvs[AllCaseEqs(),evaluate_def,COND_EXPAND_IMP,FORALL_AND_THM] >>
      gvs[AllCaseEqs(),PULL_EXISTS,
        oneline share_inst_def,
        sh_mem_load_def,sh_mem_load_byte_def,sh_mem_store_def,sh_mem_store_byte_def,
        oneline sh_mem_set_var_def, sh_mem_load32_def, sh_mem_store32_def,
        set_var_def,locals_rel_def,word_exp_def,the_words_def,word_op_def,
        get_var_def,state_component_equality,lookup_insert,flush_state_def] >>
      metis_tac[lookup_insert]) >>
    imp_res_tac pull_exp_every_var_exp>>
    imp_res_tac pull_exp_ok>>
    imp_res_tac flatten_exp_ok>>
    imp_res_tac flatten_exp_every_var_exp>>
    assume_tac flatten_exp_binary_branch_exp >>
    qmatch_goalsub_abbrev_tac `evaluate prog` >>
    `prog = (Seq (inst_select_exp c temp temp expr) (ShareInst op c' (Var temp)),
       st with locals := loc)`
      by (every_case_tac >> gvs[]) >>
    qpat_x_assum `Abbrev (prog = _)` kall_tac >>
    first_x_assum $ qspec_then `pull_exp exp` assume_tac >>
    drule inst_select_exp_thm >>
    gvs[every_var_exp_def] >>
    ntac 3 (disch_then drule) >>
    disch_then $ qspecl_then [`c`, `temp`] assume_tac >>
    gvs[AllCaseEqs(),evaluate_def,COND_EXPAND_IMP,FORALL_AND_THM] >>
    gvs[AllCaseEqs(),PULL_EXISTS,
      oneline share_inst_def,
      sh_mem_load_def,sh_mem_load_byte_def,sh_mem_store_def,sh_mem_store_byte_def,
      oneline sh_mem_set_var_def, sh_mem_load32_def, sh_mem_store32_def,
      set_var_def,locals_rel_def,word_exp_def,the_words_def,word_op_def,
      get_var_def,state_component_equality,lookup_insert,flush_state_def] >>
    metis_tac[lookup_insert])
  >- ( (* If *)
    gvs[AllCaseEqs(),evaluate_def]>>
    Cases_on`ri`>>
    fs[get_var_imm_def]>>
    imp_res_tac locals_rel_get_var>>
    fs[every_var_def,every_var_imm_def])
  >>
    imp_res_tac locals_rel_evaluate_thm>>
    ntac 14 (pop_assum kall_tac)>>
    full_simp_tac(srw_ss())[LET_THM,evaluate_def,every_var_def]>>
    qpat_abbrev_tac `stt = st with locals := A`>>
    Cases_on`get_vars args stt`>>full_simp_tac(srw_ss())[]>>
    IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
    Cases_on`ret`>>full_simp_tac(srw_ss())[add_ret_loc_def]
    >-(*Tail Call*)
      (Cases_on`find_code dest x st.code st.stack_size`>>Cases_on`handler`>>
      TRY(PairCases_on`x'`)>>full_simp_tac(srw_ss())[]>>
      full_simp_tac(srw_ss())[call_env_def, flush_state_def,dec_clock_def,
       state_component_equality,locals_rel_def])
    >>
      PairCases_on`x'`>>full_simp_tac(srw_ss())[add_ret_loc_def]>>
      ntac 6 (TOP_CASE_TAC>>full_simp_tac(srw_ss())[]) >-
        (Cases_on `handler` >>
        fs [call_env_def, flush_state_def,state_component_equality,locals_rel_def] >>
        Cases_on `x''` >> fs [] >> Cases_on `r` >> fs [] >> Cases_on `r''` >>
          fs [push_env_def, state_component_equality] >>  metis_tac [])
      >>
      full_simp_tac(srw_ss())[]>>
      qpat_x_assum`A=(res,rst with locals:=loc')` mp_tac>>
      qpat_abbrev_tac`st = call_env B lsz C`>>
      qpat_abbrev_tac`st' = call_env B lsz C`>>
      `st' = st''` by
        (unabbrev_all_tac>>
        Cases_on`handler`>>TRY(PairCases_on`x''`)>>
        full_simp_tac(srw_ss())[call_env_def, flush_state_def,push_env_def,dec_clock_def,push_env_def,LET_THM,
         env_to_list_def,state_component_equality])>>
      Cases_on`evaluate(q',st'')`>>
      Cases_on`q''`>>full_simp_tac(srw_ss())[]>>
      Cases_on`x''`>>full_simp_tac(srw_ss())[]
      >-
        (IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
        FULL_CASE_TAC>>full_simp_tac(srw_ss())[]>>
        IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
        ntac 2 (FULL_CASE_TAC>>full_simp_tac(srw_ss())[])>>srw_tac[][]>>
        res_tac>>full_simp_tac(srw_ss())[]>>
        qpat_abbrev_tac`D = set_vars A B C`>>
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
  rw[]>>
  fs[three_to_two_reg_def,evaluate_def,state_component_equality]>>
  TRY (
    gvs[AllCaseEqs(),inst_def,assign_def,word_exp_def,get_vars_def,get_var_def,set_vars_def,alist_insert_def,the_words_def,distinct_tar_reg_def,every_inst_def]>>
    EVERY_CASE_TAC >>
    gvs[word_exp_def,lookup_insert,set_var_def,insert_shadow]>>rw[]>>
    rw[]>>gvs[insert_shadow,integer_wordTheory.word_0_w2i]>>
    NO_TAC)
  >- (
    rpt (pairarg_tac>>gvs[])>>
    gvs[inst_def,assign_def,word_exp_def,get_vars_def,get_var_def,set_vars_def,alist_insert_def,the_words_def,distinct_tar_reg_def,every_inst_def]>>
    gvs[AllCaseEqs()] >>
    fs[lookup_alist_insert] >>
    EVERY_CASE_TAC >>
    gvs[word_exp_def,alist_insert_def] >>
    fs[get_var_def,set_var_def,lookup_insert,insert_shadow])
  >- (
    rw[]>>gvs[]>>
    rpt (pairarg_tac>>gvs[])>>
    gvs[AllCaseEqs(),every_inst_def]>>
    first_x_assum drule_all>>rw[] >>
    first_x_assum drule >> rw[])
  >- (
    gvs[AllCaseEqs(),every_inst_def]>>
    fs[add_ret_loc_def]>>
    every_case_tac>>
    gvs[call_env_def,push_env_def] >>
    rpt (pairarg_tac >> gvs[]) >>
    every_case_tac>> gvs[] >>
    res_tac >> gvs[])
  >- (
    gvs[AllCaseEqs(),every_inst_def]>>
    fs[add_ret_loc_def]>>
    every_case_tac>>
    gvs[call_env_def,push_env_def])
QED

Theorem evaluate_three_to_two_reg_prog:
  evaluate (prog,s) = (res,s') ∧ res ≠ SOME Error ∧
  every_inst distinct_tar_reg prog
  ⇒
  evaluate(three_to_two_reg_prog t prog,s) = (res,s')
Proof
  rw[word_instTheory.three_to_two_reg_prog_def]>>
  drule_all three_to_two_reg_correct>>
  simp[]
QED

val _ = export_theory ();
