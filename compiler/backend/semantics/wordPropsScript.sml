(*
  Properties about wordLang and its semantics
*)
open preamble BasicProvers
     wordLangTheory wordSemTheory
     asmTheory reg_allocTheory backendPropsTheory;

(*
Main lemmas:
0) Clock lemmas (add_clock, dec_clock, IO monotonicity)
1) Code table constancy across eval
2) Swapping stack for one with identical values (but different keys)
3) Thms to handle the permutation oracle
4) mono and conj for every_var etc.
5) Effect of extra locals (locals_rel)
6) Other misc things and defs followed by syntactic things
*)

val _ = temp_delsimps ["NORMEQ_CONV"]

val _ = new_theory "wordProps";

(* TODO: move *)

Theorem mem_list_rearrange:
    ∀ls x f. MEM x (list_rearrange f ls) ⇔ MEM x ls
Proof
  full_simp_tac(srw_ss())[MEM_EL]>>srw_tac[][wordSemTheory.list_rearrange_def]>>
  imp_res_tac BIJ_IFF_INV>>
  full_simp_tac(srw_ss())[BIJ_DEF,INJ_DEF,SURJ_DEF]>>
  srw_tac[][EQ_IMP_THM]>>full_simp_tac(srw_ss())[EL_GENLIST]
  >- metis_tac[]>>
  qexists_tac `g n`>>full_simp_tac(srw_ss())[]
QED

val GENLIST_I =
  GENLIST_EL |> Q.SPECL [`xs`,`\i. EL i xs`,`LENGTH xs`]
    |> SIMP_RULE std_ss []

val ALL_DISTINCT_EL = ``ALL_DISTINCT xs``
  |> ONCE_REWRITE_CONV [GSYM GENLIST_I]
  |> SIMP_RULE std_ss [ALL_DISTINCT_GENLIST]

Theorem PERM_list_rearrange:
   !f xs. ALL_DISTINCT xs ==> PERM xs (list_rearrange f xs)
Proof
  srw_tac[][] \\ match_mp_tac PERM_ALL_DISTINCT
  \\ full_simp_tac(srw_ss())[mem_list_rearrange]
  \\ full_simp_tac(srw_ss())[wordSemTheory.list_rearrange_def] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[ALL_DISTINCT_GENLIST] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[BIJ_DEF,INJ_DEF,SURJ_DEF]
  \\ full_simp_tac(srw_ss())[ALL_DISTINCT_EL]
QED

Theorem PERM_ALL_DISTINCT_MAP:
   !xs ys. PERM xs ys ==>
            ALL_DISTINCT (MAP f xs) ==>
            ALL_DISTINCT (MAP f ys) /\ !x. MEM x ys <=> MEM x xs
Proof
  full_simp_tac(srw_ss())[MEM_PERM] \\ srw_tac[][]
  \\ `PERM (MAP f xs) (MAP f ys)` by full_simp_tac(srw_ss())[PERM_MAP]
  \\ metis_tac [ALL_DISTINCT_PERM]
QED

Theorem ALL_DISTINCT_MEM_IMP_ALOOKUP_SOME = Q.prove(`
  !xs x y. ALL_DISTINCT (MAP FST xs) /\ MEM (x,y) xs ==> ALOOKUP xs x = SOME y`,
  Induct \\ full_simp_tac(srw_ss())[]
  \\ Cases \\ full_simp_tac(srw_ss())[ALOOKUP_def] \\ srw_tac[][]
  \\ res_tac \\ full_simp_tac(srw_ss())[MEM_MAP,FORALL_PROD]
  \\ rev_full_simp_tac(srw_ss())[]) |> SPEC_ALL
  |> curry save_thm "ALL_DISTINCT_MEM_IMP_ALOOKUP_SOME";

(* -- *)

(* Clock lemmas *)

(*TODO: define globally somewhere? *)
fun get_thms ty = { case_def = TypeBase.case_def_of ty, nchotomy = TypeBase.nchotomy_of ty }
val case_eq_thms = pair_case_eq::bool_case_eq::map (prove_case_eq_thm o get_thms)
  [``:'a option``,``:'a list``,``:'a word_loc``,``:'a inst``
  ,``:'a arith``,``:'a addr``,``:memop``,``:'a wordSem$result``,``:'a ffi_result``] |> LIST_CONJ |> curry save_thm "case_eq_thms"

Theorem set_store_const[simp]:
   (set_store x y z).clock = z.clock ∧
   (set_store x y z).ffi = z.ffi ∧
   (set_store x y z).compile = z.compile ∧
   (set_store x y z).compile_oracle = z.compile_oracle ∧
   (set_store x y z).be = z.be ∧
   (set_store x y z).data_buffer = z.data_buffer ∧
   (set_store x y z).code_buffer = z.code_buffer ∧
   (set_store x y z).code = z.code ∧
   (set_store x y z).locals_size = z.locals_size ∧
   (set_store x y z).stack_limit = z.stack_limit ∧
   (set_store x y z).stack_max = z.stack_max ∧
   (set_store x y z).stack_size = z.stack_size
Proof
  EVAL_TAC
QED

Theorem set_store_with_const[simp]:
   (set_store x y (z with clock := k)) = set_store x y z with clock := k
Proof
  EVAL_TAC
QED

Theorem stack_size_eq:
  (stack_size(StackFrame n l NONE::stack) = OPTION_MAP2 $+ n (stack_size stack)) /\
  (stack_size(StackFrame n l (SOME handler)::stack) =
     OPTION_MAP2 $+ (OPTION_MAP ($+ 3) n) (stack_size stack)) /\
  (stack_size [] = SOME 1)
Proof
  rw[stack_size_def,stack_size_frame_def]
QED

Theorem stack_size_eq2:
  (stack_size(sfrm::stack) =
    OPTION_MAP2 $+ (stack_size_frame sfrm) (stack_size stack)) /\
  (stack_size [] = SOME 1)
Proof
  rw[stack_size_def,stack_size_frame_def]
QED

Theorem push_env_const[simp]:
   (push_env x y z).clock = z.clock ∧
   (push_env x y z).ffi = z.ffi ∧
   (push_env x y z).termdep = z.termdep ∧
   (push_env x y z).data_buffer = z.data_buffer ∧
   (push_env x y z).code_buffer = z.code_buffer ∧
   (push_env x y z).compile = z.compile ∧
   (push_env x y z).compile_oracle = z.compile_oracle ∧
   (push_env x y z).gc_fun = z.gc_fun ∧
   (push_env x y z).be = z.be ∧
   (push_env x y z).code = z.code ∧
   (push_env x y z).stack_limit = z.stack_limit ∧
   (push_env x y z).stack_size = z.stack_size
Proof
  Cases_on`y`>>simp[push_env_def,UNCURRY] >>
  rename1`SOME p` >>
  PairCases_on`p` >>
  srw_tac[][push_env_def] >> srw_tac[][]
QED

Theorem push_env_with_const[simp]:
   (push_env x y (z with clock := k) = push_env x y z with clock := k) ∧
   (push_env x y (z with locals := l) = push_env x y z with locals := l)
Proof
  Cases_on`y`>>srw_tac[][push_env_def] >> unabbrev_all_tac >> simp[state_component_equality] >>
  rename1`SOME p` >>
  PairCases_on`p` >>
  srw_tac[][push_env_def] >> unabbrev_all_tac >> simp[state_component_equality]
QED

Theorem pop_env_const:
   pop_env x = SOME y ⇒
   y.clock = x.clock /\
   y.ffi = x.ffi ∧
   y.be = x.be ∧
   y.compile = x.compile ∧
   y.compile_oracle = x.compile_oracle ∧
   y.data_buffer = x.data_buffer ∧
   y.code_buffer = x.code_buffer ∧
   y.code = x.code ∧
   y.stack_limit = x.stack_limit ∧
   y.stack_max = x.stack_max ∧
   y.stack_size = x.stack_size
Proof
   srw_tac[][pop_env_def] >>
   every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][]
QED

Theorem pop_env_with_const[simp]:
   pop_env (z with clock := k) = OPTION_MAP (λs. s with clock := k) (pop_env z) ∧
   pop_env (z with locals := l) = pop_env z
Proof
  srw_tac[][pop_env_def] >> every_case_tac >> full_simp_tac(srw_ss())[]
QED

Theorem call_env_const[simp]:
   (call_env x ss y).clock = y.clock ∧
   (call_env x ss y).compile_oracle = y.compile_oracle ∧
   (call_env x ss y).compile = y.compile ∧
   (call_env x ss y).be = y.be ∧
   (call_env x ss y).gc_fun = y.gc_fun ∧
   (call_env x ss y).ffi = y.ffi ∧
   (call_env x ss y).code = y.code ∧
   (call_env x ss y).code_buffer = y.code_buffer ∧
   (call_env x ss y).data_buffer = y.data_buffer ∧
   (call_env x ss y).stack_limit = y.stack_limit ∧
   (call_env x ss y).stack_size = y.stack_size
Proof
  EVAL_TAC
QED

Theorem call_env_with_const[simp]:
   call_env x ss (y with clock := k) = call_env x ss y with clock := k
Proof
  EVAL_TAC
QED

Theorem flush_state_const[simp]:
   (flush_state b y).clock = y.clock ∧
   (flush_state b y).compile_oracle = y.compile_oracle ∧
   (flush_state b y).compile = y.compile ∧
   (flush_state b y).be = y.be ∧
   (flush_state b y).gc_fun = y.gc_fun ∧
   (flush_state b y).ffi = y.ffi ∧
   (flush_state b y).code = y.code ∧
   (flush_state b y).code_buffer = y.code_buffer ∧
   (flush_state b y).data_buffer = y.data_buffer ∧
   (flush_state b y).stack_limit = y.stack_limit ∧
   (flush_state b y).stack_size = y.stack_size ∧
   (flush_state F y).stack      = y.stack
Proof
  Cases_on `b` \\ EVAL_TAC
QED

Theorem flush_state_with_const[simp]:
   flush_state b (y with clock := k) = flush_state b y with clock := k
Proof
 Cases_on `b` \\ EVAL_TAC
QED

Theorem has_space_with_const[simp]:
   has_space x (y with clock := k) = has_space x y
Proof
  EVAL_TAC
QED

Theorem gc_const:
   gc x = SOME y ⇒
   y.clock = x.clock ∧
   y.ffi = x.ffi ∧
   y.code = x.code ∧
   y.be = x.be ∧
   y.code_buffer = x.code_buffer ∧
   y.data_buffer = x.data_buffer ∧
   y.compile = x.compile ∧
   y.compile_oracle = x.compile_oracle ∧
   y.locals_size = x.locals_size ∧
   y.stack_limit = x.stack_limit ∧
   y.stack_max = x.stack_max ∧
   y.stack_size = x.stack_size
Proof
  simp[gc_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> srw_tac[][]
QED

Theorem gc_with_const[simp]:
   gc (x with clock := k) = OPTION_MAP (λs. s with clock := k) (gc x) ∧
   gc (x with locals := l) = OPTION_MAP (λs. s with locals := l) (gc x)
Proof
  EVAL_TAC >>
  CASE_TAC >> EVAL_TAC >>
  CASE_TAC >> EVAL_TAC >>
  CASE_TAC >> EVAL_TAC >>
  CASE_TAC >> EVAL_TAC
QED

Theorem alloc_const:
   alloc c names s = (r,s') ⇒
   s'.clock = s.clock ∧
   s'.ffi = s.ffi ∧
   s'.code = s.code ∧
   s'.be = s.be ∧
   s'.code_buffer = s.code_buffer ∧
   s'.data_buffer = s.data_buffer ∧
   s'.compile = s.compile ∧
   s'.compile_oracle = s.compile_oracle ∧
   s'.stack_limit = s.stack_limit ∧
   s'.stack_size = s.stack_size
Proof
  srw_tac[][alloc_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  imp_res_tac pop_env_const >> full_simp_tac(srw_ss())[] >>
  imp_res_tac gc_const >> full_simp_tac(srw_ss())[]
QED

Theorem alloc_with_const[simp]:
   alloc c names (s with clock := k) =
   (λ(r,s). (r,s with clock := k)) (alloc c names s)
Proof
  srw_tac[][alloc_def] >>
  CASE_TAC >> full_simp_tac(srw_ss())[] >>
  CASE_TAC >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  CASE_TAC >> full_simp_tac(srw_ss())[] >>
  CASE_TAC >> full_simp_tac(srw_ss())[] >>
  CASE_TAC >> full_simp_tac(srw_ss())[] >>
  CASE_TAC >> full_simp_tac(srw_ss())[]
QED

Theorem get_var_with_const[simp]:
   get_var x (y with clock := k) = get_var x y /\
   get_var x (y with permute := p) = get_var x y /\
   get_var x (y with code_buffer := cb) = get_var x y /\
   get_var x (y with data_buffer := db) = get_var x y /\
   get_var x (y with code := cc) = get_var x y /\
   get_var x (y with compile_oracle := co) = get_var x y /\
   get_var x (y with compile := ccc) = get_var x y /\
   get_var x (y with stack := xs) = get_var x y /\
   get_var x (y with locals_size := ss) = get_var x y /\
   get_var x (y with stack_limit := n) = get_var x y /\
   get_var x (y with stack_max := ss) = get_var x y /\
   get_var x (y with stack_size := ssize) = get_var x y
Proof
  EVAL_TAC
QED

Theorem get_vars_with_const[simp]:
   get_vars x (y with clock := k) = get_vars x y /\
   get_vars x (y with permute := p) = get_vars x y /\
   get_vars x (y with code_buffer := cb) = get_vars x y /\
   get_vars x (y with data_buffer := db) = get_vars x y /\
   get_vars x (y with code := cc) = get_vars x y /\
   get_vars x (y with compile_oracle := co) = get_vars x y /\
   get_vars x (y with compile := ccc) = get_vars x y /\
   get_vars x (y with stack := xs) = get_vars x y /\
   get_vars x (y with locals_size := ss) = get_vars x y /\
   get_vars x (y with stack_limit := n) = get_vars x y /\
   get_vars x (y with stack_max := ss) = get_vars x y /\
   get_vars x (y with stack_size := ssize) = get_vars x y
Proof
  Induct_on`x`>>srw_tac[][get_vars_def]
QED

Theorem get_fp_var_with_const[simp]:
   get_fp_var x (y with clock := k) = get_fp_var x y
Proof
  EVAL_TAC
QED

Theorem set_var_const[simp]:
   (set_var x y z).clock = z.clock ∧
   (set_var x y z).be = z.be ∧
   (set_var x y z).ffi = z.ffi ∧
   (set_var x y z).compile = z.compile ∧
   (set_var x y z).compile_oracle = z.compile_oracle ∧
   (set_var x y z).code_buffer = z.code_buffer ∧
   (set_var x y z).data_buffer = z.data_buffer ∧
   (set_var x y z).stack = z.stack ∧
   (set_var x y z).locals_size = z.locals_size ∧
   (set_var x y z).stack_limit = z.stack_limit ∧
   (set_var x y z).stack_max = z.stack_max ∧
   (set_var x y z).stack_size = z.stack_size
Proof
  EVAL_TAC
QED

Theorem set_fp_var_const[simp]:
   (set_fp_var x y z).clock = z.clock ∧
   (set_fp_var x y z).ffi = z.ffi ∧
   (set_fp_var x y z).stack = z.stack ∧
   (set_fp_var x y z).locals_size = z.locals_size ∧
   (set_fp_var x y z).stack_limit = z.stack_limit ∧
   (set_fp_var x y z).stack_max = z.stack_max ∧
   (set_fp_var x y z).stack_size = z.stack_size
Proof
  EVAL_TAC
QED

Theorem set_var_with_const[simp]:
   set_var x y (z with clock := k) = set_var x y z with clock := k /\
   set_var x y (z with permute := p) = set_var x y z with permute := p
Proof
  EVAL_TAC
QED

Theorem set_fp_var_with_const[simp]:
   set_fp_var x y (z with clock := k) = set_fp_var x y z with clock := k
Proof
  EVAL_TAC
QED

Theorem set_vars_const[simp]:
   (set_vars x y z).clock = z.clock ∧
   (set_vars x y z).compile_oracle = z.compile_oracle ∧
   (set_vars x y z).code = z.code ∧
   (set_vars x y z).code_buffer = z.code_buffer ∧
   (set_vars x y z).data_buffer = z.data_buffer ∧
   (set_vars x y z).compile = z.compile ∧
   (set_vars x y z).be = z.be ∧
   (set_vars x y z).ffi = z.ffi ∧
   (set_vars x y z).locals_size = z.locals_size ∧
   (set_vars x y z).stack_limit = z.stack_limit ∧
   (set_vars x y z).stack_max = z.stack_max ∧
   (set_vars x y z).stack_size = z.stack_size
Proof
  EVAL_TAC
QED

Theorem set_vars_with_const[simp]:
   set_vars x y (z with clock := k) = set_vars x y z with clock := k /\
   set_vars x y (z with permute := p) = set_vars x y z with permute := p
Proof
  EVAL_TAC
QED

Theorem mem_load_with_const[simp]:
   mem_load x (y with clock := k) = mem_load x y ∧
   mem_load x (y with code := c) = mem_load x y ∧
   mem_load x (y with compile_oracle := co) = mem_load x y ∧
   mem_load x (y with compile := cc) = mem_load x y
Proof
  EVAL_TAC
QED

Theorem mem_store_const_full:
   mem_store x y z = SOME a ⇒
   a.clock = z.clock ∧
   a.be = z.be ∧
   a.ffi = z.ffi ∧
   a.handler = z.handler ∧
   a.code = z.code ∧
   a.code_buffer = z.code_buffer ∧
   a.data_buffer = z.data_buffer ∧
   a.compile = z.compile ∧
   a.compile_oracle = z.compile_oracle ∧
   a.stack = z.stack ∧
   a.locals_size = z.locals_size ∧
   a.stack_limit = z.stack_limit ∧
   a.stack_max = z.stack_max ∧
   a.stack_size = z.stack_size
Proof
  EVAL_TAC >> srw_tac[][] >> srw_tac[][]
QED

Theorem mem_store_const:
   mem_store x y z = SOME a ⇒
   a.clock = z.clock ∧
   a.ffi = z.ffi
Proof
  metis_tac [mem_store_const_full]
QED

Theorem mem_store_with_const[simp]:
   mem_store x z (y with clock := k) = OPTION_MAP (λs. s with clock := k) (mem_store x z y)
Proof
  EVAL_TAC >> every_case_tac >> simp[]
QED

Theorem word_exp_with_const[simp]:
   ∀x y k c co cc.
  word_exp (x with clock := k) y = word_exp x y ∧
  word_exp (x with code := c) y = word_exp x y ∧
  word_exp (x with compile_oracle := co) y = word_exp x y ∧
  word_exp (x with compile := cc) y = word_exp x y
Proof
  recInduct word_exp_ind >>
  rw[word_exp_def] >>
  every_case_tac >> fs[]>>
  ntac 2 (pop_assum mp_tac)>>
  qpat_abbrev_tac`ls = MAP A B`>>
  qpat_abbrev_tac`ls' = MAP A B`>>
  `ls = ls'` by
    (unabbrev_all_tac>>fs[MAP_EQ_f]) >>
  rw[]
QED

Theorem assign_const_full:
   assign x y z = SOME a ⇒
   a.code = z.code ∧
   a.code_buffer = z.code_buffer ∧
   a.data_buffer = z.data_buffer ∧
   a.compile = z.compile ∧
   a.compile_oracle = z.compile_oracle ∧
   a.clock = z.clock ∧
   a.ffi = z.ffi ∧
   a.handler = z.handler ∧
   a.stack = z.stack ∧
   a.locals_size = z.locals_size ∧
   a.stack_limit = z.stack_limit ∧
   a.stack_max = z.stack_max ∧
   a.stack_size = z.stack_size
Proof
  EVAL_TAC >> every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> srw_tac[][]
QED

Theorem assign_const:
   assign x y z = SOME a ⇒
   a.clock = z.clock ∧
   a.ffi = z.ffi
Proof
  metis_tac [assign_const_full]
QED

Theorem assign_with_const[simp]:
   assign x y (z with clock := k) = OPTION_MAP (λs. s with clock := k) (assign x y z)
Proof
  EVAL_TAC >> every_case_tac >> EVAL_TAC >> full_simp_tac(srw_ss())[]
QED

Theorem inst_with_const[simp]:
   inst i (s with clock := k) = OPTION_MAP (λs. s with clock := k) (inst i s)
Proof
  rw[inst_def] >> every_case_tac >> full_simp_tac(srw_ss())[]
QED

Theorem inst_const_full:
   inst i s = SOME s' ⇒
   s'.code = s.code ∧
   s'.code_buffer = s.code_buffer ∧
   s'.data_buffer = s.data_buffer ∧
   s'.compile = s.compile ∧
   s'.compile_oracle = s.compile_oracle ∧
   s'.clock = s.clock ∧
   s'.ffi = s.ffi ∧
   s'.handler = s.handler ∧
   s'.stack = s.stack ∧
   s'.locals_size = s.locals_size ∧
   s'.stack_limit = s.stack_limit ∧
   s'.stack_max = s.stack_max ∧
   s'.stack_size = s.stack_size
Proof
  rw[inst_def, set_var_def,set_fp_var_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  imp_res_tac assign_const_full >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  imp_res_tac mem_store_const_full >> full_simp_tac(srw_ss())[] >> srw_tac[][]
QED

Theorem inst_const:
   inst i s = SOME s' ⇒
   s'.clock = s.clock ∧
   s'.ffi = s.ffi
Proof
  metis_tac [inst_const_full]
QED

Theorem jump_exc_const:
   jump_exc s = SOME (x,y) ⇒
   x.clock = s.clock ∧
   x.ffi = s.ffi
Proof
  EVAL_TAC >> every_case_tac >> EVAL_TAC >> srw_tac[][] >> srw_tac[][]
QED

Theorem jump_exc_with_const[simp]:
   jump_exc (s with clock := k) = OPTION_MAP (λ(s,t). (s with clock := k, t)) (jump_exc s)
Proof
  EVAL_TAC >> every_case_tac >> EVAL_TAC
QED

Theorem get_var_imm_with_const[simp]:
   get_var_imm x (y with clock := k) = get_var_imm x y
Proof
  Cases_on`x`>>EVAL_TAC
QED

Theorem dec_clock_const[simp]:
   (dec_clock s).be = s.be /\
   (dec_clock s).ffi = s.ffi /\
   (dec_clock s).code = s.code /\
   (dec_clock s).code_buffer = s.code_buffer /\
   (dec_clock s).data_buffer = s.data_buffer /\
   (dec_clock s).compile_oracle = s.compile_oracle ∧
   (dec_clock s).stack = s.stack ∧
   (dec_clock s).permute = s.permute ∧
   (dec_clock s).compile = s.compile ∧
   (dec_clock s).locals_size = s.locals_size ∧
   (dec_clock s).stack_limit = s.stack_limit ∧
   (dec_clock s).stack_max = s.stack_max ∧
   (dec_clock s).stack_size = s.stack_size
Proof
  EVAL_TAC
QED

(*code and gc_fun are unchanged across eval*)
Theorem pop_env_code_gc_fun_clock:
    pop_env r = SOME x ⇒
  r.code = x.code ∧
  r.code_buffer = x.code_buffer ∧
  r.data_buffer = x.data_buffer ∧
  r.gc_fun = x.gc_fun ∧
  r.clock = x.clock ∧
  r.be = x.be ∧
  r.mdomain = x.mdomain ∧
  r.compile = x.compile ∧
  r.compile_oracle = x.compile_oracle ∧
  r.stack_limit = x.stack_limit ∧
  r.stack_max = x.stack_max ∧
  r.stack_size = x.stack_size
Proof
  fs[pop_env_def]>>EVERY_CASE_TAC>>fs[state_component_equality]
QED
(* Standard add clock lemma for FBS *)

(* TODO: generated names *)
Theorem evaluate_add_clock:
   ∀p s r s'.
    evaluate (p,s) = (r,s') ∧ r ≠ SOME TimeOut ⇒
    evaluate (p,s with clock := s.clock + extra) = (r,s' with clock := s'.clock + extra)
Proof
  recInduct evaluate_ind >>
  srw_tac[][evaluate_def] >>
  TRY CASE_TAC >> full_simp_tac(srw_ss())[] >> rveq >> full_simp_tac(srw_ss())[] >> rveq >>
  TRY CASE_TAC >> full_simp_tac(srw_ss())[] >>
  TRY CASE_TAC >> full_simp_tac(srw_ss())[] >> rveq >> full_simp_tac(srw_ss())[] >> rveq >>
  TRY (
    rename1`find_code _ (add_ret_loc _ _)` >>
    Cases_on`get_vars args s`>>full_simp_tac(srw_ss())[]>>
    Cases_on`find_code dest (add_ret_loc (SOME x) x') s.code s.stack_size`>>full_simp_tac(srw_ss())[]>>
    PairCases_on`x''`>>PairCases_on`x`>>full_simp_tac(srw_ss())[]>>
    Cases_on`cut_env x1 s.locals`>>full_simp_tac(srw_ss())[]>>
    qpat_x_assum`A=(r,s')` mp_tac>>
    rpt(IF_CASES_TAC>>full_simp_tac(srw_ss())[])>>
    full_case_tac>>full_simp_tac(srw_ss())[]>>Cases_on`q`>>TRY(Cases_on `x''`)>>
    fsrw_tac[ARITH_ss][dec_clock_def]>>
    rev_full_simp_tac(srw_ss()++ARITH_ss)[]>>
    every_case_tac >> full_simp_tac(srw_ss())[] >> rveq >> full_simp_tac(srw_ss())[] >>
    rev_full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[] >>
    imp_res_tac pop_env_const >> full_simp_tac(srw_ss())[] >>
    rev_full_simp_tac(srw_ss())[] >> rveq >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    full_simp_tac(srw_ss())[])>>
  TRY (
    rename1`find_code _ (add_ret_loc _ _)` >>
    Cases_on`get_vars args s`>>full_simp_tac(srw_ss())[]>>
    Cases_on`find_code dest (add_ret_loc ret x') s.code s.stack_size`>>full_simp_tac(srw_ss())[]>>
    Cases_on`ret`>>full_simp_tac(srw_ss())[]>>
    PairCases_on`x''`>>full_simp_tac(srw_ss())[]>>
    PairCases_on`x'''`>>full_simp_tac(srw_ss())[]>>
    Cases_on`cut_env x'''1 s.locals`>>full_simp_tac(srw_ss())[]>>
    qpat_x_assum`A=(r,s')` mp_tac>>
    rpt(IF_CASES_TAC>>full_simp_tac(srw_ss())[])>>
    Cases_on`evaluate (x''1,call_env x''0 x''2 (push_env x'' (SOME x) (dec_clock s)))`>>Cases_on`q`>>TRY(Cases_on`x'''`)>>
    fsrw_tac[ARITH_ss][dec_clock_def]>>
    rev_full_simp_tac(srw_ss()++ARITH_ss)[]>>srw_tac[][]>>
    every_case_tac >> full_simp_tac(srw_ss())[] >> rveq >> full_simp_tac(srw_ss())[] >>
    rev_full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[] >>
    imp_res_tac pop_env_const >> full_simp_tac(srw_ss())[] >>
    rev_full_simp_tac(srw_ss())[] >> rveq >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    full_simp_tac(srw_ss())[])>>
  TRY (
    rename1`alloc _ _ _ = _` >>
    fs[alloc_def,gc_def,LET_THM]>> every_case_tac >>
    fs[call_env_def,push_env_def,LET_THM,env_to_list_def
      ,set_store_def,state_component_equality,flush_state_def]>>
    imp_res_tac pop_env_code_gc_fun_clock>>fs[]) >>
  full_simp_tac(srw_ss())[LET_THM,dec_clock_def] >>
  TRY pairarg_tac >> full_simp_tac(srw_ss())[] >> rveq >> full_simp_tac(srw_ss())[] >>
  imp_res_tac alloc_const >> full_simp_tac(srw_ss())[] >>
  imp_res_tac inst_const >> full_simp_tac(srw_ss())[] >>
  TRY(Cases_on`mem_store c x s`)>>
  imp_res_tac mem_store_const >> fs[]>>
  simp[state_component_equality,dec_clock_def] >>
  full_simp_tac(srw_ss())[ffiTheory.call_FFI_def,LET_THM] >>rfs[]>>
  every_case_tac >> full_simp_tac(srw_ss())[] >> rveq >> full_simp_tac(srw_ss())[] >> rveq >>
  simp[state_component_equality,dec_clock_def] >>
  imp_res_tac jump_exc_const >> full_simp_tac(srw_ss())[] >>
  rev_full_simp_tac(srw_ss())[] >>fsrw_tac[ARITH_ss][] >>
  rev_full_simp_tac(srw_ss()++ARITH_ss)[]>>rveq>>full_simp_tac(srw_ss())[]>>
  fs[call_env_def,flush_state_def]>>metis_tac[]
QED

val tac = EVERY_CASE_TAC>>full_simp_tac(srw_ss())[state_component_equality]
val tac2 =
  strip_tac>>rveq>>full_simp_tac(srw_ss())[]>>
  imp_res_tac evaluate_clock>>full_simp_tac(srw_ss())[]>>
  `¬ (s.clock ≤ r.clock)` by DECIDE_TAC>>full_simp_tac(srw_ss())[]>>
  `s.clock -1 -r.clock = s.clock - r.clock-1` by DECIDE_TAC>>full_simp_tac(srw_ss())[]

(* This lemma is interesting in wordLang because of the use of MustTerminate

   To remove MustTerminate, we need to inject an exact number of clock ticks
   corresponding to the ticks used in the MustTerminate block

   The number of clock ticks is fixed for any program, and can be characterized by st.clock - rst.clock *)

Theorem evaluate_dec_clock:
   ∀prog st res rst.
  evaluate(prog,st) = (res,rst) ⇒
  evaluate(prog,st with clock:=st.clock-rst.clock) = (res,rst with clock:=0)
Proof
  recInduct evaluate_ind >>srw_tac[][evaluate_def]>>full_simp_tac(srw_ss())[call_env_def,dec_clock_def]
  >- (tac>>imp_res_tac alloc_const>>full_simp_tac(srw_ss())[])
  >- tac
  >- (TOP_CASE_TAC>>full_simp_tac(srw_ss())[]>> assume_tac inst_const>>tac)
  >- tac
  >- tac
  >- tac
  >- tac
  >- (tac>>imp_res_tac mem_store_const>>full_simp_tac(srw_ss())[])
  >- DECIDE_TAC
  >- `F`by DECIDE_TAC
  >- (full_simp_tac(srw_ss())[state_component_equality]>>DECIDE_TAC)
  >- (srw_tac[][]>>full_simp_tac(srw_ss())[state_component_equality,LET_THM])
  >-
    (qpat_x_assum`A=(res,rst)` mp_tac>>simp[]>>pairarg_tac>>full_simp_tac(srw_ss())[]>>
    IF_CASES_TAC>>full_simp_tac(srw_ss())[]
    >-
      (strip_tac>>full_simp_tac(srw_ss())[]>>
      imp_res_tac evaluate_clock>>full_simp_tac(srw_ss())[]>>
      imp_res_tac evaluate_add_clock>>full_simp_tac(srw_ss())[]>>
      first_x_assum(qspec_then`s1'.clock - rst.clock` mp_tac)>>simp[])
    >>
      strip_tac>>full_simp_tac(srw_ss())[])
  >- tac
  >- (tac>>imp_res_tac jump_exc_const>>full_simp_tac(srw_ss())[])
  >- tac
  >-
     (tac>>fs[]>>pairarg_tac>>fs[]>>
     every_case_tac>>fs[state_component_equality])
  >- tac
  >- tac
  >- (tac>>fs[cut_env_def]>> rveq >> fs [])
  >>
    qpat_x_assum`A=(res,rst)` mp_tac>>
    ntac 6 (TOP_CASE_TAC>>full_simp_tac(srw_ss())[])
    >-
      (ntac 3 (TOP_CASE_TAC>>full_simp_tac(srw_ss())[state_component_equality])>>
      TOP_CASE_TAC>>full_simp_tac(srw_ss())[]>>
      tac2>>
      first_x_assum(qspec_then`r` assume_tac)>>rev_full_simp_tac(srw_ss())[])
    >>
      ntac 7 (TOP_CASE_TAC>>full_simp_tac(srw_ss())[])>-
        (strip_tac>>rveq>>full_simp_tac(srw_ss())[flush_state_def])>>
      ntac 2 (TOP_CASE_TAC>>full_simp_tac(srw_ss())[])>-
        tac2>>
      TOP_CASE_TAC
      >-
        (TOP_CASE_TAC>-tac2>>
        TOP_CASE_TAC>-tac2>>
        reverse TOP_CASE_TAC>-
          (tac2>>imp_res_tac pop_env_const>>
          rveq>>full_simp_tac(srw_ss())[])>>
        strip_tac>>full_simp_tac(srw_ss())[]>>
        rev_full_simp_tac(srw_ss())[]>>
        imp_res_tac evaluate_clock>>full_simp_tac(srw_ss())[]>>
        imp_res_tac evaluate_add_clock>>full_simp_tac(srw_ss())[]>>
        imp_res_tac pop_env_const>>rveq>>full_simp_tac(srw_ss())[]>>
        first_x_assum(qspec_then`r.clock-rst.clock` kall_tac)>>
        first_x_assum(qspec_then`r.clock-rst.clock` mp_tac)>>
        simp[])
      >-
        (TOP_CASE_TAC>-tac2>>
        ntac 3 (TOP_CASE_TAC>>full_simp_tac(srw_ss())[])>>
        TOP_CASE_TAC>-tac2>>
        reverse TOP_CASE_TAC>- tac2>>
        strip_tac>>full_simp_tac(srw_ss())[]>>
        rev_full_simp_tac(srw_ss())[]>>
        imp_res_tac evaluate_clock>>full_simp_tac(srw_ss())[]>>
        imp_res_tac evaluate_add_clock>>full_simp_tac(srw_ss())[]>>
        imp_res_tac pop_env_const>>rveq>>full_simp_tac(srw_ss())[]>>
        first_x_assum(qspec_then`r.clock-rst.clock` kall_tac)>>
        first_x_assum(qspec_then`r.clock-rst.clock` mp_tac)>>
        simp[])
      >>
        tac2
QED

(* IO and clock monotonicity *)

Theorem evaluate_io_events_mono:
   !exps s1 res s2.
    evaluate (exps,s1) = (res, s2)
    ⇒
    s1.ffi.io_events ≼ s2.ffi.io_events
Proof
  recInduct evaluate_ind >> ntac 5 strip_tac >>
  rpt conj_tac >>
  rpt gen_tac >>
  full_simp_tac(srw_ss())[evaluate_def] >>
  rpt gen_tac >>
  rpt (pop_assum mp_tac) >>
  rpt (TOP_CASE_TAC >> full_simp_tac(srw_ss())[]) >>
  rpt (disch_then strip_assume_tac ORELSE gen_tac) >> full_simp_tac(srw_ss())[] >>
  rveq >> full_simp_tac(srw_ss())[] >>
  imp_res_tac alloc_const >> full_simp_tac(srw_ss())[] >>
  imp_res_tac inst_const >> full_simp_tac(srw_ss())[] >>
  imp_res_tac mem_store_const >> full_simp_tac(srw_ss())[] >>
  imp_res_tac jump_exc_const >> full_simp_tac(srw_ss())[] >>
  imp_res_tac pop_env_const >> full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[LET_THM] >>
  TRY (pairarg_tac >> full_simp_tac(srw_ss())[] >> every_case_tac >> full_simp_tac(srw_ss())[]) >>
  rveq >> full_simp_tac(srw_ss())[] >>
  TRY (CHANGED_TAC(full_simp_tac(srw_ss())[ffiTheory.call_FFI_def]) >>
       every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] ) >>
  metis_tac[IS_PREFIX_TRANS]
QED

Theorem with_clock_ffi:
   (s with clock := y).ffi = s.ffi
Proof
  EVAL_TAC
QED

Theorem evaluate_add_clock_io_events_mono:
   ∀exps s extra.
    (SND(evaluate(exps,s))).ffi.io_events ≼
    (SND(evaluate(exps,s with clock := s.clock + extra))).ffi.io_events
Proof
  recInduct evaluate_ind >>
  srw_tac[][evaluate_def,LET_THM] >>
  TRY (
    rename1`find_code` >>
    Cases_on`get_vars args s`>>full_simp_tac(srw_ss())[]>>
    IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
    Cases_on`ret`>>full_simp_tac(srw_ss())[] >- (
      every_case_tac >> full_simp_tac(srw_ss())[] >> rveq >>
      imp_res_tac evaluate_io_events_mono >> full_simp_tac(srw_ss())[] >>
      imp_res_tac evaluate_add_clock >> full_simp_tac(srw_ss())[] >>
      fsrw_tac[ARITH_ss][dec_clock_def] >>
      rpt(first_x_assum(qspec_then`extra`mp_tac)>>simp[])) >>
    split_pair_case_tac >> full_simp_tac(srw_ss())[] >>
    qpat_abbrev_tac`opt = find_code _ _ _ _` >>
    Cases_on`opt`>>full_simp_tac(srw_ss())[markerTheory.Abbrev_def]>>
    split_pair_case_tac >> full_simp_tac(srw_ss())[] >>
    Cases_on`cut_env names s.locals`>>full_simp_tac(srw_ss())[]>>
    IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
    CASE_TAC >> full_simp_tac(srw_ss())[] >>
    CASE_TAC >> full_simp_tac(srw_ss())[] >>
    CASE_TAC >> full_simp_tac(srw_ss())[] >>
    CASE_TAC >> full_simp_tac(srw_ss())[] >> rveq >>
    IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
    TRY IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
    TRY (
      split_pair_case_tac >> full_simp_tac(srw_ss())[] >>
      split_pair_case_tac >> full_simp_tac(srw_ss())[] >>
      imp_res_tac evaluate_add_clock >> full_simp_tac(srw_ss())[] >>
      fsrw_tac[ARITH_ss][dec_clock_def] >>
      qpat_x_assum`z ≠ SOME TimeOut ⇒ _`mp_tac >>
      qmatch_assum_rename_tac`z ≠ SOME TimeOut ⇒ _` >>
      Cases_on`z=SOME TimeOut`>>full_simp_tac(srw_ss())[]>-(
        strip_tac >>
        every_case_tac >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
        rpt(first_x_assum(qspec_then`extra`mp_tac)>>simp[]) >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
        imp_res_tac evaluate_io_events_mono >> full_simp_tac(srw_ss())[] >>
        imp_res_tac pop_env_const >> rveq >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
        metis_tac[evaluate_io_events_mono,set_var_const,IS_PREFIX_TRANS,SND,PAIR,set_var_with_const,with_clock_ffi]) >>
      rpt(first_x_assum(qspec_then`extra`mp_tac)>>simp[]) >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
      every_case_tac >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
      rpt(first_x_assum(qspec_then`extra`mp_tac)>>simp[]) >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
      imp_res_tac evaluate_io_events_mono >> full_simp_tac(srw_ss())[] >>
      imp_res_tac pop_env_const >> rveq >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
      metis_tac[evaluate_io_events_mono,set_var_const,IS_PREFIX_TRANS,SND,PAIR,set_var_with_const,with_clock_ffi]) >>
    TRY(
      split_pair_case_tac >> full_simp_tac(srw_ss())[] >>
      imp_res_tac evaluate_add_clock >> full_simp_tac(srw_ss())[] >>
      fsrw_tac[ARITH_ss][dec_clock_def] >>
      rpt(first_x_assum(qspec_then`extra`mp_tac)>>simp[]) >> srw_tac[][] >>
      every_case_tac >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
      rpt(first_x_assum(qspec_then`extra`mp_tac)>>simp[]) >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
      imp_res_tac evaluate_io_events_mono >> full_simp_tac(srw_ss())[] >>
      imp_res_tac pop_env_const >> rveq >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
      metis_tac[evaluate_io_events_mono,set_var_const,IS_PREFIX_TRANS,SND,PAIR,set_var_with_const,with_clock_ffi]) >>
    every_case_tac >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >> rveq >> full_simp_tac(srw_ss())[] >>
    rpt(first_x_assum(qspec_then`extra`mp_tac)>>simp[]) >> srw_tac[][] >>
    imp_res_tac evaluate_io_events_mono >> full_simp_tac(srw_ss())[] >>
    imp_res_tac pop_env_const >> rveq >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
    metis_tac[evaluate_io_events_mono,set_var_const,IS_PREFIX_TRANS,SND,PAIR,set_var_with_const,with_clock_ffi]) >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  rpt (pairarg_tac >> full_simp_tac(srw_ss())[]) >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  imp_res_tac evaluate_add_clock >> full_simp_tac(srw_ss())[] >>
  rveq >> full_simp_tac(srw_ss())[] >>
  imp_res_tac evaluate_io_events_mono >> rev_full_simp_tac(srw_ss())[] >>
  metis_tac[evaluate_io_events_mono,IS_PREFIX_TRANS,SND,PAIR]
QED

Theorem alloc_code_gc_fun_const:
    alloc x names s = (res,t) ⇒
  t.code = s.code /\
  t.code_buffer = s.code_buffer /\
  t.data_buffer = s.data_buffer /\
  t.gc_fun = s.gc_fun /\
  t.mdomain = s.mdomain /\
  t.be = s.be ∧
  t.compile = s.compile ∧
  t.compile_oracle = s.compile_oracle ∧
  t.stack_limit = s.stack_limit ∧
  t.stack_size = s.stack_size
Proof
  fs[alloc_def,gc_def,LET_THM]>>EVERY_CASE_TAC>>
  fs[call_env_def,push_env_def,LET_THM,env_to_list_def
    ,set_store_def,state_component_equality,flush_state_def]>>
  imp_res_tac pop_env_code_gc_fun_clock>>fs[]
QED

val inst_code_gc_fun_const = Q.prove(`
  inst i s = SOME t ⇒
  s.code = t.code /\ s.gc_fun = t.gc_fun /\ s.mdomain = t.mdomain /\ s.be = t.be ∧ s.compile = t.compile ∧ s.stack_size = t.stack_size ∧ s.stack_limit = t.stack_limit`,
  Cases_on`i`>>fs[inst_def,assign_def]>>EVERY_CASE_TAC>>fs[set_var_def,state_component_equality,mem_store_def,set_fp_var_def]);

Theorem evaluate_consts:
   !xs s1 vs s2.
     evaluate (xs,s1) = (vs,s2) ==>
     s1.gc_fun = s2.gc_fun /\
     s1.mdomain = s2.mdomain /\
     s1.be = s2.be ∧
     s1.compile = s2.compile ∧
(*     s1.stack_size = s2.stack_size ∧*)
     s1.stack_limit = s2.stack_limit
Proof
  recInduct evaluate_ind
  \\ fs[evaluate_def,LET_THM]
  \\ reverse (rpt conj_tac>>rpt gen_tac>>rpt DISCH_TAC)
  >- (rename1 `bad_dest_args _ _`
     \\ pop_assum mp_tac
     \\ ntac 6 (TOP_CASE_TAC>>fs[])
     >- (rpt(TOP_CASE_TAC
        \\ fs[call_env_def,flush_state_def,state_component_equality,dec_clock_def]))
     \\ ntac 6 (TOP_CASE_TAC>>fs[])
     \\ Cases_on`handler`>>TRY(PairCases_on`x''`)
     \\ fs[state_component_equality,call_env_def,flush_state_def
          ,push_env_def,LET_THM,env_to_list_def,dec_clock_def]
     \\ TOP_CASE_TAC>>fs[state_component_equality]
     \\ ntac 6 (TOP_CASE_TAC>>fs[set_var_def])
     \\ imp_res_tac pop_env_code_gc_fun_clock \\ fs[])
  \\ fs[jump_exc_def]
  \\ EVERY_CASE_TAC
  \\ fs[set_vars_def,state_component_equality,set_var_def,flush_state_def
       ,set_store_def,mem_store_def,call_env_def,flush_state_def,dec_clock_def]
  \\ TRY(pairarg_tac \\ fs[])
  \\ EVERY_CASE_TAC
  \\ fs[set_vars_def,state_component_equality
       ,set_var_def,set_store_def,mem_store_def
       ,call_env_def,flush_state_def,dec_clock_def,flush_state_def]
  \\ metis_tac[alloc_code_gc_fun_const,inst_code_gc_fun_const
              ,state_component_equality]
QED

(* TODO: monotonicity *)

(* -- *)

Theorem get_vars_length_lemma:
   !ls s y. get_vars ls s = SOME y ==>
           LENGTH y = LENGTH ls
Proof
  Induct>>full_simp_tac(srw_ss())[get_vars_def]>>
  Cases_on`get_var h s`>>full_simp_tac(srw_ss())[]>>
  Cases_on`get_vars ls s`>>full_simp_tac(srw_ss())[]>>
  metis_tac[LENGTH]
QED

(*--Stack Swap Lemma--*)

(*Stacks look the same except for the keys (e.g. recoloured and in order)*)
val s_frame_val_eq_def = Define`
  (s_frame_val_eq (StackFrame n ls NONE) (StackFrame n' ls' NONE)
     <=> MAP SND ls = MAP SND ls' /\ n=n') /\
  (s_frame_val_eq (StackFrame n ls (SOME y)) (StackFrame n' ls' (SOME y'))
     <=> MAP SND ls = MAP SND ls' /\ y=y' /\ n=n') /\
  (s_frame_val_eq _ _ = F)`

val s_val_eq_def = Define`
  (s_val_eq [] [] = T) /\
  (s_val_eq (x::xs) (y::ys) = (s_val_eq xs ys /\
                                    s_frame_val_eq x y)) /\
  (s_val_eq _ _ = F)`

(*Stacks look the same except for the values (e.g. result of gc)*)
val s_frame_key_eq_def = Define`
  (s_frame_key_eq (StackFrame n ls NONE) (StackFrame n' ls' NONE)
     <=> MAP FST ls = MAP FST ls' /\ n=n') /\
  (s_frame_key_eq (StackFrame n ls (SOME y)) (StackFrame n' ls' (SOME y'))
     <=> MAP FST ls = MAP FST ls' /\ y=y' /\ n=n') /\
  (s_frame_key_eq _ _ = F)`

val s_key_eq_def = Define`
  (s_key_eq [] [] = T) /\
  (s_key_eq (x::xs) (y::ys) = (s_key_eq xs ys /\
                                    s_frame_key_eq x y)) /\
  (s_key_eq _ _ = F)`

(*Reflexive*)
Theorem s_key_eq_refl:
   !ls .s_key_eq ls ls = T
Proof
   Induct >> srw_tac[][s_key_eq_def]>>
   Cases_on`h`>> Cases_on`o'`>>Cases_on`o0`>>srw_tac[][s_frame_key_eq_def]
QED

Theorem s_val_eq_refl:
   !ls.s_val_eq ls ls = T
Proof
  Induct >> srw_tac[][s_val_eq_def]>>
  Cases_on`h`>> Cases_on`o'`>>Cases_on`o0`>>srw_tac[][s_frame_val_eq_def]
QED

(*transitive*)
val s_frame_key_eq_trans = Q.prove(
  `!a b c. s_frame_key_eq a b /\ s_frame_key_eq b c ==>
            s_frame_key_eq a c`,
  Cases_on`a`>>Cases_on`b`>>Cases_on`c`>>
  Cases_on`o'`>>Cases_on`o''`>>Cases_on`o'''`>>
  Cases_on`o0`>>Cases_on`o0'`>>Cases_on`o0''`>>
  full_simp_tac(srw_ss())[s_frame_key_eq_def]);

Theorem s_key_eq_trans:
   !a b c. s_key_eq a b /\ s_key_eq b c ==>
            s_key_eq a c
Proof
  Induct>>
  Cases_on`b`>>Cases_on`c`>>full_simp_tac(srw_ss())[s_key_eq_def]>>
  srw_tac[][]>>metis_tac[s_frame_key_eq_trans]
QED

val s_frame_val_eq_trans = Q.prove(
  `!a b c. s_frame_val_eq a b /\ s_frame_val_eq b c ==>
            s_frame_val_eq a c`,
  Cases_on`a`>>Cases_on`b`>>Cases_on`c`>>
  Cases_on`o'`>>Cases_on`o''`>>Cases_on`o'''`>>
  Cases_on`o0`>>Cases_on`o0'`>>Cases_on`o0''`>>
  full_simp_tac(srw_ss())[s_frame_val_eq_def]);

val s_val_eq_trans = Q.prove(
  `!a b c. s_val_eq a b /\ s_val_eq b c ==>
            s_val_eq a c`,
  Induct>>
  Cases_on`b`>>Cases_on`c`>>full_simp_tac(srw_ss())[s_val_eq_def]>>
  srw_tac[][]>>metis_tac[s_frame_val_eq_trans]);

(*Symmetric*)
val s_frame_key_eq_sym = Q.prove(
  `!a b. s_frame_key_eq a b <=> s_frame_key_eq b a`,
  Cases>>Cases>>Cases_on`o'`>>Cases_on`o''`>>
  Cases_on`o0`>>Cases_on`o0'`>>full_simp_tac(srw_ss())[s_frame_key_eq_def,EQ_SYM_EQ]);

Theorem s_key_eq_sym:
   !a b. s_key_eq a b <=> s_key_eq b a
Proof
  Induct>> Cases_on`b`>>full_simp_tac(srw_ss())[s_key_eq_def]>>
  strip_tac>>metis_tac[s_frame_key_eq_sym]
QED

val s_frame_val_eq_sym = Q.prove(
   `!a b. s_frame_val_eq a b <=> s_frame_val_eq b a`,
  Cases>>Cases>>Cases_on`o'`>>Cases_on`o''`>>
  Cases_on`o0`>>Cases_on`o0'`>>full_simp_tac(srw_ss())[s_frame_val_eq_def,EQ_SYM_EQ]);

Theorem s_val_eq_sym:
   !a b. s_val_eq a b <=> s_val_eq b a
Proof
  Induct>> Cases_on`b`>>full_simp_tac(srw_ss())[s_val_eq_def]>>
  strip_tac>>metis_tac[s_frame_val_eq_sym]
QED

val s_frame_val_and_key_eq = Q.prove(
  `!s t. s_frame_val_eq s t /\ s_frame_key_eq s t ==> s = t`,
  Cases>>Cases>>Cases_on`o'`>>Cases_on`o''`>>Cases_on`o0`>>Cases_on`o0'`>>
  full_simp_tac(srw_ss())[s_frame_val_eq_def,s_frame_key_eq_def,LIST_EQ_MAP_PAIR]);

Theorem s_val_and_key_eq:
   !s t. s_val_eq s t /\ s_key_eq s t ==> s =t
Proof
  Induct>-
    (Cases>>full_simp_tac(srw_ss())[s_val_eq_def])>>
  srw_tac[][]>>
  Cases_on`t`>>full_simp_tac(srw_ss())[s_val_eq_def,s_key_eq_def,s_frame_val_and_key_eq]
QED

val dec_stack_stack_key_eq = Q.prove(
  `!wl st st'. dec_stack wl st = SOME st' ==> s_key_eq st st'`,
  ho_match_mp_tac dec_stack_ind>>srw_tac[][dec_stack_def]>>
  full_simp_tac(srw_ss())[s_key_eq_def]>>
  every_case_tac>>full_simp_tac(srw_ss())[]>>srw_tac[][]>>full_simp_tac(srw_ss())[dec_stack_def]>>srw_tac[][]>>
  Cases_on `handler`>>
  full_simp_tac(srw_ss())[s_key_eq_def,s_frame_key_eq_def,MAP_ZIP,NOT_LESS]);

(*gc preserves the stack_key relation*)
Theorem gc_s_key_eq:
   !s x. gc s = SOME x ==> s_key_eq s.stack x.stack
Proof
  srw_tac[][gc_def] >>full_simp_tac(srw_ss())[LET_THM]>>every_case_tac>>full_simp_tac(srw_ss())[]>>
  IMP_RES_TAC dec_stack_stack_key_eq>>
  full_simp_tac(srw_ss())[state_component_equality]>>rev_full_simp_tac(srw_ss())[]
QED

val s_val_eq_enc_stack = Q.prove(
  `!st st'. s_val_eq st st' ==> enc_stack st = enc_stack st'`,
  Induct>>Cases_on`st'`>>full_simp_tac(srw_ss())[s_val_eq_def]>>
  Cases_on`h`>>Cases_on`h'`>>Cases_on`o''`>>Cases_on`o'`>>Cases_on`o0'`>>Cases_on`o0`>>
  full_simp_tac(srw_ss())[s_frame_val_eq_def,enc_stack_def]);

val s_val_eq_dec_stack = Q.prove(
  `!q st st' x. s_val_eq st st' /\ dec_stack q st = SOME x ==>
    ?y. dec_stack q st' = SOME y /\ s_val_eq x y`,
   ho_match_mp_tac dec_stack_ind >> srw_tac[][] >>
   Cases_on`st'`>>full_simp_tac(srw_ss())[s_val_eq_def,s_val_eq_refl]>>
   Cases_on`h`>>full_simp_tac(srw_ss())[dec_stack_def]>>
   pop_assum mp_tac>>CASE_TAC >>
   first_x_assum(qspecl_then [`t`,`x'`] assume_tac)>> rev_full_simp_tac(srw_ss())[]>>
   strip_tac>>pop_assum (SUBST1_TAC o SYM)>>
   full_simp_tac(srw_ss())[s_frame_val_eq_def,s_val_eq_def]>>
   `LENGTH l' = LENGTH l` by
    (Cases_on `handler` \\ Cases_on `o'` \\ Cases_on `o0` \\ full_simp_tac(srw_ss())[s_frame_val_eq_def]
     \\ metis_tac[LENGTH_MAP]) \\ full_simp_tac(srw_ss())[NOT_LESS]
   \\ Cases_on `handler` \\ Cases_on `o'` \\ Cases_on `o0` \\ full_simp_tac(srw_ss())[s_frame_val_eq_def,s_val_eq_def]
   \\ full_simp_tac(srw_ss())[MAP_ZIP,LENGTH_TAKE]);

(*gc succeeds on all stacks related by stack_val and there are relations
  in the result*)
Theorem gc_s_val_eq:
   !s x st y. s_val_eq s.stack st /\
             gc s = SOME y ==>
      ?z. gc (s with stack := st) = SOME (y with stack := z) /\
          s_val_eq y.stack z /\ s_key_eq z st
Proof
  srw_tac[][gc_def]>>full_simp_tac(srw_ss())[LET_THM]>>
  SIMP_TAC std_ss [markerTheory.Abbrev_def]>>
  IMP_RES_TAC s_val_eq_enc_stack>>full_simp_tac(srw_ss())[]>>
  qpat_x_assum `x = SOME y` mp_tac>>
  ntac 4 CASE_TAC>>
  IMP_RES_TAC s_val_eq_dec_stack>> full_simp_tac(srw_ss())[]>>
  strip_tac>>full_simp_tac(srw_ss())[]>>
  IMP_RES_TAC dec_stack_stack_key_eq>>
  IMP_RES_TAC s_key_eq_sym>>
  Q.EXISTS_TAC`y'`>>full_simp_tac(srw_ss())[state_component_equality]>>rev_full_simp_tac(srw_ss())[]
QED

(*Slightly more general theorem allows the unused locals to be differnt*)
Theorem gc_s_val_eq_word_state:
   !s tlocs tstack y.
          s_val_eq s.stack tstack /\
          gc s = SOME y ==>
    ?zlocs zstack.
          gc (s with <|stack:=tstack;locals:=tlocs|>) =
          SOME (y with <|stack:=zstack;locals:=zlocs|>) /\
          s_val_eq y.stack zstack /\ s_key_eq zstack tstack
Proof
  srw_tac[][gc_def]>>full_simp_tac(srw_ss())[LET_THM]>>
  SIMP_TAC std_ss [markerTheory.Abbrev_def]>>
  IMP_RES_TAC s_val_eq_enc_stack>>full_simp_tac(srw_ss())[]>>
  qpat_x_assum `x = SOME y` mp_tac>>
  ntac 4 CASE_TAC>>
  IMP_RES_TAC s_val_eq_dec_stack>> full_simp_tac(srw_ss())[]>>
  strip_tac>>full_simp_tac(srw_ss())[]>>
  IMP_RES_TAC dec_stack_stack_key_eq>>
  IMP_RES_TAC s_key_eq_sym>>
  Q.EXISTS_TAC`tlocs`>>
  Q.EXISTS_TAC`y'`>>
  full_simp_tac(srw_ss())[state_component_equality]>>rev_full_simp_tac(srw_ss())[]
QED

(*Most generalised gc_s_val_eq*)
Theorem gc_s_val_eq_gen:
   !s t s'.
  s.gc_fun = t.gc_fun ∧
  s.memory = t.memory ∧
  s.mdomain = t.mdomain ∧
  s.store = t.store ∧
  s_val_eq s.stack t.stack ∧
  s.stack_size = t.stack_size /\
  s.stack_max = t.stack_max /\
  s.stack_limit = t.stack_limit /\
  gc s = SOME s' ⇒
  ?t'.
  gc t = SOME t' ∧
  s_val_eq s'.stack t'.stack ∧
  s_key_eq t.stack t'.stack ∧
  t'.memory = s'.memory ∧
  t'.store = s'.store /\
  t'.stack_size = s'.stack_size /\
  t'.stack_max = s'.stack_max /\
  t'.stack_limit = s'.stack_limit
Proof
  srw_tac[][]>>
  full_simp_tac(srw_ss())[gc_def,LET_THM]>>
  IMP_RES_TAC s_val_eq_enc_stack>>
  every_case_tac>>rev_full_simp_tac(srw_ss())[]>>
  IMP_RES_TAC s_val_eq_dec_stack>>full_simp_tac(srw_ss())[]>>
  qpat_x_assum`A=s'` (SUBST_ALL_TAC o SYM)>>
  IMP_RES_TAC dec_stack_stack_key_eq>>full_simp_tac(srw_ss())[]>>
  metis_tac[s_val_eq_sym]
QED

(*pushing and popping maintain the stack_key relation*)
Theorem push_env_pop_env_s_key_eq:
   ∀s t x b. s_key_eq (push_env x b s).stack t.stack ⇒
       ∃n l ls opt.
              t.stack = (StackFrame n l opt)::ls ∧
              ∃y. (pop_env t = SOME y ∧
                   y.locals = fromAList l ∧
                   domain x = domain y.locals ∧
                   s_key_eq s.stack y.stack)
Proof
  srw_tac[][]>>Cases_on`b`>>TRY(PairCases_on`x'`)>>full_simp_tac(srw_ss())[push_env_def]>>
  full_simp_tac(srw_ss())[LET_THM,env_to_list_def]>>Cases_on`t.stack`>>
  full_simp_tac(srw_ss())[s_key_eq_def,pop_env_def]>>BasicProvers.EVERY_CASE_TAC>>
  full_simp_tac(srw_ss())[domain_fromAList,s_frame_key_eq_def]>>
  qpat_x_assum `A = MAP FST l` (SUBST1_TAC o SYM)>>
  full_simp_tac(srw_ss())[EXTENSION,mem_list_rearrange,MEM_MAP,QSORT_MEM,MEM_toAList
    ,EXISTS_PROD,domain_lookup]
QED

val get_vars_stack_swap = Q.prove(
  `!l s t. s.locals = t.locals ==>
    get_vars l s = get_vars l t`,
  Induct>>full_simp_tac(srw_ss())[get_vars_def,get_var_def]>>
  srw_tac[][]>> every_case_tac>>
  metis_tac[NOT_NONE_SOME,SOME_11]);

val get_vars_stack_swap_simp = Q.prove(
  `!args. get_vars args (s with stack := xs) = get_vars args s`,
  `(s with stack:=xs).locals = s.locals` by full_simp_tac(srw_ss())[]>>
  metis_tac[get_vars_stack_swap]);

Theorem s_val_eq_length:
   !s t. s_val_eq s t ==> LENGTH s = LENGTH t
Proof
  Induct>>Cases>>full_simp_tac(srw_ss())[s_val_eq_def,LENGTH]>>
  Cases>>full_simp_tac(srw_ss())[s_val_eq_def]
QED

Theorem s_key_eq_length:
   !s t. s_key_eq s t ==> LENGTH s = LENGTH t
Proof
  Induct>>Cases>>full_simp_tac(srw_ss())[s_key_eq_def,LENGTH]>>
  Cases>>full_simp_tac(srw_ss())[s_key_eq_def]
QED

val s_val_eq_APPEND = Q.prove(
  `!s t x y. (s_val_eq s t /\ s_val_eq x y)==> s_val_eq (s++x) (t++y)`,
  ho_match_mp_tac (fetch "-" "s_val_eq_ind")>>
  srw_tac[][]>>full_simp_tac(srw_ss())[s_val_eq_def]);

val s_val_eq_REVERSE = Q.prove(
  `!s t. s_val_eq s t ==> s_val_eq (REVERSE s) (REVERSE t)`,
  ho_match_mp_tac (fetch "-" "s_val_eq_ind")>>
  srw_tac[][]>>full_simp_tac(srw_ss())[s_val_eq_def,s_val_eq_APPEND]);

val s_val_eq_TAKE = Q.prove(
  `!s t n. s_val_eq s t ==> s_val_eq (TAKE n s) (TAKE n t)`,
  ho_match_mp_tac (fetch "-" "s_val_eq_ind")>>rw[]>>
  Cases_on`n`>>fs[s_val_eq_def]);

val s_val_eq_LASTN = Q.prove(
  `!s t n. s_val_eq s t
    ==> s_val_eq (LASTN n s) (LASTN n t)`,
  ho_match_mp_tac (fetch "-" "s_val_eq_ind")>>
  srw_tac[][LASTN_def]>>full_simp_tac(srw_ss())[s_val_eq_def]>>
  `s_val_eq [x] [y]` by full_simp_tac(srw_ss())[s_val_eq_def]>>
  `s_val_eq (REVERSE s ++ [x]) (REVERSE t ++[y])` by
    full_simp_tac(srw_ss())[s_val_eq_APPEND,s_val_eq_REVERSE]>>
  IMP_RES_TAC s_val_eq_TAKE>>
  metis_tac[s_val_eq_REVERSE]);

val s_key_eq_APPEND = Q.prove(
  `!s t x y. (s_key_eq s t /\ s_key_eq x y)==> s_key_eq (s++x) (t++y)`,
  ho_match_mp_tac (fetch "-" "s_key_eq_ind")>>
  srw_tac[][]>>full_simp_tac(srw_ss())[s_key_eq_def]);

val s_key_eq_REVERSE = Q.prove(
  `!s t. s_key_eq s t ==> s_key_eq (REVERSE s) (REVERSE t)`,
  ho_match_mp_tac (fetch "-" "s_key_eq_ind")>>
  srw_tac[][]>>full_simp_tac(srw_ss())[s_key_eq_def,s_key_eq_APPEND]);

val s_key_eq_TAKE = Q.prove(
  `!s t n. s_key_eq s t ==> s_key_eq (TAKE n s) (TAKE n t)`,
  ho_match_mp_tac (fetch "-" "s_key_eq_ind")>>
  rw[]>>Cases_on`n`>>fs[s_key_eq_def]);

val s_key_eq_LASTN = Q.prove(
  `!s t n. s_key_eq s t
    ==> s_key_eq (LASTN n s) (LASTN n t)`,
  ho_match_mp_tac (fetch "-" "s_key_eq_ind")>>
  srw_tac[][LASTN_def]>>full_simp_tac(srw_ss())[s_key_eq_def]>>
  `s_key_eq [x] [y]` by full_simp_tac(srw_ss())[s_key_eq_def]>>
  `s_key_eq (REVERSE s ++ [x]) (REVERSE t ++[y])` by
    full_simp_tac(srw_ss())[s_key_eq_APPEND,s_key_eq_REVERSE]>>
  IMP_RES_TAC s_key_eq_TAKE>>
  metis_tac[s_key_eq_REVERSE]);

Theorem s_key_eq_tail:
  !a b c d. s_key_eq (a::b) (c::d) ==> s_key_eq b d
Proof
  full_simp_tac(srw_ss())[s_key_eq_def]
QED

val s_val_eq_tail = Q.prove(
 `!a b c d. s_val_eq (a::b) (c::d) ==> s_val_eq b d`,
  full_simp_tac(srw_ss())[s_val_eq_def]);

val s_key_eq_LASTN_exists = Q.prove(
  `!s t n m e y xs. s_key_eq s t /\
    LASTN n s = StackFrame m e (SOME y)::xs
    ==> ?e' ls. LASTN n t = StackFrame m e' (SOME y)::ls
        /\ MAP FST e' = MAP FST e
        /\ s_key_eq xs ls`,
   rpt strip_tac>>
   IMP_RES_TAC s_key_eq_LASTN>>
   first_x_assum (qspec_then `n` assume_tac)>> rev_full_simp_tac(srw_ss())[]>>
   Cases_on`LASTN n t`>>
   full_simp_tac(srw_ss())[s_key_eq_def]>>
   Cases_on`h`>>Cases_on`o'`>>Cases_on`o0`>>full_simp_tac(srw_ss())[s_frame_key_eq_def]);

Theorem s_val_eq_LASTN_exists:
   !s t n m e y xs. s_val_eq s t /\
   LASTN n s = StackFrame m e (SOME y)::xs
    ==> ?e' ls. LASTN n t = StackFrame m e' (SOME y)::ls
       /\ MAP SND e' = MAP SND e
       /\ s_val_eq xs ls
Proof
  rpt strip_tac>>
  IMP_RES_TAC s_val_eq_LASTN>>
  first_x_assum (qspec_then `n` assume_tac)>> rev_full_simp_tac(srw_ss())[]>>
  Cases_on`LASTN n t`>>
  full_simp_tac(srw_ss())[s_val_eq_def]>>
  Cases_on`h`>>Cases_on`o'`>>Cases_on`o0`>>full_simp_tac(srw_ss())[s_frame_val_eq_def]
QED

Theorem LASTN_LENGTH_cond:
   !n xs. n = LENGTH xs ==> LASTN n xs =xs
Proof
  metis_tac[LASTN_LENGTH_ID]
QED

val handler_eq = Q.prove(
  `x with handler := x.handler = x`, full_simp_tac(srw_ss())[state_component_equality]);

(*Stack is irrelevant to word_exp*)
val word_exp_stack_swap = Q.prove(
  `!s e st. word_exp s e = word_exp (s with stack:=st) e`,
  ho_match_mp_tac word_exp_ind>>
  srw_tac[][word_exp_def]
  >-
    (first_x_assum(qspec_then `st` SUBST1_TAC)>>
    every_case_tac>>full_simp_tac(srw_ss())[mem_load_def])
  >-
    (qpat_abbrev_tac`ls = MAP A B`>>
    qpat_abbrev_tac`ls' = MAP A B`>>
    (`ls = ls'` by
      (unabbrev_all_tac>>fs[MEM_MAP,MAP_EQ_f]))>>
    fs[])>>
  every_case_tac>>full_simp_tac(srw_ss())[]);

Theorem s_val_eq_stack_size:
  ∀xs ys.
   s_val_eq xs ys ==>
   stack_size xs = stack_size ys
Proof
  ho_match_mp_tac (fetch "-" "s_val_eq_ind") >>
  rw[s_val_eq_def] >>
  rename1 `s_frame_val_eq x y` >>
  Cases_on `x` >> Cases_on `y` >>
  rename1 `s_frame_val_eq (StackFrame _ _ ss1) (StackFrame _ _ ss2)` >>
  Cases_on `ss1` >> Cases_on `ss2` >> fs[s_frame_val_eq_def,stack_size_eq]
QED

Theorem s_val_append_eq_stack_size:
  !stk stk' frm. s_val_eq stk stk' ==>
    stack_size (frm::stk) = stack_size (frm::stk')
Proof
  rw [] >>
  drule s_val_eq_stack_size >> rw [] >>
  fs [stack_size_def]
QED

(*Stack swap theorem for evaluate*)
Theorem evaluate_stack_swap:
    !c s.
      case evaluate (c,s) of
      | (SOME Error,s1) => T
      | (SOME (FinalFFI e),s1) => s1.stack = [] /\ s1.locals = LN /\
                             (!xs. s_val_eq s.stack xs ==>
                                   evaluate(c,s with stack := xs) =
                                        (SOME (FinalFFI e), s1))
      | (SOME TimeOut,s1) => s1.stack = [] /\ s1.locals = LN /\
                             (!xs. s_val_eq s.stack xs ==>
                                   evaluate(c,s with stack := xs) =
                                        (SOME TimeOut, s1))
      | (SOME NotEnoughSpace,s1) => s1.stack = [] /\ s1.locals = LN /\
                                    (!xs. s_val_eq s.stack xs ==>
                                          evaluate(c,s with stack := xs) =
                                               (SOME NotEnoughSpace, s1))
                             (*for both errors,
                               the stack and locs should also be [] so the swapped stack
                               result should be exactly the same*)
      | (SOME (Exception x y),s1) =>
            (s.handler<LENGTH s.stack) /\ (*precondition for jump_exc*)
            (?e n ls m lss.
                (LASTN (s.handler+1) s.stack = StackFrame m e (SOME n)::ls) /\
                Abbrev (m = s1.locals_size) /\
                (MAP FST e = MAP FST lss /\
                   s1.locals = fromAList lss) /\
                (s_key_eq s1.stack ls) /\ (s1.handler = case n of(a,b,c)=>a) /\
                (!xs e' ls'.
                           (LASTN (s.handler+1) xs =
                             StackFrame m e' (SOME n):: ls') /\
                           (s_val_eq s.stack xs) ==> (*this implies n=n' and m=m'*)
                           ?st locs.
                           (evaluate (c,s with stack := xs) =
                              (SOME (Exception x y),
                               s1 with <| stack := st;
                                          handler := case n of (a,b,c) => a;
                                          locals := locs |>) /\
                            (?lss'. MAP FST e' = MAP FST lss' /\
                               locs = fromAList lss' /\
                               MAP SND lss = MAP SND lss')/\
                            s_val_eq s1.stack st /\ s_key_eq ls' st)))
      (*NONE, SOME Result cases*)
      | (res,s1) => (s_key_eq s.stack s1.stack) /\ (s1.handler = s.handler) /\
                    (!xs. s_val_eq s.stack xs ==>
                          ?st. evaluate (c,s with stack := xs) =
                                (res, s1 with stack := st)  /\
                                s_val_eq s1.stack st /\
                                s_key_eq xs st)
Proof
  simp_tac std_ss [markerTheory.Abbrev_def]
  >> ho_match_mp_tac (evaluate_ind |> Q.SPEC`UNCURRY P` |> SIMP_RULE (srw_ss())[] |> Q.GEN`P`) >> srw_tac[][]
  >-(*Skip*)
    (fs [evaluate_def,s_key_eq_refl]>>srw_tac[][]>>HINT_EXISTS_TAC>>fs[s_key_eq_refl])
  >-(*Alloc*)
    (fs[evaluate_def,alloc_def]>>reverse every_case_tac>>
    (every_case_tac>>
    IMP_RES_TAC gc_s_key_eq>>
    IMP_RES_TAC push_env_pop_env_s_key_eq>>
    qpat_x_assum`_.stack = _`kall_tac>>
    `s_key_eq s.stack y.stack` by full_simp_tac(srw_ss())[set_store_def]>>
    full_simp_tac(srw_ss())[SOME_11]>>TRY(CONJ_TAC>>srw_tac[][]>-
      (qpat_x_assum`gc a = SOME b` mp_tac>>
      qpat_x_assum`pop_env a = b` mp_tac>>
      full_simp_tac(srw_ss())[pop_env_def,gc_def,push_env_def,set_store_def
        ,LET_THM,env_to_list_def]>>
      every_case_tac>>full_simp_tac(srw_ss())[s_key_eq_def,s_frame_key_eq_def]>>
      srw_tac[][]>>full_simp_tac(srw_ss())[]))>> TRY(full_simp_tac(srw_ss())[call_env_def,flush_state_def,fromList2_def]>>srw_tac[][])>>
    full_case_tac>>full_simp_tac(srw_ss())[get_var_def]>>
    Q.MATCH_ASSUM_ABBREV_TAC `gc a = y`>>
    Q.MATCH_ASSUM_ABBREV_TAC `gc b = SOME x'`>>
    `s_val_eq b.stack a.stack /\ b with stack:=a.stack = a` by
      (conj_asm1_tac >> TRY(drule s_val_eq_stack_size) >>
      full_simp_tac(srw_ss())[push_env_def,LET_THM,env_to_list_def,set_store_def]>>
      bossLib.UNABBREV_ALL_TAC>>
      full_simp_tac(srw_ss())[s_val_eq_def,s_frame_val_eq_def,s_val_eq_sym])>>
    Q.UNABBREV_TAC `y`>>
    IMP_RES_TAC gc_s_val_eq>>rev_full_simp_tac(srw_ss())[]>>
    Q.UNABBREV_TAC`b`>>Q.UNABBREV_TAC`a`>>
    full_simp_tac(srw_ss())[push_env_def,set_store_def,LET_THM,env_to_list_def]>>
    Cases_on`x'.stack`>>
    Cases_on`z'`>>full_simp_tac(srw_ss())[s_key_eq_def,state_component_equality]>>
    `h=h'` by (
      full_simp_tac(srw_ss())[s_val_eq_def,s_key_eq_def]>>
      `s_frame_key_eq h' h` by metis_tac[s_frame_key_eq_trans]>>
      metis_tac[s_frame_val_and_key_eq,s_frame_key_eq_sym])>>
    full_simp_tac(srw_ss())[pop_env_def] >>Cases_on`h'`>>Cases_on`o'`>>full_simp_tac(srw_ss())[s_frame_key_eq_def]>>
    full_simp_tac(srw_ss())[state_component_equality]>>
    full_simp_tac(srw_ss())[has_space_def])
    >-
      (full_simp_tac(srw_ss())[state_component_equality,CaseEq"option",CaseEq"prod",CaseEq"word_loc",
                              PULL_EXISTS,CaseEq"bool"]>>
       qexists_tac `x'' with stack := t'` >> simp[] >> rfs [] >>
       fs [s_val_eq_def] >> dxrule s_val_eq_stack_size >> rw [])
    >-
      (full_simp_tac(srw_ss())[state_component_equality,CaseEq"option",CaseEq"prod",CaseEq"word_loc",
                              PULL_EXISTS,CaseEq"bool"]>>
       qexists_tac `x'' with stack := t'` >> simp[] >>  rfs [] >>
       fs [s_val_eq_def] >> dxrule s_val_eq_stack_size >> rw [])>>
    Q.EXISTS_TAC`t'`>>
    full_simp_tac(srw_ss())[state_component_equality,CaseEq"option",CaseEq"prod",CaseEq"word_loc",
                              PULL_EXISTS,CaseEq"bool"]>>
    qexists_tac `x'' with stack := t'` >> simp[] >>
    metis_tac[s_val_eq_def,s_key_eq_sym])
  >-(*Move*)
    (full_simp_tac(srw_ss())[evaluate_def]>>every_case_tac>>
    full_simp_tac(srw_ss())[set_vars_def,s_key_eq_refl]>>
    rpt strip_tac>>HINT_EXISTS_TAC>>
    assume_tac get_vars_stack_swap_simp>>
    full_simp_tac(srw_ss())[s_key_eq_refl])
  >-(*Inst*)
    (full_simp_tac(srw_ss())[evaluate_def,inst_def,assign_def,LET_THM]>>
    every_case_tac>>full_simp_tac(srw_ss())[set_var_def,s_key_eq_refl,set_fp_var_def]>>
    fs[get_vars_stack_swap_simp]>>
    srw_tac [] []>>full_simp_tac(srw_ss())[set_var_def,s_key_eq_refl]>>
    every_case_tac>>full_simp_tac(srw_ss())[set_var_def,s_key_eq_refl]>>
    full_simp_tac(srw_ss())[GEN_ALL(SYM(SPEC_ALL word_exp_stack_swap)),s_key_eq_refl,mem_store_def]>>
    srw_tac [] []>>full_simp_tac(srw_ss())[set_var_def,s_key_eq_refl,get_var_def,mem_load_def,get_fp_var_def]>>
    rfs[]>>
    TRY(HINT_EXISTS_TAC>>
    full_simp_tac(srw_ss())[GEN_ALL(SYM(SPEC_ALL word_exp_stack_swap)),s_key_eq_refl])>>
    rw[]>>fs[])
  >- (*Assign*)
    (fs[evaluate_def]>>every_case_tac>>
    fs[set_var_def,s_key_eq_refl]>>
    rpt strip_tac>>
    HINT_EXISTS_TAC>>
    full_simp_tac(srw_ss())[GEN_ALL(SYM(SPEC_ALL word_exp_stack_swap)),s_key_eq_refl])
  >-(*Get*)
    (fs[evaluate_def]>>every_case_tac>>
    fs[set_var_def,s_key_eq_refl]>>
    full_simp_tac(srw_ss())[set_store_def,s_key_eq_refl]>>
    rpt strip_tac>>
    HINT_EXISTS_TAC>>
    full_simp_tac(srw_ss())[GEN_ALL(SYM(SPEC_ALL word_exp_stack_swap)),s_key_eq_refl])
  >-(*Set*)
    (fs[evaluate_def]>>every_case_tac>>
    fs[set_store_def,s_key_eq_refl]>>
    rpt strip_tac>>
    HINT_EXISTS_TAC>>
    full_simp_tac(srw_ss())[GEN_ALL(SYM(SPEC_ALL word_exp_stack_swap)),s_key_eq_refl])
  >-(*OpCurrHeap*)
    (fs[evaluate_def]>>every_case_tac>>
    fs[set_var_def,s_key_eq_refl]>>
    full_simp_tac(srw_ss())[set_store_def,s_key_eq_refl]>>
    rpt strip_tac>>
    HINT_EXISTS_TAC>>
    full_simp_tac(srw_ss())[GEN_ALL(SYM(SPEC_ALL word_exp_stack_swap)),s_key_eq_refl])
  >-(*Store*)
    (full_simp_tac(srw_ss())[evaluate_def]>>every_case_tac>>
    full_simp_tac(srw_ss())[mem_store_def,state_component_equality,s_key_eq_refl]>>
    rpt strip_tac>>HINT_EXISTS_TAC>>
    full_simp_tac(srw_ss())[GEN_ALL(SYM(SPEC_ALL word_exp_stack_swap)),s_key_eq_refl,get_var_def,
       state_component_equality])
  >- (*Tick*)
    (full_simp_tac(srw_ss())[evaluate_def]>>every_case_tac>- full_simp_tac(srw_ss())[call_env_def,flush_state_def,fromList2_def] >>
    full_simp_tac(srw_ss())[dec_clock_def,s_key_eq_refl]>>
    rpt strip_tac>>Q.EXISTS_TAC`xs`>>full_simp_tac(srw_ss())[s_key_eq_refl])
  >- (*MustTerminate*)
    (full_simp_tac(srw_ss())[evaluate_def]>>
    LET_ELIM_TAC>> every_case_tac>>full_simp_tac(srw_ss())[]>>
    TRY(srw_tac[][]>>res_tac>>simp[]>>metis_tac[])
    >-
      (qexists_tac`lss`>>simp[]>>
      srw_tac[][]>>res_tac>>simp[]>>
      metis_tac[])
    >>
    ntac 5 strip_tac>>
    res_tac>>
    rev_full_simp_tac(srw_ss())[]>>simp[])
  >-(*Seq*)
    (full_simp_tac(srw_ss())[evaluate_def]>>
    Cases_on`evaluate(c',s)`>>
    full_simp_tac(srw_ss())[LET_THM]>>
    IF_CASES_TAC>-
      (*q = NONE*)
      (every_case_tac>>
      full_simp_tac(srw_ss())[s_key_eq_trans]>> TRY
        (qho_match_abbrev_tac`A ∧ ∀xs. P xs` >> unabbrev_all_tac >> simp[] >>
        CONJ_TAC>-metis_tac[s_key_eq_trans]>>
        rpt strip_tac>>
        first_x_assum(qspec_then `xs` assume_tac)>>rev_full_simp_tac(srw_ss())[]>>
        first_x_assum(qspec_then `st` assume_tac)>>rev_full_simp_tac(srw_ss())[]>>
        HINT_EXISTS_TAC>>metis_tac[s_key_eq_trans])
        >-
        (ASSUME_TAC (INST_TYPE [``:'b``|->``:'a``]s_key_eq_LASTN_exists)>>
        (*get the result stack from first eval*)
        IMP_RES_TAC s_key_eq_length>>full_simp_tac(srw_ss())[]>>
        first_x_assum(qspecl_then [`r.stack`,`s.stack`,`s.handler+1`,`r'.locals_size`,`e`,`n`,`ls`] assume_tac)>>
        `s_key_eq r.stack s.stack` by srw_tac[][s_key_eq_sym]>>
        full_simp_tac(srw_ss())[]>>rev_full_simp_tac(srw_ss())[]>>Q.EXISTS_TAC`lss`>>
        simp[]>>CONJ_TAC>-metis_tac[s_key_eq_trans]>>
        rpt strip_tac>>
        first_x_assum(qspec_then `xs` assume_tac)>>
        rev_full_simp_tac(srw_ss())[]>>
        IMP_RES_TAC s_key_eq_LASTN_exists>>
        last_x_assum(qspecl_then [`st`,`e'''`,`ls'''`] assume_tac)>>
        rev_full_simp_tac(srw_ss())[]>>
        HINT_EXISTS_TAC>>
        Q.EXISTS_TAC`fromAList lss'`>>
        full_simp_tac(srw_ss())[]>>
        CONJ_TAC>- (Q.EXISTS_TAC`lss'`>>full_simp_tac(srw_ss())[])>>
        metis_tac[s_key_eq_trans])>>
        rpt strip_tac>>
        first_x_assum(qspec_then `xs` assume_tac)>>rev_full_simp_tac(srw_ss())[])>>
      Cases_on`q`>>full_simp_tac(srw_ss())[]>>
      Cases_on`x`>>full_simp_tac(srw_ss())[]>>
      rpt strip_tac>-
        (first_x_assum(qspec_then `xs` assume_tac)>>rev_full_simp_tac(srw_ss())[]>>HINT_EXISTS_TAC>>
        full_simp_tac(srw_ss())[])>-
      (Q.EXISTS_TAC`lss`>>full_simp_tac(srw_ss())[]>>
      rpt strip_tac>>
      first_x_assum (qspecl_then [`xs`,`e'`,`ls'`] assume_tac)>>rev_full_simp_tac(srw_ss())[]>>
      HINT_EXISTS_TAC>>
      Q.EXISTS_TAC`fromAList lss'`>>full_simp_tac(srw_ss())[]>>
      Q.EXISTS_TAC`lss'`>>full_simp_tac(srw_ss())[])>>
      first_x_assum (qspec_then `xs` assume_tac)>> rev_full_simp_tac(srw_ss())[]>>HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[])
  >-(*Return*)
    (full_simp_tac(srw_ss())[evaluate_def]>> every_case_tac>>
    full_simp_tac(srw_ss())[call_env_def,flush_state_def,s_key_eq_refl]>>
    rpt strip_tac>>full_simp_tac(srw_ss())[get_var_def]>>HINT_EXISTS_TAC>>
    full_simp_tac(srw_ss())[state_component_equality,s_key_eq_refl] >>
    drule s_val_eq_stack_size >> fs [])
  >-(*Raise*)
    (full_simp_tac(srw_ss())[evaluate_def]>>every_case_tac>>full_simp_tac(srw_ss())[get_var_def,jump_exc_def]>>
    qpat_x_assum `(a = SOME x)` mp_tac>>
    every_case_tac>>full_simp_tac(srw_ss())[state_component_equality]>>
    strip_tac>> Q.EXISTS_TAC `l`>>
    full_simp_tac(srw_ss())[EQ_SYM_EQ,s_key_eq_refl]>>
    rpt strip_tac>>
    IMP_RES_TAC s_val_eq_length>>full_simp_tac(srw_ss())[EQ_SYM_EQ,state_component_equality]>>
    full_simp_tac(srw_ss())[s_key_eq_refl]>>
    `s.handler + 1<= LENGTH s.stack` by metis_tac[arithmeticTheory.LESS_OR,arithmeticTheory.ADD1]>>
    rpt (qpat_x_assum `a = LASTN b c` (ASSUME_TAC o SYM))>>
    IMP_RES_TAC s_val_eq_LASTN>>
    first_x_assum(qspec_then `s.handler+1` assume_tac)>>rev_full_simp_tac(srw_ss())[]>>
    IMP_RES_TAC s_val_eq_tail>>
    full_simp_tac(srw_ss())[s_val_eq_def,s_frame_val_eq_def]>>
    Q.EXISTS_TAC`e'`>>full_simp_tac(srw_ss())[])
  >-(*If*)
    (full_simp_tac(srw_ss())[evaluate_def]>>
    ntac 4 full_case_tac>>full_simp_tac(srw_ss())[]>>
    Cases_on`word_cmp cmp c''' c`>> full_simp_tac(srw_ss())[]>>
    every_case_tac>>
    full_simp_tac(srw_ss())[s_key_eq_trans]>>srw_tac[][]>>
    TRY(last_x_assum(qspec_then `xs` assume_tac)>>rev_full_simp_tac(srw_ss())[]>>
    full_simp_tac(srw_ss())[get_var_def]>>Cases_on`ri`>>full_simp_tac(srw_ss())[get_var_imm_def,get_var_def]>>
    HINT_EXISTS_TAC>>metis_tac[s_key_eq_trans])>>
    qexists_tac`lss`>>full_simp_tac(srw_ss())[]>>srw_tac[][]>>
    IMP_RES_TAC s_val_eq_LASTN_exists>>
    last_x_assum(qspecl_then [`xs`,`e'''`,`ls'''`] assume_tac)>>
    Cases_on`ri`>>rev_full_simp_tac(srw_ss())[get_var_def,get_var_imm_def]>>
    HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[]>>
    qexists_tac`fromAList lss'`>>full_simp_tac(srw_ss())[]>>
    qexists_tac`lss'`>>full_simp_tac(srw_ss())[])
  >- (*LocValue*) (
    fs[evaluate_def,set_var_def,state_component_equality,s_key_eq_refl]
    \\ rw[s_key_eq_refl,state_component_equality] )
  >- (* Install *) (
    fs[evaluate_def]>>
    TOP_CASE_TAC>>fs[]>>
    reverse (TOP_CASE_TAC)>>fs[]
    >-(
      pop_assum mp_tac>>
      simp[case_eq_thms]>>rw[]>>
      pairarg_tac>>fs[]>>
      qpat_x_assum`_ = (SOME _,_)` mp_tac>>
      simp[case_eq_thms]>>rw[])
    >>
      fs[case_eq_thms]>>
      pairarg_tac>>fs[case_eq_thms]>>
      rw[]>>fs[state_component_equality]>>
      metis_tac[s_key_eq_refl])
  >- (* CBW *) (
    fs[evaluate_def]>>rw[]>>
    fs[case_eq_thms]>>
    every_case_tac>>fs[state_component_equality]>>
    metis_tac[s_key_eq_refl])
  >- (* DBW *) (
    fs[evaluate_def]>>rw[]>>
    fs[case_eq_thms]>>
    every_case_tac>>fs[state_component_equality]>>
    metis_tac[s_key_eq_refl])
  >-(*FFI*)
   (full_simp_tac(srw_ss())[evaluate_def]>>
    every_case_tac >> fs [state_component_equality]>>
    TRY (fs [call_env_def,flush_state_def] \\ EVAL_TAC \\ NO_TAC) >>
    metis_tac[s_key_eq_refl]) >>
  (*Call*)
  full_simp_tac(srw_ss())[evaluate_def]>>
  Cases_on`get_vars args s`>> full_simp_tac(srw_ss())[]>>
  IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
  Cases_on`find_code dest (add_ret_loc ret x) s.code s.stack_size`>>
  full_simp_tac(srw_ss())[]>>
  Cases_on`x'`>>full_simp_tac(srw_ss())[]>>
  Cases_on`r`>>full_simp_tac(srw_ss())[]>>
  Cases_on`ret`>>full_simp_tac(srw_ss())[]
  >-
    (*Tail Call*)
    (Cases_on`handler`>>full_simp_tac(srw_ss())[]>>
    every_case_tac>>
    full_simp_tac(srw_ss())[dec_clock_def,call_env_def,flush_state_def,fromList2_def] >>
    TRY (strip_tac >> strip_tac >>
     drule s_val_eq_stack_size >>
     strip_tac >> fs [] >>
     first_x_assum(qspec_then `xs` assume_tac)>> rfs [] >>
     qexists_tac`st`>> fs [] >> NO_TAC) >>
     qexists_tac `lss` >> rw [] >>
     drule s_val_eq_stack_size >>
     rw [EQ_SYM_EQ] >>
     first_x_assum (qspecl_then [`xs`,`e'`,`ls'`] mp_tac) >>
     rw [] >>
     fs [] >> metis_tac [])
    >>
    (*Returning call*)
    PairCases_on`x'`>> full_simp_tac(srw_ss())[]>>
    IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
    Cases_on`cut_env x'1 s.locals`>>full_simp_tac(srw_ss())[]>>
    Cases_on`s.clock=0`>-
      (full_simp_tac(srw_ss())[call_env_def,flush_state_def,fromList2_def]>>srw_tac[][]>>
      assume_tac get_vars_stack_swap_simp>>
      first_x_assum(qspec_then `args` (SUBST1_TAC)) >>
      simp [] >> every_case_tac >> fs[] >> rfs [] >>
      rw[state_component_equality] >>
      Cases_on `handler` >-
        (rw[push_env_def,ELIM_UNCURRY,stack_size_eq] >>
         imp_res_tac s_val_eq_stack_size >> rw[]) >>
      rename1 `push_env _ (SOME handler)` >>
      PairCases_on `handler` >>
      rw[push_env_def,ELIM_UNCURRY,stack_size_eq] >>
      imp_res_tac s_val_eq_stack_size >> rw[]
      )>>
    full_simp_tac(srw_ss())[]>>
    Cases_on`evaluate (q',call_env q r' (push_env x' handler (dec_clock s)))`>>
    Cases_on`q''`>>full_simp_tac(srw_ss())[]>>Cases_on`x''`>>full_simp_tac(srw_ss())[]
    >-
      (*Result*)
      (full_simp_tac(srw_ss())[get_vars_stack_swap_simp]>>
      IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
      full_case_tac>>
      IF_CASES_TAC>>
      full_simp_tac(srw_ss())[set_var_def,call_env_def,flush_state_def]>>
      IMP_RES_TAC push_env_pop_env_s_key_eq>>
      qpat_x_assum`_.stack = _`kall_tac>>
      qpat_x_assum`_.locals = fromAList _`kall_tac>>
      qpat_x_assum`domain _ = domain _.locals`kall_tac>>
      full_simp_tac(srw_ss())[dec_clock_def,SOME_11]>>
      Cases_on`evaluate(x'2,x'' with locals:=insert x'0 w0 x''.locals)`>>full_simp_tac(srw_ss())[]>>
      Cases_on`q''`>>TRY(Cases_on`x'''`)>>full_simp_tac(srw_ss())[]>>rev_full_simp_tac(srw_ss())[]>>
      `s_key_eq s.stack x''.stack` by full_simp_tac(srw_ss())[EQ_SYM_EQ]>>full_simp_tac(srw_ss())[]>>
      (*Inductive Result and None*)
      TRY
      (qho_match_abbrev_tac`A ∧ B /\ C` >> unabbrev_all_tac>>
      CONJ_TAC
      >- metis_tac[s_key_eq_trans]>>
      CONJ_ASM1_TAC >-
      (Cases_on`handler`>>
      TRY (rename1 `s_key_eq (push_env _ (SOME stkf) s).stack r.stack` >>
      PairCases_on `stkf`)>>
      full_simp_tac(srw_ss())[push_env_def,LET_THM,env_to_list_def,pop_env_def]>>
      Cases_on`r.stack`>>full_simp_tac(srw_ss())[s_key_eq_def]>>
      Cases_on`h` >> rename1 `StackFrame _ _ excp'::t` >> Cases_on`excp'` >>
      TRY (rename1 `StackFrame _ _ (SOME excp)::t` >>
      PairCases_on `excp`)>>
      full_simp_tac(srw_ss())[s_frame_key_eq_def]>>
      full_simp_tac(srw_ss())[state_component_equality]>>rev_full_simp_tac(srw_ss())[]) >>
      ntac 2 strip_tac>>
      `!a. s_val_eq (a::s.stack) (a::xs)` by
       (strip_tac>> full_simp_tac(srw_ss())[s_val_eq_def]>>
       Cases_on`a`>> rename1 `StackFrame _ l excp'` >> Cases_on`excp'` >>
       full_simp_tac(srw_ss())[s_frame_val_eq_def])>>
      Cases_on`handler`>>
      (TRY (rename1 `s_key_eq (push_env _ (SOME stkf) s).stack r.stack` >>
      PairCases_on `stkf`)>>
      full_simp_tac(srw_ss())[push_env_def,LET_THM,env_to_list_def]>>
      qpat_abbrev_tac `frame = StackFrame lsz ls n`>>
      first_x_assum (qspec_then `frame` assume_tac)>>
      drule s_val_eq_stack_size >> strip_tac >> fs [] >>
      last_x_assum(qspec_then `frame::xs` assume_tac)>>
      rev_full_simp_tac(srw_ss())[]>>
      `LENGTH xs = LENGTH s.stack` by full_simp_tac(srw_ss())[s_val_eq_length]>> full_simp_tac(srw_ss())[]>>
      Cases_on`st`>>full_simp_tac(srw_ss())[s_key_eq_def]>>
      Cases_on`r.stack`>>full_simp_tac(srw_ss())[pop_env_def,s_key_eq_def]>>
      `h = h'` by metis_tac[s_frame_key_eq_sym,s_frame_key_eq_trans,
                            s_frame_val_and_key_eq,s_val_eq_def]>>
      Cases_on`h'`>>Cases_on`o0`>>full_simp_tac(srw_ss())[]>>
      full_simp_tac(srw_ss())[state_component_equality]>>
      IMP_RES_TAC s_val_eq_tail>>
      first_x_assum(qspec_then `t` assume_tac)>> rev_full_simp_tac(srw_ss())[]>>
      TRY(rename1 `StackFrame o' l (SOME excp'')` >> Cases_on`excp''`>>
          `x''.stack = t'` by full_simp_tac(srw_ss())[EQ_SYM_EQ]>>full_simp_tac(srw_ss())[]>>rev_full_simp_tac(srw_ss())[])>>
      Q.EXISTS_TAC`st`>> full_simp_tac(srw_ss())[state_component_equality]
      >-
        (`x'' with <|locals := insert x'0 w0 x''.locals; stack := t|> =
        r with <|locals := insert x'0 w0 x''.locals;
                  locals_size := x''.locals_size; stack := t|>` by
          full_simp_tac(srw_ss())[state_component_equality]>>
        pop_assum SUBST_ALL_TAC>>
        srw_tac[][]>>
        metis_tac[state_component_equality,EQ_SYM_EQ,s_key_eq_trans])
      >>
        (`x'' with <|locals := insert x'0 w0 x''.locals; stack := t|> =
        r with <|locals := insert x'0 w0 x''.locals; locals_size := x''.locals_size;
                 stack := t; handler:=s.handler|>` by
          full_simp_tac(srw_ss())[state_component_equality]>>
        pop_assum SUBST_ALL_TAC>>
        srw_tac[][]>>
        metis_tac[state_component_equality,EQ_SYM_EQ,s_key_eq_trans])))
      (*Exceptions*)
      >-
        (`s.handler = x''.handler` by
          (Cases_on`handler`>>
          TRY (rename1 `(push_env _ (SOME excp') s).stack ` >> PairCases_on `excp'`)>>
          full_simp_tac(srw_ss())[push_env_def,LET_THM,env_to_list_def]>>
          Cases_on`r.stack`>>full_simp_tac(srw_ss())[pop_env_def,s_key_eq_def]>>
          Cases_on`h`>>
          Cases_on`o0`>>  TRY (rename1 `r.stack = StackFrame _ _ (SOME stkf)::t` >>
          PairCases_on `stkf`)>>
          full_simp_tac(srw_ss())[s_frame_key_eq_def]>>
          full_simp_tac(srw_ss())[state_component_equality]
          )>>
        CONJ_ASM1_TAC >- metis_tac[s_key_eq_length]>>
        `s_key_eq x''.stack s.stack` by metis_tac[s_key_eq_sym]>>
        IMP_RES_TAC s_key_eq_LASTN_exists>>
        full_simp_tac(srw_ss())[]>>
        (*check*)
        qexists_tac`lss`>>full_simp_tac(srw_ss())[]>>
        CONJ_TAC>-
          metis_tac[s_key_eq_trans]
        >>
        rpt strip_tac>>full_simp_tac(srw_ss())[]>>
        `!a. s_val_eq (a::s.stack) (a::xs)` by
         (strip_tac>> full_simp_tac(srw_ss())[s_val_eq_def]>>Cases_on`a`>>
          Cases_on`o'`>>Cases_on`o0`>>full_simp_tac(srw_ss())[s_frame_val_eq_def])>>
        Cases_on`handler`>>
        TRY (rename1 `(push_env _ (SOME excp'') s).stack ` >> PairCases_on `excp''`)>>
        full_simp_tac(srw_ss())[push_env_def,LET_THM,env_to_list_def]>>
        qpat_abbrev_tac `frame = StackFrame SS A B`>>
        first_x_assum (qspec_then `frame` assume_tac)>>
        drule s_val_eq_stack_size >> strip_tac >> fs [] >>
        last_x_assum(qspec_then `frame::xs` assume_tac)>>
        rev_full_simp_tac(srw_ss())[]>>
        `LENGTH xs = LENGTH s.stack` by full_simp_tac(srw_ss())[s_val_eq_length]>> full_simp_tac(srw_ss())[]>>
        Cases_on`st`>>full_simp_tac(srw_ss())[s_key_eq_def]>>
        Cases_on`r.stack`>>full_simp_tac(srw_ss())[pop_env_def,s_key_eq_def]>>
        `h = h'` by metis_tac[s_frame_key_eq_sym,s_frame_key_eq_trans,
                              s_frame_val_and_key_eq,s_val_eq_def]>>
        Cases_on`h'`>>Cases_on`o0`>>
        full_simp_tac(srw_ss())[Abbr`frame`,s_frame_key_eq_def]>>
        TRY(rename1 `r.stack = StackFrame _ _ (SOME stkf)::t'` >> PairCases_on`stkf`)>>
        full_simp_tac(srw_ss())[state_component_equality]>>
        IMP_RES_TAC s_val_eq_tail>>
        first_x_assum(qspec_then `t` assume_tac)>> rev_full_simp_tac(srw_ss())[]>>
        IMP_RES_TAC s_key_eq_LASTN_exists>>
        first_x_assum(qspecl_then[`e''''`,`ls''''`] assume_tac)>>rev_full_simp_tac(srw_ss())[]
        >-
          (`x'' with <|locals := insert x'0 w0 x''.locals; stack := t|> =
           r with <|locals := insert x'0 w0 x''.locals; locals_size := x''.locals_size; stack := t|>` by
             full_simp_tac(srw_ss())[state_component_equality]>>
          full_simp_tac(srw_ss())[PULL_EXISTS]>>
          HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[]>>
          qexists_tac`lss'`>>full_simp_tac(srw_ss())[]>>
          metis_tac[s_key_eq_trans])
        >>
          (`x'' with <|locals := insert x'0 w0 x''.locals; stack := t|> =
          r with <|locals := insert x'0 w0 x''.locals; locals_size := x''.locals_size; stack := t; handler:=stkf0|>` by
            full_simp_tac(srw_ss())[state_component_equality]>>
          full_simp_tac(srw_ss())[PULL_EXISTS]>>
          HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[]>>
          qexists_tac`lss'`>>full_simp_tac(srw_ss())[]>>
          metis_tac[s_key_eq_trans]))
      (*The rest*)
      >>
      (
      ntac 2 strip_tac>>
      `!a. s_val_eq (a::s.stack) (a::xs)` by
       (strip_tac>> full_simp_tac(srw_ss())[s_val_eq_def]>>Cases_on`a`>>
        Cases_on`o0`>>full_simp_tac(srw_ss())[s_frame_val_eq_def])>>
      Cases_on`handler`>>
      TRY(rename1 `r.handler = (push_env _ (SOME stkf) s).handler` >> PairCases_on`stkf`)>>
      full_simp_tac(srw_ss())[push_env_def,LET_THM,env_to_list_def]>>
      qpat_abbrev_tac `frame = StackFrame lsz ls n`>>
      first_x_assum (qspec_then `frame` assume_tac)>>
      drule s_val_eq_stack_size >> strip_tac >> fs [] >>
      last_x_assum(qspec_then `frame::xs` assume_tac)>>
      rev_full_simp_tac(srw_ss())[]>>
      `LENGTH xs = LENGTH s.stack` by full_simp_tac(srw_ss())[s_val_eq_length]>> full_simp_tac(srw_ss())[]>>
      Cases_on`st`>>full_simp_tac(srw_ss())[s_key_eq_def]>>
      Cases_on`r.stack`>>full_simp_tac(srw_ss())[pop_env_def,s_key_eq_def]>>
      `h = h'` by metis_tac[s_frame_key_eq_sym,s_frame_key_eq_trans,
                            s_frame_val_and_key_eq,s_val_eq_def]>>
      Cases_on`h'`>>Cases_on`o0`>>
      full_simp_tac(srw_ss())[Abbr`frame`,s_frame_key_eq_def]>>
      TRY (rename1 `h = StackFrame _ _ (SOME excp')` >> Cases_on `excp'`) >>
      full_simp_tac(srw_ss())[state_component_equality]>>
      IMP_RES_TAC s_val_eq_tail>>
      first_x_assum(qspec_then `t` assume_tac)>> rev_full_simp_tac(srw_ss())[]
      >-
        (`x'' with <|locals := insert x'0 w0 x''.locals; stack := t|> =
         r with <|locals := insert x'0 w0 x''.locals; locals_size := x''.locals_size;
                   stack := t|>` by
        full_simp_tac(srw_ss())[state_component_equality]>>
        full_simp_tac(srw_ss())[])
      >>
        (
        `x'' with <|locals := insert x'0 w0 x''.locals; stack := t|> =
        r with <|locals := insert x'0 w0 x''.locals; locals_size := x''.locals_size;
                 stack := t; handler:=x''.handler|>` by
          full_simp_tac(srw_ss())[state_component_equality]>>
        pop_assum SUBST_ALL_TAC>>
        srw_tac[][]>>
        metis_tac[state_component_equality,EQ_SYM_EQ,s_key_eq_trans])))
     >-
     (*Exception*)
     (Cases_on`handler` >> fs []
      >-
       (*no handler*)
       (fs [call_env_def,flush_state_def,push_env_def,env_to_list_def,dec_clock_def,LET_THM]>>
       CONJ_ASM1_TAC
       >-
       (IMP_RES_TAC prim_recTheory.LESS_LEMMA1>>
       qpat_x_assum `LASTN a as=b` mp_tac>>simp[]>>
       qpat_abbrev_tac `frame = StackFrame lsz a b`>>
       `LENGTH s.stack+1 = LENGTH (frame::s.stack) ` by full_simp_tac(srw_ss())[arithmeticTheory.ADD1]>>
       pop_assum SUBST1_TAC>> fs [LASTN_LENGTH_ID]>>
       Q.UNABBREV_TAC`frame`>>fs[option_nchotomy]) >>
       fs[GEN_ALL LASTN_TL]>>
       Q.EXISTS_TAC`lss`>>full_simp_tac(srw_ss())[]>>rpt strip_tac>>
       assume_tac get_vars_stack_swap_simp>>
       first_x_assum(qspec_then `args` assume_tac)>>full_simp_tac(srw_ss())[]>>
       qpat_abbrev_tac `frame = StackFrame lsz a b`>>
       `s.handler < LENGTH xs` by (IMP_RES_TAC s_val_eq_length>>full_simp_tac(srw_ss())[])>>
       first_x_assum(qspecl_then [`frame::xs`,`e'`,`ls'`] assume_tac)>>rev_full_simp_tac(srw_ss())[]>>
       IMP_RES_TAC (GEN_ALL LASTN_TL)>>
       last_x_assum(qspec_then `frame` assume_tac)>>
       full_simp_tac(srw_ss())[]>> rev_full_simp_tac(srw_ss())[]>>
       `s_val_eq (frame::s.stack) (frame::xs)` by
         metis_tac[s_val_eq_def,s_frame_val_eq_def] >>
       drule s_val_eq_stack_size >> strip_tac >> fs []>>
       HINT_EXISTS_TAC >>
       Q.EXISTS_TAC`fromAList lss'`>> fs[state_component_equality]>>
       Q.EXISTS_TAC`lss'`>> fs []) >>
       (*handler*)
       PairCases_on`x''`>>
       fs [call_env_def,flush_state_def,push_env_def,dec_clock_def,LET_THM,env_to_list_def]>>
       every_case_tac>>rfs[set_var_def]>>fs[]>>
       `r.handler = s.handler` by
       (`LENGTH s.stack +1 =
        LENGTH (StackFrame s.locals_size (list_rearrange (s.permute 0)
           (QSORT key_val_compare (toAList x')))
           (SOME (s.handler,x''2,x''3))::s.stack)` by fs [arithmeticTheory.ADD1]>>
         pop_assum SUBST_ALL_TAC>>
         fs [LASTN_LENGTH_ID]>> Cases_on `n` >> fs [] >> rveq >>
         metis_tac[s_key_eq_trans,s_key_eq_sym])>>
       TRY
         (qho_match_abbrev_tac`A ∧ B /\ C` >> unabbrev_all_tac>>
         (ONCE_REWRITE_TAC[CONJ_ASSOC]>>CONJ_TAC
         >-
         (`LENGTH s.stack +1 =
           LENGTH (StackFrame s.locals_size (list_rearrange (s.permute 0)
           (QSORT key_val_compare (toAList x')))
           (SOME (s.handler,x''2,x''3))::s.stack)` by full_simp_tac(srw_ss())[arithmeticTheory.ADD1]>>
         pop_assum SUBST_ALL_TAC>>
         full_simp_tac(srw_ss())[LASTN_LENGTH_ID]>>
         metis_tac[s_key_eq_trans,s_key_eq_sym])>>
         rpt strip_tac>>
         assume_tac get_vars_stack_swap_simp>>
         first_x_assum(qspec_then `args` assume_tac)>>full_simp_tac(srw_ss())[]>>
         qpat_abbrev_tac`frame = StackFrame lsz c d`>>
         `s_val_eq (frame::s.stack) (frame::xs)` by
           metis_tac[s_val_eq_def,s_frame_val_eq_def]>>
         drule s_val_eq_stack_size >> strip_tac >> fs [] >>
         IMP_RES_TAC s_val_eq_LASTN_exists>>
         `LENGTH s.stack = LENGTH xs` by full_simp_tac(srw_ss())[s_val_eq_length] >>
         first_x_assum(qspec_then`frame::xs` assume_tac)>>rev_full_simp_tac(srw_ss())[]>>
         first_x_assum(qspecl_then [`frame::xs`,`e'`,`ls'`] assume_tac)>>rev_full_simp_tac(srw_ss())[]>>
         `LENGTH s.stack +1 = LENGTH (frame::s.stack) /\
          LENGTH s.stack +1 = LENGTH (frame::xs)` by
           full_simp_tac(srw_ss())[arithmeticTheory.ADD1,s_val_eq_length]>>
          full_simp_tac(srw_ss())[LASTN_LENGTH_cond]>>
          `MAP FST lss = MAP FST lss'` by metis_tac[EQ_SYM_EQ]>>
          `lss = lss'` by full_simp_tac(srw_ss())[LIST_EQ_MAP_PAIR]>>
          full_simp_tac(srw_ss())[]>>
          last_x_assum(qspec_then `st` assume_tac)>>
          rev_full_simp_tac(srw_ss())[]>>HINT_EXISTS_TAC>>
          metis_tac[s_key_eq_trans,handler_eq]))
          >-
          (CONJ_TAC >- (
          `LENGTH s.stack +1 =
           LENGTH (StackFrame s.locals_size (list_rearrange (s.permute 0)
           (QSORT key_val_compare (toAList x')))
           (SOME (s.handler,x''2,x''3))::s.stack)` by full_simp_tac(srw_ss())[arithmeticTheory.ADD1]>>
           pop_assum SUBST_ALL_TAC>>
           full_simp_tac(srw_ss())[LASTN_LENGTH_ID]>>
           `LENGTH ls = LENGTH r.stack` by full_simp_tac(srw_ss())[s_key_eq_length] >>
           full_simp_tac(srw_ss())[])>>
           IMP_RES_TAC s_key_eq_LASTN_exists>>
           Q.EXISTS_TAC`e''`>>
           Q.EXISTS_TAC`n`>>
           Q.EXISTS_TAC`ls''`>>
           full_simp_tac(srw_ss())[]>>
           Q.EXISTS_TAC`lss'`>>
          (*check*)
           CONJ_TAC>-
           (`LENGTH s.stack +1 =
             LENGTH (StackFrame s.locals_size (list_rearrange (s.permute 0)
             (QSORT key_val_compare (toAList x')))
             (SOME (s.handler,x''2,x''3))::s.stack)` by full_simp_tac(srw_ss())[arithmeticTheory.ADD1]>>
           pop_assum SUBST_ALL_TAC>>
           full_simp_tac(srw_ss())[LASTN_LENGTH_ID]>>
           `LENGTH ls = LENGTH r.stack` by full_simp_tac(srw_ss())[s_key_eq_length]>>
           full_simp_tac(srw_ss())[EQ_SYM_EQ])>>
           full_simp_tac(srw_ss())[]>>
           CONJ_TAC>- metis_tac[s_key_eq_trans]>>
           rpt strip_tac>>
           assume_tac get_vars_stack_swap_simp>>
           first_x_assum(qspec_then `args` assume_tac)>>full_simp_tac(srw_ss())[]>>
           qpat_abbrev_tac`frame = StackFrame lsz c d`>>
           `s_val_eq (frame::s.stack) (frame::xs)` by
             metis_tac[s_val_eq_def,s_frame_val_eq_def]>>
           drule s_val_eq_stack_size >> strip_tac >> fs [] >>
           IMP_RES_TAC s_val_eq_LASTN_exists>>
           pop_assum kall_tac>>
           first_x_assum(qspec_then `frame::xs` assume_tac)>>
           rev_full_simp_tac(srw_ss())[]>>
           `LENGTH s.stack = LENGTH xs` by full_simp_tac(srw_ss())[s_val_eq_length] >>
           first_x_assum(qspecl_then [`frame::xs`,`e''''`,`ls''''`] assume_tac)>>
           rev_full_simp_tac(srw_ss())[]>>
           `LENGTH s.stack +1 = LENGTH (frame::s.stack) /\
            LENGTH s.stack +1 = LENGTH (frame::xs)` by
             full_simp_tac(srw_ss())[arithmeticTheory.ADD1,s_val_eq_length]>>
           full_simp_tac(srw_ss())[LASTN_LENGTH_cond]>>
           `MAP FST lss = MAP FST lss''` by metis_tac[EQ_SYM_EQ]>>
           `lss'' = lss` by full_simp_tac(srw_ss())[LIST_EQ_MAP_PAIR]>>
           full_simp_tac(srw_ss())[]>>
           IMP_RES_TAC s_key_eq_LASTN_exists>>
           qpat_x_assum `LASTN _ _ = StackFrame _ _ _::_` mp_tac >>
           rename [`LASTN _ st = StackFrame _ e5 _::ls5`]>> strip_tac >>
           first_x_assum (qspecl_then [`st`,`e5`,`ls5`] assume_tac)>>
           rev_full_simp_tac(srw_ss())[]>>
           full_simp_tac(srw_ss())[handler_eq]>>
           HINT_EXISTS_TAC>>Q.EXISTS_TAC`fromAList lss'''`>>
           full_simp_tac(srw_ss())[handler_eq]>>
           CONJ_TAC >-
             metis_tac[handler_eq]>>
           CONJ_TAC>-
            (Q.EXISTS_TAC`lss'''`>>full_simp_tac(srw_ss())[])>>
           metis_tac[s_key_eq_trans])>>
          (*TimeOut*)
           rpt strip_tac>>
           assume_tac get_vars_stack_swap_simp>>
           first_x_assum(qspec_then `args` assume_tac)>>full_simp_tac(srw_ss())[]>>
           qpat_abbrev_tac`frame = StackFrame lsz c d`>>
           `s_val_eq (frame::s.stack) (frame::xs)` by
             metis_tac[s_val_eq_def,s_frame_val_eq_def]>>
           drule s_val_eq_stack_size >> strip_tac >> fs [] >>
           IMP_RES_TAC s_val_eq_LASTN_exists>>
           `LENGTH s.stack = LENGTH xs` by full_simp_tac(srw_ss())[s_val_eq_length] >>
           first_x_assum(qspec_then`frame::xs` assume_tac)>>rev_full_simp_tac(srw_ss())[]>>
           first_x_assum(qspecl_then [`frame::xs`,`e'`,`ls'`] assume_tac)>>rev_full_simp_tac(srw_ss())[]>>
           `LENGTH s.stack +1 = LENGTH (frame::s.stack) /\
            LENGTH s.stack +1 = LENGTH (frame::xs)` by
              full_simp_tac(srw_ss())[arithmeticTheory.ADD1,s_val_eq_length]>>
            full_simp_tac(srw_ss())[LASTN_LENGTH_cond]>>
            `MAP FST lss = MAP FST lss'` by metis_tac[EQ_SYM_EQ]>>
            `lss = lss'` by full_simp_tac(srw_ss())[LIST_EQ_MAP_PAIR]>>
            pop_assum (SUBST1_TAC o SYM)>>
            full_simp_tac(srw_ss())[]>>
            first_x_assum(qspec_then `st` assume_tac)>>
            rev_full_simp_tac(srw_ss())[]>>
            metis_tac[handler_eq])>>
    (*Cleanup...*)
    ntac 2 strip_tac>>
    assume_tac get_vars_stack_swap_simp>>
    first_x_assum(qspec_then `args` SUBST1_TAC)>>simp[]>>
    `!a. s_val_eq (a::s.stack) (a::xs)` by
       (strip_tac >> fs [s_val_eq_def] >> Cases_on `a` >>
        rename1 `StackFrame n vs excp` >> Cases_on `excp` >>
        fs [s_frame_val_eq_def]) >>
     Cases_on`handler`>> TRY(PairCases_on`x''`)>>
     fs [push_env_def,LET_THM,env_to_list_def,dec_clock_def]>>
     qpat_abbrev_tac `frame = StackFrame lsz ls n`>>
     first_x_assum (qspec_then `frame` assume_tac)>>
     first_x_assum(qspec_then `frame::xs` assume_tac)>>
     drule s_val_eq_stack_size >> strip_tac >> fs [] >>
     rfs [call_env_def,flush_state_def] >>
     `LENGTH xs = LENGTH s.stack` by full_simp_tac(srw_ss())[s_val_eq_length]>> full_simp_tac(srw_ss())[]
QED


(*--Stack Swap Lemma DONE--*)

(*--Permute Swap Lemma--*)

val ignore_inc = Q.prove(`
  ∀perm:num->num->num.
  (λn. perm(n+0)) = perm`,srw_tac[][FUN_EQ_THM]);

val ignore_perm = Q.prove(`
  ∀st. st with permute := st.permute = st` ,
  srw_tac[][]>>full_simp_tac(srw_ss())[state_component_equality]);

Theorem get_vars_perm:
    ∀args.get_vars args (st with permute:=perm) = get_vars args st
Proof
  Induct>>srw_tac[][get_vars_def,get_var_def]
QED

Theorem pop_env_perm:
    pop_env (rst with permute:=perm) =
  (case pop_env rst of
    NONE => NONE
  | SOME rst' => SOME (rst' with permute:=perm))
Proof
  full_simp_tac(srw_ss())[pop_env_def]>>every_case_tac>>
  full_simp_tac(srw_ss())[state_component_equality]
QED

val gc_perm = Q.prove(`
  gc st = SOME x ⇒
  gc (st with permute:=perm) = SOME (x with permute := perm)`,
  full_simp_tac(srw_ss())[gc_def,LET_THM]>>every_case_tac>>
  full_simp_tac(srw_ss())[state_component_equality]);

Theorem get_var_perm:
    get_var n (st with permute:=perm) =
  (get_var n st)
Proof
full_simp_tac(srw_ss())[get_var_def]
QED

Theorem get_fp_var_perm:
    get_fp_var n (st with permute:=perm) =
  (get_fp_var n st)
Proof
full_simp_tac(srw_ss())[get_fp_var_def]
QED

Theorem get_var_imm_perm:
    get_var_imm n (st with permute:=perm) =
  (get_var_imm n st)
Proof
  Cases_on`n`>>
  fs[get_var_imm_def]
QED

Theorem set_var_perm[simp]:
    set_var v x (s with permute:=perm) =
  (set_var v x s) with permute:=perm
Proof
  full_simp_tac(srw_ss())[set_var_def]
QED

Theorem set_fp_var_perm:
    set_fp_var v x (s with permute:=perm) =
  (set_fp_var v x s) with permute:=perm
Proof
  full_simp_tac(srw_ss())[set_fp_var_def]
QED

val get_vars_perm = Q.prove(`
  ∀ls. get_vars ls (st with permute:=perm) =
  (get_vars ls st)`,
  Induct>>full_simp_tac(srw_ss())[get_vars_def,get_var_perm]);

Theorem set_vars_perm[simp]:
    ∀ls. set_vars ls x (st with permute := perm) =
       (set_vars ls x st) with permute:=perm
Proof
  full_simp_tac(srw_ss())[set_vars_def]
QED

val word_state_rewrites = Q.prove(`
  (st with clock:=A) with permute:=B =
  (st with <|clock:=A ;permute:=B|>)`,
  full_simp_tac(srw_ss())[]);

val perm_assum_tac = (first_x_assum(qspec_then`perm`assume_tac)>>
          full_simp_tac(srw_ss())[dec_clock_def,push_env_def,env_to_list_def,LET_THM]>>
          qexists_tac`λx. if x = 0 then st.permute 0 else perm' (x-1)`>>
          full_simp_tac(srw_ss())[call_env_def]>>
          `(λn. perm' n) = perm'` by full_simp_tac(srw_ss())[FUN_EQ_THM]>>
          simp[]);

Theorem word_exp_perm[simp]:
    ∀s exp. word_exp (s with permute:=perm) exp =
          word_exp s exp
Proof
  ho_match_mp_tac word_exp_ind>>srw_tac[][word_exp_def]
  >-
    (every_case_tac>>full_simp_tac(srw_ss())[mem_load_def])
  >>
    qpat_abbrev_tac`ls = MAP A B`>>
    qpat_abbrev_tac`ls' = MAP A B`>>
    `ls = ls'` by
      (unabbrev_all_tac>>fs[MAP_EQ_f])>> fs[]
QED

val mem_store_perm = Q.prove(`
  mem_store a (w:'a word_loc) (s with permute:=perm) =
  case mem_store a w s of
    NONE => NONE
  | SOME x => SOME(x with permute:=perm)`,
  full_simp_tac(srw_ss())[mem_store_def]>>every_case_tac>>
  full_simp_tac(srw_ss())[state_component_equality]);

val jump_exc_perm = Q.prove(`
  jump_exc (st with permute:=perm) =
  case jump_exc st of
    NONE => NONE
  | SOME (x,l1,l2) => SOME (x with permute:=perm,l1,l2)`,
  full_simp_tac(srw_ss())[jump_exc_def]>>
  every_case_tac>>
  full_simp_tac(srw_ss())[state_component_equality]);

(*For any target result permute, we can find an initial permute such that the
  final permute is equal to the target *)
Theorem permute_swap_lemma:
    ∀prog st perm.
  let (res,rst) = evaluate(prog,st) in
    res ≠ SOME Error  (*Note: actually provable without this assum, but this is simpler*)
    ⇒
    ∃perm'. evaluate(prog,st with permute := perm') =
    (res,rst with permute:=perm)
Proof
  ho_match_mp_tac (evaluate_ind |> Q.SPEC`UNCURRY P` |> SIMP_RULE (srw_ss())[] |> Q.GEN`P`) >> srw_tac[][]>>full_simp_tac(srw_ss())[evaluate_def]
  >-
    metis_tac[ignore_perm]
  >-
    (full_simp_tac(srw_ss())[alloc_def]>>
    qexists_tac`λx. if x = 0 then st.permute 0 else perm (x-1)`>>
    fs[]>>
    full_case_tac>>full_case_tac>>full_simp_tac(srw_ss())[]
    >-
      (Cases_on`x`>>full_simp_tac(srw_ss())[])
    >>
    full_case_tac>>full_simp_tac(srw_ss())[]>>
    Cases_on`gc (push_env x NONE (set_store AllocSize (Word c) st))`>>
    fs[push_env_def,env_to_list_def,LET_THM,set_store_def]>>
    imp_res_tac gc_perm>>full_simp_tac(srw_ss())[pop_env_perm]>>
    ntac 3 (full_case_tac>>full_simp_tac(srw_ss())[])>>
    full_simp_tac(srw_ss())[has_space_def]>>
    IF_CASES_TAC>>
    full_simp_tac(srw_ss())[state_component_equality,FUN_EQ_THM,call_env_def,flush_state_def] >>
    metis_tac [])
  >-
    (qexists_tac`perm`>>fs[]>>
    ntac 2 (full_case_tac>>full_simp_tac(srw_ss())[])>>
    fs[])
  >-
    (qexists_tac`perm`>>
    fs[inst_def,assign_def,LET_THM]>>every_case_tac>>
    fs[mem_store_perm,mem_load_def]>>
    full_simp_tac(srw_ss())[set_var_perm,word_exp_perm,get_var_perm,mem_store_perm,mem_load_def,get_vars_perm,get_fp_var_perm,set_fp_var_perm]>>
    rfs[]>>fs[]>>rveq>>
    fs[state_component_equality])
  >-
    (fs[]>>
    every_case_tac>>fs[state_component_equality])
  >-
    (every_case_tac>>fs[state_component_equality])
  >-
    (fs[]>>every_case_tac>>fs[set_store_def,state_component_equality])
  >-
    (fs[]>>every_case_tac>>fs[set_store_def,state_component_equality])
  >-
    (fs[]>>every_case_tac>>fs[set_store_def,state_component_equality,mem_store_perm])
  >-
    (qexists_tac`perm`>>
    every_case_tac>>full_simp_tac(srw_ss())[dec_clock_def,call_env_def,flush_state_def]>>
    full_simp_tac(srw_ss())[state_component_equality])
  >- (*MustTerminate*)
    (full_simp_tac(srw_ss())[LET_THM]>>
    qpat_x_assum`A=(res,rst)` mp_tac>>
    TOP_CASE_TAC>>simp[]>>
    pairarg_tac>>simp[]>>
    TOP_CASE_TAC>>simp[]>>srw_tac[][]>>
    first_x_assum(qspec_then`perm` assume_tac)>>full_simp_tac(srw_ss())[]>>
    pairarg_tac>>full_simp_tac(srw_ss())[]>>rev_full_simp_tac(srw_ss())[]>>
    qexists_tac`perm'`>>simp[])
  >- (*Seq*)
    (full_simp_tac(srw_ss())[evaluate_def,LET_THM]>>
    Cases_on`evaluate(prog,st)`>>full_simp_tac(srw_ss())[]>>
    Cases_on`q`>>full_simp_tac(srw_ss())[]
    >-
      (last_x_assum(qspec_then `perm` assume_tac)>>full_simp_tac(srw_ss())[]>>
      last_x_assum(qspec_then `perm'` assume_tac)>>full_simp_tac(srw_ss())[]>>
      qexists_tac`perm''`>>full_simp_tac(srw_ss())[])
    >>
      first_x_assum(qspecl_then[`perm`]assume_tac)>>rev_full_simp_tac(srw_ss())[]>>
      Cases_on`x`>>full_simp_tac(srw_ss())[]>>
      qexists_tac`perm'`>>full_simp_tac(srw_ss())[]>>
      qpat_x_assum`A=res`(SUBST1_TAC o SYM)>>full_simp_tac(srw_ss())[])
  >-
    (fs[]>>every_case_tac>>
    full_simp_tac(srw_ss())[call_env_def,flush_state_def,state_component_equality] >>
    metis_tac [])
  >-
    (fs[]>>every_case_tac>>
    full_simp_tac(srw_ss())[jump_exc_perm]>>metis_tac[state_component_equality])
  >-
    (Cases_on`ri`>>
    full_simp_tac(srw_ss())[get_var_imm_def]>>every_case_tac>>full_simp_tac(srw_ss())[]
    >>
      full_simp_tac(srw_ss())[LET_THM])
  >- (*LocValue*)
    (qexists_tac`perm`>>rw[]>>fs[set_var_def,state_component_equality])
  >- (*Install*)
    (qexists_tac`perm`>>fs[case_eq_thms,UNCURRY])
  >- (* CBW *)
    fs[case_eq_thms,state_component_equality]
  >- (* DBW *)
    fs[case_eq_thms,state_component_equality]
  >- (*FFI*)
    (qexists_tac`perm`>>
    full_simp_tac(srw_ss())[get_var_perm,call_env_def,flush_state_def]>>
    every_case_tac>>
    TRY(rename[`call_FFI st.ffi ffi_index conf bytes`] >>
        Cases_on`call_FFI st.ffi ffi_index conf bytes`) >>
    full_simp_tac(srw_ss())[LET_THM,state_component_equality])
  >- (*Call*)
    (fs[evaluate_def]>>
    ntac 6 (TOP_CASE_TAC>>full_simp_tac(srw_ss())[])
    >- (*Tail Call*)
      (every_case_tac>>
      TRY(qexists_tac`perm`>>
        full_simp_tac(srw_ss())[state_component_equality,call_env_def,flush_state_def]>>NO_TAC)
      (* >- (qexists_tac `perm` >> *)
      (*    fs [call_env_def,flush_state_def,state_component_equality] >> metis_tac []) *) >>
      Cases_on`x'`>> fs [dec_clock_def] >>
      first_x_assum(qspec_then `perm` assume_tac)>> fs [] >>
      qexists_tac `perm'` >> fs [state_component_equality,call_env_def,flush_state_def] >>
      TOP_CASE_TAC >> fs [state_component_equality])
    >>
      ntac 5 TOP_CASE_TAC>>full_simp_tac(srw_ss())[]>>
      ntac 2 (TOP_CASE_TAC>>full_simp_tac(srw_ss())[])
      >-
        (full_simp_tac(srw_ss())[call_env_def,flush_state_def]>>
        qexists_tac`perm`>>full_simp_tac(srw_ss())[state_component_equality]>>
        qpat_x_assum `0 = _` (assume_tac o GSYM) >>
        qpat_x_assum `SOME 0 = _` (assume_tac o GSYM) >>
        qpat_x_assum `[] = _` (assume_tac o GSYM) >>
        Cases_on `handler` >> fs[push_env_def,ELIM_UNCURRY,stack_size_eq] >>
        rename1 `push_env _ (SOME handler)` >>
        PairCases_on `handler` >>
        fs[push_env_def,ELIM_UNCURRY,stack_size_eq]
        )
      >>
      Cases_on `evaluate (q',call_env q r' (push_env x' handler (dec_clock st)))` >>
      rename1 `evaluate _ = (rtemp, r)` >>
      Cases_on`rtemp`>>full_simp_tac(srw_ss())[]>>
      rename1 `evaluate _ = (SOME rtemp, r)` >>
      Cases_on`rtemp`>>full_simp_tac(srw_ss())[]
      >-
       (qpat_x_assum`A=(res,rst)` mp_tac>>
        IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
        full_case_tac>>full_simp_tac(srw_ss())[]>>
        IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
        rename1 `evaluate (prog,set_var ntmp vtmp stmp)` >>
        Cases_on `evaluate (prog,set_var ntmp vtmp stmp)` >>
        rename1 `(prog', prgst )= (res,rst)` >>
        Cases_on`prog'` >>
        TRY(rename1 `(SOME restmp,prgst) = (res,rst)` >> Cases_on`restmp`)>>
        full_simp_tac(srw_ss())[]>>srw_tac[][]>>
        first_x_assum(qspec_then`perm`assume_tac)>>full_simp_tac(srw_ss())[]>>
        first_x_assum(qspec_then`perm'`assume_tac)>>full_simp_tac(srw_ss())[]>>
        qexists_tac`λx. if x = 0 then st.permute 0 else perm'' (x-1)`>>
        Cases_on`handler`>>
        TRY(rename1 `call_env _ _ (push_env _ (SOME stkf) (dec_clock _)) with
            permute := _` >> PairCases_on`stkf`)>>
        full_simp_tac(srw_ss())[dec_clock_def,push_env_def,env_to_list_def,LET_THM,call_env_def,flush_state_def]>>
        `(λn. perm'' n) = perm''` by full_simp_tac(srw_ss())[FUN_EQ_THM]>>
        full_simp_tac(srw_ss())[state_component_equality,call_env_def,flush_state_def]>>
        full_simp_tac(srw_ss())[pop_env_perm]>>full_simp_tac(srw_ss())[])
      >-
        (full_case_tac>>full_simp_tac(srw_ss())[]
        >-
          (perm_assum_tac>>
          qpat_x_assum`A=res` (SUBST1_TAC o SYM)>>full_simp_tac(srw_ss())[]) >>
        rename1 `evaluate (_,call_env _ _ (push_env _ (SOME stkf) (dec_clock _))) =
        (SOME (Exception _ _),_)` >>
        PairCases_on`stkf` >> full_simp_tac(srw_ss())[] >>
        qpat_x_assum `A=(res,rst)` mp_tac>>
        ntac 2 (IF_CASES_TAC>>full_simp_tac(srw_ss())[])>>
        srw_tac[][]>>
        Cases_on`res = SOME Error`>>full_simp_tac(srw_ss())[]>>
        first_x_assum(qspec_then`perm`assume_tac)>>full_simp_tac(srw_ss())[]>>
        first_x_assum(qspec_then`perm'`assume_tac) >> full_simp_tac(srw_ss())[]>>
        qexists_tac`λx. if x = 0 then st.permute 0 else perm'' (x-1)`>>
        full_simp_tac(srw_ss())[dec_clock_def,push_env_def,env_to_list_def,LET_THM]>>
        `(λn. perm'' n) = perm''` by full_simp_tac(srw_ss())[FUN_EQ_THM]>>
        full_simp_tac(srw_ss())[state_component_equality,call_env_def,flush_state_def]>>
        full_simp_tac(srw_ss())[]) >>
      perm_assum_tac >>
      Cases_on`handler` >>
      TRY (rename1 `evaluate (_, push_env _ (SOME stkf) _ with
           <|locals := _; locals_size := _; stack_max:= _; permute := _; clock := _|>)` >> PairCases_on`stkf`) >>
      full_simp_tac(srw_ss())[push_env_def,env_to_list_def,LET_THM,dec_clock_def]>>
      qpat_x_assum`A=res` (SUBST1_TAC o SYM)>>full_simp_tac(srw_ss())[])
QED

(*Monotonicity*)
Theorem every_var_inst_mono:
    ∀P inst Q.
  (∀x. P x ⇒ Q x) ∧
  every_var_inst P inst
  ⇒
  every_var_inst Q inst
Proof
  ho_match_mp_tac every_var_inst_ind>>srw_tac[][every_var_inst_def]>>
  Cases_on`ri`>>full_simp_tac(srw_ss())[every_var_imm_def]
QED

Theorem every_var_exp_mono:
    ∀P exp Q.
  (∀x. P x ⇒ Q x) ∧
  every_var_exp P exp
  ⇒
  every_var_exp Q exp
Proof
  ho_match_mp_tac every_var_exp_ind>>srw_tac[][every_var_exp_def]>>
  full_simp_tac(srw_ss())[EVERY_MEM]
QED

Theorem every_name_mono:
    ∀P names Q.
  (∀x. P x ⇒ Q x) ∧
  every_name P names ⇒ every_name Q names
Proof
  srw_tac[][every_name_def]>>
  metis_tac[EVERY_MONOTONIC]
QED

Theorem every_var_mono:
    ∀P prog Q.
  (∀x. P x ⇒ Q x) ∧
  every_var P prog
  ⇒
  every_var Q prog
Proof
  ho_match_mp_tac every_var_ind>>srw_tac[][every_var_def]>>
  TRY(Cases_on`ret`>>full_simp_tac(srw_ss())[]>>PairCases_on`x`>>Cases_on`h`>>full_simp_tac(srw_ss())[]>>TRY(Cases_on`x`)>>full_simp_tac(srw_ss())[])>>
  TRY(Cases_on`r`>>full_simp_tac(srw_ss())[])>>
  TRY(Cases_on`ri`>>full_simp_tac(srw_ss())[every_var_imm_def])>>
  metis_tac[EVERY_MONOTONIC,every_var_inst_mono,every_var_exp_mono,every_name_mono]
QED

(*Conjunct*)
Theorem every_var_inst_conj:
    ∀P inst Q.
  every_var_inst P inst ∧ every_var_inst Q inst ⇔
  every_var_inst (λx. P x ∧ Q x) inst
Proof
  ho_match_mp_tac every_var_inst_ind>>srw_tac[][every_var_inst_def]>>
  TRY(Cases_on`ri`>>full_simp_tac(srw_ss())[every_var_imm_def])>>
  metis_tac[]
QED

Theorem every_var_exp_conj:
    ∀P exp Q.
  every_var_exp P exp ∧ every_var_exp Q exp ⇔
  every_var_exp (λx. P x ∧ Q x) exp
Proof
  ho_match_mp_tac every_var_exp_ind>>srw_tac[][every_var_exp_def]>>
  full_simp_tac(srw_ss())[EVERY_MEM]>>
  metis_tac[]
QED

Theorem every_name_conj:
    ∀P names Q.
  every_name P names ∧ every_name Q names ⇔
  every_name (λx. P x ∧ Q x) names
Proof
  srw_tac[][every_name_def]>>
  metis_tac[EVERY_CONJ]
QED

Theorem every_var_conj:
    ∀P prog Q.
  every_var P prog  ∧ every_var Q prog ⇔
  every_var (λx. P x ∧ Q x) prog
Proof
  ho_match_mp_tac every_var_ind>>srw_tac[][every_var_def]>>
  TRY(Cases_on`ret`>>full_simp_tac(srw_ss())[])>>
  TRY(PairCases_on`x`>>Cases_on`h`>>full_simp_tac(srw_ss())[])>>
  TRY(Cases_on`x`>>full_simp_tac(srw_ss())[])>>
  TRY(Cases_on`r`>>full_simp_tac(srw_ss())[])>>
  TRY(Cases_on`ri`>>full_simp_tac(srw_ss())[every_var_imm_def])>>
  TRY(metis_tac[EVERY_CONJ,every_var_inst_conj,every_var_exp_conj,every_name_conj])
QED

(*Similar lemmas about every_stack_var*)
Theorem every_var_imp_every_stack_var:
    ∀P prog.
  every_var P prog ⇒ every_stack_var P prog
Proof
  ho_match_mp_tac every_stack_var_ind>>
  srw_tac[][every_stack_var_def,every_var_def]>>
  Cases_on`ret`>>
  Cases_on`h`>>full_simp_tac(srw_ss())[]>>
  PairCases_on`x`>>full_simp_tac(srw_ss())[]>>
  Cases_on`x'`>>Cases_on`r`>>full_simp_tac(srw_ss())[]
QED

Theorem every_stack_var_mono:
    ∀P prog Q.
  (∀x. P x ⇒ Q x) ∧
  every_stack_var P prog
  ⇒
  every_stack_var Q prog
Proof
  ho_match_mp_tac every_stack_var_ind>>srw_tac[][every_stack_var_def]>>
  TRY(Cases_on`ret`>>full_simp_tac(srw_ss())[]>>PairCases_on`x`>>Cases_on`h`>>full_simp_tac(srw_ss())[]>>TRY(Cases_on`x`>>Cases_on`r`>>full_simp_tac(srw_ss())[]))>>
  metis_tac[every_name_mono]
QED

Theorem every_stack_var_conj:
    ∀P prog Q.
  every_stack_var P prog  ∧ every_stack_var Q prog ⇔
  every_stack_var (λx. P x ∧ Q x) prog
Proof
  ho_match_mp_tac every_stack_var_ind>>srw_tac[][every_stack_var_def]>>
  TRY(Cases_on`ret`>>full_simp_tac(srw_ss())[])>>
  TRY(PairCases_on`x`>>Cases_on`h`>>full_simp_tac(srw_ss())[])>>
  TRY(Cases_on`x`>>Cases_on`r`>>full_simp_tac(srw_ss())[])>>
  TRY(metis_tac[EVERY_CONJ,every_name_conj])
QED

(* Locals extend lemma *)
val locals_rel_def = Define`
  locals_rel temp (s:'a word_loc num_map) t ⇔ (∀x. x < temp ⇒ lookup x s = lookup x t)`

Theorem the_words_EVERY_IS_SOME:
   ∀ls x.
  the_words ls = SOME x ⇒
  EVERY IS_SOME ls
Proof
  Induct>>fs[]>>Cases>>fs[the_words_def]>>
  TOP_CASE_TAC>>fs[]>>
  TOP_CASE_TAC>>fs[]
QED

Theorem locals_rel_word_exp:
  ∀s exp w.
    every_var_exp (λx. x < temp) exp ∧
    word_exp s exp = SOME w ∧
    locals_rel temp s.locals loc ⇒
    word_exp (s with locals:=loc) exp = SOME w
Proof
  ho_match_mp_tac word_exp_ind>>srw_tac[][]>>
  full_simp_tac(srw_ss())[word_exp_def,every_var_exp_def,locals_rel_def]
  >-
    (every_case_tac>>
    res_tac>>full_simp_tac(srw_ss())[])
  >-
    (qpat_x_assum`A= SOME w` mp_tac>>full_case_tac>>full_simp_tac(srw_ss())[mem_load_def])
  >-
    (qpat_x_assum`A= SOME w` mp_tac>>
    qpat_abbrev_tac`ls = MAP A B`>>
    qpat_abbrev_tac`ls' = MAP A B`>>
    TOP_CASE_TAC>>rw[]>>
    `ls = ls'` by
      (imp_res_tac the_words_EVERY_IS_SOME>>
      unabbrev_all_tac>>fs[MAP_EQ_f]>>
      fs[EVERY_MAP,EVERY_MEM]>>
      rw[]>>res_tac>>
      fs[IS_SOME_EXISTS])>>
    fs[])
  >>
    every_case_tac>>res_tac>>full_simp_tac(srw_ss())[]
QED

Theorem locals_rel_get_vars:
    ∀ls vs.
  get_vars ls st = SOME vs ∧
  EVERY (λx. x < temp) ls ∧
  locals_rel temp st.locals loc ⇒
  get_vars ls (st with locals:= loc) = SOME vs
Proof
  Induct>>full_simp_tac(srw_ss())[get_vars_def]>>srw_tac[][]>>
  qpat_x_assum`A=SOME vs` mp_tac>>ntac 2 full_case_tac>>srw_tac[][]>>
  res_tac>>full_simp_tac(srw_ss())[get_var_def,locals_rel_def]>>
  res_tac>>
  full_simp_tac(srw_ss())[]
QED

Theorem locals_rel_alist_insert:
    ∀ls vs s t.
  locals_rel temp s t ∧
  EVERY (λx. x < temp) ls ⇒
  locals_rel temp (alist_insert ls vs s) (alist_insert ls vs t)
Proof
  ho_match_mp_tac alist_insert_ind>>full_simp_tac(srw_ss())[alist_insert_def,locals_rel_def]>>
  srw_tac[][]>>
  Cases_on`x'=ls`>>full_simp_tac(srw_ss())[lookup_insert]
QED

Theorem locals_rel_get_var:
    r < temp ∧
  get_var r st = SOME x ∧
  locals_rel temp st.locals loc ⇒
  get_var r (st with locals:=loc) = SOME x
Proof
  full_simp_tac(srw_ss())[get_var_def,locals_rel_def]>>
  metis_tac[]
QED

Theorem locals_rel_get_var_imm:
    every_var_imm (λx.x<temp) r ∧
  get_var_imm r st = SOME x ∧
  locals_rel temp st.locals loc ⇒
  get_var_imm r (st with locals:=loc) = SOME x
Proof
  Cases_on`r`>>full_simp_tac(srw_ss())[get_var_imm_def,every_var_imm_def]>>
  metis_tac[locals_rel_get_var]
QED

val locals_rel_set_var = Q.prove(`
  ∀n s t.
  locals_rel temp s t ⇒
  locals_rel temp (insert n v s) (insert n v t)`,
  srw_tac[][]>>full_simp_tac(srw_ss())[locals_rel_def,lookup_insert]);

val locals_rel_cut_env = Q.prove(`
  locals_rel temp loc loc' ∧
  every_name (λx. x < temp) names ∧
  cut_env names loc = SOME x ⇒
  cut_env names loc' = SOME x`,
  srw_tac[][locals_rel_def,cut_env_def,SUBSET_DEF,every_name_def]>>
  full_simp_tac(srw_ss())[EVERY_MEM,toAList_domain]
  >- metis_tac[domain_lookup]
  >>
  full_simp_tac(srw_ss())[lookup_inter]>>srw_tac[][]>>every_case_tac>>
  full_simp_tac(srw_ss())[domain_lookup]>>res_tac>>
  metis_tac[option_CLAUSES]);

(*Extra temporaries not mentioned in program
  do not affect evaluation*)

val srestac = qpat_x_assum`A=res`sym_sub_tac>>full_simp_tac(srw_ss())[];

Theorem locals_rel_evaluate_thm:
  ∀prog st res rst loc temp.
    evaluate (prog,st) = (res,rst) ∧
    res ≠ SOME Error ∧
    every_var (λx.x < temp) prog ∧
    locals_rel temp st.locals loc ⇒
    ∃loc'.
      evaluate (prog,st with locals:=loc) = (res,rst with locals:=loc') ∧
      case res of
      | NONE => locals_rel temp rst.locals loc'
      | SOME _ => rst.locals = loc'
Proof
  completeInduct_on`prog_size (K 0) prog`>>
  rpt strip_tac>>
  Cases_on`prog`>>
  full_simp_tac(srw_ss())[evaluate_def,LET_THM]
  >-
    (srestac>>metis_tac[])
  >-
    (qpat_x_assum `A = (res,rst)` mp_tac>> ntac 2 full_case_tac>>
    full_simp_tac(srw_ss())[every_var_def]>>
    imp_res_tac locals_rel_get_vars>>
    full_simp_tac(srw_ss())[set_vars_def]>>imp_res_tac locals_rel_alist_insert>>
    full_simp_tac(srw_ss())[state_component_equality]>>
    srw_tac[][]>>full_simp_tac(srw_ss())[]>>metis_tac[])
  >-
    (Cases_on`i`>>full_simp_tac(srw_ss())[inst_def,every_var_def,every_var_inst_def]
    >-
      (srestac>>metis_tac[])
    >-
      (full_simp_tac(srw_ss())[assign_def,word_exp_def,set_var_def]>>
      imp_res_tac locals_rel_set_var>>
      full_simp_tac(srw_ss())[state_component_equality]>>
      srestac>>metis_tac[])
    >-
      (reverse (Cases_on`a`)>>fs[assign_def,LET_THM]>>
      qpat_x_assum`A=(res,rst)` mp_tac>>
      TRY (* everything not special*)
        (qpat_abbrev_tac`ls = A:num list`>>
        FULL_CASE_TAC>>fs[]>>
        imp_res_tac locals_rel_get_vars>>fs[every_var_inst_def]>>
        unabbrev_all_tac>>fs[]>>
        EVERY_CASE_TAC>>rw[]>>
        fs[locals_rel_set_var,state_component_equality,set_var_def])
      >>
      qpat_abbrev_tac`A = word_exp B C`>>
      Cases_on`A`>>full_simp_tac(srw_ss())[markerTheory.Abbrev_def]>>srw_tac[][]>>
      pop_assum (assume_tac o SYM)>>
      imp_res_tac locals_rel_word_exp>>
      full_simp_tac(srw_ss())[every_var_exp_def,every_var_inst_def]>>
      TRY(Cases_on`r`)>>rev_full_simp_tac(srw_ss())[every_var_exp_def,every_var_imm_def]>>
      full_simp_tac(srw_ss())[set_var_def]>>
      metis_tac[locals_rel_set_var])
    >-
      (Cases_on`a`>>Cases_on`m`>>full_simp_tac(srw_ss())[assign_def]>>
      qpat_x_assum`A=(res,rst)` mp_tac>>
      qpat_abbrev_tac`A = word_exp B C`>>
      Cases_on`A`>>full_simp_tac(srw_ss())[markerTheory.Abbrev_def]>>
      TRY (ntac 2 full_case_tac>>full_simp_tac(srw_ss())[])>>
      srw_tac[][]>>
      TRY(qpat_x_assum `SOME A = B` (assume_tac o SYM))>>
      imp_res_tac locals_rel_word_exp>>
      imp_res_tac locals_rel_get_var>>
      full_simp_tac(srw_ss())[every_var_exp_def,every_var_inst_def]>>
      rev_full_simp_tac(srw_ss())[every_var_exp_def,every_var_imm_def]>>
      full_simp_tac(srw_ss())[set_var_def,mem_store_def,mem_load_def]>>
      full_simp_tac(srw_ss())[state_component_equality]>>
      EVERY_CASE_TAC>>fs[state_component_equality]>>
      metis_tac[locals_rel_set_var])
    >-
      (Cases_on`f`>>fs[get_fp_var_def]>>every_case_tac>>
      fs[set_var_def,set_fp_var_def,every_var_inst_def]>>
      imp_res_tac locals_rel_get_var>>
      rw[]>>fs[]>>
      metis_tac[locals_rel_set_var]))
  >-
    (every_case_tac>>imp_res_tac locals_rel_word_exp>>full_simp_tac(srw_ss())[every_var_def]>>
    rev_full_simp_tac(srw_ss())[state_component_equality,set_var_def]>>
    qpat_x_assum`A=rst.locals` sym_sub_tac>>
    metis_tac[locals_rel_set_var])
  >-
    (every_case_tac>>full_simp_tac(srw_ss())[set_var_def,state_component_equality,set_var_def]>>
    metis_tac[locals_rel_set_var])
  >-
    (every_case_tac>>imp_res_tac locals_rel_word_exp>>full_simp_tac(srw_ss())[every_var_def]>>
    rev_full_simp_tac(srw_ss())[state_component_equality,set_store_def]>>
    metis_tac[locals_rel_set_var])
  >-
    (every_case_tac>>imp_res_tac locals_rel_word_exp>>full_simp_tac(srw_ss())[every_var_def]>>
    imp_res_tac locals_rel_get_var>>full_simp_tac(srw_ss())[]>>
    rev_full_simp_tac(srw_ss())[state_component_equality,mem_store_def]>>
    metis_tac[])
  >-
    (full_simp_tac(srw_ss())[PULL_FORALL,GSYM AND_IMP_INTRO]>>
    qpat_x_assum`A=(res,rst)` mp_tac>>
    IF_CASES_TAC>>simp[]>>
    pairarg_tac>>simp[]>>
    IF_CASES_TAC>>simp[]>>
    first_x_assum(qspec_then`p` mp_tac)>>
    simp[prog_size_def]>>srw_tac[][]>>full_simp_tac(srw_ss())[every_var_def]>>
    res_tac>>full_simp_tac(srw_ss())[]>>
    first_x_assum(qspec_then`loc` mp_tac)>>
    pop_assum kall_tac>>
    simp[]>>strip_tac>>
    simp[]>>
    metis_tac[])
  >-
    (*Call*)
    (Cases_on`get_vars l st`>>full_simp_tac(srw_ss())[every_var_def]>>
    imp_res_tac locals_rel_get_vars>>full_simp_tac(srw_ss())[]>>
    IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
    Cases_on`find_code o1 (add_ret_loc o' x) st.code st.stack_size`>>
    TRY(PairCases_on`x'`)>>full_simp_tac(srw_ss())[]>>
    Cases_on`o'`>>full_simp_tac(srw_ss())[]
    >-(*Tail Call*)
      (full_simp_tac(srw_ss())[call_env_def,flush_state_def,dec_clock_def]>>
      IF_CASES_TAC>>full_simp_tac(srw_ss())[state_component_equality,locals_rel_def]>>
      CASE_TAC>>full_simp_tac(srw_ss())[])
    >>
      PairCases_on`x'`>>full_simp_tac(srw_ss())[]>>
      IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
      qmatch_assum_rename_tac`domain x1 <> {}` >>
      Cases_on`cut_env x1 st.locals`>>full_simp_tac(srw_ss())[]>>
      imp_res_tac locals_rel_cut_env>>full_simp_tac(srw_ss())[]>>
      IF_CASES_TAC>-
        (full_simp_tac(srw_ss())[call_env_def,flush_state_def,state_component_equality,locals_rel_def]>>
        CASE_TAC>>full_simp_tac(srw_ss())[] >> metis_tac [])
      >>
      full_simp_tac(srw_ss())[]>>qpat_x_assum`A=(res,rst)` mp_tac>>
      qpat_abbrev_tac`st = call_env B SS C`>>
      qpat_abbrev_tac`st' = call_env B SS C`>>
      `st' = st''` by
        (unabbrev_all_tac>>
        Cases_on`o0`>>TRY(PairCases_on`x''`)>>
        full_simp_tac(srw_ss())[call_env_def,flush_state_def,push_env_def,dec_clock_def,push_env_def,LET_THM,env_to_list_def,state_component_equality])>>
      every_case_tac>>srw_tac[][]>>
      full_simp_tac(srw_ss())[state_component_equality,locals_rel_def])
  >-
    (full_simp_tac(srw_ss())[PULL_FORALL,GSYM AND_IMP_INTRO]>>Cases_on`evaluate (p,st)`>>full_simp_tac(srw_ss())[]>>
    first_assum(qspec_then`p` mp_tac)>>
    first_x_assum(qspec_then`p0` mp_tac)>>
    `q ≠ SOME Error` by (every_case_tac >> full_simp_tac(srw_ss())[])>>
    simp[prog_size_def]>>srw_tac[][]>>full_simp_tac(srw_ss())[every_var_def]>>res_tac>>
    simp[]>>IF_CASES_TAC>>full_simp_tac(srw_ss())[state_component_equality]>>
    res_tac>>
    first_x_assum(qspec_then`loc` assume_tac)>>rev_full_simp_tac(srw_ss())[locals_rel_def])
  >-
    (full_simp_tac(srw_ss())[PULL_FORALL,GSYM AND_IMP_INTRO]>>
    qpat_x_assum`A=(res,rst)`mp_tac >> ntac 4 (full_case_tac>>full_simp_tac(srw_ss())[])>>
    IF_CASES_TAC>>srw_tac[][]>>
    imp_res_tac locals_rel_get_var>>imp_res_tac locals_rel_get_var_imm>>
    full_simp_tac(srw_ss())[every_var_def]>>rev_full_simp_tac(srw_ss())[]
    >-
      (first_x_assum(qspec_then`p`mp_tac)>>full_simp_tac(srw_ss())[GSYM PULL_FORALL]>>
      impl_tac>- (full_simp_tac(srw_ss())[prog_size_def]>>DECIDE_TAC)>>strip_tac>>
      res_tac>>full_simp_tac(srw_ss())[])
    >>
      (first_x_assum(qspec_then`p0`mp_tac)>>full_simp_tac(srw_ss())[GSYM PULL_FORALL]>>
      impl_tac>- (full_simp_tac(srw_ss())[prog_size_def]>>DECIDE_TAC)>>strip_tac>>
      res_tac>>full_simp_tac(srw_ss())[]))
  >-
    (*alloc*)
    (every_case_tac>>imp_res_tac locals_rel_get_var>>rev_full_simp_tac(srw_ss())[every_var_def]>>
    full_simp_tac(srw_ss())[alloc_def]>>qpat_x_assum`A=(res,rst)` mp_tac>>
    ntac 6 (full_case_tac>>full_simp_tac(srw_ss())[])>>srw_tac[][]>>
    imp_res_tac locals_rel_cut_env>>
    full_simp_tac(srw_ss())[]>>
    qpat_x_assum` A = SOME x'` mp_tac>>
    full_simp_tac(srw_ss())[push_env_def,set_store_def,LET_THM,env_to_list_def,gc_def]>>
    full_case_tac>>TRY(PairCases_on`x''`)>>TRY(PairCases_on`x''''`)>>
    full_simp_tac(srw_ss())[]>>full_case_tac>>full_simp_tac(srw_ss())[pop_env_def]>>srw_tac[][]>>
    full_simp_tac(srw_ss())[state_component_equality,locals_rel_def]>>
    CASE_TAC>>full_simp_tac(srw_ss())[call_env_def,flush_state_def]>>
    CASE_TAC>>full_simp_tac(srw_ss())[call_env_def,flush_state_def]>>
    qpat_x_assum`A=x''` sym_sub_tac>>full_simp_tac(srw_ss())[])
  >-
    (every_case_tac>>imp_res_tac locals_rel_get_var>>rev_full_simp_tac(srw_ss())[every_var_def]>>
    full_simp_tac(srw_ss())[jump_exc_def,state_component_equality,locals_rel_def]>>
    metis_tac[])
  >-
    (every_case_tac>>imp_res_tac locals_rel_get_var>>rev_full_simp_tac(srw_ss())[every_var_def]>>
    full_simp_tac(srw_ss())[call_env_def,flush_state_def,state_component_equality,locals_rel_def] >> metis_tac [])
  >-
    (IF_CASES_TAC>>full_simp_tac(srw_ss())[call_env_def,flush_state_def,state_component_equality,dec_clock_def]>>
    srestac>>full_simp_tac(srw_ss())[]>>metis_tac[])
  >-
    (gvs[every_var_def,word_exp_def,AllCaseEqs(),the_words_def]>>
     fs [PULL_EXISTS,state_component_equality,set_var_def] >>
     imp_res_tac locals_rel_get_var>>
     fs [get_var_def] \\ res_tac \\ fs [] >>
     fs [locals_rel_def,lookup_insert])
  >-
    (rw[]>>fs[set_var_def,state_component_equality]>>rveq>>fs[]>>
    qpat_x_assum`A=rst.locals` sym_sub_tac>>
    metis_tac[locals_rel_set_var])
  >- (* Install *)
    (fs[case_eq_thms,UNCURRY,every_var_def]>>rw[]>>
    imp_res_tac locals_rel_cut_env>>
    imp_res_tac locals_rel_get_var>>fs[state_component_equality]>>
    match_mp_tac locals_rel_set_var>>
    fs[locals_rel_def])
  >-
    (fs[case_eq_thms,every_var_def]>>rw[]>>
    imp_res_tac locals_rel_get_var>>fs[state_component_equality])
  >-
    (fs[case_eq_thms,every_var_def]>>rw[]>>
    imp_res_tac locals_rel_get_var>>fs[state_component_equality])
  >-
    (qpat_x_assum `A = (res,rst)` mp_tac>> ntac 5 full_case_tac>>
    full_simp_tac(srw_ss())[every_var_def]>>
    imp_res_tac locals_rel_get_var>>imp_res_tac locals_rel_cut_env>>
    fs[call_env_def,flush_state_def]>>
    full_case_tac>>fs[state_component_equality,locals_rel_def]>>
    full_case_tac>>fs[state_component_equality,locals_rel_def]>>
    full_case_tac>>fs[state_component_equality,locals_rel_def]>>
    full_case_tac>>fs[state_component_equality,locals_rel_def]>>
    full_case_tac>>fs[state_component_equality,locals_rel_def]>>
    full_case_tac>>fs[state_component_equality,locals_rel_def]>>
    fs[pairTheory.ELIM_UNCURRY] >> rpt strip_tac >> rveq >> fs[case_eq_thms] >>
    rveq >> fs[case_eq_thms,state_component_equality])
QED

val gc_fun_ok_def = Define `
  gc_fun_ok (f:'a gc_fun_type) =
    !wl m d s wl1 m1 s1.
      Handler IN FDOM s /\
      (f (wl,m,d,s \\ Handler) = SOME (wl1,m1,s1)) ==>
      (LENGTH wl = LENGTH wl1) /\
      ~(Handler IN FDOM s1) /\
      (f (wl,m,d,s) = SOME (wl1,m1,s1 |+ (Handler,s ' Handler)))`

(* wordLang syntactic things, TODO: not updated for install,cbw,dbw *)
(* No expressions occur except in Set, where it must be a Var expr *)
val flat_exp_conventions_def = Define`
  (*These should be converted to Insts*)
  (flat_exp_conventions (Assign v exp) ⇔ F) ∧
  (flat_exp_conventions (Store exp num) ⇔ F) ∧
  (*The only place where top level (expression) vars are allowed*)
  (flat_exp_conventions (Set store_name (Var r)) ⇔ T) ∧
  (flat_exp_conventions (Set store_name _) ⇔ F) ∧
  (flat_exp_conventions (Seq p1 p2) ⇔
    flat_exp_conventions p1 ∧ flat_exp_conventions p2) ∧
  (flat_exp_conventions (If cmp r1 ri e2 e3) ⇔
    flat_exp_conventions e2 ∧ flat_exp_conventions e3) ∧
  (flat_exp_conventions (MustTerminate p) ⇔ flat_exp_conventions p) ∧
  (flat_exp_conventions (Call ret dest args h) ⇔
    ((case ret of
      NONE => T
    | SOME (v,cutset,ret_handler,l1,l2) =>
        flat_exp_conventions ret_handler) ∧
    (case h of
      NONE => T
    | SOME (v,prog,l1,l2) => flat_exp_conventions prog))) ∧
  (flat_exp_conventions _ ⇔ T)`

(* Well-formed instructions
  This also includes the FP conditions since we do not allocate them
*)
val inst_ok_less_def = Define`
  (inst_ok_less (c:'a asm_config) (Arith (Binop b r1 r2 (Imm w))) ⇔
    c.valid_imm (INL b) w) ∧
  (inst_ok_less c (Arith (Shift l r1 r2 n)) ⇔
    (((n = 0) ==> (l = Lsl)) ∧ n < dimindex(:'a))) ∧
  (inst_ok_less c (Arith (Shift l r1 r2 n)) ⇔
    (((n = 0) ==> (l = Lsl)) ∧ n < dimindex(:'a))) ∧
  (inst_ok_less c (Arith (Div r1 r2 r3)) ⇔
    (c.ISA ∈ {ARMv8; MIPS; RISC_V})) ∧
  (inst_ok_less c (Arith (LongMul r1 r2 r3 r4)) ⇔
    ((c.ISA = ARMv7 ⇒ r1 ≠ r2) ∧
    (c.ISA = ARMv8 ∨ c.ISA = RISC_V ∨ c.ISA = Ag32 ⇒ r1 ≠ r3 ∧ r1 ≠ r4))) ∧
  (inst_ok_less c (Arith (LongDiv r1 r2 r3 r4 r5)) =
    (c.ISA = x86_64)) ∧
  (inst_ok_less c (Arith (AddCarry r1 r2 r3 r4)) ⇔
    (((c.ISA = MIPS) \/ (c.ISA = RISC_V)) ==> r1 ≠ r3  ∧ r1 ≠ r4)) ∧
  (inst_ok_less c (Arith (AddOverflow r1 r2 r3 r4)) ⇔
    (((c.ISA = MIPS) \/ (c.ISA = RISC_V)) ==> r1 ≠ r3)) ∧
  (inst_ok_less c (Arith (SubOverflow r1 r2 r3 r4)) ⇔
    (((c.ISA = MIPS) \/ (c.ISA = RISC_V)) ==> r1 ≠ r3)) ∧
  (inst_ok_less c (Mem m r (Addr r' w)) ⇔
    if m IN {Load; Store} then addr_offset_ok c w else byte_offset_ok c w) ∧
  (inst_ok_less c (FP (FPLess r d1 d2)) ⇔  fp_reg_ok d1 c ∧ fp_reg_ok d2 c) ∧
  (inst_ok_less c (FP (FPLessEqual r d1 d2)) ⇔ fp_reg_ok d1 c  ∧ fp_reg_ok d2 c) ∧
  (inst_ok_less c (FP (FPEqual r d1 d2)) ⇔ fp_reg_ok d1 c  ∧ fp_reg_ok d2 c)  ∧
  (inst_ok_less c (FP (FPAbs d1 d2)) ⇔
    (c.two_reg_arith ==> (d1 <> d2)) ∧ fp_reg_ok d1 c  ∧ fp_reg_ok d2 c) ∧
  (inst_ok_less c (FP (FPNeg d1 d2)) ⇔
    (c.two_reg_arith ==> (d1 <> d2)) ∧ fp_reg_ok d1 c  ∧ fp_reg_ok d2 c) ∧
  (inst_ok_less c (FP (FPSqrt d1 d2)) ⇔ fp_reg_ok d1 c  ∧ fp_reg_ok d2 c) ∧
  (inst_ok_less c (FP (FPAdd d1 d2 d3)) ⇔
    (c.two_reg_arith ==> (d1 = d2)) ∧
    fp_reg_ok d1 c  ∧ fp_reg_ok d2 c ∧ fp_reg_ok d3 c) ∧
  (inst_ok_less c (FP (FPSub d1 d2 d3)) ⇔
    (c.two_reg_arith ==> (d1 = d2)) ∧
    fp_reg_ok d1 c  ∧ fp_reg_ok d2 c  ∧ fp_reg_ok d3 c) ∧
  (inst_ok_less c (FP (FPMul d1 d2 d3)) ⇔
    (c.two_reg_arith ==> (d1 = d2)) ∧
    fp_reg_ok d1 c  ∧ fp_reg_ok d2 c  ∧ fp_reg_ok d3 c) ∧
  (inst_ok_less c (FP (FPDiv d1 d2 d3)) ⇔
    (c.two_reg_arith ==> (d1 = d2)) ∧
    fp_reg_ok d1 c  ∧ fp_reg_ok d2 c  ∧ fp_reg_ok d3 c) ∧
  (inst_ok_less c (FP (FPFma d1 d2 d3)) <=>
    (c.ISA = ARMv7) /\
    2 < c.fp_reg_count /\
    fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c) /\
  (inst_ok_less c (FP (FPMov d1 d2)) ⇔ fp_reg_ok d1 c  ∧ fp_reg_ok d2 c) ∧
  (inst_ok_less c (FP (FPMovToReg r1 r2 d)) ⇔
      ((dimindex(:'a) = 32) ==> r1 <> r2) ∧ fp_reg_ok d c) ∧
  (inst_ok_less c (FP (FPMovFromReg d r1 r2)) ⇔
      ((dimindex(:'a) = 32) ==> r1 <> r2) ∧ fp_reg_ok d c) ∧
  (inst_ok_less c (FP (FPToInt d1 d2)) ⇔ fp_reg_ok d1 c  ∧ fp_reg_ok d2 c) ∧
  (inst_ok_less c (FP (FPFromInt d1 d2)) ⇔ fp_reg_ok d1 c  ∧ fp_reg_ok d2 c) ∧
  (inst_ok_less _ _ = T)`

(* Instructions have distinct targets and read vars -- set by SSA form *)
val distinct_tar_reg_def = Define`
  (distinct_tar_reg (Arith (Binop bop r1 r2 ri))
    ⇔ (r1 ≠ r2 ∧ case ri of (Reg r3) => r1 ≠ r3 | _ => T)) ∧
  (distinct_tar_reg  (Arith (Shift l r1 r2 n))
    ⇔ r1 ≠ r2) ∧
  (distinct_tar_reg (Arith (AddCarry r1 r2 r3 r4))
    ⇔ r1 ≠ r2 ∧ r1 ≠ r3 ∧ r1 ≠ r4) ∧
  (distinct_tar_reg (Arith (AddOverflow r1 r2 r3 r4))
    ⇔ r1 ≠ r2 ∧ r1 ≠ r3 ∧ r1 ≠ r4) ∧
  (distinct_tar_reg (Arith (SubOverflow r1 r2 r3 r4))
    ⇔ r1 ≠ r2 ∧ r1 ≠ r3 ∧ r1 ≠ r4) ∧
  (distinct_tar_reg _ ⇔ T)`

(*Instructions are 2 register code for arith ok
  Currently no two_reg for Mul and Div
*)
val two_reg_inst_def = Define`
  (two_reg_inst (Arith (Binop bop r1 r2 ri))
    ⇔ (r1 = r2)) ∧
  (two_reg_inst (Arith (Shift l r1 r2 n))
    ⇔ (r1 = r2)) ∧
  (two_reg_inst (Arith (AddCarry r1 r2 r3 r4))
    ⇔ (r1 = r2)) ∧
  (two_reg_inst (Arith (AddOverflow r1 r2 r3 r4))
    ⇔ (r1 = r2)) ∧
  (two_reg_inst (Arith (SubOverflow r1 r2 r3 r4))
    ⇔ (r1 = r2)) ∧
  (two_reg_inst _ ⇔ T)`

(* Recursor over instructions *)
Definition every_inst_def:
  (every_inst P (Inst i) ⇔ P i) ∧
  (every_inst P (Seq p1 p2) ⇔ (every_inst P p1 ∧ every_inst P p2)) ∧
  (every_inst P (If cmp r1 ri c1 c2) ⇔ every_inst P c1 ∧ every_inst P c2) ∧
  (every_inst P (OpCurrHeap bop r1 r2) ⇔ P (Arith (Binop bop r1 r2 (Reg r2)))) ∧
  (every_inst P (MustTerminate p) ⇔ every_inst P p) ∧
  (every_inst P (Call ret dest args handler)
    ⇔ (case ret of
        NONE => T
      | SOME (n,names,ret_handler,l1,l2) => every_inst P ret_handler ∧
      (case handler of
        NONE => T
      | SOME (n,h,l1,l2) => every_inst P h))) ∧
  (every_inst P prog ⇔ T)
End

(* Every instruction is well-formed, including the jump hidden in If *)
val full_inst_ok_less_def = Define`
  (full_inst_ok_less c (Inst i) ⇔ inst_ok_less c i) ∧
  (full_inst_ok_less c (Seq p1 p2) ⇔
    (full_inst_ok_less c p1 ∧ full_inst_ok_less c p2)) ∧
  (full_inst_ok_less c (If cmp r1 ri c1 c2) ⇔
    ((case ri of Imm w => c.valid_imm (INR cmp) w | _ => T) ∧
    full_inst_ok_less c c1 ∧ full_inst_ok_less c c2)) ∧
  (full_inst_ok_less c (MustTerminate p) ⇔ full_inst_ok_less c p) ∧
  (full_inst_ok_less c (Call ret dest args handler)
    ⇔ (case ret of
        NONE => T
      | SOME (n,names,ret_handler,l1,l2) => full_inst_ok_less c ret_handler ∧
      (case handler of
        NONE => T
      | SOME (n,h,l1,l2) => full_inst_ok_less c h))) ∧
  (full_inst_ok_less c prog ⇔ T)`

(* All cutsets are well-formed *)
val wf_cutsets_def = Define`
  (wf_cutsets (Alloc n s) = wf s) ∧
  (wf_cutsets (Install _ _ _ _ s) = wf s) ∧
  (wf_cutsets (Call ret dest args h) =
    (case ret of
      NONE => T
    | SOME (v,cutset,ret_handler,l1,l2) =>
      wf cutset ∧
      wf_cutsets ret_handler ∧
      (case h of
        NONE => T
      | SOME (v,prog,l1,l2) =>
        wf_cutsets prog))) ∧
  (wf_cutsets (FFI x1 y1 x2 y2 z args) = wf args) ∧
  (wf_cutsets (MustTerminate s) = wf_cutsets s) ∧
  (wf_cutsets (Seq s1 s2) =
    (wf_cutsets s1 ∧ wf_cutsets s2)) ∧
  (wf_cutsets (If cmp r1 ri e2 e3) =
    (wf_cutsets e2 ∧
     wf_cutsets e3)) ∧
  (wf_cutsets _ = T)`

val inst_arg_convention_def = Define`
  (inst_arg_convention (Arith (AddCarry r1 r2 r3 r4)) ⇔ r4 = 0) ∧
  (* Note: these are not necessary *)
  (inst_arg_convention (Arith (AddOverflow r1 r2 r3 r4)) ⇔ r4 = 0) ∧
  (inst_arg_convention (Arith (SubOverflow r1 r2 r3 r4)) ⇔ r4 = 0) ∧
  (* Follows conventions for x86 *)
  (inst_arg_convention (Arith (LongMul r1 r2 r3 r4)) ⇔ r1 = 6 ∧ r2 = 0 ∧ r3 = 0 ∧ r4 = 4) ∧
  (inst_arg_convention (Arith (LongDiv r1 r2 r3 r4 r5)) ⇔ r1 = 0 ∧ r2 = 6 ∧ r3 = 6 ∧ r4 = 0) ∧
  (inst_arg_convention _ = T)`

(* Syntactic conventions for allocator *)
val call_arg_convention_def = Define`
  (call_arg_convention (Inst i) = inst_arg_convention i) ∧
  (call_arg_convention (Return x y) = (y=2)) ∧
  (call_arg_convention (Raise y) = (y=2)) ∧
  (call_arg_convention (Install ptr len _ _ _) = (ptr = 2 ∧ len = 4)) ∧
  (call_arg_convention (FFI x ptr len ptr2 len2 args) = (ptr = 2 ∧ len = 4 ∧
                                                         ptr2 = 6 ∧ len2 = 8)) ∧
  (call_arg_convention (Alloc n s) = (n=2)) ∧
  (call_arg_convention (Call ret dest args h) =
    (case ret of
      NONE => args = GENLIST (\x.2*x) (LENGTH args)
    | SOME (v,cutset,ret_handler,l1,l2) =>
      args = GENLIST (\x.2*(x+1)) (LENGTH args) ∧
      (v = 2) ∧ call_arg_convention ret_handler ∧
    (case h of  (*Does not check the case where Calls are ill-formed*)
      NONE => T
    | SOME (v,prog,l1,l2) =>
      (v = 2) ∧ call_arg_convention prog))) ∧
  (call_arg_convention (MustTerminate s1) =
    call_arg_convention s1) ∧
  (call_arg_convention (Seq s1 s2) =
    (call_arg_convention s1 ∧ call_arg_convention s2)) ∧
  (call_arg_convention (If cmp r1 ri e2 e3) =
    (call_arg_convention e2 ∧
     call_arg_convention e3)) ∧
  (call_arg_convention p = T)`

(*Before allocation, generated by SSA CC*)
val pre_alloc_conventions_def = Define`
  pre_alloc_conventions p =
    (every_stack_var is_stack_var p ∧
    call_arg_convention p)`

(*After allocation, generated by allocator and/or the oracles*)
val post_alloc_conventions_def = Define`
  post_alloc_conventions k prog =
    (every_var is_phy_var prog ∧
    every_stack_var (λx. x ≥ 2*k) prog ∧
    call_arg_convention prog)`

(* This is the current order of passes and the required syntactic conventions
that they need to establish or preserve

data-to-word (every_inst (\i.F))
Inst select (flat_exp_conventions, full_inst_ok_less) -- DONE
SSA (flat_exp_conventions, full_inst_ok_less, pre_alloc_conventions, wf_cutsets ) -- DONE
3-to-2 reg (flat_exp_conventions, full_inst_ok_less, pre_alloc_conventions, wf_cutsets, every_inst two_reg_inst) -- DONE
register allocation (flat_exp_conventions, full_inst_ok_less, post_alloc_conventions, every_inst two_reg_inst) -- DONE
word_remove (flat_exp_conventions, full_inst_ok_less, post_alloc_conventions, every_inst two_reg_inst)
word_to_word (everything in word_remove)
word_to_stack (probably needs to extend full_inst_ok_less and two_reg_inst)
*)

(* This is for label preservation -- wordLang shouldn't need to inspect the labels explicitly
  We will need theorems of the form:
  extract_labels prog = extract_labels (transform prog)
*)

val extract_labels_def = Define`
  (extract_labels (Call ret dest args h) =
    (case ret of
      NONE => []
    | SOME (v,cutset,ret_handler,l1,l2) =>
      let ret_rest = extract_labels ret_handler in
    (case h of
      NONE => [(l1,l2)] ++ ret_rest
    | SOME (v,prog,l1',l2') =>
      let h_rest = extract_labels prog in
      [(l1,l2);(l1',l2')]++ret_rest++h_rest))) ∧
  (extract_labels (MustTerminate s1) = extract_labels s1) ∧
  (extract_labels (Seq s1 s2) =
    extract_labels s1 ++ extract_labels s2) ∧
  (extract_labels (If cmp r1 ri e2 e3) =
    (extract_labels e2 ++ extract_labels e3)) ∧
  (extract_labels _ = [])`

Theorem env_to_list_lookup_equiv:
   env_to_list y f = (q,r) ==>
    (!n. ALOOKUP q n = lookup n y) /\
    (!x1 x2. MEM (x1,x2) q ==> lookup x1 y = SOME x2)
Proof
  fs[wordSemTheory.env_to_list_def,LET_DEF] \\ srw_tac[][]
  \\ `ALL_DISTINCT (MAP FST (toAList y))` by fs[ALL_DISTINCT_MAP_FST_toAList]
  \\ imp_res_tac (MATCH_MP PERM_ALL_DISTINCT_MAP
        (QSORT_PERM |> Q.ISPEC `key_val_compare` |> SPEC_ALL))
  \\ `ALL_DISTINCT (QSORT key_val_compare (toAList y))`
        by imp_res_tac ALL_DISTINCT_MAP
  \\ pop_assum (assume_tac o Q.SPEC `f (0:num)` o MATCH_MP PERM_list_rearrange)
  \\ imp_res_tac PERM_ALL_DISTINCT_MAP
  \\ rpt (qpat_x_assum `!x. pp ==> qq` (K all_tac))
  \\ rpt (qpat_x_assum `!x y. pp ==> qq` (K all_tac)) \\ rfs[]
  \\ rpt (pop_assum (mp_tac o Q.GEN `x` o SPEC_ALL))
  \\ rpt (pop_assum (mp_tac o SPEC ``f:num->num->num``))
  \\ Q.ABBREV_TAC `xs =
       (list_rearrange (f 0) (QSORT key_val_compare (toAList y)))`
  \\ rpt strip_tac \\ rfs[MEM_toAList]
  \\ Cases_on `?i. MEM (n,i) xs` \\ fs[] THEN1
     (imp_res_tac ALL_DISTINCT_MEM_IMP_ALOOKUP_SOME \\ fs[]
      \\ UNABBREV_ALL_TAC \\ fs[] \\ rfs[MEM_toAList])
  \\ `~MEM n (MAP FST xs)` by rfs[MEM_MAP,FORALL_PROD]
  \\ fs[GSYM ALOOKUP_NONE]
  \\ UNABBREV_ALL_TAC \\ fs[] \\ rfs[MEM_toAList]
  \\ Cases_on `lookup n y` \\ fs[]
QED

Theorem env_to_list_ALL_DISTINCT:
  env_to_list y perm = (vs,other) ==> ALL_DISTINCT (MAP FST vs)
Proof
  fs [wordSemTheory.env_to_list_def] \\ rw []
  \\ qmatch_goalsub_abbrev_tac `list_rearrange _ l`
  \\ `PERM (toAList y) l` by fs [Abbr`l`,sortingTheory.QSORT_PERM]
  \\ qsuff_tac `PERM l (list_rearrange (perm 0) l)`
  THEN1
   (strip_tac
    \\ `PERM (toAList y) (list_rearrange (perm 0) l)` by imp_res_tac PERM_TRANS
    \\ drule (Q.ISPEC `FST` sortingTheory.PERM_MAP) \\ strip_tac
    \\ drule (GSYM ALL_DISTINCT_PERM) \\ fs [ALL_DISTINCT_MAP_FST_toAList])
  \\ match_mp_tac PERM_list_rearrange
  \\ drule (GSYM ALL_DISTINCT_PERM) \\ fs [] \\ rw []
  \\ match_mp_tac (Q.ISPEC `FST` listTheory.ALL_DISTINCT_MAP)
  \\ fs [ALL_DISTINCT_MAP_FST_toAList]
QED

val max_var_exp_IMP = Q.prove(`
  ∀exp.
  P 0 ∧ every_var_exp P exp ⇒
  P (max_var_exp exp)`,
  ho_match_mp_tac max_var_exp_ind>>fs[max_var_exp_def,every_var_exp_def]>>
  srw_tac[][]>>
  match_mp_tac list_max_intro>>
  fs[EVERY_MAP,EVERY_MEM]);

Theorem max_var_intro:
    ∀prog.
  P 0 ∧ every_var P prog ⇒
  P (max_var prog)
Proof
  ho_match_mp_tac max_var_ind>>
  fs[every_var_def,max_var_def,max_var_exp_IMP,MAX_DEF]>>srw_tac[][]>>
  TRY(metis_tac[max_var_exp_IMP])>>
  TRY (match_mp_tac list_max_intro>>fs[EVERY_APPEND,every_name_def])
  >-
    (Cases_on`i`>>TRY(Cases_on`a`)>>TRY(Cases_on`m`)>>
    TRY(Cases_on`f`)>>
    fs[max_var_inst_def,every_var_inst_def,every_var_imm_def,MAX_DEF]>>
    EVERY_CASE_TAC>>fs[every_var_imm_def])
  >-
    (TOP_CASE_TAC>>unabbrev_all_tac>>fs[list_max_intro]>>
    EVERY_CASE_TAC>>fs[LET_THM]>>srw_tac[][]>>
    match_mp_tac list_max_intro>>fs[EVERY_APPEND,every_name_def])
  >> (unabbrev_all_tac>>EVERY_CASE_TAC>>fs[every_var_imm_def])
QED

val get_code_labels_def = Define`
  (get_code_labels (Call r d a h) =
    (case d of SOME x => {x} | _ => {}) ∪
    (case r of SOME (_,_,x,_,_) => get_code_labels x | _ => {}) ∪
    (case h of SOME (_,x,l1,l2) => get_code_labels x | _ => {})) ∧
  (get_code_labels (Seq p1 p2) = get_code_labels p1 ∪ get_code_labels p2) ∧
  (get_code_labels (If _ _ _ p1 p2) = get_code_labels p1 ∪ get_code_labels p2) ∧
  (get_code_labels (MustTerminate p) = get_code_labels p) ∧
  (get_code_labels (LocValue _ l1) = {l1}) ∧
  (get_code_labels _ = {})`;
val _ = export_rewrites["get_code_labels_def"];

(* TODO: This seems like it must have been established before
  handler labels point only within the current table entry
*)
val good_handlers_def = Define`
  (good_handlers n (Call r d a h) <=>
    case r of
      NONE => T
    | SOME (_,_,x,_,_) => good_handlers n x ∧
    (case h of SOME (_,x,l1,_) => l1 = n ∧ good_handlers n x | _ => T)) ∧
  (good_handlers n (Seq p1 p2) <=> good_handlers n p1 ∧ good_handlers n p2) ∧
  (good_handlers n (If _ _ _ p1 p2) <=> good_handlers n p1 ∧ good_handlers n p2) ∧
  (good_handlers n (MustTerminate p) <=> good_handlers n p) ∧
  (good_handlers n _ <=> T)`;
val _ = export_rewrites["good_handlers_def"];

val good_code_labels_def = Define`
  good_code_labels p elabs ⇔
  EVERY (λ(n,m,pp). good_handlers n pp) p ∧
  (BIGUNION (set (MAP (λ(n,m,pp). (get_code_labels pp)) p))) ⊆
  (set (MAP FST p) ∪ elabs)`;

Theorem push_env_dec_clock_stack:
  (push_env y opt (wordSem$dec_clock t)).stack_max =
  (push_env y opt t).stack_max /\
  (push_env y opt (wordSem$dec_clock t)).stack =
  (push_env y opt t).stack
Proof
  Cases_on `opt` \\ TRY (PairCases_on `x`)
  \\ fs [wordSemTheory.push_env_def]
  \\ pairarg_tac \\ fs [wordSemTheory.dec_clock_def]
QED

Theorem set_store_stack_max_greater_bound:
  !v x s t. set_store v x s = t /\
  option_le (OPTION_MAP2 $+ (stack_size s.stack) s.locals_size) s.stack_max ==>
     option_le (OPTION_MAP2 $+ (stack_size t.stack) t.locals_size) t.stack_max
Proof
  rw [set_store_def, stack_size_def] >> fs []
QED


Theorem stack_size_some_at_least_one:
  !stk sz. stack_size stk = SOME sz ==> 1 <= sz
Proof
  Induct >> rw [stack_size_eq2] >>
  res_tac >> fs [] >> DECIDE_TAC
QED

Theorem push_call_option_le_stack_max_preserved:
  !args sz  env handler s.
  option_le
    (OPTION_MAP2 $+
       (stack_size (call_env args sz (push_env env handler s)).stack)
       (call_env args sz (push_env env handler s)).locals_size)
   (call_env args sz  (push_env env handler s)).stack_max
Proof

rw [call_env_def] >>
     Cases_on `handler` >> fs [push_env_def, state_fn_updates]
     >- (
       pairarg_tac >> fs [] >>
       qpat_abbrev_tac `sts = stack_size _` >>
       Cases_on `sts` >- fs [OPTION_MAP2_DEF] >>
       Cases_on `s.stack_max` >-fs [OPTION_MAP2_DEF]>>
       `1 <= x` by (match_mp_tac stack_size_some_at_least_one >> unabbrev_all_tac >> metis_tac []) >>
       fs [OPTION_MAP2_DEF] >> every_case_tac >> fs []) >>
     Cases_on `x` >> Cases_on `r` >>  Cases_on `r'` >> fs [push_env_def, state_fn_updates] >>
     pairarg_tac >> fs [] >>
     qpat_abbrev_tac `sts = stack_size _` >>
     Cases_on `sts` >- fs [OPTION_MAP2_DEF] >>
     Cases_on `s.stack_max` >-fs [OPTION_MAP2_DEF]>>
     `1 <= x` by (match_mp_tac stack_size_some_at_least_one >> unabbrev_all_tac >> metis_tac []) >>
     fs [OPTION_MAP2_DEF] >> every_case_tac >> fs []

QED


Theorem pop_env_option_le_stack_max_preserved:
  !s t.
    option_le (OPTION_MAP2 $+ (stack_size s.stack) s.locals_size) s.stack_max /\
    pop_env s = SOME t ==>
      option_le (OPTION_MAP2 $+ (stack_size t.stack) t.locals_size) t.stack_max
Proof
  rw [pop_env_def] >>
  every_case_tac >> fs [] >> rveq >>
  fs [state_fn_updates, stack_size_eq2, stack_size_frame_def] >>
  qmatch_asmsub_rename_tac `s.stack = StackFrame lsz _ _ :: tlstk` >>
  Cases_on `lsz` >>
  Cases_on `stack_size tlstk` >>
  Cases_on `s.locals_size` >>
  Cases_on `s.stack_max` >>
  fs [OPTION_MAP2_DEF]
QED


Theorem  dec_stack_stack_size_some_not_none:
  !xs stk stk' x. dec_stack xs stk = SOME stk' /\ stack_size stk = SOME x  ==>
     stack_size stk' <> NONE
Proof
  ho_match_mp_tac dec_stack_ind >>rw [dec_stack_def]
  >- (fs [stack_size_eq2] >> metis_tac []) >>
  every_case_tac >> fs [] >> rveq >> Cases_on `handler` >>
  fs [stack_size_eq2, stack_size_frame_def]
QED


Theorem  dec_stack_stack_size_not_none_not_none:
  !xs stk stk'. dec_stack xs stk = SOME stk' /\ stack_size stk <> NONE  ==>
     stack_size stk' <> NONE
Proof
  ho_match_mp_tac dec_stack_ind >>rw [dec_stack_def]
  >- (fs [stack_size_eq2] >> metis_tac []) >>
  every_case_tac >> fs [] >> rveq >> Cases_on `handler` >>
  fs [stack_size_eq2, stack_size_frame_def]
QED


Theorem  dec_stack_stack_size_some_leq:
  !xs stk stk' x y. dec_stack xs stk = SOME stk' /\
    stack_size stk = SOME x  /\
    stack_size stk' = SOME y ==>
      y <= x
Proof
  ho_match_mp_tac dec_stack_ind >>rw [dec_stack_def]
  >- (fs [stack_size_eq2] >> DECIDE_TAC) >>
  every_case_tac >> fs [] >> rveq >> Cases_on `handler` >>
  fs [stack_size_eq2, stack_size_frame_def] >> rveq >> rfs []
QED



Theorem flush_state_option_le_stack_max_preserved:
  !s p.
     option_le (OPTION_MAP2 $+ (stack_size s.stack) s.locals_size) s.stack_max ==>
     let t = flush_state p s in
       option_le
         (OPTION_MAP2 $+ (stack_size t.stack)
             t.locals_size) t.stack_max
Proof
  rw [LET_DEF] >>
  Cases_on `p` >>
  fs [flush_state_def] >>
  Cases_on `stack_size s.stack` >>
  Cases_on `s.locals_size` >>
  Cases_on `s.stack_max` >>
  fs [stack_size_eq2, stack_size_frame_def,OPTION_MAP2_DEF] >>
  drule stack_size_some_at_least_one >> DECIDE_TAC
QED


Theorem LASTN_stack_size_SOME:
  !n stack stack' x.
  LASTN n stack = stack'
  /\ stack_size stack = SOME x
  /\ n <= LENGTH stack ==>
  ?y. stack_size stack' = SOME y /\ y <= x
Proof
  Induct_on `stack` >> rw[LASTN_ALT,stack_size_eq] >>
  fs[stack_size_eq2] >>
  res_tac >>
  goal_assum drule >>
  intLib.COOPER_TAC
QED

Theorem evaluate_option_le_stack_max_preserved:
  !p s r t. evaluate (p, s) = (r, t) /\
     option_le (OPTION_MAP2 $+ (stack_size s.stack) s.locals_size) s.stack_max ==>
     option_le (OPTION_MAP2 $+ (stack_size t.stack) t.locals_size) t.stack_max
Proof
  recInduct evaluate_ind >>
  rw [evaluate_def] >> simp []
  >- (
     (*  Alloc *)
     every_case_tac >> fs [] >>
     fs [alloc_def] >> every_case_tac >> fs []
     >- (
       fs [gc_def, flush_state_def, set_store_def] >>
       every_case_tac >>
       fs [push_env_def, env_to_list_def] >> rveq >>
       fs [state_fn_updates] >>
       fs [stack_size_eq2, stack_size_frame_def] >>
       ntac 5 (pop_assum kall_tac) >>
       fs [option_le_def] >>
       Cases_on `s.locals_size` >> Cases_on `stack_size s.stack` >> Cases_on `s.stack_max` >>
       fs [OPTION_MAP_DEF] >> drule stack_size_some_at_least_one >>
       DECIDE_TAC) >>
     TRY (
     rveq >>
     fs [gc_def] >> every_case_tac >> fs [] >>
     fs [push_env_def, env_to_list_def, flush_state_def, pop_env_def] >> rveq >>
     every_case_tac >> fs [set_store_def] >> rveq >>
     fs [state_fn_updates, dec_stack_def] >>
     every_case_tac >> fs [] >> rveq >>
     qpat_abbrev_tac `lra = list_rearrange _ _` >>
     pop_assum kall_tac >>
     fs [stack_size_eq2, stack_size_frame_def] >>
     Cases_on `s.stack_max` >>
     Cases_on `s.locals_size` >>
     Cases_on `stack_size s.stack` >>
     Cases_on `stack_size t'` >>
     fs [OPTION_MAP2_DEF]
     >- (
       drule dec_stack_stack_size_some_not_none >>
       disch_then drule >> metis_tac []) >>
     drule dec_stack_stack_size_some_leq >>
     disch_then drule >> fs [] >> NO_TAC) >>
     rveq >>
     fs [gc_def] >> every_case_tac >> fs [] >>
     fs [push_env_def, env_to_list_def, flush_state_def, pop_env_def] >> rveq >>
     every_case_tac >> fs [set_store_def] >> rveq >>
     fs [state_fn_updates, dec_stack_def] >>
     every_case_tac >> fs [] >> rveq >>
     qpat_abbrev_tac `lra = list_rearrange _ _` >>
     pop_assum kall_tac >>
     fs [stack_size_eq2, stack_size_frame_def] >>
     Cases_on `s.stack_max` >>
     Cases_on `s.locals_size` >>
     Cases_on `stack_size s.stack` >>
     fs [OPTION_MAP2_DEF] >>
     drule stack_size_some_at_least_one >> DECIDE_TAC)
  >- (
    every_case_tac >> fs [set_vars_def] >> rveq >> fs [state_fn_updates])
  >- (
    every_case_tac >> fs [] >> rveq >> drule inst_const_full >>
    fs [])
  >- (
   every_case_tac >> fs [set_vars_def] >> rveq >> fs [state_fn_updates])
  >- (
   every_case_tac >> fs [set_vars_def] >> rveq >> fs [state_fn_updates])
  >- (
   every_case_tac >> fs [set_store_def] >> rveq >> fs [state_fn_updates])
  >- (
   every_case_tac >> fs [set_store_def] >> rveq >> fs [state_fn_updates])
  >- (
   every_case_tac >> fs [mem_store_def] >> rveq >> fs [state_fn_updates])
  >- (
   fs [flush_state_def] >> fs [stack_size_eq2] >>
   Cases_on `s.locals_size` >> Cases_on `stack_size s.stack` >> Cases_on `s.stack_max` >>
   fs [OPTION_MAP_DEF] >> drule stack_size_some_at_least_one >> DECIDE_TAC)
  >- (
    pairarg_tac >> fs [] >> every_case_tac >> fs [] >> rveq >> fs [state_fn_updates])
  >- (
    pairarg_tac >> fs [] >> every_case_tac >> fs [] >> rveq >> fs [state_fn_updates])
  >- (
   every_case_tac >> fs [flush_state_def] >> rveq >> fs[state_fn_updates] >>
   Cases_on `s.locals_size` >> Cases_on `stack_size s.stack` >> Cases_on `s.stack_max` >>
   fs [OPTION_MAP_DEF])
  >- (
   fs [jump_exc_def] >>  every_case_tac >> fs [] >> rveq >> fs[state_fn_updates] >>
   Cases_on `stack_size s.stack` >>  Cases_on `s.locals_size` >>  Cases_on `s.stack_max` >>
   fs [OPTION_MAP2_DEF, option_le_def] >>
   `s.handler + 1 <= LENGTH s.stack` by DECIDE_TAC >>
   drule LASTN_stack_size_SOME >>
   disch_then drule >> strip_tac >> rfs [] >>
   fs[stack_size_eq2, stack_size_frame_def])
  >- (every_case_tac >> fs [])
  >- (
    every_case_tac >> fs [] >> pairarg_tac >> fs [] >> every_case_tac >> fs [] >>
    rveq >> fs [state_fn_updates])
  >- (
    every_case_tac >> fs [] >> rveq >> fs [state_fn_updates])
  >- (
    every_case_tac >> fs [] >> rveq >> fs [state_fn_updates])
  >- (
    every_case_tac >> fs [] >> rveq >> fs [state_fn_updates, flush_state_def, stack_size_eq2] >>
    Cases_on `s.locals_size` >> Cases_on `stack_size s.stack` >> Cases_on `s.stack_max` >>
    fs [OPTION_MAP_DEF] >> drule stack_size_some_at_least_one >> DECIDE_TAC) >>
  (* Call *)
  qpat_x_assum `_ = (_,_)` mp_tac >>
  TOP_CASE_TAC >- (strip_tac >>rveq >> fs []) >>
  TOP_CASE_TAC >- (strip_tac >>rveq >> fs []) >>
  TOP_CASE_TAC >- (strip_tac >>rveq >> fs []) >>
  TOP_CASE_TAC >> TOP_CASE_TAC >> TOP_CASE_TAC >>
  qmatch_asmsub_rename_tac `find_code dest _ _ _ = SOME (clargs,exp,lsz)`
  (* tail call *)
  >- (rpt IF_CASES_TAC >> fs []
     >- (
      strip_tac >> fs [flush_state_def] >> rveq >> fs[state_fn_updates, stack_size_eq2] >>
      Cases_on `s.locals_size` >> Cases_on `stack_size s.stack` >> Cases_on `s.stack_max` >>
      fs [OPTION_MAP_DEF] >> drule stack_size_some_at_least_one >> DECIDE_TAC)
     >- (
       TOP_CASE_TAC >> TOP_CASE_TAC >>
       strip_tac >> rveq >> rfs [] >> fs [call_env_def] >>
       Cases_on `stack_size s.stack` >> Cases_on `lsz` >> Cases_on ` s.stack_max` >> fs [] >>
       fs [option_le_def])
     >> strip_tac >>rveq >> fs []) >>
  (* returning call *)
  qmatch_asmsub_rename_tac `find_code dest (add_ret_loc (SOME retarg) vargs) _ _ = _` >>
  ntac 4 TOP_CASE_TAC >>
  qmatch_asmsub_rename_tac `find_code _ (add_ret_loc (SOME (n,names,ret_handler,l1,l2)) vargs) _ _ = _` >>
  IF_CASES_TAC >- (strip_tac >>rveq >> fs []) >>
  TOP_CASE_TAC >- (strip_tac >>rveq >> fs []) >>
  IF_CASES_TAC
  >- (
    strip_tac >> fs [flush_state_def] >> rveq >> fs [stack_size_eq2, state_fn_updates] >>
    fs [call_env_def] >>
    Cases_on `handler` >> fs [push_env_def, state_fn_updates]
    >- (
      pairarg_tac >> fs [] >>
      qpat_abbrev_tac `sts = stack_size _` >>
      Cases_on `sts` >- fs [OPTION_MAP2_DEF] >>
      qmatch_asmsub_rename_tac  `Abbrev (SOME sts' = _)` >>
      Cases_on `s.stack_max` >-fs [OPTION_MAP2_DEF]>>
      `1 <= sts'` by (match_mp_tac stack_size_some_at_least_one >> unabbrev_all_tac >> metis_tac []) >>
      fs [OPTION_MAP2_DEF] >> every_case_tac >> fs []) >>
    Cases_on `x'` >> Cases_on `r` >>  Cases_on `r'` >> fs [push_env_def, state_fn_updates] >>
    pairarg_tac >> fs [] >>
    qpat_abbrev_tac `sts = stack_size _` >>
    Cases_on `sts` >- fs [OPTION_MAP2_DEF] >>
    qmatch_asmsub_rename_tac  `Abbrev (SOME sts' = _)` >>
    Cases_on `s.stack_max` >-fs [OPTION_MAP2_DEF]>>
    `1 <= sts'` by (match_mp_tac stack_size_some_at_least_one >> unabbrev_all_tac >> metis_tac []) >>
    fs [OPTION_MAP2_DEF] >> every_case_tac >> fs []) >>
  ntac 2 TOP_CASE_TAC
  >- (
    strip_tac >> rveq >>
    PRED_ASSUM is_forall kall_tac >>
    qmatch_asmsub_rename_tac  `push_env env handler _` >>
    qmatch_asmsub_rename_tac  `evaluate (exp,_)= (_,stnew)` >>
    (* what is the better way of doing this spec? something using disch_then ... *)
    first_x_assum (qspecl_then [`vargs`, `clargs`, `exp`, `lsz`, `n`, `names`,
          `ret_handler`, `l1`, `l2`, `env`] mp_tac) >> PURE_ASM_REWRITE_TAC [] >>
    simp_tac bool_ss [] >>
    disch_then (qspecl_then [`NONE`,`stnew`] mp_tac) >> simp_tac bool_ss [] >>
    rpt (pop_assum kall_tac) >>
    strip_tac >>
    assume_tac push_call_option_le_stack_max_preserved >>
    res_tac >> rfs []) >>
  TOP_CASE_TAC >>
  qmatch_asmsub_rename_tac  `push_env env handler _` >>
  qmatch_asmsub_rename_tac  `evaluate (exp,_)= (_,stnew)`
  >- ( (*  SOME result *)
   TOP_CASE_TAC
   >- (
     strip_tac >> rveq >>
     PRED_ASSUM is_forall kall_tac >>
     first_x_assum (qspecl_then [`vargs`, `clargs`, `exp`, `lsz`, `n`, `names`,
          `ret_handler`, `l1`, `l2`, `env`] mp_tac) >> PURE_ASM_REWRITE_TAC [] >>
     simp_tac bool_ss [] >>
     disch_then (qspecl_then [`SOME (Result w w0)`,`stnew`] mp_tac) >> simp_tac bool_ss [] >>
     rpt (pop_assum kall_tac) >>
     strip_tac >>
     assume_tac push_call_option_le_stack_max_preserved >>
     res_tac >> rfs []) >>
   TOP_CASE_TAC
   >- (
     strip_tac >> rveq >>
     PRED_ASSUM is_forall kall_tac >>
     first_x_assum (qspecl_then [`vargs`, `clargs`, `exp`, `lsz`, `n`, `names`,
          `ret_handler`, `l1`, `l2`, `env`] mp_tac) >> PURE_ASM_REWRITE_TAC [] >>
     simp_tac bool_ss [] >>
     disch_then (qspecl_then [`SOME (Result (Loc l1 l2) w0)`,`stnew`] mp_tac) >> simp_tac bool_ss [] >>
     rpt (pop_assum kall_tac) >>
     strip_tac >>
     assume_tac push_call_option_le_stack_max_preserved >>
     res_tac >> rfs [])>>
   IF_CASES_TAC
   >- (
     rveq >> strip_tac >>
     last_x_assum (qspec_then `vargs` kall_tac) >>
     last_x_assum (qspecl_then [`vargs`, `clargs`, `exp`, `lsz`, `n`, `names`,
          `ret_handler`, `l1`, `l2`, `env`] mp_tac) >> simp_tac bool_ss [] >>
     PURE_ONCE_ASM_REWRITE_TAC [] >> simp_tac bool_ss [] >>
     qmatch_asmsub_rename_tac `pop_env stnew = SOME popst` >>
     disch_then (qspecl_then [`stnew`, `w0` , `popst`] mp_tac) >> simp_tac bool_ss [] >>
     PURE_ONCE_ASM_REWRITE_TAC [] >> simp_tac bool_ss [] >>
     disch_then (qspecl_then [`r`, `t`] mp_tac) >> simp_tac bool_ss [] >>
     strip_tac >>
     PRED_ASSUM is_forall kall_tac >>
     first_x_assum (qspecl_then [`vargs`, `clargs`, `exp`, `lsz`, `n`, `names`,
          `ret_handler`, `l1`, `l2`, `env`] mp_tac) >> simp_tac bool_ss [] >>
     PURE_ONCE_ASM_REWRITE_TAC [] >> simp_tac bool_ss [] >>
     disch_then (qspecl_then [`SOME (Result (Loc l1 l2) w0)`,`stnew`] mp_tac) >>  simp_tac bool_ss [] >>
     strip_tac >>
     assume_tac push_call_option_le_stack_max_preserved >>
     res_tac >> fs [] >>
     pop_assum kall_tac >>
     drule pop_env_option_le_stack_max_preserved >>
     disch_then drule >>
     rw []) >>
   strip_tac >> rveq >>
   last_x_assum (qspec_then `vargs` kall_tac) >>
   last_x_assum (qspecl_then [`vargs`, `clargs`, `exp`, `lsz`, `n`, `names`,
          `ret_handler`, `l1`, `l2`, `env`] mp_tac) >> simp_tac bool_ss [] >>
   PURE_ONCE_ASM_REWRITE_TAC [] >> simp_tac bool_ss [] >>
   qmatch_asmsub_rename_tac `pop_env stnew = SOME popst` >>
   disch_then (qspecl_then [`stnew`, `w0` , `popst`] mp_tac) >> simp_tac bool_ss [] >>
   PURE_ONCE_ASM_REWRITE_TAC [] >> simp_tac bool_ss [] >>
   pop_assum mp_tac >>
   PURE_ONCE_REWRITE_TAC [PAIR_EQ] >>
   strip_tac >> rveq >>
   PRED_ASSUM is_forall kall_tac >>
   first_x_assum (qspecl_then [`vargs`, `clargs`, `exp`, `lsz`, `n`, `names`,
          `ret_handler`, `l1`, `l2`, `env`] mp_tac) >> simp_tac bool_ss [] >>
   PURE_ONCE_ASM_REWRITE_TAC [] >> simp_tac bool_ss [] >>
   disch_then (qspecl_then [`SOME (Result (Loc  l1 l2) w0)`,`stnew`] mp_tac) >>  simp_tac bool_ss [] >>
   strip_tac >>
   assume_tac push_call_option_le_stack_max_preserved >>
   res_tac >> fs [] >>
   pop_assum kall_tac >>
   drule pop_env_option_le_stack_max_preserved >>
   disch_then drule >>
   rw [])
  >- (TOP_CASE_TAC
   >- (
     strip_tac >> rveq >>
     PRED_ASSUM is_forall kall_tac >>
     PRED_ASSUM is_forall kall_tac >>
     last_x_assum (qspecl_then [`vargs`, `clargs`, `exp`, `lsz`, `n`, `names`,
          `ret_handler`, `l1`, `l2`, `env`] mp_tac) >> simp_tac bool_ss [] >>
     PURE_ONCE_ASM_REWRITE_TAC [] >> simp_tac bool_ss [] >>
     disch_then (qspecl_then [`SOME (Exception w w0)`,`stnew`] mp_tac) >> simp_tac bool_ss [] >>
     rpt (pop_assum kall_tac) >>
     strip_tac >>
     assume_tac push_call_option_le_stack_max_preserved >>
     res_tac >> rfs []) >>
   TOP_CASE_TAC >> TOP_CASE_TAC >> TOP_CASE_TAC >>
   IF_CASES_TAC
   >- (
     PURE_ONCE_REWRITE_TAC [PAIR_EQ] >>
     strip_tac >> rveq >>
     PRED_ASSUM is_forall kall_tac >>
     first_x_assum (qspecl_then [`vargs`, `clargs`, `exp`, `lsz`, `n`, `names`,
          `ret_handler`, `l1`, `l2`, `env`] mp_tac) >> simp_tac bool_ss [] >>
     PURE_ONCE_ASM_REWRITE_TAC [] >> simp_tac bool_ss [] >>
     disch_then (qspecl_then [`SOME (Exception w w0)`,`stnew`] mp_tac) >>  simp_tac bool_ss [] >>
     rpt (pop_assum kall_tac) >>
     strip_tac >>
     assume_tac push_call_option_le_stack_max_preserved >>
     res_tac >> rfs []) >>
  IF_CASES_TAC
  >- (
    pop_assum mp_tac >>
    pop_assum mp_tac >>
    simp_tac bool_ss [] >>
    rpt strip_tac >> rveq >>
    last_x_assum (qspecl_then [`vargs`, `clargs`, `exp`, `lsz`, `n`, `names`,
          `ret_handler`, `l1`, `l2`, `env`] mp_tac) >> simp_tac bool_ss [] >>
    PURE_ONCE_ASM_REWRITE_TAC [] >> simp_tac bool_ss [] >>
    disch_then (qspecl_then [`stnew`, `w0`, `q`, `q'`, `q''`, `r'`] mp_tac) >>
    simp_tac bool_ss [] >>
    PURE_ONCE_ASM_REWRITE_TAC [] >> simp_tac bool_ss [] >>
    disch_then (qspecl_then [`r`,`t`] mp_tac) >>
    simp_tac bool_ss [] >>
    PRED_ASSUM is_forall kall_tac >>
    first_x_assum (qspecl_then [`vargs`, `clargs`, `exp`, `lsz`, `n`, `names`,
          `ret_handler`, `l1`, `l2`, `env`] mp_tac) >> simp_tac bool_ss [] >>
    PURE_ONCE_ASM_REWRITE_TAC [] >> simp_tac bool_ss [] >>
    disch_then (qspecl_then [`SOME (Exception (Loc q'' r') w0)`, `stnew`] mp_tac) >>
    simp_tac bool_ss [] >>
    rpt (pop_assum kall_tac) >>
    strip_tac >>
    assume_tac push_call_option_le_stack_max_preserved >>
    res_tac >> rfs []) >>
  PURE_ONCE_REWRITE_TAC [PAIR_EQ] >>
  strip_tac >> rveq >>
  PRED_ASSUM is_forall kall_tac >>
  first_x_assum (qspecl_then [`vargs`, `clargs`, `exp`, `lsz`, `n`, `names`,
          `ret_handler`, `l1`, `l2`, `env`] mp_tac) >> simp_tac bool_ss [] >>
  PURE_ONCE_ASM_REWRITE_TAC [] >> simp_tac bool_ss [] >>
  disch_then (qspecl_then [`SOME (Exception w w0)`,`stnew`] mp_tac) >>  simp_tac bool_ss [] >>
  rpt (pop_assum kall_tac) >>
  strip_tac >>
  assume_tac push_call_option_le_stack_max_preserved >>
  res_tac >> rfs [])
  >- (
   strip_tac >> rveq >>
   PRED_ASSUM is_forall kall_tac >>
   first_x_assum (qspecl_then [`vargs`, `clargs`, `exp`, `lsz`, `n`, `names`,
          `ret_handler`, `l1`, `l2`, `env`] mp_tac) >> simp_tac bool_ss [] >>
   PURE_ONCE_ASM_REWRITE_TAC [] >> simp_tac bool_ss [] >>
   disch_then (qspecl_then [`SOME TimeOut`,`stnew`] mp_tac) >>  simp_tac bool_ss [] >>
   rpt (pop_assum kall_tac) >>
   strip_tac >>
   assume_tac push_call_option_le_stack_max_preserved >>
   res_tac >> rfs [])
  >- (
   strip_tac >> rveq >>
   PRED_ASSUM is_forall kall_tac >>
   first_x_assum (qspecl_then [`vargs`, `clargs`, `exp`, `lsz`, `n`, `names`,
          `ret_handler`, `l1`, `l2`, `env`] mp_tac) >> simp_tac bool_ss [] >>
   PURE_ONCE_ASM_REWRITE_TAC [] >> simp_tac bool_ss [] >>
   disch_then (qspecl_then [`SOME NotEnoughSpace`,`stnew`] mp_tac) >>  simp_tac bool_ss [] >>
   rpt (pop_assum kall_tac) >>
   strip_tac >>
   assume_tac push_call_option_le_stack_max_preserved >>
   res_tac >> rfs [])
  >- (
   strip_tac >> rveq >>
   PRED_ASSUM is_forall kall_tac >>
   first_x_assum (qspecl_then [`vargs`, `clargs`, `exp`, `lsz`, `n`, `names`,
          `ret_handler`, `l1`, `l2`, `env`] mp_tac) >> simp_tac bool_ss [] >>
   PURE_ONCE_ASM_REWRITE_TAC [] >> simp_tac bool_ss [] >>
   disch_then (qspecl_then [`SOME (FinalFFI f)`,`stnew`] mp_tac) >>  simp_tac bool_ss [] >>
   rpt (pop_assum kall_tac) >>
   strip_tac >>
   assume_tac push_call_option_le_stack_max_preserved >>
   res_tac >> rfs []) >>
  strip_tac >> rveq >>
  PRED_ASSUM is_forall kall_tac >>
  first_x_assum (qspecl_then [`vargs`, `clargs`, `exp`, `lsz`, `n`, `names`,
          `ret_handler`, `l1`, `l2`, `env`] mp_tac) >> simp_tac bool_ss [] >>
  PURE_ONCE_ASM_REWRITE_TAC [] >> simp_tac bool_ss [] >>
  disch_then (qspecl_then [`SOME Error`,`stnew`] mp_tac) >>  simp_tac bool_ss [] >>
  rpt (pop_assum kall_tac) >>
  strip_tac >>
  assume_tac push_call_option_le_stack_max_preserved >>
  res_tac >> rfs []
QED


Theorem push_env_stack_max_eq:
  (push_env env handler s).stack_max =
  OPTION_MAP2 MAX s.stack_max
    (stack_size (push_env env handler s).stack)
Proof
  Cases_on `handler` >-
    (fs[push_env_def,ELIM_UNCURRY]) >-
    (PairCases_on `x` >>
     fs[push_env_def,ELIM_UNCURRY])
QED


Theorem evaluate_stack_max:
  !c s1 res s2.
  evaluate (c,s1) = (res,s2) ==>
  case s1.stack_max of
    NONE => s2.stack_max = NONE
  | SOME stack_max =>
      the stack_max s2.stack_max >= stack_max
Proof
  recInduct wordSemTheory.evaluate_ind >>
  rw[wordSemTheory.evaluate_def,CaseEq"option",CaseEq"word_loc"] >>
  rw[set_vars_const] >>
  TRY(EVERY_ASSUM (fn thm => if is_forall(concl thm) then NO_TAC else ALL_TAC) >>
      TOP_CASE_TAC >>
      fs[alloc_def,CaseEq"option",CaseEq"prod",CaseEq"list",CaseEq"stack_frame",CaseEq"bool",
         CaseEq"inst",CaseEq"arith",CaseEq"word_loc",CaseEq"addr",CaseEq"memop",assign_def,
         word_exp_def,mem_store_def,CaseEq"fp",jump_exc_def,CaseEq"ffi_result",
         inst_def,call_env_def,flush_state_def,gc_def,pop_env_def,push_env_def,ELIM_UNCURRY,the_eqn,
         OPTION_MAP2_DEF,IS_SOME_EXISTS,MAX_DEF] >>
      rveq >> fs[] >> rveq >> fs[] >> rpt(TOP_CASE_TAC >> fs[] >> rveq) >>
      NO_TAC) >>
  TRY(TOP_CASE_TAC >> pairarg_tac >> fs[CaseEq"bool",the_eqn] >> rveq >> rw[] >>
      res_tac >> every_case_tac >> fs[]) >>
  TRY(rename1 `word_cmp` >> TOP_CASE_TAC >> fs[CaseEq"bool",the_eqn]) >>
  TOP_CASE_TAC >>
  fs[CaseEq "bool",CaseEq"option",CaseEq"prod",CaseEq"wordSem$result",the_eqn] >>
  rveq >> simp[call_env_def,flush_state_def] >>
  rpt(first_x_assum (drule_then strip_assume_tac)) >>
  fs[] >> rpt(first_x_assum (drule_then strip_assume_tac)) >>
  fs[pop_env_def,CaseEq "list",CaseEq"stack_frame",CaseEq"option",CaseEq"prod",
     push_env_def,push_env_stack_max_eq,call_env_def,flush_state_def] >>
  rveq >> fs[] >>
  rfs[OPTION_MAP2_DEF,MAX_DEF] >> fs[] >>
  rpt(PURE_FULL_CASE_TAC >> fs[IS_SOME_EXISTS] >> rveq) >>
  fs[stack_size_eq]
QED

Theorem evaluate_stack_max_IS_SOME:
  ∀c s1 res s2.
    evaluate (c,s1) = (res,s2) /\ IS_SOME s2.stack_max ⇒
    IS_SOME s1.stack_max
Proof
  rw[] >> dxrule_then assume_tac evaluate_stack_max >>
  PURE_FULL_CASE_TAC >> fs[]
QED

Theorem evaluate_stack_max_le:
  !c s1 res s2.
  evaluate (c,s1) = (res,s2) ==>
  option_le s1.stack_max s2.stack_max
Proof
  rpt strip_tac >> dxrule evaluate_stack_max >>
  fs[the_eqn] >>
  every_case_tac >> fs[]
QED

Theorem evaluate_stack_limit:
  !c s1 res s2.
  evaluate (c,s1) = (res,s2) ==>
  s2.stack_limit = s1.stack_limit
Proof
  recInduct wordSemTheory.evaluate_ind >>
  rw[wordSemTheory.evaluate_def,CaseEq"option",CaseEq"word_loc"] >>
  rw[set_vars_const] >>
  TRY(EVERY_ASSUM (fn thm => if is_forall(concl thm) then NO_TAC else ALL_TAC) >>
      fs[alloc_def,CaseEq"option",CaseEq"prod",CaseEq"list",CaseEq"stack_frame",CaseEq"bool",
         CaseEq"inst",CaseEq"arith",CaseEq"word_loc",CaseEq"addr",CaseEq"memop",assign_def,
         word_exp_def,mem_store_def,CaseEq"fp",jump_exc_def,CaseEq"ffi_result",
         inst_def,call_env_def,gc_def,pop_env_def,push_env_def,ELIM_UNCURRY] >> rveq >> fs[] >>
      rveq >> fs[] >>
      NO_TAC) >>
  TRY(pairarg_tac >> fs[CaseEq"bool"] >> rveq >> rw[] >> NO_TAC) >>
  TRY(rename1 `word_cmp` >> fs[CaseEq"bool"]) >>
  fs[CaseEq "bool",CaseEq"option",CaseEq"prod",CaseEq"wordSem$result"] >>
  rveq >> simp[call_env_def] >>
  rpt(first_x_assum (drule_then strip_assume_tac)) >>
  fs[] >> rpt(first_x_assum (drule_then strip_assume_tac)) >>
  fs[pop_env_def,CaseEq "list",CaseEq"stack_frame",CaseEq"option",CaseEq"prod"] >>
  rveq >> fs[]
QED


Theorem evaluate_stack_limit_stack_max_eq:
  !c s1 res s2.
  evaluate (c,s1) = (res,s2) /\ the s1.stack_limit s1.stack_max >= s1.stack_limit ==>
  the s2.stack_limit s2.stack_max >= s2.stack_limit
Proof
  rpt strip_tac >>
  imp_res_tac evaluate_stack_max >>
  imp_res_tac evaluate_stack_limit >>
  fs[the_eqn] >>
  rpt(PURE_FULL_CASE_TAC >> fs[] >> rveq)
QED

Theorem evaluate_stack_limit_stack_max:
  !c s1 res s2.
  evaluate (c,s1) = (res,s2) /\ the (s1.stack_limit + 1) s1.stack_max > s1.stack_limit ==>
  the (s2.stack_limit + 1) s2.stack_max > s2.stack_limit
Proof
  rpt strip_tac >>
  imp_res_tac evaluate_stack_max >>
  imp_res_tac evaluate_stack_limit >>
  fs[the_eqn] >>
  rpt(PURE_FULL_CASE_TAC >> fs[] >> rveq)
QED



val inc_clock_def = Define `
  inc_clock n (t:('a,'c,'ffi) wordSem$state) = t with clock := t.clock + n`;

Theorem inc_clock_0[simp]:
   !t. inc_clock 0 t = t
Proof
  full_simp_tac(srw_ss())[inc_clock_def,wordSemTheory.state_component_equality]
QED

Theorem inc_clock_inc_clock[simp]:
   !t. inc_clock n (inc_clock m t) = inc_clock (n+m) t
Proof
  full_simp_tac(srw_ss())[inc_clock_def,wordSemTheory.state_component_equality,AC ADD_ASSOC ADD_COMM]
QED



Theorem evaluate_call_push_dec_option_le_stack_max:
  !p args sz env handler s res t ck.
    evaluate (p, call_env args sz
               (push_env env handler (dec_clock (s with clock := ck)))) =(res,t) ==>
    option_le (call_env args sz (push_env env handler s)).stack_max t.stack_max

Proof
  rw [] >>
  drule evaluate_stack_max >>
  TOP_CASE_TAC >> fs [] >> rw [] >>
  Cases_on ` t.stack_max` >> fs [the_eqn] >>
  Cases_on `handler` >> TRY (Cases_on `x''` >> Cases_on `r` >> Cases_on `r'`) >>
  (fs[call_env_def, push_env_def, dec_clock_def, OPTION_MAP2_DEF,IS_SOME_EXISTS,MAX_DEF,
      the_eqn, CaseEq"option", THE_DEF] >> rveq >> fs [] >>
  every_case_tac >> Cases_on `s.locals_size`  >> pairarg_tac >>
  fs[OPTION_MAP2_DEF,IS_SOME_EXISTS,MAX_DEF, the_eqn, CaseEq"option",THE_DEF] >> rveq >>
  every_case_tac >>  fs [] >> rveq >>
  fs[OPTION_MAP2_DEF,IS_SOME_EXISTS,MAX_DEF, the_eqn, CaseEq"option",
     THE_DEF,stack_size_eq2, stack_frame_size_def] >> rveq >> fs [])
QED

Theorem evaluate_stack_max_only_grows:
  !p s r t ck r' t'.
     evaluate (p,s) = (r,t) /\
     evaluate (p,inc_clock ck s) = (r',t') ==>
       option_le t.stack_max t'.stack_max
Proof
  recInduct evaluate_ind >> reverse(rpt strip_tac)
  >- (* Call *)
     (fs[evaluate_def,inc_clock_def] >>
      Cases_on `get_vars args s` >> fs[] >> rveq >> fs[] >>
      Cases_on `bad_dest_args dest args` >> fs[] >> rveq >> fs[] >>
      Cases_on `find_code dest (add_ret_loc ret x) s.code s.stack_size` >> fs[] >> rveq >> fs[] >>
      fs[CaseEq"prod"] >> rveq >> fs[] >> rveq >>
      Cases_on `ret`
      >- (* Tail call *)
      (Cases_on `handler` >> fs[] >> rveq >> fs[] >>
       reverse(Cases_on `s.clock`) >-
         (fs[dec_clock_def,ADD1] >>
          fs[CaseEq"prod",CaseEq"option"] >> rveq >> fs[] >>
          res_tac) >>
       fs[] >> rveq >>
       Cases_on `ck = 0` >> fs[flush_state_def] >> rveq >> fs[] >>
       fs[CaseEq"prod",CaseEq"option"] >> rveq >> fs[] >>
       imp_res_tac evaluate_stack_max_le >>
       fs[call_env_def,option_le_max]) >>
      (* Returning calls *)
      fs[CaseEq"prod"] >> rveq >> fs[] >> rveq >> fs[] >>
      Cases_on `domain names = ∅` >> fs[] >> rveq >> fs[] >>
      Cases_on `cut_env names s.locals` >> fs[] >> rveq >> fs[] >>
      reverse(Cases_on `s.clock`) >-
         (fs[dec_clock_def,ADD1] >>
          fs[CaseEq"prod",CaseEq"option",
             CaseEq"bool"] >> rveq >> fs[] >>
          res_tac >>
          TRY(rename1 `ck + nn` >>
              qpat_x_assum `evaluate (prog, _ with clock := nn) = _` assume_tac >>
              drule_then(qspec_then `ck` mp_tac) evaluate_add_clock >>
              impl_tac >- simp[] >> strip_tac >>
              fs[]) >>
          rename1 `ck + nn` >>
          rename1 `evaluate (prog, _ with clock := nn) = (SOME res,_)` >>
          (reverse(Cases_on `res = TimeOut`) >-
             (qpat_x_assum `evaluate (prog, _ with clock := nn) = _` assume_tac >>
              drule_then(qspec_then `ck` mp_tac) evaluate_add_clock >>
              impl_tac >- simp[] >> strip_tac >>
              fs[] >> rveq >>
              fs[CaseEq"wordSem$result",CaseEq "bool",
                 CaseEq "option",CaseEq"prod"] >> fs[] >> rveq >> fs[] >>
              imp_res_tac pop_env_const >>
              fs[] >>
              res_tac)) >>
          fs[] >> rveq >> fs[] >>
          fs[CaseEq"wordSem$result",CaseEq "bool",
             CaseEq "option",CaseEq"prod"] >>
          fs[] >> rveq >> fs[] >>
          imp_res_tac pop_env_const >>
          fs[] >>
          res_tac >>
          imp_res_tac evaluate_stack_max_le >>
          fs[set_var_def] >> metis_tac[option_le_trans]) >>
      fs[] >>
      Cases_on `ck = 0` >> fs[] >> rveq >> fs[flush_state_def] >>
      fs[CaseEq"wordSem$result",CaseEq "bool",
         CaseEq "option",CaseEq"prod"] >> fs[] >> rveq >> fs[] >>
      imp_res_tac pop_env_const >>
      fs[] >>
      res_tac >>
      imp_res_tac evaluate_stack_max_le >>
      fs[set_var_def] >>
      TRY(Cases_on `handler`) >>
      fs[call_env_def,push_env_def,dec_clock_def,ELIM_UNCURRY] >> metis_tac[option_le_trans])
  >> (* Every case except call *)
  fs[evaluate_def,inc_clock_def,
     CaseEq"option",CaseEq"word_loc",CaseEq"bool",
     CaseEq"prod",CaseEq"list",CaseEq"ffi_result",
     ELIM_UNCURRY,flush_state_def] >>
  rveq >> fs[] >> rveq >> fs[] >> res_tac >>
  (* The remainder deals with subcases originating from Seq *)
  fs[FST_EQ_EQUIV] >>
  rfs[] >> res_tac >>
  qpat_x_assum `evaluate(c1,s) = _` assume_tac >>
  drule_then (qspec_then `ck` mp_tac) evaluate_add_clock >>
  rw[] >>
  fs[] >>
  res_tac >>
  imp_res_tac evaluate_stack_max_le >>
  metis_tac[option_le_trans]
QED

Theorem evaluate_code_only_grows:
  !p s r t. evaluate (p,s) = (r,t) ==> subspt s.code t.code
Proof
  recInduct evaluate_ind \\ rpt conj_tac \\ rpt gen_tac \\ strip_tac
  THEN1 (* Skip *)
   (fs [wordSemTheory.evaluate_def])
  THEN1 (* Alloc *)
   (fs [wordSemTheory.evaluate_def] \\ rveq
    \\ fs [CaseEq"option",CaseEq"word_loc",bool_case_eq] \\ rveq \\ fs []
    \\ imp_res_tac alloc_const \\ fs [])
  THEN1 (* Move *)
   (fs [wordSemTheory.evaluate_def] \\ rveq
    \\ fs [CaseEq"option",CaseEq"word_loc",bool_case_eq] \\ rveq \\ fs [])
  THEN1 (* Inst *)
   (fs [wordSemTheory.evaluate_def] \\ rveq
    \\ fs [CaseEq"option",CaseEq"word_loc",bool_case_eq] \\ rveq \\ fs []
    \\ imp_res_tac inst_const_full \\ fs [])
  THEN1 (* Assign *)
   (fs [wordSemTheory.evaluate_def] \\ rveq
    \\ fs [CaseEq"option",CaseEq"word_loc",bool_case_eq] \\ rveq \\ fs []
    \\ imp_res_tac assign_const \\ fs [set_var_def])
  THEN1 (* Get *)
   (fs [wordSemTheory.evaluate_def] \\ rveq
    \\ fs [CaseEq"option",CaseEq"word_loc",bool_case_eq] \\ rveq \\ fs []
    \\ imp_res_tac assign_const \\ fs [set_var_def])
  THEN1 (* Set *)
   (fs [wordSemTheory.evaluate_def] \\ rveq
    \\ fs [CaseEq"option",CaseEq"word_loc",bool_case_eq] \\ rveq \\ fs []
    \\ fs [set_var_def])
  THEN1 (* OpCurrHeap *)
   (fs [wordSemTheory.evaluate_def] \\ rveq
    \\ fs [CaseEq"option",CaseEq"word_loc",bool_case_eq] \\ rveq \\ fs []
    \\ fs [set_var_def])
  THEN1 (* Store *)
   (fs [wordSemTheory.evaluate_def,mem_store_def] \\ rveq
    \\ fs [CaseEq"option",CaseEq"word_loc",bool_case_eq] \\ rveq \\ fs []
    \\ fs [set_var_def])
  THEN1 (* Tick *)
   (fs [wordSemTheory.evaluate_def,mem_store_def] \\ rveq
    \\ fs [CaseEq"option",CaseEq"word_loc",bool_case_eq] \\ rveq \\ fs []
    \\ fs [flush_state_def])
  THEN1 (* MustTerminate *)
   (fs [wordSemTheory.evaluate_def] \\ rveq
    \\ fs [CaseEq"option",CaseEq"word_loc",bool_case_eq] \\ rveq \\ fs []
    \\ rw [] \\ fs []
    \\ rpt (pop_assum mp_tac)
    \\ pairarg_tac \\ fs [] \\ rw [])
  THEN1 (* Seq *)
   (rpt gen_tac
    \\ fs [wordSemTheory.evaluate_def] \\ rveq
    \\ pairarg_tac \\ fs []
    \\ reverse IF_CASES_TAC THEN1 (fs [] \\ rpt strip_tac \\ rveq \\ fs [])
    \\ strip_tac \\ fs [] \\ rveq \\ fs []
    \\ imp_res_tac subspt_trans \\ fs [])
  THEN1 (* Return *)
   (fs [wordSemTheory.evaluate_def] \\ rveq
    \\ fs [CaseEq"option",CaseEq"word_loc",bool_case_eq]
    \\ rveq \\ fs [flush_state_def])
  THEN1 (* Raise *)
   (fs [wordSemTheory.evaluate_def,jump_exc_def] \\ rveq
    \\ fs [CaseEq"option",CaseEq"word_loc",bool_case_eq,CaseEq"list",
           CaseEq"stack_frame",pair_case_eq]
    \\ rveq \\ fs [flush_state_def]
    \\ rveq \\ fs [flush_state_def])
  THEN1 (* If *)
   (fs [wordSemTheory.evaluate_def] \\ rveq
    \\ fs [CaseEq"option",CaseEq"word_loc",CaseEq"bool",CaseEq"list",
           CaseEq"stack_frame",pair_case_eq]
    \\ rw [] \\ rveq \\ fs [])
  THEN1 (* LocValue *)
   (fs [wordSemTheory.evaluate_def] \\ rveq
    \\ fs [CaseEq"option",CaseEq"word_loc",bool_case_eq]
    \\ rveq \\ fs [flush_state_def,set_var_def])
  THEN1 (* Install *)
   (fs [evaluate_def,pair_case_eq,pair_case_eq,CaseEq"option",CaseEq"word_loc"]
    \\ pairarg_tac \\ fs []
    \\ fs [evaluate_def,pair_case_eq,pair_case_eq,CaseEq"option",
           CaseEq"word_loc",CaseEq"list",CaseEq"bool"]
    \\ rveq \\ fs [] \\ fs [subspt_lookup,lookup_union])
  THEN1 (* CodeBufferWrite *)
   (fs [wordSemTheory.evaluate_def] \\ rveq
    \\ fs [CaseEq"option",CaseEq"word_loc",bool_case_eq]
    \\ rveq \\ fs [set_var_def])
  THEN1 (* DataBufferWrite *)
   (fs [wordSemTheory.evaluate_def] \\ rveq
    \\ fs [CaseEq"option",CaseEq"word_loc",bool_case_eq]
    \\ rveq \\ fs [set_var_def])
  THEN1 (* FFI *)
   (fs [wordSemTheory.evaluate_def] \\ rveq
    \\ fs [CaseEq"option",CaseEq"word_loc",CaseEq"bool",CaseEq"ffi_result"]
    \\ rveq \\ fs [set_var_def,flush_state_def])
  \\ fs [wordSemTheory.evaluate_def] \\ rveq
  \\ fs [CaseEq"option",CaseEq"word_loc",CaseEq"bool",CaseEq"list",
         CaseEq"stack_frame",pair_case_eq,PULL_EXISTS,CaseEq"wordSem$result"]
  \\ rpt strip_tac \\ rveq \\ fs []
  \\ fs [set_var_def]
  \\ imp_res_tac subspt_trans \\ fs []
  \\ imp_res_tac pop_env_const \\ fs []
QED

Theorem s_key_eq_stack_size:
  !xs ys. s_key_eq xs ys ⇒ stack_size xs = stack_size ys
Proof
  Induct \\ Cases_on `ys` \\ fs [s_key_eq_def,stack_size_def]
  \\ Cases_on `h` \\ Cases
  \\ rename [`StackFrame _ _ opt`] \\ Cases_on `opt`
  \\ Cases_on `o0`
  \\ fs [s_frame_key_eq_def,stack_size_frame_def]
  \\ rw [] \\ res_tac \\ fs []
QED

Theorem evaluate_NONE_stack_size_const:
  !p s t. evaluate (p,s) = (NONE,t) ==>
          stack_size t.stack = stack_size s.stack
Proof
  rw [] \\ qspecl_then [`p`,`s`] mp_tac evaluate_stack_swap \\ fs [] \\ rw []
  \\ imp_res_tac s_key_eq_stack_size \\ fs []
QED

val _ = export_theory();
