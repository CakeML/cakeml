(*
  Properties about wordLang and its semantics
*)
Theory wordProps
Libs
  preamble BasicProvers helperLib
Ancestors
  mllist backendProps wordConvs wordLang wordSem asm reg_alloc

val _ = temp_bring_to_front_overload "Set" {Name="Set", Thy="wordLang"};

(*
Main lemmas:
0) Clock lemmas (add_clock, dec_clock, IO monotonicity)
1) Code table constancy across eval
2) Swapping stack for one with identical values (but different keys)
3) Thms to handle the permutation oracle
4) Effect of extra locals (locals_rel)
*)

(*TODO remove *)
val _ = temp_delsimps ["NORMEQ_CONV"];

(*TODO move*)
Theorem domain_fromAList_toAList:
  domain (fromAList (toAList l)) = domain l
Proof
  fs[domain_fromAList,set_MAP_FST_toAList_domain]
QED

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

Theorem ALL_DISTINCT_MEM_IMP_ALOOKUP_SOME:
  ALL_DISTINCT (MAP FST xs) /\ MEM (x,y) xs ==> ALOOKUP xs x = SOME y
Proof
  map_every qid_spec_tac [‘x’, ‘y’] >> Induct_on ‘xs’ >>
  full_simp_tac(srw_ss())[]
  \\ Cases \\ full_simp_tac(srw_ss())[ALOOKUP_def] \\ srw_tac[][]
  \\ res_tac \\ full_simp_tac(srw_ss())[MEM_MAP,FORALL_PROD]
  \\ rev_full_simp_tac(srw_ss())[]
QED

(* -- *)
(*drulel takes a list and tries to apply drule
*)
fun drulel tl = FIRST (map (drule) tl)
(*This is faster than gvs[AllCaseEqs()]*)
val CASE_ONE = (TOP_CASE_TAC ORELSE pairarg_tac )
(* Clock lemmas *)

Theorem case_eq_thms =
  (pair_case_eq::
   bool_case_eq::
   map TypeBase.case_eq_of
       [``:'a option``,``:'a list``,``:'a word_loc``,``:'a inst``,``:'a arith``,
        ``:'a addr``,``:memop``,``:'a wordSem$result``,``:'a ffi_result``])
    |> LIST_CONJ

(*helps with existence proofs
?l'. (s with locals := l) = (s with locals := l')*)
(*TODO does not work when given a goal like
?k'. (s with <|locals := l; clock := k|>) = (s with <|locals := l, clock := k |>)
*)
Theorem state_const[simp]:
   ((s with locals:= l) = (s with locals := l') <=> l = l') /\
   ((s with permute := p) = (s with permute := p') <=> p = p') /\
   ((s with clock := clk) = (s with clock := clk') <=>  clk = clk') /\
   ((s with stack := xs) = (s with stack := xs') <=>  xs = xs')
Proof
   fs[state_component_equality]
QED

Theorem PAIR_MAP_EQ_PAIR[simp]:
  (f ## g) p = (a,b) ⇔ ∃x y. p = (x,y) ∧ f x = a ∧ g y = b
Proof
  Cases_on `p` >> fs[] \\ eq_tac \\ gvs []
QED

(*TODO Weaken this simplification
What that is needed to be pulled down is when
f is a record update like (λs. s with clock := k)
*)
Theorem OPTION_CASE_OPTION_MAP[simp]:
  (option_CASE (OPTION_MAP f a) e g) = option_CASE a e (λx. g (f x))
Proof
  Cases_on `a`
  >> fs[]
QED

(*USEFUL to clean up proofs with the previous lemma*)
Theorem OPTION_CASE_MAP:
   option_CASE x NONE (λx. SOME (f x)) = OPTION_MAP f x
Proof
  Cases_on `x` >> fs[]
QED

(******CONST LEMMAS *****)
Theorem get_var_with_const[simp]:
   get_var x (y with locals_size := ls) = get_var x y /\
   get_var x (y with fp_regs:= fp) = get_var x y /\
   get_var x (y with store:= store) = get_var x y /\
   get_var x (y with stack := xs) = get_var x y /\
   get_var x (y with stack_limit := sl) = get_var x y /\
   get_var x (y with stack_max := sm) = get_var x y /\
   get_var x (y with stack_size := ssize) = get_var x y /\
   get_var x (y with memory := m) = get_var x y /\
   get_var x (y with mdomain := md) = get_var x y /\
   get_var x (y with sh_mdomain := smd) = get_var x y /\
   get_var x (y with permute := p) = get_var x y /\
   get_var x (y with ptr_eq_oracle := po) = get_var x y /\
   get_var x (y with ptr_eq_rel := prel) = get_var x y /\
   get_var x (y with compile := c) = get_var x y /\
   get_var x (y with compile_oracle := co) = get_var x y /\
   get_var x (y with code_buffer := cb) = get_var x y /\
   get_var x (y with data_buffer := db) = get_var x y /\
   get_var x (y with gc_fun := g) = get_var x y /\
   get_var x (y with handler := hd) = get_var x y /\
   get_var x (y with clock := clk) = get_var x y /\
   get_var x (y with termdep := tdep) = get_var x y /\
   get_var x (y with code := cd) = get_var x y /\
   get_var x (y with be := b) = get_var x y /\
   get_var x (y with ffi := ffi) = get_var x y
Proof
  EVAL_TAC
QED

Theorem get_vars_with_const[simp]:
   get_vars x (y with locals_size := ls) = get_vars x y /\
   get_vars x (y with fp_regs:= fp) = get_vars x y /\
   get_vars x (y with store:= store) = get_vars x y /\
   get_vars x (y with stack := xs) = get_vars x y /\
   get_vars x (y with stack_limit := sl) = get_vars x y /\
   get_vars x (y with stack_max := sm) = get_vars x y /\
   get_vars x (y with stack_size := ssize) = get_vars x y /\
   get_vars x (y with memory := m) = get_vars x y /\
   get_vars x (y with mdomain := md) = get_vars x y /\
   get_vars x (y with sh_mdomain := smd) = get_vars x y /\
   get_vars x (y with permute := p) = get_vars x y /\
   get_vars x (y with ptr_eq_oracle := po) = get_vars x y /\
   get_vars x (y with ptr_eq_rel := prel) = get_vars x y /\
   get_vars x (y with compile := c) = get_vars x y /\
   get_vars x (y with compile_oracle := co) = get_vars x y /\
   get_vars x (y with code_buffer := cb) = get_vars x y /\
   get_vars x (y with data_buffer := db) = get_vars x y /\
   get_vars x (y with gc_fun := g) = get_vars x y /\
   get_vars x (y with handler := hd) = get_vars x y /\
   get_vars x (y with clock := clk) = get_vars x y /\
   get_vars x (y with termdep := tdep) = get_vars x y /\
   get_vars x (y with code := cd) = get_vars x y /\
   get_vars x (y with be := b) = get_vars x y /\
   get_vars x (y with ffi := ffi) = get_vars x y
Proof
  Induct_on`x` >>  simp[get_vars_def]
QED

Theorem set_var_const[simp]:
   (set_var x y z).locals_size = z.locals_size ∧
   (set_var x y z).ptr_eq_oracle = z.ptr_eq_oracle ∧
   (set_var x y z).ptr_eq_rel = z.ptr_eq_rel ∧
   (set_var x y z).fp_regs = z.fp_regs ∧
   (set_var x y z).store = z.store ∧
   (set_var x y z).stack = z.stack ∧
   (set_var x y z).stack_limit = z.stack_limit ∧
   (set_var x y z).stack_max = z.stack_max ∧
   (set_var x y z).stack_size = z.stack_size ∧
   (set_var x y z).memory = z.memory ∧
   (set_var x y z).mdomain = z.mdomain ∧
   (set_var x y z).sh_mdomain = z.sh_mdomain ∧
   (set_var x y z).permute = z.permute ∧
   (set_var x y z).compile = z.compile ∧
   (set_var x y z).compile_oracle = z.compile_oracle ∧
   (set_var x y z).code_buffer = z.code_buffer ∧
   (set_var x y z).data_buffer = z.data_buffer ∧
   (set_var x y z).gc_fun = z.gc_fun ∧
   (set_var x y z).handler = z.handler ∧
   (set_var x y z).clock = z.clock ∧
   (set_var x y z).termdep = z.termdep ∧
   (set_var x y z).code = z.code ∧
   (set_var x y z).be = z.be ∧
   (set_var x y z).ffi = z.ffi
Proof
  EVAL_TAC
QED

Theorem set_var_with_const[simp]:
  set_var x y (z with locals_size := ls) = set_var x y z with locals_size := ls /\
  set_var x y (z with fp_regs := fp) = set_var x y z with fp_regs := fp /\
  set_var x y (z with store := store) = set_var x y z with store := store /\
  set_var x y (z with stack := xs) = set_var x y z with stack := xs /\
  set_var x y (z with stack_limit := sl) = set_var x y z with stack_limit := sl /\
  set_var x y (z with stack_max := sm) = set_var x y z with stack_max := sm /\
  set_var x y (z with stack_size := ssize) = set_var x y z with stack_size := ssize /\
  set_var x y (z with memory := m) = set_var x y z with memory := m /\
  set_var x y (z with mdomain := md) = set_var x y z with mdomain := md /\
  set_var x y (z with sh_mdomain := smd) = set_var x y z with sh_mdomain := smd /\
  set_var x y (z with permute := p) = set_var x y z with permute := p /\
  set_var x y (z with ptr_eq_oracle := po) = set_var x y z with ptr_eq_oracle := po /\
  set_var x y (z with ptr_eq_rel := prel) = set_var x y z with ptr_eq_rel := prel /\
  set_var x y (z with compile := c) = set_var x y z with compile := c /\
  set_var x y (z with compile_oracle := co) = set_var x y z with compile_oracle := co /\
  set_var x y (z with code_buffer := cb) = set_var x y z with code_buffer := cb /\
  set_var x y (z with data_buffer := db) = set_var x y z with data_buffer := db /\
  set_var x y (z with gc_fun := g) = set_var x y z with gc_fun := g /\
  set_var x y (z with handler := hd) = set_var x y z with handler := hd /\
  set_var x y (z with clock := clk) = set_var x y z with clock := clk /\
  set_var x y (z with termdep := tdep) = set_var x y z with termdep := tdep /\
  set_var x y (z with code := cd) = set_var x y z with code := cd /\
  set_var x y (z with be := b) = set_var x y z with be := b /\
  set_var x y (z with ffi := ffi) = set_var x y z with ffi := ffi
Proof
  EVAL_TAC
QED

Theorem unset_var_const[simp]:
   (unset_var x z).locals_size = z.locals_size ∧
   (unset_var x z).ptr_eq_oracle = z.ptr_eq_oracle ∧
   (unset_var x z).ptr_eq_rel = z.ptr_eq_rel ∧
   (unset_var x z).fp_regs = z.fp_regs ∧
   (unset_var x z).store = z.store ∧
   (unset_var x z).stack = z.stack ∧
   (unset_var x z).stack_limit = z.stack_limit ∧
   (unset_var x z).stack_max = z.stack_max ∧
   (unset_var x z).stack_size = z.stack_size ∧
   (unset_var x z).memory = z.memory ∧
   (unset_var x z).mdomain = z.mdomain ∧
   (unset_var x z).sh_mdomain = z.sh_mdomain ∧
   (unset_var x z).permute = z.permute ∧
   (unset_var x z).compile = z.compile ∧
   (unset_var x z).compile_oracle = z.compile_oracle ∧
   (unset_var x z).code_buffer = z.code_buffer ∧
   (unset_var x z).data_buffer = z.data_buffer ∧
   (unset_var x z).gc_fun = z.gc_fun ∧
   (unset_var x z).handler = z.handler ∧
   (unset_var x z).clock = z.clock ∧
   (unset_var x z).termdep = z.termdep ∧
   (unset_var x z).code = z.code ∧
   (unset_var x z).be = z.be ∧
   (unset_var x z).ffi = z.ffi
Proof
  EVAL_TAC
QED

Theorem unset_var_with_const[simp]:
  unset_var x (z with locals_size := ls) = unset_var x z with locals_size := ls /\
  unset_var x (z with fp_regs := fp) = unset_var x z with fp_regs := fp /\
  unset_var x (z with store := store) = unset_var x z with store := store /\
  unset_var x (z with stack := xs) = unset_var x z with stack := xs /\
  unset_var x (z with stack_limit := sl) = unset_var x z with stack_limit := sl /\
  unset_var x (z with stack_max := sm) = unset_var x z with stack_max := sm /\
  unset_var x (z with stack_size := ssize) = unset_var x z with stack_size := ssize /\
  unset_var x (z with memory := m) = unset_var x z with memory := m /\
  unset_var x (z with mdomain := md) = unset_var x z with mdomain := md /\
  unset_var x (z with sh_mdomain := smd) = unset_var x z with sh_mdomain := smd /\
  unset_var x (z with permute := p) = unset_var x z with permute := p /\
  unset_var x (z with ptr_eq_oracle := po) = unset_var x z with ptr_eq_oracle := po /\
  unset_var x (z with ptr_eq_rel := prel) = unset_var x z with ptr_eq_rel := prel /\
  unset_var x (z with compile := c) = unset_var x z with compile := c /\
  unset_var x (z with compile_oracle := co) = unset_var x z with compile_oracle := co /\
  unset_var x (z with code_buffer := cb) = unset_var x z with code_buffer := cb /\
  unset_var x (z with data_buffer := db) = unset_var x z with data_buffer := db /\
  unset_var x (z with gc_fun := g) = unset_var x z with gc_fun := g /\
  unset_var x (z with handler := hd) = unset_var x z with handler := hd /\
  unset_var x (z with clock := clk) = unset_var x z with clock := clk /\
  unset_var x (z with termdep := tdep) = unset_var x z with termdep := tdep /\
  unset_var x (z with code := cd) = unset_var x z with code := cd /\
  unset_var x (z with be := b) = unset_var x z with be := b /\
  unset_var x (z with ffi := ffi) = unset_var x z with ffi := ffi
Proof
  EVAL_TAC
QED

Theorem set_vars_const[simp]:
   (set_vars x y z).locals_size = z.locals_size ∧
   (set_vars x y z).ptr_eq_oracle = z.ptr_eq_oracle ∧
   (set_vars x y z).ptr_eq_rel = z.ptr_eq_rel ∧
   (set_vars x y z).fp_regs = z.fp_regs ∧
   (set_vars x y z).store = z.store ∧
   (set_vars x y z).stack = z.stack ∧
   (set_vars x y z).stack_limit = z.stack_limit ∧
   (set_vars x y z).stack_max = z.stack_max ∧
   (set_vars x y z).stack_size = z.stack_size ∧
   (set_vars x y z).memory = z.memory ∧
   (set_vars x y z).mdomain = z.mdomain ∧
   (set_vars x y z).sh_mdomain = z.sh_mdomain ∧
   (set_vars x y z).permute = z.permute ∧
   (set_vars x y z).compile = z.compile ∧
   (set_vars x y z).compile_oracle = z.compile_oracle ∧
   (set_vars x y z).code_buffer = z.code_buffer ∧
   (set_vars x y z).data_buffer = z.data_buffer ∧
   (set_vars x y z).gc_fun = z.gc_fun ∧
   (set_vars x y z).handler = z.handler ∧
   (set_vars x y z).clock = z.clock ∧
   (set_vars x y z).termdep = z.termdep ∧
   (set_vars x y z).code = z.code ∧
   (set_vars x y z).be = z.be ∧
   (set_vars x y z).ffi = z.ffi
Proof
  EVAL_TAC
QED

Theorem set_vars_with_const[simp]:
  set_vars x y (z with locals_size := ls) = set_vars x y z with locals_size := ls /\
  set_vars x y (z with fp_regs := fp) = set_vars x y z with fp_regs := fp /\
  set_vars x y (z with store := store) = set_vars x y z with store := store /\
  set_vars x y (z with stack := xs) = set_vars x y z with stack := xs /\
  set_vars x y (z with stack_limit := sl) = set_vars x y z with stack_limit := sl /\
  set_vars x y (z with stack_max := sm) = set_vars x y z with stack_max := sm /\
  set_vars x y (z with stack_size := ssize) = set_vars x y z with stack_size := ssize /\
  set_vars x y (z with memory := m) = set_vars x y z with memory := m /\
  set_vars x y (z with mdomain := md) = set_vars x y z with mdomain := md /\
  set_vars x y (z with sh_mdomain := smd) = set_vars x y z with sh_mdomain := smd /\
  set_vars x y (z with permute := p) = set_vars x y z with permute := p /\
  set_vars x y (z with ptr_eq_oracle := po) = set_vars x y z with ptr_eq_oracle := po /\
  set_vars x y (z with ptr_eq_rel := prel) = set_vars x y z with ptr_eq_rel := prel /\
  set_vars x y (z with compile := c) = set_vars x y z with compile := c /\
  set_vars x y (z with compile_oracle := co) = set_vars x y z with compile_oracle := co /\
  set_vars x y (z with code_buffer := cb) = set_vars x y z with code_buffer := cb /\
  set_vars x y (z with data_buffer := db) = set_vars x y z with data_buffer := db /\
  set_vars x y (z with gc_fun := g) = set_vars x y z with gc_fun := g /\
  set_vars x y (z with handler := hd) = set_vars x y z with handler := hd /\
  set_vars x y (z with clock := clk) = set_vars x y z with clock := clk /\
  set_vars x y (z with termdep := tdep) = set_vars x y z with termdep := tdep /\
  set_vars x y (z with code := cd) = set_vars x y z with code := cd /\
  set_vars x y (z with be := b) = set_vars x y z with be := b /\
  set_vars x y (z with ffi := ffi) = set_vars x y z with ffi := ffi
Proof
  EVAL_TAC
QED

Theorem get_store_with_const[simp]:
   get_store x (y with locals := l) = get_store x y /\
   get_store x (y with locals_size := ls) = get_store x y /\
   get_store x (y with fp_regs:= fp) = get_store x y /\
   get_store x (y with stack := xs) = get_store x y /\
   get_store x (y with stack_limit := sl) = get_store x y /\
   get_store x (y with stack_max := sm) = get_store x y /\
   get_store x (y with stack_size := ssize) = get_store x y /\
   get_store x (y with memory := m) = get_store x y /\
   get_store x (y with mdomain := md) = get_store x y /\
   get_store x (y with sh_mdomain := smd) = get_store x y /\
   get_store x (y with permute := p) = get_store x y /\
   get_store x (y with ptr_eq_oracle := po) = get_store x y /\
   get_store x (y with ptr_eq_rel := prel) = get_store x y /\
   get_store x (y with compile := c) = get_store x y /\
   get_store x (y with compile_oracle := co) = get_store x y /\
   get_store x (y with code_buffer := cb) = get_store x y /\
   get_store x (y with data_buffer := db) = get_store x y /\
   get_store x (y with gc_fun := g) = get_store x y /\
   get_store x (y with handler := hd) = get_store x y /\
   get_store x (y with clock := clk) = get_store x y /\
   get_store x (y with termdep := tdep) = get_store x y /\
   get_store x (y with code := cd) = get_store x y /\
   get_store x (y with be := b) = get_store x y /\
   get_store x (y with ffi := ffi) = get_store x y
Proof
  EVAL_TAC
QED

Theorem set_store_const[simp]:
   (set_store x y z).locals = z.locals ∧
   (set_store x y z).ptr_eq_oracle = z.ptr_eq_oracle ∧
   (set_store x y z).ptr_eq_rel = z.ptr_eq_rel ∧
   (set_store x y z).locals_size = z.locals_size ∧
   (set_store x y z).fp_regs = z.fp_regs ∧
   (set_store x y z).stack = z.stack ∧
   (set_store x y z).stack_limit = z.stack_limit ∧
   (set_store x y z).stack_max = z.stack_max ∧
   (set_store x y z).stack_size = z.stack_size ∧
   (set_store x y z).memory = z.memory ∧
   (set_store x y z).mdomain = z.mdomain ∧
   (set_store x y z).sh_mdomain = z.sh_mdomain ∧
   (set_store x y z).permute = z.permute ∧
   (set_store x y z).compile = z.compile ∧
   (set_store x y z).compile_oracle = z.compile_oracle ∧
   (set_store x y z).code_buffer = z.code_buffer ∧
   (set_store x y z).data_buffer = z.data_buffer ∧
   (set_store x y z).gc_fun = z.gc_fun ∧
   (set_store x y z).handler = z.handler ∧
   (set_store x y z).clock = z.clock ∧
   (set_store x y z).termdep = z.termdep ∧
   (set_store x y z).code = z.code ∧
   (set_store x y z).be = z.be ∧
   (set_store x y z).ffi = z.ffi
Proof
  EVAL_TAC
QED

Theorem set_store_with_const[simp]:
  set_store x y (z with locals := l) = set_store x y z with locals := l /\
  set_store x y (z with locals_size := ls) = set_store x y z with locals_size := ls /\
  set_store x y (z with fp_regs := fp) = set_store x y z with fp_regs := fp /\
  set_store x y (z with stack := xs) = set_store x y z with stack := xs /\
  set_store x y (z with stack_limit := sl) = set_store x y z with stack_limit := sl /\
  set_store x y (z with stack_max := sm) = set_store x y z with stack_max := sm /\
  set_store x y (z with stack_size := ssize) = set_store x y z with stack_size := ssize /\
  set_store x y (z with memory := m) = set_store x y z with memory := m /\
  set_store x y (z with mdomain := md) = set_store x y z with mdomain := md /\
  set_store x y (z with sh_mdomain := smd) = set_store x y z with sh_mdomain := smd /\
  set_store x y (z with permute := p) = set_store x y z with permute := p /\
  set_store x y (z with ptr_eq_oracle := po) = set_store x y z with ptr_eq_oracle := po /\
  set_store x y (z with ptr_eq_rel := prel) = set_store x y z with ptr_eq_rel := prel /\
  set_store x y (z with compile := c) = set_store x y z with compile := c /\
  set_store x y (z with compile_oracle := co) = set_store x y z with compile_oracle := co /\
  set_store x y (z with code_buffer := cb) = set_store x y z with code_buffer := cb /\
  set_store x y (z with data_buffer := db) = set_store x y z with data_buffer := db /\
  set_store x y (z with gc_fun := g) = set_store x y z with gc_fun := g /\
  set_store x y (z with handler := hd) = set_store x y z with handler := hd /\
  set_store x y (z with clock := clk) = set_store x y z with clock := clk /\
  set_store x y (z with termdep := tdep) = set_store x y z with termdep := tdep /\
  set_store x y (z with code := cd) = set_store x y z with code := cd /\
  set_store x y (z with be := b) = set_store x y z with be := b /\
  set_store x y (z with ffi := ffi) = set_store x y z with ffi := ffi
Proof
  EVAL_TAC
QED


Theorem push_env_const[simp]:
   (push_env x y z).clock = z.clock ∧
   (push_env x y z).ptr_eq_oracle = z.ptr_eq_oracle ∧
   (push_env x y z).ptr_eq_rel = z.ptr_eq_rel ∧
   (push_env x y z).memory = z.memory ∧
   (push_env x y z).store = z.store ∧
   (push_env x NONE z).handler = z.handler ∧
   (push_env x y z).ffi = z.ffi ∧
   (push_env x y z).termdep = z.termdep ∧
   (push_env x y z).data_buffer = z.data_buffer ∧
   (push_env x y z).code_buffer = z.code_buffer ∧
   (push_env x y z).compile = z.compile ∧
   (push_env x y z).compile_oracle = z.compile_oracle ∧
   (push_env x y z).mdomain = z.mdomain ∧
   (push_env x y z).sh_mdomain = z.sh_mdomain ∧
   (push_env x y z).gc_fun = z.gc_fun ∧
   (push_env x y z).be = z.be ∧
   (push_env x y z).fp_regs = z.fp_regs ∧
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
   (push_env x y (z with compile := c) = push_env x y z with compile := c) ∧
   (push_env x y (z with compile_oracle := co) = push_env x y z with compile_oracle := co) ∧
   (push_env x y (z with code := code) = push_env x y z with code := code) ∧
   (push_env x y (z with termdep := termdep) = push_env x y z with termdep := termdep) ∧
   (push_env x y (z with locals := l) = push_env x y z with locals := l) ∧
   (push_env x y (z with ptr_eq_oracle := po) = push_env x y z with ptr_eq_oracle := po) ∧
   (push_env x y (z with ptr_eq_rel := prel) = push_env x y z with ptr_eq_rel := prel)
Proof
  Cases_on`y`>>srw_tac[][push_env_def] >> unabbrev_all_tac >> simp[state_component_equality] >>
  rename1`SOME p` >>
  PairCases_on`p` >>
  srw_tac[][push_env_def] >> unabbrev_all_tac >> simp[state_component_equality]
QED

Theorem pop_env_const:
   pop_env x = SOME y ⇒
   pop_env x = SOME y ⇒
   y.clock = x.clock /\
   y.ptr_eq_oracle = x.ptr_eq_oracle /\
   y.ptr_eq_rel = x.ptr_eq_rel /\
   y.ffi = x.ffi ∧
   y.be = x.be ∧
   y.compile = x.compile ∧
   y.compile_oracle = x.compile_oracle ∧
   y.memory = x.memory ∧
   y.mdomain = x.mdomain ∧
   y.sh_mdomain = x.sh_mdomain ∧
   y.store = x.store ∧
   y.fp_regs = x.fp_regs ∧
   y.gc_fun = x.gc_fun ∧
   y.termdep = x.termdep ∧
   y.permute = x.permute ∧
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
   pop_env (z with compile:= c) = OPTION_MAP (λs. s with compile := c) (pop_env z) ∧
   pop_env (z with compile_oracle := co) = OPTION_MAP (λs. s with compile_oracle := co) (pop_env z) ∧
   pop_env (z with code := code) = OPTION_MAP (λs. s with code := code) (pop_env z) ∧
   pop_env (z with termdep := termdep) = OPTION_MAP (λs. s with termdep := termdep) (pop_env z) ∧
   pop_env (z with permute:= perm) = OPTION_MAP (λs. s with permute := perm) (pop_env z) ∧
   pop_env (z with ptr_eq_oracle := po) = OPTION_MAP (λs. s with ptr_eq_oracle := po) (pop_env z) ∧
   pop_env (z with ptr_eq_rel := prel) = OPTION_MAP (λs. s with ptr_eq_rel := prel) (pop_env z) ∧
   pop_env (z with locals := l) = pop_env z /\
   pop_env (z with locals_size := ls) = pop_env z
Proof
  srw_tac[][pop_env_def] >> every_case_tac >> full_simp_tac(srw_ss())[]
QED

(*FIXME dupe*)
(*code and gc_fun are unchanged across eval*)
Theorem pop_env_code_gc_fun_clock:
    pop_env r = SOME x ⇒
  r.ptr_eq_oracle = x.ptr_eq_oracle ∧
  r.ptr_eq_rel = x.ptr_eq_rel ∧
  r.code = x.code ∧
  r.code_buffer = x.code_buffer ∧
  r.data_buffer = x.data_buffer ∧
  r.gc_fun = x.gc_fun ∧
  r.clock = x.clock ∧
  r.be = x.be ∧
  r.mdomain = x.mdomain ∧
  r.sh_mdomain = x.sh_mdomain ∧
  r.compile = x.compile ∧
  r.compile_oracle = x.compile_oracle ∧
  r.stack_limit = x.stack_limit ∧
  r.stack_max = x.stack_max ∧
  r.stack_size = x.stack_size
Proof
  fs[pop_env_def]>>EVERY_CASE_TAC>>fs[state_component_equality]
QED

Theorem call_env_const[simp]:
   (call_env x ss y).store = y.store ∧
   (call_env x ss y).ptr_eq_oracle = y.ptr_eq_oracle ∧
   (call_env x ss y).ptr_eq_rel = y.ptr_eq_rel ∧
   (call_env x ss y).termdep = y.termdep ∧
   (call_env x ss y).clock = y.clock ∧
   (call_env x ss y).handler = y.handler ∧
   (call_env x ss y).stack = y.stack ∧
   (call_env x ss y).compile_oracle = y.compile_oracle ∧
   (call_env x ss y).compile = y.compile ∧
   (call_env x ss y).be = y.be ∧
   (call_env x ss y).memory = y.memory ∧
   (call_env x ss y).mdomain = y.mdomain ∧
   (call_env x ss y).sh_mdomain = y.sh_mdomain ∧
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
   call_env x ss (y with locals := l) = call_env x ss y /\
   call_env x ss (y with clock := k) = call_env x ss y with clock := k /\
   call_env x ss (y with termdep := termdep) = call_env x ss y with termdep := termdep /\
   call_env x ss (y with compile := c) = call_env x ss y with compile := c /\
   call_env x ss (y with compile_oracle := co) = call_env x ss y with compile_oracle := co /\
   call_env x ss (y with code := code) = call_env x ss y with code := code /\
   call_env x ss (y with handler := k) = call_env x ss y with handler := k /\
   call_env x ss (y with permute := perm) = call_env x ss y with permute := perm /\
   call_env x ss (y with ptr_eq_oracle := po) = call_env x ss y with ptr_eq_oracle := po /\
   call_env x ss (y with ptr_eq_rel := prel) = call_env x ss y with ptr_eq_rel := prel
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
   (flush_state b y).ptr_eq_oracle = y.ptr_eq_oracle ∧
   (flush_state b y).ptr_eq_rel = y.ptr_eq_rel ∧
   (flush_state F y).stack      = y.stack
Proof
  Cases_on `b` \\ EVAL_TAC
QED

Theorem flush_state_with_const[simp]:
   flush_state b (y with locals := l) = flush_state b y /\
   flush_state b (y with locals_size := ls) = flush_state b y /\
   flush_state T (y with stack := xs) = flush_state T y /\
   flush_state b (y with permute := p) = flush_state b y with permute := p /\
   flush_state b (y with ptr_eq_oracle := po) = flush_state b y with ptr_eq_oracle := po /\
   flush_state b (y with ptr_eq_rel := prel) = flush_state b y with ptr_eq_rel := prel /\
   flush_state b (y with stack_max := sm) = flush_state b y with stack_max := sm /\
   flush_state b (y with clock := k) = flush_state b y with clock := k /\
   flush_state b (y with compile_oracle := co) =
     flush_state b y with compile_oracle := co
Proof
 Cases_on `b` \\ EVAL_TAC
QED

Theorem has_space_with_const[simp]:
   has_space x (y with clock := k) = has_space x y /\
   has_space x (y with compile:= c) = has_space x y /\
   has_space x (y with compile_oracle := co) = has_space x y /\
   has_space x (y with code := code) = has_space x y /\
   has_space x (y with termdep := termdep) = has_space x y /\
   has_space x (y with locals := l) = has_space x y /\
   has_space x (y with locals_size := ls) = has_space x y /\
   has_space x (y with stack := xs) = has_space x y /\
   has_space x (y with ptr_eq_oracle := po) = has_space x y /\
   has_space x (y with ptr_eq_rel := prel) = has_space x y
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
   y.handler = x.handler ∧
   y.compile_oracle = x.compile_oracle ∧
   y.locals_size = x.locals_size ∧
   y.stack_limit = x.stack_limit ∧
   y.stack_max = x.stack_max ∧
   y.stack_size = x.stack_size ∧
   y.ptr_eq_oracle = x.ptr_eq_oracle ∧
   y.ptr_eq_rel = x.ptr_eq_rel
Proof
  simp[gc_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> srw_tac[][]
QED

Theorem gc_with_const[simp]:
   gc (x with clock := k) = OPTION_MAP (λs. s with clock := k) (gc x) ∧
   gc (x with compile := c) = OPTION_MAP (λs. s with compile := c) (gc x) ∧
   gc (x with compile_oracle := co) = OPTION_MAP (λs. s with compile_oracle := co) (gc x) ∧
   gc (x with code := code) = OPTION_MAP (λs. s with code := code) (gc x) ∧
   gc (x with permute := perm) = OPTION_MAP (λs. s with permute := perm) (gc x) ∧
   gc (x with ptr_eq_oracle := po) = OPTION_MAP (λs. s with ptr_eq_oracle := po) (gc x) ∧
   gc (x with ptr_eq_rel := prel) = OPTION_MAP (λs. s with ptr_eq_rel := prel) (gc x) ∧
   gc (x with termdep := t) = OPTION_MAP (λs. s with termdep := t) (gc x) /\
   gc (x with locals := l) = OPTION_MAP (λs. s with locals := l) (gc x) /\
   gc (x with locals_size := ls) = OPTION_MAP (λs. s with locals_size := ls) (gc x)
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
   s'.stack_size = s.stack_size ∧
   s'.ptr_eq_oracle = s.ptr_eq_oracle ∧
   s'.ptr_eq_rel = s.ptr_eq_rel
Proof
  rpt strip_tac >>
  gvs[AllCaseEqs(),alloc_def] >>
  imp_res_tac pop_env_const >> full_simp_tac(srw_ss())[] >>
  imp_res_tac gc_const >> full_simp_tac(srw_ss())[]
QED

(*TODO merge*)

Theorem alloc_code_gc_fun_const:
  alloc x names s = (res,t) ⇒
  t.ptr_eq_oracle = s.ptr_eq_oracle /\
  t.ptr_eq_rel = s.ptr_eq_rel /\
  t.code = s.code /\
  t.code_buffer = s.code_buffer /\
  t.data_buffer = s.data_buffer /\
  t.gc_fun = s.gc_fun /\
  t.mdomain = s.mdomain /\
  t.sh_mdomain = s.sh_mdomain /\
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

Theorem alloc_with_const[simp]:
   alloc c names (s with clock := k) = (I ## (λs. s with clock := k)) (alloc c names s) /\
   alloc c names (s with termdep := t) = (I ## (λs. s with termdep := t)) (alloc c names s) /\
   alloc c names (s with code := code) = (I ## (λs. s with code := code)) (alloc c names s) /\
   alloc c names (s with compile_oracle := compile_oracle) = (I ## (λs. s with compile_oracle := compile_oracle)) (alloc c names s) /\
   alloc c names (s with compile := comp) = (I ## (λs. s with compile := comp)) (alloc c names s) /\
   alloc c names (s with ptr_eq_oracle := po) = (I ## (λs. s with ptr_eq_oracle := po)) (alloc c names s) /\
   alloc c names (s with ptr_eq_rel := prel) = (I ## (λs. s with ptr_eq_rel := prel)) (alloc c names s)
Proof
  fs[alloc_def] >> EVERY_CASE_TAC >> fs[flush_state_def]
QED

Theorem get_fp_var_with_const[simp]:
   get_fp_var x (y with locals := l) = get_fp_var x y /\
   get_fp_var x (y with locals_size := ls) = get_fp_var x y /\
   get_fp_var x (y with store := store) = get_fp_var x y /\
   get_fp_var x (y with stack := xs) = get_fp_var x y /\
   get_fp_var x (y with stack_limit := sl) = get_fp_var x y /\
   get_fp_var x (y with stack_max := sm) = get_fp_var x y /\
   get_fp_var x (y with stack_size := ssize) = get_fp_var x y /\
   get_fp_var x (y with memory := m) = get_fp_var x y /\
   get_fp_var x (y with mdomain := md) = get_fp_var x y /\
   get_fp_var x (y with sh_mdomain := smd) = get_fp_var x y /\
   get_fp_var x (y with permute := p) = get_fp_var x y /\
   get_fp_var x (y with ptr_eq_oracle := po) = get_fp_var x y /\
   get_fp_var x (y with ptr_eq_rel := prel) = get_fp_var x y /\
   get_fp_var x (y with compile := c) = get_fp_var x y /\
   get_fp_var x (y with compile_oracle := co) = get_fp_var x y /\
   get_fp_var x (y with code_buffer := cb) = get_fp_var x y /\
   get_fp_var x (y with data_buffer := db) = get_fp_var x y /\
   get_fp_var x (y with gc_fun := g) = get_fp_var x y /\
   get_fp_var x (y with handler := hd) = get_fp_var x y /\
   get_fp_var x (y with clock := clk) = get_fp_var x y /\
   get_fp_var x (y with termdep := tdep) = get_fp_var x y /\
   get_fp_var x (y with code := cd) = get_fp_var x y /\
   get_fp_var x (y with be := b) = get_fp_var x y /\
   get_fp_var x (y with ffi := ffi) = get_fp_var x y
Proof
  EVAL_TAC
QED

Theorem set_fp_var_const[simp]:
   (set_fp_var x y z).locals = z.locals ∧
   (set_fp_var x y z).locals_size = z.locals_size ∧
   (set_fp_var x y z).ptr_eq_oracle = z.ptr_eq_oracle ∧
   (set_fp_var x y z).ptr_eq_rel = z.ptr_eq_rel ∧
   (set_fp_var x y z).store = z.store ∧
   (set_fp_var x y z).stack = z.stack ∧
   (set_fp_var x y z).stack_limit = z.stack_limit ∧
   (set_fp_var x y z).stack_max = z.stack_max ∧
   (set_fp_var x y z).stack_size = z.stack_size ∧
   (set_fp_var x y z).memory = z.memory ∧
   (set_fp_var x y z).mdomain = z.mdomain ∧
   (set_fp_var x y z).sh_mdomain = z.sh_mdomain ∧
   (set_fp_var x y z).permute = z.permute ∧
   (set_fp_var x y z).compile = z.compile ∧
   (set_fp_var x y z).compile_oracle = z.compile_oracle ∧
   (set_fp_var x y z).code_buffer = z.code_buffer ∧
   (set_fp_var x y z).data_buffer = z.data_buffer ∧
   (set_fp_var x y z).gc_fun = z.gc_fun ∧
   (set_fp_var x y z).handler = z.handler ∧
   (set_fp_var x y z).clock = z.clock ∧
   (set_fp_var x y z).termdep = z.termdep ∧
   (set_fp_var x y z).code = z.code ∧
   (set_fp_var x y z).be = z.be ∧
   (set_fp_var x y z).ffi = z.ffi
Proof
  EVAL_TAC
QED

Theorem set_fp_var_with_const[simp]:
  set_fp_var x y (z with locals := l) = set_fp_var x y z with locals := l /\
  set_fp_var x y (z with locals_size := ls) = set_fp_var x y z with locals_size := ls /\
  set_fp_var x y (z with store := store) = set_fp_var x y z with store := store /\
  set_fp_var x y (z with stack := xs) = set_fp_var x y z with stack := xs /\
  set_fp_var x y (z with stack_limit := sl) = set_fp_var x y z with stack_limit := sl /\
  set_fp_var x y (z with stack_max := sm) = set_fp_var x y z with stack_max := sm /\
  set_fp_var x y (z with stack_size := ssize) = set_fp_var x y z with stack_size := ssize /\
  set_fp_var x y (z with memory := m) = set_fp_var x y z with memory := m /\
  set_fp_var x y (z with mdomain := md) = set_fp_var x y z with mdomain := md /\
  set_fp_var x y (z with sh_mdomain := smd) = set_fp_var x y z with sh_mdomain := smd /\
  set_fp_var x y (z with permute := p) = set_fp_var x y z with permute := p /\
  set_fp_var x y (z with ptr_eq_oracle := po) = set_fp_var x y z with ptr_eq_oracle := po /\
  set_fp_var x y (z with ptr_eq_rel := prel) = set_fp_var x y z with ptr_eq_rel := prel /\
  set_fp_var x y (z with compile := c) = set_fp_var x y z with compile := c /\
  set_fp_var x y (z with compile_oracle := co) = set_fp_var x y z with compile_oracle := co /\
  set_fp_var x y (z with code_buffer := cb) = set_fp_var x y z with code_buffer := cb /\
  set_fp_var x y (z with data_buffer := db) = set_fp_var x y z with data_buffer := db /\
  set_fp_var x y (z with gc_fun := g) = set_fp_var x y z with gc_fun := g /\
  set_fp_var x y (z with handler := hd) = set_fp_var x y z with handler := hd /\
  set_fp_var x y (z with clock := clk) = set_fp_var x y z with clock := clk /\
  set_fp_var x y (z with termdep := tdep) = set_fp_var x y z with termdep := tdep /\
  set_fp_var x y (z with code := cd) = set_fp_var x y z with code := cd /\
  set_fp_var x y (z with be := b) = set_fp_var x y z with be := b /\
  set_fp_var x y (z with ffi := ffi) = set_fp_var x y z with ffi := ffi
Proof
  EVAL_TAC
QED

Theorem mem_load_with_const[simp]:
   mem_load x (y with locals := l) = mem_load x y ∧
   mem_load x (y with termdep := td) = mem_load x y ∧
   mem_load x (y with clock := k) = mem_load x y ∧
   mem_load x (y with stack := xs) = mem_load x y ∧
   mem_load x (y with permute := perm) = mem_load x y ∧
   mem_load x (y with ptr_eq_oracle := po) = mem_load x y ∧
   mem_load x (y with ptr_eq_rel := prel) = mem_load x y ∧
   mem_load x (y with code := c) = mem_load x y ∧
   mem_load x (y with compile_oracle := co) = mem_load x y ∧
   mem_load x (y with compile := cc) = mem_load x y
Proof
  EVAL_TAC
QED

Theorem mem_store_const:
   mem_store x y z = SOME a ⇒
   a.locals = z.locals ∧
   a.clock = z.clock ∧
   a.be = z.be ∧
   a.gc_fun = z.gc_fun ∧
   a.mdomain = z.mdomain ∧
   a.sh_mdomain = z.sh_mdomain ∧
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
   a.stack_size = z.stack_size ∧
   a.ptr_eq_oracle = z.ptr_eq_oracle ∧
   a.ptr_eq_rel = z.ptr_eq_rel
Proof
  EVAL_TAC >> srw_tac[][] >> srw_tac[][]
QED


Theorem mem_store_with_const[simp]:
   mem_store x z (y with locals := l) = OPTION_MAP (λs. s with locals := l) (mem_store x z y) /\
   mem_store x z (y with clock := k) = OPTION_MAP (λs. s with clock := k) (mem_store x z y) /\
   mem_store x z (y with code := code) = OPTION_MAP (λs. s with code := code) (mem_store x z y) /\
   mem_store x z (y with compile := c) = OPTION_MAP (λs. s with compile := c) (mem_store x z y) /\
   mem_store x z (y with compile_oracle := co) = OPTION_MAP (λs. s with compile_oracle := co) (mem_store x z y) /\
   mem_store x z (y with permute := perm) = OPTION_MAP (λs. s with permute := perm) (mem_store x z y) /\
   mem_store x z (y with ptr_eq_oracle := po) = OPTION_MAP (λs. s with ptr_eq_oracle := po) (mem_store x z y) /\
   mem_store x z (y with ptr_eq_rel := prel) = OPTION_MAP (λs. s with ptr_eq_rel := prel) (mem_store x z y) /\
   mem_store x z (y with stack := xs) = OPTION_MAP (λs. s with stack := xs) (mem_store x z y)
Proof
  EVAL_TAC >> every_case_tac >> simp[]
QED

Theorem word_exp_with_const[simp]:
   ∀x y.
  word_exp (x with clock := k) y = word_exp x y ∧
  word_exp (x with stack := xs) y = word_exp x y ∧
  word_exp (x with permute := perm) y = word_exp x y ∧
  word_exp (x with ptr_eq_oracle := po) y = word_exp x y ∧
  word_exp (x with ptr_eq_rel := prel) y = word_exp x y ∧
  word_exp (x with termdep := termdep) y = word_exp x y ∧
  word_exp (x with code := c) y = word_exp x y ∧
  word_exp (x with compile_oracle := co) y = word_exp x y ∧
  word_exp (x with compile := cc) y = word_exp x y
Proof
  recInduct word_exp_ind >> simp[word_exp_def] >>
  rpt STRIP_TAC >>
  qpat_abbrev_tac `ls = MAP A B` >>
  qpat_abbrev_tac `ls' = MAP A B` >>
  `ls = ls'`
     by (unabbrev_all_tac >> simp[MAP_EQ_f]) >>
  simp[]
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
   a.stack_size = z.stack_size ∧
   a.ptr_eq_oracle = z.ptr_eq_oracle ∧
   a.ptr_eq_rel = z.ptr_eq_rel
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
   assign x y (z with clock := k) = OPTION_MAP (λs. s with clock := k) (assign x y z) /\
   assign x y (z with code := code) = OPTION_MAP (λs. s with code := code) (assign x y z) /\
   assign x y (z with compile := c) = OPTION_MAP (λs. s with compile := c) (assign x y z) /\
   assign x y (z with compile_oracle := co) = OPTION_MAP (λs. s with compile_oracle := co) (assign x y z) /\
   assign x y (z with permute := perm) = OPTION_MAP (λs. s with permute := perm) (assign x y z) /\
   assign x y (z with ptr_eq_oracle := po) = OPTION_MAP (λs. s with ptr_eq_oracle := po) (assign x y z) /\
   assign x y (z with ptr_eq_rel := prel) = OPTION_MAP (λs. s with ptr_eq_rel := prel) (assign x y z) /\
   assign x y (z with stack := xs) = OPTION_MAP (λs. s with stack := xs) (assign x y z)
Proof
  EVAL_TAC >> every_case_tac >>  EVAL_TAC >> full_simp_tac(srw_ss())[]
QED

Theorem inst_with_const[simp]:
   inst i (s with clock := k) = OPTION_MAP (λs. s with clock := k) (inst i s) /\
   inst i (s with code := code) = OPTION_MAP (λs. s with code := code) (inst i s) /\
   inst i (s with compile := c) = OPTION_MAP (λs. s with compile := c) (inst i s) /\
   inst i (s with compile_oracle := co) = OPTION_MAP (λs. s with compile_oracle := co) (inst i s) /\
   inst i (s with permute := perm) = OPTION_MAP (λs. s with permute := perm) (inst i s) /\
   inst i (s with ptr_eq_oracle := po) = OPTION_MAP (λs. s with ptr_eq_oracle := po) (inst i s) /\
   inst i (s with ptr_eq_rel := prel) = OPTION_MAP (λs. s with ptr_eq_rel := prel) (inst i s) /\
   inst i (s with stack := xs) = OPTION_MAP (λs. s with stack := xs) (inst i s)
Proof
  rw[inst_def] >> every_case_tac >> fs[]
  >> rpt (pairarg_tac >> fs [])
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
   s'.stack_size = s.stack_size ∧
   s'.ptr_eq_oracle = s.ptr_eq_oracle ∧
   s'.ptr_eq_rel = s.ptr_eq_rel
Proof
  rw[inst_def]>>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  rpt (pairarg_tac >> fs []) >>
  imp_res_tac assign_const_full >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  imp_res_tac mem_store_const >> full_simp_tac(srw_ss())[] >> srw_tac[][]
QED

(*FIXME dupe*)
Theorem inst_code_gc_fun_const[local]:
  inst i s = SOME t ⇒
     s.ptr_eq_oracle = t.ptr_eq_oracle /\ s.ptr_eq_rel = t.ptr_eq_rel /\
     s.code = t.code /\ s.gc_fun = t.gc_fun /\ s.sh_mdomain = t.sh_mdomain /\ s.mdomain = t.mdomain /\ s.be = t.be
     ∧ s.compile = t.compile ∧ s.stack_size = t.stack_size ∧ s.stack_limit = t.stack_limit
Proof
  Cases_on`i`>>fs[inst_def,assign_def]>>
  EVERY_CASE_TAC>>
  rpt (pairarg_tac >> fs []) >>
  fs[state_component_equality,mem_store_def]
QED

Theorem inst_const:
   inst i s = SOME s' ⇒
   s'.clock = s.clock ∧
   s'.ffi = s.ffi
Proof
  metis_tac [inst_const_full]
QED

Theorem jump_exc_const:
   jump_exc s = SOME (s',y) ⇒
   s'.ptr_eq_oracle = s.ptr_eq_oracle ∧
   s'.ptr_eq_rel = s.ptr_eq_rel ∧
   s'.be = s.be ∧
   s'.gc_fun = s.gc_fun ∧
   s'.mdomain = s.mdomain ∧
   s'.sh_mdomain = s.sh_mdomain ∧
   s'.code = s.code ∧
   s'.code_buffer = s.code_buffer ∧
   s'.data_buffer = s.data_buffer ∧
   s'.compile = s.compile ∧
   s'.compile_oracle = s.compile_oracle ∧
   s'.clock = s.clock ∧
   s'.ffi = s.ffi ∧
   s'.stack_limit = s.stack_limit ∧
   s'.stack_max = s.stack_max ∧
   s'.stack_size = s.stack_size
Proof
  EVAL_TAC >> every_case_tac >> EVAL_TAC >> srw_tac[][] >> srw_tac[][]
QED

Theorem jump_exc_with_const[simp]:
   jump_exc (s with clock := k) = OPTION_MAP (λ(s,t). (s with clock := k, t)) (jump_exc s) /\
   jump_exc (s with permute := perm) = OPTION_MAP (λ(s,t). (s with permute := perm, t)) (jump_exc s) /\
   jump_exc (s with ptr_eq_oracle := po) = OPTION_MAP (λ(s,t). (s with ptr_eq_oracle := po, t)) (jump_exc s) /\
   jump_exc (s with ptr_eq_rel := prel) = OPTION_MAP (λ(s,t). (s with ptr_eq_rel := prel, t)) (jump_exc s) /\
   jump_exc (s with compile_oracle := co) = OPTION_MAP (λ(s,t). (s with compile_oracle := co, t)) (jump_exc s)
Proof
  EVAL_TAC >> every_case_tac >> EVAL_TAC
QED

Theorem get_var_imm_with_const[simp]:
   get_var_imm x (y with clock := k) = get_var_imm x y /\
   get_var_imm x (y with code := code) = get_var_imm x y /\
   get_var_imm x (y with compile := compile) = get_var_imm x y /\
   get_var_imm x (y with compile_oracle := compile_oracle) = get_var_imm x y /\
   get_var_imm x (y with termdep := td) = get_var_imm x y /\
   get_var_imm x (y with stack := xs) = get_var_imm x y /\
   get_var_imm x (y with permute := perm) = get_var_imm x y /\
   get_var_imm x (y with ptr_eq_oracle := po) = get_var_imm x y /\
   get_var_imm x (y with ptr_eq_rel := prel) = get_var_imm x y
Proof
  Cases_on`x`>>EVAL_TAC
QED

Theorem dec_clock_const[simp]:
   (dec_clock s).locals = s.locals /\
   (dec_clock s).locals_size = s.locals_size ∧
   (dec_clock s).ptr_eq_oracle = s.ptr_eq_oracle ∧
   (dec_clock s).ptr_eq_rel = s.ptr_eq_rel ∧
   (dec_clock s).fp_regs = s.fp_regs ∧
   (dec_clock s).store = s.store /\
   (dec_clock s).stack = s.stack ∧
   (dec_clock s).stack_limit = s.stack_limit ∧
   (dec_clock s).stack_max = s.stack_max ∧
   (dec_clock s).stack_size = s.stack_size /\
   (dec_clock s).memory = s.memory /\
   (dec_clock s).mdomain = s.mdomain /\
   (dec_clock s).sh_mdomain = s.sh_mdomain /\
   (dec_clock s).permute = s.permute /\
   (dec_clock s).compile = s.compile ∧
   (dec_clock s).compile_oracle = s.compile_oracle ∧
   (dec_clock s).code_buffer = s.code_buffer /\
   (dec_clock s).data_buffer = s.data_buffer /\
   (dec_clock s).gc_fun = s.gc_fun /\
   (dec_clock s).handler = s.handler /\
   (dec_clock s).termdep = s.termdep /\
   (dec_clock s).code = s.code /\
   ((dec_clock s).be <=> s.be) /\
   (dec_clock s).ffi = s.ffi /\
   (dec_clock (s with locals := locs)).clock = (dec_clock s).clock /\
   (dec_clock (s with permute := p)).clock = (dec_clock s).clock /\
   dec_clock (s with ptr_eq_oracle := po) = dec_clock s with ptr_eq_oracle := po /\
   dec_clock (s with ptr_eq_rel := prel) = dec_clock s with ptr_eq_rel := prel
Proof
  EVAL_TAC
QED

Theorem sh_mem_set_var_const:
   sh_mem_set_var r v s = (x,s') ==>
   s'.ptr_eq_oracle = s.ptr_eq_oracle ∧
   s'.ptr_eq_rel = s.ptr_eq_rel ∧
   s'.clock = s.clock ∧
   s'.compile_oracle = s.compile_oracle ∧
   s'.compile = s.compile ∧
   s'.be = s.be ∧
   s'.gc_fun = s.gc_fun ∧
   s'.mdomain = s.mdomain ∧
   s'.sh_mdomain = s.sh_mdomain ∧
   s'.code = s.code ∧
   s'.code_buffer = s.code_buffer ∧
   s'.data_buffer = s.data_buffer ∧
   s'.permute = s.permute ∧
   s'.handler = s.handler ∧
   s'.stack_limit = s.stack_limit ∧
   s'.stack_max = s.stack_max ∧
   (r = NONE ==> s'.ffi = s.ffi) ∧
   (r = SOME (FFI_final outcome) ==> s'.ffi = s.ffi) ∧
   (r = NONE ==> s'.locals_size = s.locals_size) ∧
   (r = SOME (FFI_return f l) ==> s'.locals_size = s.locals_size) ∧
   (r = NONE ==> s'.stack_max = s.stack_max) ∧
   (r = SOME (FFI_return f l) ==> s'.stack_max = s.stack_max) ∧
   (r = NONE ==> s'.stack_size = s.stack_size) ∧
   (r = SOME (FFI_return f l) ==> s'.stack_size = s.stack_size)
Proof
  Cases_on `r` >>
  gvs[sh_mem_set_var_def] >>
  rename1 `sh_mem_set_var (SOME res) _ _ = _` >>
  Cases_on `res` >>
  rpt strip_tac >>
  gvs[sh_mem_set_var_def,set_var_def] >>
  simp[flush_state_def]
QED

Theorem sh_mem_store_const:
  sh_mem_store ad v s = (res, s') ==>
  s'.ptr_eq_oracle = s.ptr_eq_oracle ∧
  s'.ptr_eq_rel = s.ptr_eq_rel ∧
  s'.clock = s.clock ∧
  s'.compile_oracle = s.compile_oracle ∧
  s'.compile = s.compile ∧
  s'.be = s.be ∧
  s'.gc_fun = s.gc_fun ∧
  s'.mdomain = s.mdomain ∧
  s'.sh_mdomain = s.sh_mdomain ∧
  s'.code = s.code ∧
  s'.code_buffer = s.code_buffer ∧
  s'.data_buffer = s.data_buffer ∧
  s'.permute = s.permute ∧
  s'.handler = s.handler ∧
  s'.stack_limit = s.stack_limit ∧
  s'.stack_max = s.stack_max ∧
  (res = SOME Error ==> s'.locals_size = s.locals_size) ∧
  (res = NONE ==> s'.locals_size = s.locals_size) ∧
  (res = NONE ==> s'.stack_max = s.stack_max) ∧
  (res = SOME Error ==> s'.stack_max = s.stack_max) ∧
  (res = NONE ==> s'.stack_size = s.stack_size) ∧
  (res = SOME Error ==> s'.stack_size = s.stack_size)
Proof
  gvs[sh_mem_store_def] >>
  rpt (TOP_CASE_TAC>> fs[]) >>
  rpt strip_tac >>
  gvs[flush_state_def]
QED

Theorem sh_mem_store_byte_const:
  sh_mem_store_byte ad v s = (res, s') ==>
  s'.ptr_eq_oracle = s.ptr_eq_oracle ∧
  s'.ptr_eq_rel = s.ptr_eq_rel ∧
  s'.clock = s.clock ∧
  s'.compile_oracle = s.compile_oracle ∧
  s'.compile = s.compile ∧
  s'.be = s.be ∧
  s'.gc_fun = s.gc_fun ∧
  s'.mdomain = s.mdomain ∧
  s'.sh_mdomain = s.sh_mdomain ∧
  s'.code = s.code ∧
  s'.code_buffer = s.code_buffer ∧
  s'.data_buffer = s.data_buffer ∧
  s'.permute = s.permute ∧
  s'.handler = s.handler ∧
  s'.stack_limit = s.stack_limit ∧
  s'.stack_max = s.stack_max ∧
  (res = SOME Error ==> s'.locals_size = s.locals_size) ∧
  (res = NONE ==> s'.locals_size = s.locals_size) ∧
  (res = NONE ==> s'.stack_max = s.stack_max) ∧
  (res = SOME Error ==> s'.stack_max = s.stack_max) ∧
  (res = NONE ==> s'.stack_size = s.stack_size) ∧
  (res = SOME Error ==> s'.stack_size = s.stack_size)
Proof
  gvs[sh_mem_store_byte_def] >>
  rpt (TOP_CASE_TAC>> fs[]) >>
  rpt strip_tac >>
  gvs[flush_state_def]
QED

Theorem sh_mem_store16_const:
  sh_mem_store16 ad v s = (res, s') ==>
  s'.ptr_eq_oracle = s.ptr_eq_oracle ∧
  s'.ptr_eq_rel = s.ptr_eq_rel ∧
  s'.clock = s.clock ∧
  s'.compile_oracle = s.compile_oracle ∧
  s'.compile = s.compile ∧
  s'.be = s.be ∧
  s'.gc_fun = s.gc_fun ∧
  s'.mdomain = s.mdomain ∧
  s'.sh_mdomain = s.sh_mdomain ∧
  s'.code = s.code ∧
  s'.code_buffer = s.code_buffer ∧
  s'.data_buffer = s.data_buffer ∧
  s'.permute = s.permute ∧
  s'.handler = s.handler ∧
  s'.stack_limit = s.stack_limit ∧
  s'.stack_max = s.stack_max ∧
  (res = SOME Error ==> s'.locals_size = s.locals_size) ∧
  (res = NONE ==> s'.locals_size = s.locals_size) ∧
  (res = NONE ==> s'.stack_max = s.stack_max) ∧
  (res = SOME Error ==> s'.stack_max = s.stack_max) ∧
  (res = NONE ==> s'.stack_size = s.stack_size) ∧
  (res = SOME Error ==> s'.stack_size = s.stack_size)
Proof
  gvs[sh_mem_store16_def] >>
  rpt (TOP_CASE_TAC>> fs[]) >>
  rpt strip_tac >>
  gvs[flush_state_def]
QED

Theorem sh_mem_store32_const:
  sh_mem_store32 ad v s = (res, s') ==>
  s'.ptr_eq_oracle = s.ptr_eq_oracle ∧
  s'.ptr_eq_rel = s.ptr_eq_rel ∧
  s'.clock = s.clock ∧
  s'.compile_oracle = s.compile_oracle ∧
  s'.compile = s.compile ∧
  s'.be = s.be ∧
  s'.gc_fun = s.gc_fun ∧
  s'.mdomain = s.mdomain ∧
  s'.sh_mdomain = s.sh_mdomain ∧
  s'.code = s.code ∧
  s'.code_buffer = s.code_buffer ∧
  s'.data_buffer = s.data_buffer ∧
  s'.permute = s.permute ∧
  s'.handler = s.handler ∧
  s'.stack_limit = s.stack_limit ∧
  s'.stack_max = s.stack_max ∧
  (res = SOME Error ==> s'.locals_size = s.locals_size) ∧
  (res = NONE ==> s'.locals_size = s.locals_size) ∧
  (res = NONE ==> s'.stack_max = s.stack_max) ∧
  (res = SOME Error ==> s'.stack_max = s.stack_max) ∧
  (res = NONE ==> s'.stack_size = s.stack_size) ∧
  (res = SOME Error ==> s'.stack_size = s.stack_size)
Proof
  gvs[sh_mem_store32_def] >>
  rpt (TOP_CASE_TAC>> fs[]) >>
  rpt strip_tac >>
  gvs[flush_state_def]
QED

Theorem share_inst_const:
  share_inst op v c s = (res, s') ==>
  s'.ptr_eq_oracle = s.ptr_eq_oracle ∧
  s'.ptr_eq_rel = s.ptr_eq_rel ∧
  s'.be = s.be ∧
  s'.gc_fun = s.gc_fun ∧
  s'.mdomain = s.mdomain ∧
  s'.sh_mdomain = s.sh_mdomain ∧
  s'.code = s.code ∧
  s'.code_buffer = s.code_buffer ∧
  s'.data_buffer = s.data_buffer ∧
  s'.compile = s.compile ∧
  s'.compile_oracle = s.compile_oracle ∧
  s'.permute = s.permute ∧
  s'.clock = s.clock ∧
  s'.handler = s.handler ∧
  s'.stack_limit = s.stack_limit ∧
  s'.stack_max = s.stack_max
Proof
  Cases_on `op` >>
  gvs[share_inst_def]
  >> rpt (CASE_ONE >> gvs[])
  >> strip_tac >> gvs[]
  >> drulel [sh_mem_set_var_const,sh_mem_store_const,sh_mem_store_byte_const,sh_mem_store16_const,sh_mem_store32_const]
  >> gvs[]
QED

(*TODO use PAIRMAP and deal with breakage*)
Theorem sh_mem_set_var_with_const[simp]:
  sh_mem_set_var res v (s with permute := p) =
  (I ## (λs. s with permute := p)) (sh_mem_set_var res v s) /\
  sh_mem_set_var res v (s with ptr_eq_oracle := po) =
  (I ## (λs. s with ptr_eq_oracle := po)) (sh_mem_set_var res v s) /\
  sh_mem_set_var res v (s with ptr_eq_rel := prel) =
  (I ## (λs. s with ptr_eq_rel := prel)) (sh_mem_set_var res v s) /\
  sh_mem_set_var res v (s with clock := k) =
  (I ## (λs. s with clock := k)) (sh_mem_set_var res v s) /\
  sh_mem_set_var res v (s with compile_oracle := co) =
  (I ## (λs. s with compile_oracle := co)) (sh_mem_set_var res v s)
Proof
  Cases_on `res` >>
  fs[sh_mem_set_var_def] >>
  rename1 `sh_mem_set_var (SOME res)` >>
  Cases_on `res` >>
  fs[sh_mem_set_var_def]
QED

Theorem sh_mem_load_with_const[simp]:
  sh_mem_load a (s with locals := l) = sh_mem_load a s /\
  sh_mem_load a (s with permute := p) = sh_mem_load a s /\
  sh_mem_load a (s with ptr_eq_oracle := po) = sh_mem_load a s /\
  sh_mem_load a (s with ptr_eq_rel := prel) = sh_mem_load a s /\
  sh_mem_load a (s with clock := k) = sh_mem_load a s /\
  sh_mem_load a (s with stack := xs) = sh_mem_load a s
Proof
  EVAL_TAC
QED

Theorem sh_mem_load_byte_with_const[simp]:
  sh_mem_load_byte a (s with locals := l) = sh_mem_load_byte a s /\
  sh_mem_load_byte a (s with permute := p) = sh_mem_load_byte a s /\
  sh_mem_load_byte a (s with ptr_eq_oracle := po) = sh_mem_load_byte a s /\
  sh_mem_load_byte a (s with ptr_eq_rel := prel) = sh_mem_load_byte a s /\
  sh_mem_load_byte a (s with clock := k) = sh_mem_load_byte a s /\
  sh_mem_load_byte a (s with stack := xs) = sh_mem_load_byte a s
Proof
  EVAL_TAC
QED

Theorem sh_mem_load16_with_const[simp]:
  sh_mem_load16 a (s with locals := l) = sh_mem_load16 a s /\
  sh_mem_load16 a (s with permute := p) = sh_mem_load16 a s /\
  sh_mem_load16 a (s with ptr_eq_oracle := po) = sh_mem_load16 a s /\
  sh_mem_load16 a (s with ptr_eq_rel := prel) = sh_mem_load16 a s /\
  sh_mem_load16 a (s with clock := k) = sh_mem_load16 a s /\
  sh_mem_load16 a (s with stack := xs) = sh_mem_load16 a s
Proof
  gvs[sh_mem_load16_def]
QED

Theorem sh_mem_load32_with_const[simp]:
  sh_mem_load32 a (s with locals := l) = sh_mem_load32 a s /\
  sh_mem_load32 a (s with permute := p) = sh_mem_load32 a s /\
  sh_mem_load32 a (s with ptr_eq_oracle := po) = sh_mem_load32 a s /\
  sh_mem_load32 a (s with ptr_eq_rel := prel) = sh_mem_load32 a s /\
  sh_mem_load32 a (s with clock := k) = sh_mem_load32 a s /\
  sh_mem_load32 a (s with stack := xs) = sh_mem_load32 a s
Proof
  EVAL_TAC
QED

Theorem sh_mem_store_with_const[simp]:
  sh_mem_store a w (s with permute := p) =
  (I ## (λs. s with permute := p)) (sh_mem_store a w s) /\
  sh_mem_store a w (s with ptr_eq_oracle := po) =
  (I ## (λs. s with ptr_eq_oracle := po)) (sh_mem_store a w s) /\
  sh_mem_store a w (s with ptr_eq_rel := prel) =
  (I ## (λs. s with ptr_eq_rel := prel)) (sh_mem_store a w s) /\
  sh_mem_store a w (s with clock := k) =
  (I ## (λs. s with clock := k)) (sh_mem_store a w s)
Proof
  fs[sh_mem_store_def] >> (rpt (CASE_ONE >> fs[]))
QED

Theorem sh_mem_store_byte_with_const[simp]:
  sh_mem_store_byte a w (s with permute := p) =
  (I ## (λs. s with permute := p)) (sh_mem_store_byte a w s) /\
  sh_mem_store_byte a w (s with ptr_eq_oracle := po) =
  (I ## (λs. s with ptr_eq_oracle := po)) (sh_mem_store_byte a w s) /\
  sh_mem_store_byte a w (s with ptr_eq_rel := prel) =
  (I ## (λs. s with ptr_eq_rel := prel)) (sh_mem_store_byte a w s) /\
  sh_mem_store_byte a w (s with clock := k) =
  (I ## (λs. s with clock := k)) (sh_mem_store_byte a w s)
Proof
  fs[sh_mem_store_byte_def] >> (rpt (CASE_ONE >> fs[]))
QED

Theorem sh_mem_store16_with_const[simp]:
  sh_mem_store16 a w (s with permute := p) =
  (I ## (λs. s with permute := p)) (sh_mem_store16 a w s) /\
  sh_mem_store16 a w (s with ptr_eq_oracle := po) =
  (I ## (λs. s with ptr_eq_oracle := po)) (sh_mem_store16 a w s) /\
  sh_mem_store16 a w (s with ptr_eq_rel := prel) =
  (I ## (λs. s with ptr_eq_rel := prel)) (sh_mem_store16 a w s) /\
  sh_mem_store16 a w (s with clock := k) =
  (I ## (λs. s with clock := k)) (sh_mem_store16 a w s)
Proof
  fs[sh_mem_store16_def] >> (rpt (CASE_ONE >> fs[]))
QED

Theorem sh_mem_store32_with_const[simp]:
  sh_mem_store32 a w (s with permute := p) =
  (I ## (λs. s with permute := p)) (sh_mem_store32 a w s) /\
  sh_mem_store32 a w (s with ptr_eq_oracle := po) =
  (I ## (λs. s with ptr_eq_oracle := po)) (sh_mem_store32 a w s) /\
  sh_mem_store32 a w (s with ptr_eq_rel := prel) =
  (I ## (λs. s with ptr_eq_rel := prel)) (sh_mem_store32 a w s) /\
  sh_mem_store32 a w (s with clock := k) =
  (I ## (λs. s with clock := k)) (sh_mem_store32 a w s)
Proof
  fs[sh_mem_store32_def] >> (rpt (CASE_ONE >> fs[]))
QED

Theorem share_inst_with_const[simp]:
   share_inst op v c (s with permute := p) =
   (I ## (λs. s with permute := p)) (share_inst op v c s) /\
   share_inst op v c (s with ptr_eq_oracle := po) =
   (I ## (λs. s with ptr_eq_oracle := po)) (share_inst op v c s) /\
   share_inst op v c (s with ptr_eq_rel := prel) =
   (I ## (λs. s with ptr_eq_rel := prel)) (share_inst op v c s) /\
   share_inst op v c (s with clock := k) =
   (I ## (λs. s with clock := k)) (share_inst op v c s) /\
   share_inst op v c (s with compile_oracle := co) =
   (I ## (λs. s with compile_oracle := co)) (share_inst op v c s)
Proof
  Cases_on `op` >> fs[share_inst_def] >> (rpt (CASE_ONE >> fs[])) >>
  gvs[sh_mem_load_def,sh_mem_load_byte_def,
      sh_mem_load16_def,sh_mem_load32_def,sh_mem_store_def,
      sh_mem_store_byte_def,sh_mem_store16_def,sh_mem_store32_def] >>
  rpt (CASE_ONE >> gvs[])
QED

Theorem cut_state_with_const[simp]:
   cut_state x (z with clock := k) = OPTION_MAP (λs. s with clock := k) (cut_state x z) /\
   cut_state x (z with code := code) = OPTION_MAP (λs. s with code := code) (cut_state x z) /\
   cut_state x (z with compile := c) = OPTION_MAP (λs. s with compile := c) (cut_state x z) /\
   cut_state x (z with compile_oracle := co) = OPTION_MAP (λs. s with compile_oracle := co) (cut_state x z) /\
   cut_state x (z with permute := perm) = OPTION_MAP (λs. s with permute := perm) (cut_state x z) /\
   cut_state x (z with ptr_eq_oracle := po) = OPTION_MAP (λs. s with ptr_eq_oracle := po) (cut_state x z) /\
   cut_state x (z with ptr_eq_rel := prel) = OPTION_MAP (λs. s with ptr_eq_rel := prel) (cut_state x z) /\
   cut_state x (z with stack := xs) = OPTION_MAP (λs. s with stack := xs) (cut_state x z)
Proof
  simp[cut_state_def]>>
  TOP_CASE_TAC>>simp[]
QED

Theorem cut_state_const:
  cut_state x s = SOME s' ⇒
  ∃l. s' = s with locals := l
Proof
  rw[cut_state_def]>>
  gvs[AllCaseEqs()]
QED

(* TODO: generated names *)

val goal = “
  λ(p:'a wordLang$prog,s:('a,'c,'ffi) wordSem$state).
     ∀r s'.
      evaluate (p, s) = (r, s') ⇒
      s'.clock = s.clock”
val ind_thm = evaluate_ind |> ISPEC goal |> CONV_RULE (DEPTH_CONV PAIRED_BETA_CONV);
val ind_goals = ind_thm |> concl |> dest_imp |> fst |> helperLib.list_dest dest_conj;

Theorem evaluate_clock_const[local]:
  ^(let fun sel s = first (can (find_term (can (match_term (Term [QUOTE s]))))) ind_goals
    in list_mk_conj (map sel
     ["Skip", "Alloc", "StoreConsts", "Move", "Inst", "Assign",
      "Get", "Set", "OpCurrHeap", "Store", "Return", "Raise",
      "wordLang$Break", "wordLang$Continue",
      "LocValue", "Install", "CodeBufferWrite", "DataBufferWrite",
      "FFI", "ShareInst", "PtrEq"]) end)
Proof
  gvs[evaluate_def] >> rpt gen_tac >>
  rpt (CASE_ONE >> gvs[]) >>
  rpt strip_tac >>
  gvs[AllCaseEqs(),UNCURRY_EQ] >>
  metis_tac[alloc_const,inst_const,mem_store_const,jump_exc_const,share_inst_const]
QED

val clock_goal = “
  λ(p:'a wordLang$prog,s:('a,'c,'ffi) wordSem$state).
    ∀k.
      evaluate (p, s with clock := k) = (λ(r,s). (r,s with clock := k)) (evaluate (p,s))”
val ind_thm2 = evaluate_ind |> ISPEC clock_goal |> CONV_RULE (DEPTH_CONV PAIRED_BETA_CONV);
val ind_goals2 = ind_thm2 |> concl |> dest_imp |> fst |> helperLib.list_dest dest_conj;

Theorem evaluate_clock_with_const[local]:
  ^(let fun sel s = first (can (find_term (can (match_term (Term [QUOTE s]))))) ind_goals2
    in list_mk_conj (map sel
     ["Skip", "Alloc", "StoreConsts", "Move", "Inst", "Assign",
      "Get", "Set", "OpCurrHeap", "Store", "Return", "Raise",
      "wordLang$Break", "wordLang$Continue",
      "LocValue", "Install", "CodeBufferWrite", "DataBufferWrite",
      "FFI", "ShareInst", "PtrEq"]) end)
Proof
  gvs[evaluate_def] >> rpt strip_tac >>
  rpt (CASE_ONE >> gvs[])
QED

val ptr_eq_oracle_goal = “
  λ(p:'a wordLang$prog,s:('a,'c,'ffi) wordSem$state).
    ∀po.
      evaluate (p, s with ptr_eq_oracle := po) =
        (λ(r,s). (r,s with ptr_eq_oracle := po)) (evaluate (p,s))”
val ind_thm3 = evaluate_ind |> ISPEC ptr_eq_oracle_goal |> CONV_RULE (DEPTH_CONV PAIRED_BETA_CONV);
val ind_goals3 = ind_thm3 |> concl |> dest_imp |> fst |> helperLib.list_dest dest_conj;

(* The listed constructs leave the pointer-equality oracle alone. PtrEq reads
   and advances the current epoch's stream and Install moves to the next
   epoch, so neither holds. *)
Theorem evaluate_ptr_eq_oracle_with_const[local]:
  ^(let fun sel s = first (can (find_term (can (match_term (Term [QUOTE s]))))) ind_goals3
    in list_mk_conj (map sel
     ["Skip", "Alloc", "StoreConsts", "Move", "Inst", "Assign",
      "Get", "Set", "OpCurrHeap", "Store", "Return", "Raise",
      "wordLang$Break", "wordLang$Continue", "Tick",
      "LocValue", "CodeBufferWrite", "DataBufferWrite",
      "FFI", "ShareInst"]) end)
Proof
  gvs[evaluate_def] >> rpt strip_tac >>
  rpt (CASE_ONE >> gvs[])
QED

val compile_oracle_goal = “
  λ(p:'a wordLang$prog,s:('a,'c,'ffi) wordSem$state).
    ∀co.
      evaluate (p, s with compile_oracle := co) =
        (λ(r,s). (r,s with compile_oracle := co)) (evaluate (p,s))”
val ind_thm4 = evaluate_ind |> ISPEC compile_oracle_goal |> CONV_RULE (DEPTH_CONV PAIRED_BETA_CONV);
val ind_goals4 = ind_thm4 |> concl |> dest_imp |> fst |> helperLib.list_dest dest_conj;

(* The listed constructs leave the compile oracle alone. Install is the only
   construct that reads it, and it shifts it. *)
Theorem evaluate_compile_oracle_with_const[local]:
  ^(let fun sel s = first (can (find_term (can (match_term (Term [QUOTE s]))))) ind_goals4
    in list_mk_conj (map sel
     ["Skip", "Alloc", "StoreConsts", "Move", "Inst", "Assign",
      "Get", "Set", "OpCurrHeap", "Store", "Return", "Raise",
      "wordLang$Break", "wordLang$Continue", "Tick",
      "LocValue", "CodeBufferWrite", "DataBufferWrite",
      "FFI", "ShareInst", "PtrEq"]) end)
Proof
  gvs[evaluate_def] >> rpt strip_tac >>
  rpt (CASE_ONE >> gvs[alloc_with_const]) >>
  gvs[dec_clock_def]
QED

(******CONST LEMMAS END *****)

(*TODO complete for all get set variaents *)
Theorem get_var_set_store[simp]:
   get_var v1 (set_store v2 x s) = get_var v1 s
Proof
  fs[set_store_def]
QED

Theorem get_var_set_fp_var[simp]:
   get_var v1 (set_fp_var v2 x s) = get_var v1 s
Proof
  fs[set_fp_var_def]
QED

Theorem get_var_set_var:
   get_var v1 (set_var v2 x s) = if v1 = v2 then SOME x else get_var v1 s
Proof
  simp[get_var_def,set_var_def,lookup_insert]
QED

Theorem get_store_set_store:
   get_store v1 (set_store v2 x s) = if v1 = v2 then SOME x else get_store v1 s
Proof
  fs[get_store_def,set_store_def,FLOOKUP_UPDATE] >>
  irule bool_case_CONG >> simp[] >> irule EQ_SYM_EQ
QED

Theorem get_fp_var_set_fp_var:
   get_fp_var v1 (set_fp_var v2 x s) = if v1 = v2 then SOME x else get_fp_var v1 s
Proof
  fs[get_fp_var_def,set_fp_var_def,FLOOKUP_UPDATE] >>
  irule bool_case_CONG >> simp[] >> irule EQ_SYM_EQ
QED

(* Standard add clock lemma for FBS *)
Theorem evaluate_add_clock:
  ∀p s r s'.
    evaluate (p,s) = (r,s') ∧ r ≠ SOME TimeOut ⇒
    evaluate (p,s with clock := s.clock + extra) = (r,s' with clock := s'.clock + extra)
Proof
  recInduct evaluate_ind >> rpt strip_tac >>
  qpat_x_assum `evaluate _ = _` mp_tac
  >~[`Tick`]
  >-(
    fs[evaluate_def,dec_clock_def] >>
    rpt (CASE_ONE >> gvs[]) >>
    strip_tac >> gvs[])
  >~[`MustTerminate`]
  >-(
    fs[evaluate_def] >>
    rpt (CASE_ONE >> gvs[]) >>
    strip_tac >> gvs[]
    )
  >~[`Seq`]
  >-(
    fs[evaluate_def] >>
    rpt (CASE_ONE >> gvs[]) >>
    strip_tac >> gvs[]
    )
  >~[`If`]
  >-(
    fs[evaluate_def] >>
    rpt (CASE_ONE >> gvs[]) >>
    strip_tac >> gvs[]
    )
  >~[`Loop`]
  >-(
    fs[evaluate_def] >>
    rpt (CASE_ONE >> gvs[]) >>
    imp_res_tac cut_state_const >>
    gvs[oneline cont_loop_def,AllCasePreds()]>>
    strip_tac >> gvs[dec_clock_def]>>rw[]>>
    gvs[oneline exit_loop_def,AllCaseEqs()]
    )
  >~[`Call`]
  >-(
    fs[evaluate_def,dec_clock_def] >>
    rpt (CASE_ONE >> gvs[]) >>
    rpt strip_tac >>
    gvs[oneline bad_fun_return_def,AllCasePreds()] >>
    drule pop_env_const >>
    strip_tac >> gvs[])
  >>
  fs[evaluate_clock_with_const]>>
  rw[]>>drulel (CONJUNCTS evaluate_clock_const)>>
  simp[]
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

Theorem with_locals_same_clock[simp]:
  s with <|locals := l; clock := s.clock|> =
  s with locals := l
Proof
  rw[state_component_equality]
QED

Theorem cont_loop_not_timeout[local]:
  cont_loop res ⇒ res ≠ SOME TimeOut
Proof
  Cases_on `res` >> gvs[cont_loop_def] >>
  Cases_on `x` >> gvs[cont_loop_def]
QED

Theorem evaluate_add_clock_body[local]:
  evaluate (c,s) = (res,s') ∧ cont_loop res ⇒
  ∀extra.
    evaluate (c,s with clock := s.clock + extra) =
    (res,s' with clock := s'.clock + extra)
Proof
  strip_tac >>
  imp_res_tac cont_loop_not_timeout >>
  drule_all evaluate_add_clock >> simp[]
QED

Theorem evaluate_dec_clock:
  ∀prog st res rst.
  evaluate(prog,st) = (res,rst) ⇒
  evaluate(prog,st with clock:=st.clock-rst.clock) = (res,rst with clock:=0)
Proof
  recInduct evaluate_ind >> rpt strip_tac >>
  (qpat_x_assum `evaluate _ = _` mp_tac)
  >~[`Tick`]
  >-(
    fs[evaluate_def,dec_clock_def] >>
    rpt (CASE_ONE >> gvs[]) >>
    strip_tac >> gvs[]
    )
  >~[`MustTerminate`]
  >-(
    fs[evaluate_def] >>
    rpt (CASE_ONE >> gvs[]) >>
    strip_tac >> gvs[]
    )
  >~[`Seq`]
  >-(
    fs[evaluate_def,dec_clock_def] >>
    rpt (CASE_ONE >> gvs[]) >>
    strip_tac >> gvs[]
    >>(
      imp_res_tac evaluate_clock
      >> imp_res_tac evaluate_add_clock
      >> fs[]
      >> first_x_assum(qspec_then`s1.clock - rst.clock` mp_tac)
      >> fs[])
    )
  >~[`If`]
  >-(
    fs[evaluate_def] >>
    rpt (CASE_ONE >> gvs[]) >>
    strip_tac >> gvs[]
    )
  >~[`Loop`]
  >-(
    strip_tac >>
    fs[evaluate_def,cut_state_def,cut_env_def] >>
    TOP_CASE_TAC >> gvs[] >>
    Cases_on `evaluate (c,x)` >> fs[] >>
    imp_res_tac evaluate_clock >> gvs[] >>
    gvs[AllCaseEqs(),AllCasePreds(),flush_state_def,
        dec_clock_def,cut_state_def,cut_env_def,state_component_equality] >>
    imp_res_tac evaluate_add_clock_body >> gvs[] >>
    first_x_assum (qspec_then `r.clock - rst.clock` mp_tac) >> simp[] >>
    imp_res_tac evaluate_clock >>
    `r.clock − rst.clock + x.clock − r.clock = x.clock − rst.clock` by
      (gvs[dec_clock_def] >> DECIDE_TAC) >>
    gvs[] >> strip_tac >> gvs[]
    )
  >~[`Call`]
  >-(
    fs[evaluate_def,dec_clock_def] >>
    ntac 6 (TOP_CASE_TAC>>gvs[])
      >-( (*Tail call*)
        rpt (CASE_ONE >> gvs[]) >>
        rpt disch_tac
        >> imp_res_tac evaluate_clock>> fs[] >> gvs[]
        )
      >-(
        PairCases_on `x'` >> fs[]
        >> ntac 3 (TOP_CASE_TAC >> fs[])
          >-(strip_tac>>rveq>>fs[])
          >-(
            ntac 2 (TOP_CASE_TAC>>full_simp_tac(srw_ss())[])
              >- tac2
              >- (
                TOP_CASE_TAC
                >-(
                  TOP_CASE_TAC>-tac2>>
                  TOP_CASE_TAC>-tac2>>
                  reverse TOP_CASE_TAC
                    >-(
                      tac2>>imp_res_tac pop_env_const>>
                      rveq>>full_simp_tac(srw_ss())[])>>
                    strip_tac>>full_simp_tac(srw_ss())[]>>
                    rev_full_simp_tac(srw_ss())[]>>
                    imp_res_tac evaluate_clock>>full_simp_tac(srw_ss())[]>>
                    imp_res_tac evaluate_add_clock>>full_simp_tac(srw_ss())[]>>
                    imp_res_tac pop_env_const>>rveq>>full_simp_tac(srw_ss())[]>>
                    first_x_assum(qspec_then`r.clock-rst.clock` kall_tac)>>
                    first_x_assum(qspec_then`r.clock-rst.clock` mp_tac)>>
                    simp[])
                >-(
                TOP_CASE_TAC>-tac2>>
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
                >>tac2
           ))
   ))
  >>
  fs[evaluate_clock_with_const] >>
  disch_tac >>
  drulel (CONJUNCTS evaluate_clock_const) >> simp[]
QED

(* IO and clock monotonicity *)

Theorem evaluate_io_events_mono:
  ∀exps s1 res s2.
   evaluate (exps,s1) = (res, s2) ⇒
   s1.ffi.io_events ≼ s2.ffi.io_events
Proof
  recInduct evaluate_ind >> rpt strip_tac >>
  (qpat_x_assum `evaluate _ = _`
    (strip_assume_tac o SRULE[evaluate_def,LET_DEF,AllCaseEqs(),UNCURRY_EQ])) >>
  rveq >> simp_tac(srw_ss())[]
  >~[`alloc`]
  >-(drule_then (simp_tac(srw_ss()) o single) alloc_const)
  >~[`inst`]
  >-(drule_then (simp_tac(srw_ss()) o single) inst_const)
  >~[`mem_store`]
  >-(drule_then (simp_tac(srw_ss()) o single) mem_store_const)
  >~[`jump_exc`]
  >-(drule_then (simp_tac(srw_ss()) o single) jump_exc_const)
  >~ [`call_FFI`]
  >- (
    qhdtm_x_assum `call_FFI`
       (strip_assume_tac o SRULE[ffiTheory.call_FFI_def,AllCaseEqs()]) >>
    rveq >> simp_tac(srw_ss())[])
  >~ [`share_inst`]
  >- (qhdtm_x_assum `share_inst`
       (strip_assume_tac o SRULE[oneline share_inst_def,
          sh_mem_store_def,sh_mem_store_byte_def,
          sh_mem_load_def,sh_mem_load_byte_def,
          sh_mem_load16_def,sh_mem_store16_def,
          sh_mem_load32_def,sh_mem_store32_def,
          oneline sh_mem_set_var_def,
          AllCaseEqs()]) >>
    rveq >> simp_tac(srw_ss())[] >>
    qhdtm_x_assum `call_FFI`
       (strip_assume_tac o SRULE[ffiTheory.call_FFI_def,AllCaseEqs()]) >>
    rveq >> simp_tac(srw_ss())[])
  (*TODO this simp call is still very slow*)
  >> full_simp_tac(srw_ss())[]
  >>~-([`pop_env`],
     drule_then (full_simp_tac(srw_ss()) o single) pop_env_const >>
     metis_tac[IS_PREFIX_TRANS])
  >>~-([`cut_state`],
    imp_res_tac cut_state_const>>rw[]>>gvs[]>>
    metis_tac[IS_PREFIX_TRANS])
  >> (metis_tac[IS_PREFIX_TRANS])
QED

Theorem SND_alt_def[local]:
   SND c = (λ(a,b). b) c
Proof
  pairarg_tac >>
  gvs[]
QED

(*TODO This format of is really weird can this be changed?*)
Theorem evaluate_add_clock_io_events_mono:
   ∀exps s extra.
    (SND(evaluate(exps,s))).ffi.io_events ≼
    (SND(evaluate(exps,s with clock := s.clock + extra))).ffi.io_events
Proof
  recInduct evaluate_ind >> rpt strip_tac
  >~[`Call`]
  >-(
    srw_tac[][evaluate_def,LET_THM] >>
    Cases_on`get_vars args s`>>full_simp_tac(srw_ss())[]>>
    IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
    Cases_on `find_code dest (add_ret_loc ret x) s.code s.stack_size` >> fs[] >>
    PairCases_on `x'` >> fs[] >>
    Cases_on`ret`>>full_simp_tac(srw_ss())[] >- (
      every_case_tac >> full_simp_tac(srw_ss())[] >> rveq >>
      imp_res_tac evaluate_io_events_mono >> full_simp_tac(srw_ss())[] >>
      imp_res_tac evaluate_add_clock >> full_simp_tac(srw_ss())[] >>
      fsrw_tac[ARITH_ss][dec_clock_def] >>
      rpt(first_x_assum(qspec_then`extra`mp_tac)>>simp[])) >>
    PairCases_on `x'` >> fs[] >>
    IF_CASES_TAC >>fs[] >>
    TOP_CASE_TAC >> fs[] >>
    IF_CASES_TAC >>fs[]
    >- (IF_CASES_TAC >> fs[] >>
       TOP_CASE_TAC >> fs[] >>
       imp_res_tac evaluate_io_events_mono >> full_simp_tac(srw_ss())[] >>
       irule IS_PREFIX_TRANS >>
       first_x_assum (irule_at Any) >>
       every_case_tac >> fs[] >>
       TRY (drule pop_env_const >> fs[]) >>
       gvs[SND_alt_def] >>
       pairarg_tac >> fs[] >>
       drule evaluate_io_events_mono >>
       fs[] >> rw[] >> gvs[])
    >- (
        fs[dec_clock_def] >>
        TOP_CASE_TAC >> fs[] >>
        (*Cleaner to just manually handle the timeout case*)
        Cases_on `q = SOME TimeOut` >> fs[]
        >- (first_x_assum(qspec_then`extra` mp_tac)>>
           disch_tac >>
           irule IS_PREFIX_TRANS >>
           first_x_assum (irule_at Any) >>
           rpt (TOP_CASE_TAC >> fs[]) >>
           TRY (drule pop_env_const >> fs[]) >>
           gvs[SND_alt_def] >>
           pairarg_tac >> fs[] >>
           drule evaluate_io_events_mono >>
          fs[] >> rw[] >> gvs[])
        >- (
           `evaluate (x'1, call_env x'0 x'2 (push_env x' handler s) with clock := extra + s.clock − 1) = (q ,r with clock := r.clock + extra)`
             by (imp_res_tac evaluate_add_clock >>
             fs[] >>
             (first_x_assum(qspec_then`extra`mp_tac)>>simp[]))
           >> fs[]
           >> rpt (TOP_CASE_TAC >>fs[])
           >> drule_then assume_tac pop_env_const >> fs[])))
  >~[`Loop`]
  >-(
    PURE_ONCE_REWRITE_TAC[evaluate_def] >>
    Cases_on `cut_state (names,LN) s` >> simp[] >>
    imp_res_tac cut_state_const >> gvs[] >>
    Cases_on `evaluate (c,s with locals := l)` >>
    Cases_on `evaluate (c,s with <|locals := l; clock := extra + s.clock|>)` >>
    simp[] >> fs[] >>
    Cases_on `q = SOME TimeOut` >> fs[]
    (* Timeout: body timed out, use body IH + transitivity *)
    >- (first_x_assum(qspec_then`extra` mp_tac) >> simp[] >> strip_tac >>
        irule IS_PREFIX_TRANS >> first_x_assum (irule_at Any) >>
        Cases_on `cont_loop q'` >> gvs[]
        >- (Cases_on `r'.clock = 0` >> gvs[flush_state_def] >>
            Cases_on `evaluate (STOP (Loop names c exit_names), dec_clock r')` >>
            imp_res_tac evaluate_io_events_mono >> gvs[dec_clock_def])
        >- (Cases_on `q' = SOME (Break 0)` >> gvs[] >>
            Cases_on `cut_state (exit_names,LN) r'` >> gvs[] >>
            imp_res_tac cut_state_const >> gvs[]))
    (* Non-timeout: evaluate_add_clock unifies both sides *)
    >- (imp_res_tac evaluate_add_clock >> fs[] >>
        first_x_assum(qspec_then`extra`mp_tac) >> simp[] >> strip_tac >> gvs[] >>
        Cases_on `cont_loop q` >> gvs[]
        >- (Cases_on `r.clock = 0` >> gvs[flush_state_def,dec_clock_def] >>
            Cases_on `extra = 0` >> gvs[] >>
            Cases_on `evaluate (STOP (Loop names c exit_names),
                                r with clock := extra − 1)` >>
            imp_res_tac evaluate_io_events_mono >> gvs[])
        >- (Cases_on `q = SOME (Break 0)` >> gvs[] >>
            Cases_on `cut_state (exit_names,LN) r` >> gvs[] >>
            imp_res_tac cut_state_const >> gvs[])))
  >> fs[evaluate_clock_with_const] >> gvs[SND_alt_def]
  >> rpt (pairarg_tac >> gvs[])
  >> fs[evaluate_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  rpt (pairarg_tac >> full_simp_tac(srw_ss())[]) >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  imp_res_tac evaluate_add_clock >> full_simp_tac(srw_ss())[] >>
  rveq >> fs[] >>
  rpt (first_x_assum(qspec_then`extra`mp_tac)>>simp[]  ) >>
  imp_res_tac evaluate_io_events_mono >> rev_full_simp_tac(srw_ss())[] >>
  metis_tac[evaluate_io_events_mono,IS_PREFIX_TRANS,SND,PAIR]
QED

Theorem evaluate_consts:
   !xs s1 vs s2.
     evaluate (xs,s1) = (vs,s2) ==>
     s1.gc_fun = s2.gc_fun /\
     s1.ptr_eq_rel = s2.ptr_eq_rel /\
     (s1.ptr_eq_oracle = NONE ⇒ s2.ptr_eq_oracle = NONE) /\
     s1.mdomain = s2.mdomain /\
     s1.sh_mdomain = s2.sh_mdomain /\
     s1.be = s2.be ∧
     s1.compile = s2.compile ∧
(*     s1.stack_size = s2.stack_size ∧*)
     s1.stack_limit = s2.stack_limit
Proof
  recInduct evaluate_ind
  \\ fs[evaluate_def,LET_THM,dec_clock_def,flush_state_def]
  \\ (rpt conj_tac>>rpt gen_tac)
  >> rpt (CASE_ONE >> gvs[])
  >> strip_tac >> fs[]
  >> TRY (drulel [alloc_code_gc_fun_const, inst_code_gc_fun_const, mem_store_const,jump_exc_const,share_inst_const,pop_env_code_gc_fun_clock,evaluate_clock])
  >> imp_res_tac cut_state_const
  >> strip_tac >> gvs[]
QED

(* ---- the pointer-equality oracle ---- *)

(* The oracle is indexed by install epoch: [po e] is the answer stream of the
   e-th epoch, PtrEq consumes one answer of the current epoch and Install moves
   to the next one.  A trace records, epoch by epoch, the answers a concrete
   (oracle-free) run would consume. *)

Definition epoch_append_def:
  epoch_append tr1 tr2 = FRONT tr1 ++ [LAST tr1 ++ HD tr2] ++ TL tr2
End

Theorem epoch_append_not_nil[local,simp]:
  epoch_append t1 t2 ≠ []
Proof
  rw [epoch_append_def]
QED

Theorem epoch_append_SING[local,simp]:
  epoch_append [a] t2 = (a ++ HD t2) :: TL t2
Proof
  rw [epoch_append_def]
QED

Theorem epoch_append_CONS:
  t1 ≠ [] ⇒ epoch_append (a::t1) t2 = a :: epoch_append t1 t2
Proof
  Cases_on `t1` \\ rw [epoch_append_def]
QED

Theorem epoch_append_LENGTH[local,simp]:
  t1 ≠ [] ∧ t2 ≠ [] ⇒
  LENGTH (epoch_append t1 t2) = LENGTH t1 + LENGTH t2 - 1
Proof
  Cases_on `t1` \\ Cases_on `t2` \\ rw [epoch_append_def, LENGTH_FRONT]
QED

(* The answers the concrete run produces, as a function of the program and the
   state: the switch's existential witness, made canonical so that it can be
   compared across clocks. *)
Definition ptr_eq_trace_def:
  (ptr_eq_trace (PtrEq dst v1 v2 t f) (s:('a,'c,'ffi) wordSem$state) =
     case (get_var v1 s, get_var v2 s) of
     | (SOME (Word w1), SOME (Word w2)) => [[w1 = w2]]
     | _ => [[]]) ∧
  (ptr_eq_trace (Install ptr len dptr dlen names) s =
     case evaluate (Install ptr len dptr dlen names, s) of
     | (NONE,_) => [[];[]]
     | _ => [[]]) ∧
  (ptr_eq_trace (MustTerminate p) s =
     if s.termdep = 0 then [[]]
     else
       ptr_eq_trace p (s with <| clock := MustTerminate_limit (:'a);
                                 termdep := s.termdep - 1 |>)) ∧
  (ptr_eq_trace (Seq c1 c2) s =
     let (res,s1) = evaluate (c1,s) in
       if res = NONE then epoch_append (ptr_eq_trace c1 s) (ptr_eq_trace c2 s1)
       else ptr_eq_trace c1 s) ∧
  (ptr_eq_trace (If cmp r1 ri c1 c2) s =
     case (get_var r1 s, get_var_imm ri s) of
     | (SOME x, SOME y) =>
         (case word_cmp cmp x y of
          | SOME T => ptr_eq_trace c1 s
          | SOME F => ptr_eq_trace c2 s
          | NONE => [[]])
     | _ => [[]]) ∧
  (ptr_eq_trace (Loop names c exit_names) s =
     case cut_state (names,LN) s of
     | NONE => [[]]
     | SOME s0 =>
         (let (res,s1) = evaluate (c,s0) in
            if cont_loop res ∧ s1.clock ≠ 0 then
              epoch_append (ptr_eq_trace c s0)
                (ptr_eq_trace (STOP (Loop names c exit_names)) (dec_clock s1))
            else ptr_eq_trace c s0)) ∧
  (ptr_eq_trace (Call ret dest args handler) s =
     case get_vars args s of
     | NONE => [[]]
     | SOME xs =>
       if bad_dest_args dest args then [[]]
       else
         (case find_code dest (add_ret_loc ret xs) s.code s.stack_size of
          | NONE => [[]]
          | SOME (args1,prog1,ss) =>
            (case ret of
             | NONE =>
                 (if handler = NONE ∧ s.clock ≠ 0 then
                    ptr_eq_trace prog1 (call_env args1 ss (dec_clock s))
                  else [[]])
             | SOME (n,names,ret_handler,l1,l2) =>
                 if domain (FST names) = {} ∨ ¬ALL_DISTINCT n then [[]]
                 else
                   (case cut_envs names s.locals of
                    | NONE => [[]]
                    | SOME envs =>
                      if s.clock = 0 then [[]]
                      else
                        (let s0 = call_env args1 ss
                                    (push_env envs handler (dec_clock s)) in
                         let b1 = ptr_eq_trace prog1 s0 in
                           case evaluate (prog1,s0) of
                           | (SOME (Result x ys),s2) =>
                               (if x ≠ Loc l1 l2 ∨ LENGTH ys ≠ LENGTH n then b1
                                else
                                  case pop_env s2 of
                                  | NONE => b1
                                  | SOME s1 =>
                                    if domain s1.locals =
                                       domain (FST envs) ∪ domain (SND envs)
                                    then
                                      epoch_append b1
                                        (ptr_eq_trace ret_handler
                                           (set_vars n ys s1))
                                    else b1)
                           | (SOME (Exception x y),s2) =>
                               (case handler of
                                | NONE => b1
                                | SOME (n',h,l1',l2') =>
                                  if x ≠ Loc l1' l2' ∨
                                     domain s2.locals ≠
                                     domain (FST envs) ∪ domain (SND envs)
                                  then b1
                                  else
                                    epoch_append b1
                                      (ptr_eq_trace h (set_var n' y s2)))
                           | _ => b1))))) ∧
  (ptr_eq_trace prog s = [[]])
Termination
  WF_REL_TAC `inv_image (measure I LEX measure I LEX measure (prog_size (K 0)))
               (λ(xs,s). (s.termdep,s.clock,xs))`
  \\ rpt strip_tac
  \\ gvs [STOP_def,dec_clock_def]
  \\ rpt (qpat_x_assum `_ = evaluate _` (assume_tac o SYM))
  \\ imp_res_tac evaluate_clock \\ gvs []
  \\ imp_res_tac cut_state_const \\ gvs []
  \\ imp_res_tac pop_env_const \\ gvs [pop_env_def,AllCaseEqs()]
End

(* The oracle left after a run whose trace is tr. *)
Definition drop_trace_def:
  drop_trace [] po = po ∧
  drop_trace (bs::tr) po =
    if tr = [] then (0 =+ shift_seq (LENGTH bs) (po 0)) po
    else drop_trace tr (shift_seq 1 po)
End

Theorem shift_seq_shift_seq[local]:
  shift_seq m (shift_seq n f) = shift_seq (n + m) f
Proof
  rw [shift_seq_def,FUN_EQ_THM]
QED

Theorem shift_seq_0[local,simp]:
  shift_seq 0 f = f
Proof
  rw [shift_seq_def,FUN_EQ_THM]
QED

Theorem with_same_compile_oracle[local,simp]:
  s with compile_oracle := s.compile_oracle = s
Proof
  rw [state_component_equality]
QED

Theorem shift_seq_UPDATE_0[local]:
  0 < n ⇒ shift_seq n ((0 =+ x) f) = shift_seq n f
Proof
  rw [shift_seq_def,FUN_EQ_THM,combinTheory.APPLY_UPDATE_THM]
QED

Theorem drop_trace_NIL_epoch[local,simp]:
  drop_trace [[]] po = po
Proof
  rw [drop_trace_def,shift_seq_def,FUN_EQ_THM,combinTheory.APPLY_UPDATE_THM] >>
  rw []
QED

Theorem drop_trace_new_epoch[local,simp]:
  drop_trace [[];[]] po = shift_seq 1 po
Proof
  rw [drop_trace_def]
QED

(* An oracle agrees with a trace when, epoch by epoch, it answers as the trace
   records.  Beyond the trace it is unconstrained. *)
Definition epoch_prefix_def:
  epoch_prefix tr e a ⇔
    e < LENGTH tr ⇒ ∀k. k < LENGTH (EL e tr) ⇒ EL k (EL e tr) = a k
End

Definition trace_agrees_def:
  trace_agrees tr po ⇔ ∀e. epoch_prefix tr e (po e)
End

(* Growing the clock keeps every completed epoch and extends the last one. *)
Definition ptr_eq_trace_prefix_def:
  ptr_eq_trace_prefix tr1 tr2 ⇔
    LENGTH tr1 ≤ LENGTH tr2 ∧
    (∀e. e + 1 < LENGTH tr1 ⇒ EL e tr2 = EL e tr1) ∧
    (tr1 ≠ [] ⇒ LAST tr1 ≼ EL (LENGTH tr1 - 1) tr2)
End

Theorem ptr_eq_trace_not_nil[local,simp]:
  ∀p s. ptr_eq_trace p s ≠ []
Proof
  recInduct ptr_eq_trace_ind >> rpt strip_tac >>
  qpat_x_assum `ptr_eq_trace _ _ = []` mp_tac >>
  simp [Once ptr_eq_trace_def] >>
  rpt (pairarg_tac >> gvs []) >>
  every_case_tac >> gvs [] >>
  rpt (pairarg_tac >> gvs []) >>
  every_case_tac >> gvs []
QED

Theorem ptr_eq_trace_LENGTH_NOT_0[local,simp]:
  ∀p s. LENGTH (ptr_eq_trace p s) ≠ 0
Proof
  simp [LENGTH_NIL]
QED

Theorem drop_trace_append:
  ∀t1 t2 po.
    t1 ≠ [] ∧ t2 ≠ [] ⇒
    drop_trace (epoch_append t1 t2) po = drop_trace t2 (drop_trace t1 po)
Proof
  Induct >> rw [] >>
  reverse (Cases_on `t1`) >> gvs []
  >- gvs [epoch_append_CONS, drop_trace_def] >>
  Cases_on `t2` >> gvs [] >>
  Cases_on `t` >>
  gvs [drop_trace_def, shift_seq_UPDATE_0, combinTheory.APPLY_UPDATE_THM,
       combinTheory.UPDATE_EQ, shift_seq_shift_seq]
QED

Theorem trace_agrees_NIL[local,simp]:
  trace_agrees [] po
Proof
  rw [trace_agrees_def,epoch_prefix_def]
QED

Theorem trace_agrees_CONS:
  trace_agrees (bs::tr) po ⇔
  (∀k. k < LENGTH bs ⇒ EL k bs = po 0 k) ∧ trace_agrees tr (shift_seq 1 po)
Proof
  rw [trace_agrees_def,epoch_prefix_def,shift_seq_def] >>
  eq_tac >> rw []
  >- (first_x_assum (qspec_then `0` mp_tac) >> simp [])
  >- (first_x_assum (qspec_then `SUC e` mp_tac) >> simp [ADD1])
  >> Cases_on `e` >> gvs [ADD1]
QED

Theorem trace_agrees_append1:
  ∀t1 t2 po.
    t1 ≠ [] ∧ t2 ≠ [] ∧ trace_agrees (epoch_append t1 t2) po ⇒
    trace_agrees t1 po
Proof
  Induct >> rw [] >>
  reverse (Cases_on `t1`) >> gvs []
  >- (
    gvs [epoch_append_CONS] >>
    qpat_x_assum `trace_agrees _ _` mp_tac >>
    simp [Once trace_agrees_CONS] >> strip_tac >>
    simp [Once trace_agrees_CONS] >>
    first_x_assum irule >> qexists_tac `t2` >> simp []) >>
  Cases_on `t2` >> gvs [] >>
  qpat_x_assum `trace_agrees _ _` mp_tac >>
  simp [Once trace_agrees_CONS] >> strip_tac >>
  simp [Once trace_agrees_CONS] >>
  rw [] >> first_x_assum (qspec_then `k` mp_tac) >>
  simp [EL_APPEND_EQN]
QED

Theorem trace_agrees_append2:
  ∀t1 t2 po.
    t1 ≠ [] ∧ t2 ≠ [] ∧ trace_agrees (epoch_append t1 t2) po ⇒
    trace_agrees t2 (drop_trace t1 po)
Proof
  Induct >> rw [] >>
  reverse (Cases_on `t1`) >> gvs []
  >- (gvs [epoch_append_CONS, drop_trace_def] >>
      qpat_x_assum `trace_agrees _ _` mp_tac >>
      simp [Once trace_agrees_CONS] >> strip_tac >>
      first_x_assum irule >> simp []) >>
  Cases_on `t2` >> gvs [drop_trace_def] >>
  qpat_x_assum `trace_agrees _ _` mp_tac >>
  simp [Once trace_agrees_CONS] >> strip_tac >>
  simp [Once trace_agrees_CONS, shift_seq_UPDATE_0] >>
  rw [combinTheory.APPLY_UPDATE_THM, shift_seq_def] >>
  first_x_assum (qspec_then `LENGTH h + k` mp_tac) >>
  simp [EL_APPEND_EQN]
QED

(* Running under any oracle that agrees with the concrete run's trace
   reproduces the concrete run exactly.  Reflexivity of ptr_eq_rel is the only
   property of the attenuator this needs.  The SOME Error escape is forced by
   MustTerminate: when its body times out it returns the state from BEFORE the
   body, so the answers the body consumed are still pending in that state's
   oracle. *)
Theorem ptr_eq_trace_agrees:
  ∀p s r s'.
    evaluate (p,s) = (r,s') ∧ s.ptr_eq_oracle = NONE ∧
    (∀m dm st w. s.ptr_eq_rel m dm st w w) ⇒
    ∀po. trace_agrees (ptr_eq_trace p s) po ⇒
      ∃rest. evaluate (p,s with ptr_eq_oracle := SOME po) =
               (r,s' with ptr_eq_oracle := SOME rest) ∧
             (r ≠ SOME Error ⇒ rest = drop_trace (ptr_eq_trace p s) po)
Proof
  recInduct evaluate_ind >> rpt strip_tac
  >~[`MustTerminate`] >- suspend "MustTerminate"
  >~[`Seq`] >- suspend "Seq"
  >~[`If`] >- suspend "If"
  >~[`Loop`] >- suspend "Loop"
  >~[`Call`] >- suspend "Call"
  >~[`PtrEq`] >- suspend "PtrEq"
  >~[`Install`] >- suspend "Install"
  >> simp[ptr_eq_trace_def] >> rw[] >>
  qexists_tac`po` >>
  gvs[evaluate_ptr_eq_oracle_with_const]
QED

Resume ptr_eq_trace_agrees[MustTerminate]:
  qpat_x_assum`evaluate _ = _` mp_tac>>
  qpat_x_assum`trace_agrees _ _` mp_tac>>
  simp[Once ptr_eq_trace_def,evaluate_def]>>
  IF_CASES_TAC>>simp[]
  >- (rw[]>>metis_tac[])>>
  rpt(pairarg_tac>>simp[])>>
  rpt strip_tac>>gvs[]>>
  first_x_assum(qspec_then`po`strip_assume_tac)>>
  gvs[]>>
  Cases_on`res = SOME TimeOut`>>gvs[]>>
  simp[state_component_equality]>>
  simp[Once ptr_eq_trace_def]>>metis_tac[]
QED

Resume ptr_eq_trace_agrees[Seq]:
  qpat_x_assum`evaluate (Seq _ _,_) = _` mp_tac>>
  qpat_x_assum`trace_agrees _ _` mp_tac>>
  simp[Once ptr_eq_trace_def,evaluate_def]>>
  rpt(pairarg_tac>>simp[])>>
  rpt strip_tac>>gvs[]>>
  reverse (Cases_on`res = NONE`)>>gvs[]
  >- (
    `ptr_eq_trace (Seq c1 c2) s = ptr_eq_trace c1 s` by
      (simp[Once ptr_eq_trace_def]>>gvs[])>>
    gvs[]>>res_tac>>gvs[]>>metis_tac[])>>
  imp_res_tac evaluate_consts>>gvs[]>>
  `trace_agrees (ptr_eq_trace c1 s) po` by
    metis_tac[trace_agrees_append1,ptr_eq_trace_not_nil]>>
  `trace_agrees (ptr_eq_trace c2 s1) (drop_trace (ptr_eq_trace c1 s) po)` by
    metis_tac[trace_agrees_append2,ptr_eq_trace_not_nil]>>
  res_tac>>gvs[]>>
  `ptr_eq_trace (Seq c1 c2) s =
     epoch_append (ptr_eq_trace c1 s) (ptr_eq_trace c2 s1)` by
    (simp[Once ptr_eq_trace_def]>>gvs[])>>
  gvs[drop_trace_append]>>
  metis_tac[]
QED

Resume ptr_eq_trace_agrees[If]:
  qpat_x_assum`evaluate _ = _` mp_tac>>
  qpat_x_assum`trace_agrees _ _` mp_tac>>
  simp[ptr_eq_trace_def,evaluate_def]>>
  rpt (CASE_ONE >> simp[])>>
  rpt strip_tac>>gvs[]>>
  metis_tac[]
QED

Resume ptr_eq_trace_agrees[Loop]:
  qpat_x_assum`evaluate (Loop _ _ _,_) = _`
    (mp_tac o SIMP_RULE (srw_ss()) [Once evaluate_def])>>
  Cases_on`cut_state (names,LN) s`
  >- (simp[evaluate_def]>>rw[]>>metis_tac[])>>
  rename1`cut_state (names,LN) s = SOME s0`>>simp[]>>
  Cases_on`evaluate (c,s0)`>>simp[]>>
  rename1`evaluate (c,s0) = (res,s1)`>>
  `trace_agrees (ptr_eq_trace c s0) po` by
    (qpat_x_assum`trace_agrees (ptr_eq_trace (Loop _ _ _) _) _` mp_tac>>
     simp[Once ptr_eq_trace_def]>>
     metis_tac[trace_agrees_append1,ptr_eq_trace_not_nil])>>
  imp_res_tac cut_state_const>>gvs[]>>
  res_tac>>gvs[]>>
  simp[evaluate_def]>>
  `cut_state (names,LN) (s with ptr_eq_oracle := SOME po) =
     SOME (s with <|locals := l; ptr_eq_oracle := SOME po|>)` by gvs[]>>
  gvs[]>>
  reverse (Cases_on`cont_loop res`)
  >- (
    `ptr_eq_trace (Loop names c exit_names) s =
       ptr_eq_trace c (s with locals := l)` by
      (simp[Once ptr_eq_trace_def]>>gvs[])>>
    gvs[]>>
    Cases_on`cut_state (exit_names,LN) s1`>>
    gvs[oneline exit_loop_def,AllCaseEqs()]>>
    rw[]>>gvs[]>>metis_tac[])>>
  gvs[]>>
  `res ≠ SOME Error` by (strip_tac>>gvs[])>>
  gvs[]>>
  reverse (Cases_on`s1.clock = 0`)
  >- (
    `ptr_eq_trace (Loop names c exit_names) s =
       epoch_append (ptr_eq_trace c (s with locals := l))
         (ptr_eq_trace (STOP (Loop names c exit_names)) (dec_clock s1))` by
      (simp[Once ptr_eq_trace_def]>>gvs[])>>
    `trace_agrees (ptr_eq_trace (STOP (Loop names c exit_names)) (dec_clock s1))
       (drop_trace (ptr_eq_trace c (s with locals := l)) po)` by
      metis_tac[trace_agrees_append2,ptr_eq_trace_not_nil]>>
    imp_res_tac evaluate_consts>>gvs[dec_clock_def]>>
    res_tac>>gvs[]>>
    gvs[drop_trace_append]>>
    metis_tac[])>>
  `ptr_eq_trace (Loop names c exit_names) s =
     ptr_eq_trace c (s with locals := l)` by
    (simp[Once ptr_eq_trace_def]>>gvs[])>>
  gvs[flush_state_def]>>rw[]>>gvs[]>>metis_tac[]
QED

Resume ptr_eq_trace_agrees[Call]:
  qpat_x_assum`evaluate (Call _ _ _ _,_) = _`
    (mp_tac o SIMP_RULE (srw_ss()) [Once evaluate_def])>>
  Cases_on`get_vars args s`
  >- (
    simp[evaluate_def,Once ptr_eq_trace_def]>>rw[]>>gvs[]>>
    qexists_tac`po`>>gvs[])>>
  rename1`get_vars args s = SOME xs`>>simp[]>>
  Cases_on`bad_dest_args dest args`
  >- (
    simp[evaluate_def,Once ptr_eq_trace_def]>>rw[]>>gvs[]>>
    qexists_tac`po`>>gvs[])>>
  gvs[]>>
  Cases_on`find_code dest (add_ret_loc ret xs) s.code s.stack_size`
  >- (
    simp[evaluate_def,Once ptr_eq_trace_def]>>rw[]>>gvs[]>>
    qexists_tac`po`>>gvs[])>>
  rename1`find_code _ _ _ _ = SOME fc`>>
  PairCases_on`fc`>>gvs[]>>
  Cases_on`ret`
  >- (
    gvs[]>>
    Cases_on`handler = NONE`>>gvs[]
    >- (
      Cases_on`s.clock = 0`>>gvs[]
      >- (
        simp[evaluate_def,Once ptr_eq_trace_def]>>rw[]>>gvs[]>>
        qexists_tac`po`>>gvs[])>>
      `ptr_eq_trace (Call NONE dest args NONE) s =
         ptr_eq_trace fc1 (call_env fc0 fc2 (dec_clock s))` by
        (simp[Once ptr_eq_trace_def]>>gvs[])>>
      gvs[]>>
      Cases_on`evaluate (fc1,call_env fc0 fc2 (dec_clock s))`>>gvs[]>>
      res_tac>>gvs[]>>
      simp[evaluate_def]>>gvs[]>>
      rw[]>>gvs[]>>metis_tac[])>>
    simp[evaluate_def,Once ptr_eq_trace_def]>>rw[]>>gvs[]>>
    qexists_tac`po`>>gvs[])>>
  PairCases_on`x`>>gvs[]>>
  Cases_on`domain x1 = {} ∨ ¬ALL_DISTINCT x0`>>gvs[]
  >- (
    simp[evaluate_def,Once ptr_eq_trace_def]>>rw[]>>gvs[]>>
    qexists_tac`po`>>gvs[])
  >- (
    simp[evaluate_def,Once ptr_eq_trace_def]>>rw[]>>gvs[]>>
    qexists_tac`po`>>gvs[])>>
  Cases_on`cut_envs (x1,x2) s.locals`>>gvs[]
  >- (
    simp[evaluate_def,Once ptr_eq_trace_def]>>rw[]>>gvs[]>>
    qexists_tac`po`>>gvs[])>>
  rename1`cut_envs (x1,x2) s.locals = SOME envs`>>
  Cases_on`s.clock = 0`>>gvs[]
  >- (
    simp[evaluate_def,Once ptr_eq_trace_def]>>rw[]>>gvs[]>>
    qexists_tac`po`>>gvs[])>>
  Cases_on`evaluate
             (fc1,call_env fc0 fc2 (push_env envs handler (dec_clock s)))`>>
  rename1`evaluate (fc1,_) = (bres,bst)`>>
  Cases_on`bres`
  >- (
    `ptr_eq_trace (Call (SOME (x0,(x1,x2),x3,x4,x5)) dest args handler) s =
       ptr_eq_trace fc1
         (call_env fc0 fc2 (push_env envs handler (dec_clock s)))` by
      (simp[Once ptr_eq_trace_def]>>gvs[])>>
    gvs[]>>res_tac>>gvs[]>>
    simp[evaluate_def]>>gvs[]>>
    rw[]>>gvs[state_component_equality]>>metis_tac[])>>
  rename1`evaluate (fc1,_) = (SOME bx,bst)`>>
  Cases_on`bx`
  >- (
    gvs[]>>
    Cases_on`w = Loc x4 x5 ⇒ LENGTH l ≠ LENGTH x0`>>gvs[]
    >- (
      `ptr_eq_trace (Call (SOME (x0,(x1,x2),x3,x4,x5)) dest args handler) s =
         ptr_eq_trace fc1
           (call_env fc0 fc2 (push_env envs handler (dec_clock s)))` by
        (simp[Once ptr_eq_trace_def]>>gvs[])>>
      gvs[]>>res_tac>>gvs[]>>
      simp[evaluate_def]>>gvs[]>>
      rw[]>>gvs[state_component_equality]>>metis_tac[])>>
    Cases_on`pop_env bst`>>gvs[]
    >- (
      `ptr_eq_trace (Call (SOME (x0,(x1,x2),x3,x4,x5)) dest args handler) s =
         ptr_eq_trace fc1
           (call_env fc0 fc2 (push_env envs handler (dec_clock s)))` by
        (simp[Once ptr_eq_trace_def]>>gvs[])>>
      gvs[]>>res_tac>>gvs[]>>
      simp[evaluate_def]>>gvs[]>>
      rw[]>>gvs[state_component_equality]>>metis_tac[])>>
    rename1`pop_env bst = SOME s1`>>
    Cases_on`domain s1.locals = domain (FST envs) ∪ domain (SND envs)`>>gvs[]
    >- (
      `ptr_eq_trace (Call (SOME (x0,(x1,x2),x3,x4,x5)) dest args handler) s =
         epoch_append
           (ptr_eq_trace fc1
              (call_env fc0 fc2 (push_env envs handler (dec_clock s))))
           (ptr_eq_trace x3 (set_vars x0 l s1))` by
        (simp[Once ptr_eq_trace_def]>>gvs[])>>
      gvs[]>>
      `trace_agrees
         (ptr_eq_trace fc1
            (call_env fc0 fc2 (push_env envs handler (dec_clock s)))) po` by
        (qspecl_then
           [`ptr_eq_trace fc1
               (call_env fc0 fc2 (push_env envs handler (dec_clock s)))`,
            `ptr_eq_trace x3 (set_vars x0 l s1)`,`po`]
           mp_tac trace_agrees_append1>>gvs[])>>
      `trace_agrees (ptr_eq_trace x3 (set_vars x0 l s1))
         (drop_trace
            (ptr_eq_trace fc1
               (call_env fc0 fc2 (push_env envs handler (dec_clock s)))) po)` by
        (qspecl_then
           [`ptr_eq_trace fc1
               (call_env fc0 fc2 (push_env envs handler (dec_clock s)))`,
            `ptr_eq_trace x3 (set_vars x0 l s1)`,`po`]
           mp_tac trace_agrees_append2>>gvs[])>>
      imp_res_tac evaluate_consts>>
      imp_res_tac pop_env_const>>
      res_tac>>gvs[]>>
      simp[evaluate_def]>>gvs[drop_trace_append])>>
    `ptr_eq_trace (Call (SOME (x0,(x1,x2),x3,x4,x5)) dest args handler) s =
       ptr_eq_trace fc1
         (call_env fc0 fc2 (push_env envs handler (dec_clock s)))` by
      (simp[Once ptr_eq_trace_def]>>gvs[])>>
    gvs[]>>res_tac>>gvs[]>>
    simp[evaluate_def]>>gvs[]>>
    rw[]>>gvs[state_component_equality]>>metis_tac[])
  >- (
    gvs[]>>
    Cases_on`handler`>>gvs[]
    >- (
      `ptr_eq_trace (Call (SOME (x0,(x1,x2),x3,x4,x5)) dest args NONE) s =
         ptr_eq_trace fc1
           (call_env fc0 fc2 (push_env envs NONE (dec_clock s)))` by
        (simp[Once ptr_eq_trace_def]>>gvs[])>>
      gvs[]>>res_tac>>gvs[]>>
      simp[evaluate_def]>>gvs[]>>
      rw[]>>gvs[state_component_equality]>>metis_tac[])>>
    rename1`push_env _ (SOME hnd) _`>>PairCases_on`hnd`>>gvs[]>>
    Cases_on`w = Loc hnd2 hnd3`>>gvs[]
    >- (
      Cases_on`domain bst.locals = domain (FST envs) ∪ domain (SND envs)`>>gvs[]
      >- (
        `ptr_eq_trace
           (Call (SOME (x0,(x1,x2),x3,x4,x5)) dest args
              (SOME (hnd0,hnd1,hnd2,hnd3))) s =
           epoch_append
             (ptr_eq_trace fc1
                (call_env fc0 fc2
                   (push_env envs (SOME (hnd0,hnd1,hnd2,hnd3)) (dec_clock s))))
             (ptr_eq_trace hnd1 (set_var hnd0 w0 bst))` by
          (simp[Once ptr_eq_trace_def]>>gvs[])>>
        gvs[]>>
        `trace_agrees
           (ptr_eq_trace fc1
              (call_env fc0 fc2
                 (push_env envs (SOME (hnd0,hnd1,hnd2,hnd3)) (dec_clock s)))) po` by
          (qspecl_then
             [`ptr_eq_trace fc1
                 (call_env fc0 fc2
                    (push_env envs (SOME (hnd0,hnd1,hnd2,hnd3)) (dec_clock s)))`,
              `ptr_eq_trace hnd1 (set_var hnd0 w0 bst)`,`po`]
             mp_tac trace_agrees_append1>>gvs[])>>
        `trace_agrees (ptr_eq_trace hnd1 (set_var hnd0 w0 bst))
           (drop_trace
              (ptr_eq_trace fc1
                 (call_env fc0 fc2
                    (push_env envs (SOME (hnd0,hnd1,hnd2,hnd3))
                       (dec_clock s)))) po)` by
          (qspecl_then
             [`ptr_eq_trace fc1
                 (call_env fc0 fc2
                    (push_env envs (SOME (hnd0,hnd1,hnd2,hnd3)) (dec_clock s)))`,
              `ptr_eq_trace hnd1 (set_var hnd0 w0 bst)`,`po`]
             mp_tac trace_agrees_append2>>gvs[])>>
        imp_res_tac evaluate_consts>>
        res_tac>>gvs[]>>
        simp[evaluate_def]>>gvs[drop_trace_append])>>
      `ptr_eq_trace
         (Call (SOME (x0,(x1,x2),x3,x4,x5)) dest args
            (SOME (hnd0,hnd1,hnd2,hnd3))) s =
         ptr_eq_trace fc1
           (call_env fc0 fc2
              (push_env envs (SOME (hnd0,hnd1,hnd2,hnd3)) (dec_clock s)))` by
        (simp[Once ptr_eq_trace_def]>>gvs[])>>
      gvs[]>>res_tac>>gvs[]>>
      simp[evaluate_def]>>gvs[]>>
      rw[]>>gvs[state_component_equality]>>metis_tac[])>>
    `ptr_eq_trace
       (Call (SOME (x0,(x1,x2),x3,x4,x5)) dest args
          (SOME (hnd0,hnd1,hnd2,hnd3))) s =
       ptr_eq_trace fc1
         (call_env fc0 fc2
            (push_env envs (SOME (hnd0,hnd1,hnd2,hnd3)) (dec_clock s)))` by
      (simp[Once ptr_eq_trace_def]>>gvs[])>>
    gvs[]>>res_tac>>gvs[]>>
    simp[evaluate_def]>>gvs[]>>
    rw[]>>gvs[state_component_equality]>>metis_tac[])>>
  `ptr_eq_trace (Call (SOME (x0,(x1,x2),x3,x4,x5)) dest args handler) s =
     ptr_eq_trace fc1
       (call_env fc0 fc2 (push_env envs handler (dec_clock s)))` by
    (simp[Once ptr_eq_trace_def]>>gvs[])>>
  gvs[]>>res_tac>>gvs[]>>
  simp[evaluate_def]>>gvs[]>>
  rw[]>>gvs[state_component_equality]>>metis_tac[]
QED

Resume ptr_eq_trace_agrees[PtrEq]:
  gvs[evaluate_def,AllCaseEqs()]
  >~[`set_var _ _ _`]
  >- (gvs[ptr_eq_trace_def,trace_agrees_CONS,drop_trace_def] >>
      rw[] >> gvs[])
  >> simp[ptr_eq_trace_def] >> metis_tac[]
QED

Resume ptr_eq_trace_agrees[Install]:
  qpat_x_assum `evaluate _ = _` mp_tac >>
  simp[Once ptr_eq_trace_def,evaluate_def] >>
  rpt(CASE_ONE >> simp[]) >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Finalise ptr_eq_trace_agrees;

(* ptr_eq_trace_prefix is a preorder, and it relates to epoch_append exactly as ≼
   relates to ++. *)

Theorem ptr_eq_trace_prefix_refl[local,simp]:
  ptr_eq_trace_prefix tr tr
Proof
  rw [ptr_eq_trace_prefix_def] >> gvs [LAST_EL, PRE_SUB1]
QED

Theorem ptr_eq_trace_prefix_NIL[local,simp]:
  ptr_eq_trace_prefix [] tr
Proof
  rw [ptr_eq_trace_prefix_def]
QED

Theorem ptr_eq_trace_prefix_SING:
  ptr_eq_trace_prefix [a] tr ⇔ tr ≠ [] ∧ a ≼ HD tr
Proof
  Cases_on `tr` >> rw [ptr_eq_trace_prefix_def]
QED

Theorem ptr_eq_trace_prefix_NIL_epoch[local,simp]:
  ptr_eq_trace_prefix [[]] tr ⇔ tr ≠ []
Proof
  Cases_on `tr` >> rw [ptr_eq_trace_prefix_def]
QED

Theorem ptr_eq_trace_prefix_CONS:
  ∀a t1 tr.
    t1 ≠ [] ⇒
    (ptr_eq_trace_prefix (a::t1) tr ⇔
     tr ≠ [] ∧ a = HD tr ∧ ptr_eq_trace_prefix t1 (TL tr))
Proof
  rpt strip_tac >>
  Cases_on `t1` >> gvs [] >>
  Cases_on `tr` >> gvs [ptr_eq_trace_prefix_def] >>
  eq_tac >> strip_tac >> gvs []
  >- (conj_asm1_tac
      >- (first_x_assum (qspec_then `0` mp_tac) >> simp []) >>
      rw [] >>
      first_x_assum (qspec_then `SUC e` mp_tac) >> simp [ADD1]) >>
  rw [] >>
  Cases_on `e` >> gvs [ADD1]
QED

Theorem ptr_eq_trace_prefix_trans:
  ∀t1 t2 t3. ptr_eq_trace_prefix t1 t2 ∧ ptr_eq_trace_prefix t2 t3 ⇒ ptr_eq_trace_prefix t1 t3
Proof
  rw [ptr_eq_trace_prefix_def] >>
  `t2 ≠ []` by (strip_tac >> gvs []) >>
  gvs [] >>
  Cases_on `LENGTH t1 = LENGTH t2` >> gvs []
  >- (`LAST t2 = EL (LENGTH t2 - 1) t2` by gvs [LAST_EL, PRE_SUB1] >>
      metis_tac [rich_listTheory.IS_PREFIX_TRANS]) >>
  `LENGTH t1 - 1 + 1 < LENGTH t2` by (Cases_on `t1` >> gvs []) >>
  metis_tac []
QED

Theorem ptr_eq_trace_prefix_epoch_append:
  ∀t1 t2. t1 ≠ [] ∧ t2 ≠ [] ⇒ ptr_eq_trace_prefix t1 (epoch_append t1 t2)
Proof
  Induct >> rw [] >>
  reverse (Cases_on `t1`) >> gvs []
  >- (gvs [epoch_append_CONS] >> simp [ptr_eq_trace_prefix_CONS]) >>
  gvs [ptr_eq_trace_prefix_SING]
QED

Theorem ptr_eq_trace_prefix_epoch_append1:
  ∀t1 t2 t3.
    t1 ≠ [] ∧ t2 ≠ [] ∧ t3 ≠ [] ∧ ptr_eq_trace_prefix t1 t2 ⇒
    ptr_eq_trace_prefix t1 (epoch_append t2 t3)
Proof
  metis_tac [ptr_eq_trace_prefix_trans, ptr_eq_trace_prefix_epoch_append]
QED

Theorem ptr_eq_trace_prefix_epoch_append_cong:
  ∀t1 t2 t2'.
    t1 ≠ [] ∧ t2 ≠ [] ∧ t2' ≠ [] ∧ ptr_eq_trace_prefix t2 t2' ⇒
    ptr_eq_trace_prefix (epoch_append t1 t2) (epoch_append t1 t2')
Proof
  Induct >> rw [] >>
  reverse (Cases_on `t1`) >> gvs []
  >- (gvs [epoch_append_CONS] >> simp [ptr_eq_trace_prefix_CONS]) >>
  Cases_on `t2` >> Cases_on `t2'` >> gvs [] >>
  reverse (Cases_on `t`) >> gvs []
  >- (gvs [ptr_eq_trace_prefix_CONS] >> gvs [ptr_eq_trace_prefix_CONS]) >>
  gvs [ptr_eq_trace_prefix_SING] >>
  Cases_on `t'` >> gvs [ptr_eq_trace_prefix_SING, ptr_eq_trace_prefix_CONS]
QED

Theorem dec_clock_add_clock[local]:
  s.clock ≠ 0 ⇒
  dec_clock (s with clock := extra + s.clock) =
  dec_clock s with clock := extra + (dec_clock s).clock
Proof
  rw[dec_clock_def,state_component_equality]
QED

(* The answers a run produces only grow with the clock, and a run that does
   not time out produces the same answers at every larger clock. *)
Theorem ptr_eq_trace_mono:
  ∀p s r s' extra.
    evaluate (p,s) = (r,s') ⇒
    ptr_eq_trace_prefix (ptr_eq_trace p s)
      (ptr_eq_trace p (s with clock := s.clock + extra)) ∧
    (r ≠ SOME TimeOut ⇒
     ptr_eq_trace p (s with clock := s.clock + extra) = ptr_eq_trace p s)
Proof
  recInduct evaluate_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt (disch_then strip_assume_tac) >> rpt gen_tac >>
  rpt (disch_then strip_assume_tac)
  >~[`MustTerminate`] >- suspend "MustTerminate"
  >~[`Seq`] >- suspend "Seq"
  >~[`If`] >- suspend "If"
  >~[`Loop`] >- suspend "Loop"
  >~[`Call`] >- suspend "Call"
  >~[`Install`] >- suspend "Install"
  >> simp[ptr_eq_trace_def]
QED

Resume ptr_eq_trace_mono[MustTerminate]:
  simp[ptr_eq_trace_def]
QED

Resume ptr_eq_trace_mono[Install]:
  `r ≠ SOME TimeOut` by (
    qpat_x_assum`evaluate _ = _` mp_tac >>
    simp[evaluate_def] >> rpt(CASE_ONE >> simp[]) >> rw[] >> gvs[]) >>
  drule_all evaluate_add_clock >>
  disch_then(qspec_then`extra`assume_tac) >>
  simp[ptr_eq_trace_def] >> gvs[] >>
  Cases_on`r` >> gvs[]
QED

Resume ptr_eq_trace_mono[Seq]:
  qpat_x_assum`evaluate _ = _` mp_tac>>
  simp[evaluate_def,ptr_eq_trace_def]>>
  rpt(pairarg_tac>>simp[])>>
  strip_tac>>
  first_x_assum(qspecl_then[`res`,`s1`,`extra`]mp_tac)>>
  simp[]>>strip_tac>>
  Cases_on`res = SOME TimeOut`>>gvs[]
  >- (rw[]>>gvs[]>>irule ptr_eq_trace_prefix_epoch_append1>>simp[]) >>
  qpat_assum`evaluate (c1,s) = _`(mp_then Any mp_tac evaluate_add_clock)>>
  simp[]>>strip_tac>>gvs[]>>
  Cases_on`res = NONE`>>gvs[]>>
  irule ptr_eq_trace_prefix_epoch_append_cong>>simp[]
QED

Resume ptr_eq_trace_mono[If]:
  qpat_x_assum`evaluate _ = _` mp_tac>>
  simp[evaluate_def,ptr_eq_trace_def]>>
  rpt(CASE_ONE>>simp[])>>
  strip_tac>>gvs[]>>metis_tac[]
QED

Resume ptr_eq_trace_mono[Loop]:
  qid_spec_tac`extra`>>
  qpat_x_assum`evaluate _ = _` mp_tac>>
  simp[evaluate_def,ptr_eq_trace_def]>>
  rpt(CASE_ONE>>simp[])>>
  rpt(pairarg_tac>>simp[])>>
  strip_tac>>gvs[]>>
  imp_res_tac cut_state_const>>gvs[]>>
  gen_tac>>
  rpt(first_x_assum(qspec_then`extra`strip_assume_tac))
  >- (Cases_on`evaluate (c,s with <|locals:=l;clock:=extra+s.clock|>)`>>rw[]>>
      gvs[]>>irule ptr_eq_trace_prefix_epoch_append1>>simp[])
  >- (`res ≠ SOME TimeOut` by metis_tac[cont_loop_not_timeout]>>
      imp_res_tac evaluate_add_clock>>
      first_x_assum(qspec_then`extra`assume_tac)>>
      gvs[dec_clock_add_clock]>>
      irule ptr_eq_trace_prefix_epoch_append_cong>>simp[])
  >- (drule evaluate_add_clock>>disch_then(qspec_then`extra`assume_tac)>>gvs[])
  >- (drule evaluate_add_clock>>disch_then(qspec_then`extra`assume_tac)>>gvs[])
  >- (reverse(Cases_on`res = SOME TimeOut`)>>gvs[]
      >- (drule evaluate_add_clock>>disch_then(qspec_then`extra`assume_tac)>>
          gvs[])>>
      Cases_on`evaluate (c,s with <|locals:=l;clock:=extra+s.clock|>)`>>rw[]>>
      gvs[]>>irule ptr_eq_trace_prefix_epoch_append1>>simp[])
QED

Resume ptr_eq_trace_mono[Call]:
  qid_spec_tac`extra`>>
  qpat_x_assum`evaluate _ = _` mp_tac>>
  simp[evaluate_def,ptr_eq_trace_def]>>
  Cases_on`s.clock = 0`>>gvs[]
  >- (
    rpt(CASE_ONE>>gvs[])>>strip_tac>>gvs[]>>rw[]>>
    rpt(CASE_ONE>>gvs[])) >>
  rpt(CASE_ONE>>gvs[])>>
  strip_tac>>gvs[]>>
  gen_tac>>
  rpt(first_x_assum(qspec_then`extra`strip_assume_tac))>>
  imp_res_tac pop_env_const>>
  qpat_assum`evaluate (_,call_env _ _ _) = _`
    (mp_then Any mp_tac evaluate_add_clock)>>
  simp[dec_clock_add_clock,ptr_eq_trace_prefix_epoch_append_cong,
       ptr_eq_trace_prefix_epoch_append1]>>
  rpt(CASE_ONE>>gvs[])
  >- (`q'' ≠ SOME TimeOut` by (strip_tac>>gvs[])>>gvs[])
  >- (strip_tac>>gvs[]>>irule ptr_eq_trace_prefix_epoch_append_cong>>simp[])
  >- (strip_tac>>gvs[]>>irule ptr_eq_trace_prefix_epoch_append_cong>>simp[])
  >> irule ptr_eq_trace_prefix_epoch_append1>>simp[]
QED

Finalise ptr_eq_trace_mono;

(* Taking n+1 epochs of a trace takes all of a prefix that is no longer, and
   an epoch_append at or beyond epoch n leaves those epochs alone. *)

Theorem TAKE_epoch_append_short:
  ∀t1 t2 n.
    t1 ≠ [] ∧ t2 ≠ [] ∧ LENGTH t1 ≤ n + 1 ⇒
    TAKE (n+1) (epoch_append t1 t2) =
    epoch_append t1 (TAKE (n + 2 - LENGTH t1) t2)
Proof
  Induct >> rw [] >>
  reverse (Cases_on `t1`) >> gvs []
  >- (
    gvs [epoch_append_CONS] >>
    Cases_on `n` >> gvs [] >>
    first_x_assum (qspecl_then [`t2`,`n'`] mp_tac) >>
    simp [ADD1]) >>
  Cases_on `t2` >> gvs [epoch_append_SING]
QED

Theorem TAKE_epoch_append_long:
  ∀t1 t2 n.
    t1 ≠ [] ∧ n + 2 ≤ LENGTH t1 ⇒
    TAKE (n+1) (epoch_append t1 t2) = TAKE (n+1) t1
Proof
  Induct >> rw [] >>
  reverse (Cases_on `t1`) >> gvs []
  >- (
    gvs [epoch_append_CONS] >>
    Cases_on `n` >> gvs [] >>
    first_x_assum (qspecl_then [`t2`,`n'`] mp_tac) >>
    simp [ADD1]) >>
  gvs []
QED

(* The Loop and Call clauses of ptr_eq_trace, each under the guards that
   select one branch of the clause. *)

Theorem ptr_eq_trace_Loop_NONE[local]:
  cut_state (names,LN) s = NONE ⇒
  ptr_eq_trace (Loop names c exit_names) s = [[]]
Proof
  rw[]>>simp[Once ptr_eq_trace_def]
QED

Theorem ptr_eq_trace_Call_NONE[local]:
  get_vars args s = NONE ⇒
  ptr_eq_trace (Call ret dest args handler) s = [[]]
Proof
  rw[]>>simp[Once ptr_eq_trace_def]
QED

Theorem ptr_eq_trace_Call_bad[local]:
  get_vars args s = SOME xs ∧ bad_dest_args dest args ⇒
  ptr_eq_trace (Call ret dest args handler) s = [[]]
Proof
  rw[]>>simp[Once ptr_eq_trace_def]
QED

Theorem ptr_eq_trace_Call_nocode[local]:
  get_vars args s = SOME xs ∧ ¬bad_dest_args dest args ∧
  find_code dest (add_ret_loc ret xs) s.code s.stack_size = NONE ⇒
  ptr_eq_trace (Call ret dest args handler) s = [[]]
Proof
  rw[]>>simp[Once ptr_eq_trace_def]
QED

Theorem ptr_eq_trace_Call_tail[local]:
  get_vars args s = SOME xs ∧ ¬bad_dest_args dest args ∧
  find_code dest (add_ret_loc ret xs) s.code s.stack_size =
    SOME (args1,prog1,ss) ∧ ret = NONE ⇒
  ptr_eq_trace (Call ret dest args handler) s =
    if handler = NONE ∧ s.clock ≠ 0 then
      ptr_eq_trace prog1 (call_env args1 ss (dec_clock s))
    else [[]]
Proof
  rpt strip_tac>>gvs[]>>simp[Once ptr_eq_trace_def]
QED

Theorem ptr_eq_trace_Call_ret[local]:
  ∀args s xs dest rn n1 n2 ret_handler l1 l2 args1 prog1 ss envs handler
   bres bst.
  get_vars args s = SOME xs ∧ ¬bad_dest_args dest args ∧
  find_code dest (add_ret_loc (SOME (rn,(n1,n2),ret_handler,l1,l2)) xs) s.code
    s.stack_size = SOME (args1,prog1,ss) ∧
  domain n1 ≠ ∅ ∧ ALL_DISTINCT rn ∧
  cut_envs (n1,n2) s.locals = SOME envs ∧ s.clock ≠ 0 ∧
  evaluate (prog1,call_env args1 ss (push_env envs handler (dec_clock s))) =
    (bres,bst) ⇒
  ptr_eq_trace (Call (SOME (rn,(n1,n2),ret_handler,l1,l2)) dest args handler)
    s =
    (let b1 = ptr_eq_trace prog1
                (call_env args1 ss (push_env envs handler (dec_clock s))) in
       case bres of
       | SOME (Result w l) =>
           (if w ≠ Loc l1 l2 ∨ LENGTH l ≠ LENGTH rn then b1
            else
              case pop_env bst of
              | NONE => b1
              | SOME s1 =>
                if domain s1.locals = domain (FST envs) ∪ domain (SND envs)
                then
                  epoch_append b1 (ptr_eq_trace ret_handler (set_vars rn l s1))
                else b1)
       | SOME (Exception w w0) =>
           (case handler of
            | NONE => b1
            | SOME (hn,h,hl1,hl2) =>
              if w ≠ Loc hl1 hl2 ∨
                 domain bst.locals ≠ domain (FST envs) ∪ domain (SND envs)
              then b1
              else epoch_append b1 (ptr_eq_trace h (set_var hn w0 bst)))
       | _ => b1)
Proof
  rpt strip_tac>>gvs[]>>simp[Once ptr_eq_trace_def]
QED

(* The returning call's trace extends the body's, and once the body has used up
   the first m+1 epochs the call contributes nothing further to them. *)
Theorem ptr_eq_trace_Call_ret_bound[local]:
  ∀args s xs dest rn n1 n2 ret_handler l1 l2 args1 prog1 ss envs handler
   bres bst.
  get_vars args s = SOME xs ∧ ¬bad_dest_args dest args ∧
  find_code dest (add_ret_loc (SOME (rn,(n1,n2),ret_handler,l1,l2)) xs) s.code
    s.stack_size = SOME (args1,prog1,ss) ∧
  domain n1 ≠ ∅ ∧ ALL_DISTINCT rn ∧
  cut_envs (n1,n2) s.locals = SOME envs ∧ s.clock ≠ 0 ∧
  evaluate (prog1,call_env args1 ss (push_env envs handler (dec_clock s))) =
    (bres,bst) ⇒
  LENGTH (ptr_eq_trace prog1
            (call_env args1 ss (push_env envs handler (dec_clock s)))) ≤
  LENGTH (ptr_eq_trace
            (Call (SOME (rn,(n1,n2),ret_handler,l1,l2)) dest args handler) s) ∧
  ∀m. ¬(LENGTH (ptr_eq_trace prog1
          (call_env args1 ss (push_env envs handler (dec_clock s)))) ≤ m + 1 ∧
        bres ≠ SOME Error) ⇒
      TAKE (m + 1)
        (ptr_eq_trace
           (Call (SOME (rn,(n1,n2),ret_handler,l1,l2)) dest args handler) s) =
      TAKE (m + 1)
        (ptr_eq_trace prog1
           (call_env args1 ss (push_env envs handler (dec_clock s))))
Proof
  rpt gen_tac>>strip_tac>>
  drule_all ptr_eq_trace_Call_ret>>
  strip_tac>>
  gvs[]>>
  every_case_tac>>
  gvs[TAKE_epoch_append_long]>>
  rpt strip_tac>>
  qmatch_goalsub_abbrev_tac`LENGTH t1 ≤ LENGTH t1 + LENGTH t2 − 1`>>
  `LENGTH t2 ≠ 0` by simp[Abbr`t2`]>>
  Cases_on`LENGTH t2`>>gvs[]
QED

Theorem ptr_eq_trace_Loop_SOME[local]:
  cut_state (names,LN) s = SOME s0 ∧ evaluate (c,s0) = (res,s1) ⇒
  ptr_eq_trace (Loop names c exit_names) s =
    if cont_loop res ∧ s1.clock ≠ 0 then
      epoch_append (ptr_eq_trace c s0)
        (ptr_eq_trace (STOP (Loop names c exit_names)) (dec_clock s1))
    else ptr_eq_trace c s0
Proof
  rw[]>>simp[Once ptr_eq_trace_def]
QED

(* A run reads its compile oracle only at Install, and the e-th Install reads
   entry e in full and the configuration of entry e+1.  So agreement on the
   first n entries and on the configuration of entry n fixes the first n+1
   epochs of the trace.  The guard on the second conjunct is a disjunction over
   the two runs so that the induction hypothesis covers whichever of them is
   the shorter; it excludes a failed Install, which reads entry n in full, and
   MustTerminate on a body timeout, which returns the state from before the
   body and so discards the installs the body performed. *)
Theorem evaluate_compile_oracle_prefix:
  ∀p s r s' co' n r2 s2.
    evaluate (p,s) = (r,s') ∧
    evaluate (p,s with compile_oracle := co') = (r2,s2) ∧
    s.ptr_eq_oracle = NONE ∧
    (∀j. j < n ⇒ s.compile_oracle j = co' j) ∧
    FST (s.compile_oracle n) = FST (co' n) ⇒
    TAKE (n+1) (ptr_eq_trace p s) =
    TAKE (n+1) (ptr_eq_trace p (s with compile_oracle := co')) ∧
    ((LENGTH (ptr_eq_trace p s) ≤ n + 1 ∧ r ≠ SOME Error) ∨
     (LENGTH (ptr_eq_trace p (s with compile_oracle := co')) ≤ n + 1 ∧
      r2 ≠ SOME Error) ⇒
       r2 = r ∧
       s2 = s' with compile_oracle :=
                shift_seq (LENGTH (ptr_eq_trace p s) - 1) co' ∧
       ptr_eq_trace p (s with compile_oracle := co') = ptr_eq_trace p s)
Proof
  recInduct evaluate_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt (disch_then strip_assume_tac) >> rpt gen_tac >>
  rpt (disch_then strip_assume_tac)
  >~[`MustTerminate`] >- suspend "MustTerminate"
  >~[`Seq`] >- suspend "Seq"
  >~[`If`] >- suspend "If"
  >~[`Loop`] >- suspend "Loop"
  >~[`Call`] >- suspend "Call"
  >~[`Install`] >- suspend "Install"
  >> gvs[ptr_eq_trace_def,evaluate_compile_oracle_with_const]
  >> rpt(CASE_ONE >> gvs[])
QED

Resume evaluate_compile_oracle_prefix[MustTerminate]:
  rpt(qpat_x_assum`∀a. _`mp_tac)>>
  Cases_on`s.termdep = 0`>>
  gvs[evaluate_def,ptr_eq_trace_def]>>
  rpt(pairarg_tac>>gvs[])>>
  strip_tac>>strip_tac>>
  first_x_assum(qspecl_then[`co'`,`n`,`res`,`s1`]mp_tac)>>
  simp[]>>strip_tac>>
  Cases_on`res' = SOME TimeOut`>>gvs[]>>
  Cases_on`res = SOME TimeOut`>>gvs[]
QED

Resume evaluate_compile_oracle_prefix[Install]:
  Cases_on`n = 0`>>gvs[]
  >- (
    qpat_x_assum`evaluate _ = _` mp_tac>>
    qpat_x_assum`evaluate _ = _` mp_tac>>
    gvs[evaluate_def,ptr_eq_trace_def]>>
    rpt(CASE_ONE>>gvs[])) >>
  `s.compile_oracle 0 = co' 0` by gvs[]>>
  `FST (s.compile_oracle 1) = FST (co' 1)` by
    (Cases_on`1 < n`>-gvs[]>>`n = 1` by simp[]>>gvs[])>>
  qpat_x_assum`evaluate _ = _` mp_tac>>
  qpat_x_assum`evaluate _ = _` mp_tac>>
  gvs[evaluate_def,ptr_eq_trace_def]>>
  rpt(CASE_ONE>>gvs[])>>
  gvs[shift_seq_def]>>
  gvs[state_component_equality,FUN_EQ_THM]
QED

Resume evaluate_compile_oracle_prefix[Seq]:
  rpt(qpat_x_assum`∀a. _`mp_tac)>>
  qpat_x_assum`evaluate (Seq _ _,_) = _` mp_tac>>
  qpat_x_assum`evaluate (Seq _ _,_) = _` mp_tac>>
  simp[Once ptr_eq_trace_def,evaluate_def]>>
  rpt(pairarg_tac>>simp[])>>
  Cases_on`LENGTH (ptr_eq_trace c1 s) ≤ n + 1 ∧ res ≠ SOME Error`
  >- (
    rpt (disch_then strip_assume_tac)>>
    first_assum(qspecl_then[`co'`,`n`,`res'`,`s1'`]mp_tac)>>
    impl_tac >- (rpt conj_tac>>first_assum ACCEPT_TAC)>>
    strip_tac>>
    first_x_assum(qspecl_then[`s.compile_oracle`,`n`,`res`,`s1`]mp_tac)>>
    PURE_REWRITE_TAC[with_same_compile_oracle]>>
    impl_tac >- (rpt conj_tac >- first_assum ACCEPT_TAC >>
                 rpt strip_tac>>REFL_TAC)>>
    strip_tac>>
    qpat_x_assum`_ ⇒ _ ∧ s1' = _ ∧ _` mp_tac>>
    impl_tac >- (disj1_tac>>first_assum ACCEPT_TAC)>>
    strip_tac>>
    qpat_x_assum`_ ⇒ _ ∧ s1 = _ ∧ _` mp_tac>>
    impl_tac >- (disj1_tac>>first_assum ACCEPT_TAC)>>
    strip_tac>>
    Cases_on`res = NONE`
    >- (
      qpat_x_assum`NONE = res ⇒ _` mp_tac>>
      `s1.compile_oracle =
         shift_seq (LENGTH (ptr_eq_trace c1 s) − 1) s.compile_oracle` by
        (qpat_x_assum`s1 = s1 with compile_oracle := _` mp_tac>>
         simp[state_component_equality])>>
      qpat_x_assum`s1 = s1 with compile_oracle := _` kall_tac>>
      gvs[]>>
      `s1.ptr_eq_oracle = NONE` by (imp_res_tac evaluate_consts>>gvs[])>>
      `LENGTH (ptr_eq_trace c1 s) ≠ 0` by simp[]>>
      disch_then(qspecl_then
        [`shift_seq (LENGTH (ptr_eq_trace c1 s) − 1) co'`,
         `n + 1 - LENGTH (ptr_eq_trace c1 s)`,`r2`,`s2`]mp_tac)>>
      impl_tac >- (
        rpt conj_tac
        >- first_assum ACCEPT_TAC
        >- first_assum ACCEPT_TAC
        >- (simp[shift_seq_def]>>rw[]>>first_x_assum irule>>simp[])
        >- (simp[shift_seq_def]>>
            `n + 1 - LENGTH (ptr_eq_trace c1 s) +
               (LENGTH (ptr_eq_trace c1 s) - 1) = n` by simp[]>>
            simp[]))>>
      strip_tac>>
      `ptr_eq_trace (Seq c1 c2) s =
         epoch_append (ptr_eq_trace c1 s) (ptr_eq_trace c2 s1)` by
        (simp[Once ptr_eq_trace_def]>>gvs[])>>
      `ptr_eq_trace (Seq c1 c2) (s with compile_oracle := co') =
         epoch_append (ptr_eq_trace c1 s)
           (ptr_eq_trace c2 (s1 with compile_oracle :=
              shift_seq (LENGTH (ptr_eq_trace c1 s) − 1) co'))` by
        (simp[Once ptr_eq_trace_def]>>gvs[])>>
      simp[TAKE_epoch_append_short,shift_seq_shift_seq]>>
      `n + 1 - LENGTH (ptr_eq_trace c1 s) + 1 =
         n + 2 - LENGTH (ptr_eq_trace c1 s)` by simp[]>>
      gvs[]>>
      gvs[shift_seq_shift_seq]>>
      `LENGTH (ptr_eq_trace c1 s) ≠ 0 ∧ LENGTH (ptr_eq_trace c2 s1) ≠ 0` by
        simp[LENGTH_NIL]>>
      `LENGTH (ptr_eq_trace c1 s) - 1 + (LENGTH (ptr_eq_trace c2 s1) - 1) =
         LENGTH (ptr_eq_trace c1 s) + LENGTH (ptr_eq_trace c2 s1) - 2` by simp[]>>
      gvs[]>>
      strip_tac>>gvs[])
    >- (
      qpat_x_assum`NONE = res ⇒ _` kall_tac>>
      gvs[]>>
      `ptr_eq_trace (Seq c1 c2) (s with compile_oracle := co') =
         ptr_eq_trace c1 s` by
        (simp[Once ptr_eq_trace_def]>>gvs[])>>
      `ptr_eq_trace (Seq c1 c2) s = ptr_eq_trace c1 s` by
        (simp[Once ptr_eq_trace_def]>>gvs[])>>
      gvs[])) >>
  Cases_on`LENGTH (ptr_eq_trace c1 (s with compile_oracle := co')) ≤ n + 1 ∧
           res' ≠ SOME Error`
  >- (
    rpt (disch_then strip_assume_tac)>>
    qpat_x_assum`NONE = res ⇒ _` kall_tac>>
    first_x_assum(qspecl_then[`co'`,`n`,`res'`,`s1'`]mp_tac)>>
    impl_tac >- (rpt conj_tac>>first_assum ACCEPT_TAC)>>
    strip_tac>>
    qpat_x_assum`_ ⇒ _ ∧ s1' = _ ∧ _` mp_tac>>
    impl_tac >- (disj2_tac>>first_assum ACCEPT_TAC)>>
    strip_tac>>
    gvs[])
  >- (
    rpt (disch_then strip_assume_tac)>>
    qpat_x_assum`NONE = res ⇒ _` kall_tac>>
    first_x_assum(qspecl_then[`co'`,`n`,`res'`,`s1'`]mp_tac)>>
    impl_tac >- (rpt conj_tac>>first_assum ACCEPT_TAC)>>
    strip_tac>>
    `ptr_eq_trace (Seq c1 c2) (s with compile_oracle := co') =
       (if res' = NONE then
          epoch_append (ptr_eq_trace c1 (s with compile_oracle := co'))
            (ptr_eq_trace c2 s1')
        else ptr_eq_trace c1 (s with compile_oracle := co'))` by
      (simp[Once ptr_eq_trace_def]>>gvs[])>>
    `ptr_eq_trace (Seq c1 c2) s =
       (if res = NONE then
          epoch_append (ptr_eq_trace c1 s) (ptr_eq_trace c2 s1)
        else ptr_eq_trace c1 s)` by
      (simp[Once ptr_eq_trace_def]>>gvs[])>>
    Cases_on`res = NONE`>>Cases_on`res' = NONE`>>gvs[]>>
    gvs[TAKE_epoch_append_long]>>
    qspecl_then[`c2`,`s1`]assume_tac ptr_eq_trace_LENGTH_NOT_0>>
    qspecl_then[`c2`,`s1'`]assume_tac ptr_eq_trace_LENGTH_NOT_0>>
    rw[]>>gvs[])
QED

Resume evaluate_compile_oracle_prefix[If]:
  rpt(qpat_x_assum`∀a b c d e. _`mp_tac)>>
  Cases_on`get_var r1 s`>>Cases_on`get_var_imm ri s`>>
  gvs[evaluate_def,ptr_eq_trace_def]>>
  Cases_on`word_cmp cmp x x'`>>gvs[]>>
  rename1`word_cmp cmp x x' = SOME b`>>Cases_on`b`>>gvs[]>>
  strip_tac>>
  first_x_assum(qspecl_then[`co'`,`n`,`r2`,`s2`]mp_tac)>>
  simp[]>>strip_tac>>gvs[]
QED

Resume evaluate_compile_oracle_prefix[Loop]:
  rpt(qpat_x_assum`∀a. _`mp_tac)>>
  Cases_on`cut_state (names,LN) s`
  >- (
    qpat_x_assum`evaluate (Loop _ _ _,_) = _`
      (mp_tac o SIMP_RULE (srw_ss()) [Once evaluate_def])>>
    qpat_x_assum`evaluate (Loop _ _ _,_) = _`
      (mp_tac o SIMP_RULE (srw_ss()) [Once evaluate_def])>>
    `ptr_eq_trace (Loop names c exit_names) s = [[]]` by
      (irule ptr_eq_trace_Loop_NONE>>simp[])>>
    `ptr_eq_trace (Loop names c exit_names) (s with compile_oracle := co') =
       [[]]` by (irule ptr_eq_trace_Loop_NONE>>simp[])>>
    ntac 2 (pop_assum (fn th => PURE_REWRITE_TAC[th]))>>
    simp[])>>
  rename1`cut_state (names,LN) s = SOME s0`>>
  `cut_state (names,LN) (s with compile_oracle := co') =
     SOME (s0 with compile_oracle := co')` by simp[]>>
  `s0.compile_oracle = s.compile_oracle` by
    (imp_res_tac cut_state_const>>simp[])>>
  `s0.ptr_eq_oracle = NONE` by (imp_res_tac cut_state_const>>simp[])>>
  qpat_assum`cut_state (names,LN) (s with compile_oracle := co') = _`
    (fn cs2 =>
       qpat_x_assum`evaluate (Loop _ _ _,_ with compile_oracle := _) = _`
         (mp_tac o SIMP_RULE (srw_ss()) [Once evaluate_def, cs2]))>>
  qpat_assum`cut_state (names,LN) s = SOME s0`
    (fn cs =>
       qpat_x_assum`evaluate (Loop _ _ _,_) = _`
         (mp_tac o SIMP_RULE (srw_ss()) [Once evaluate_def, cs]))>>
  Cases_on`evaluate (c,s0)`>>
  Cases_on`evaluate (c,s0 with compile_oracle := co')`>>
  rename1`evaluate (c,s0) = (res,s1)`>>
  rename1`evaluate (c,s0 with compile_oracle := co') = (res',s1')`>>
  simp[]>>
  `ptr_eq_trace (Loop names c exit_names) s =
     (if cont_loop res ∧ s1.clock ≠ 0 then
        epoch_append (ptr_eq_trace c s0)
          (ptr_eq_trace (STOP (Loop names c exit_names)) (dec_clock s1))
      else ptr_eq_trace c s0)` by
    (irule ptr_eq_trace_Loop_SOME>>simp[])>>
  `ptr_eq_trace (Loop names c exit_names) (s with compile_oracle := co') =
     (if cont_loop res' ∧ s1'.clock ≠ 0 then
        epoch_append (ptr_eq_trace c (s0 with compile_oracle := co'))
          (ptr_eq_trace (STOP (Loop names c exit_names)) (dec_clock s1'))
      else ptr_eq_trace c (s0 with compile_oracle := co'))` by
    (irule ptr_eq_trace_Loop_SOME>>simp[])>>
  ntac 2 (pop_assum (fn th => PURE_REWRITE_TAC[th]))>>
  Cases_on`LENGTH (ptr_eq_trace c s0) ≤ n + 1 ∧ res ≠ SOME Error`
  >- (
    rpt (disch_then strip_assume_tac)>>
    first_assum(qspecl_then[`co'`,`n`,`res'`,`s1'`]mp_tac)>>
    impl_tac >- (rpt conj_tac>>first_assum ACCEPT_TAC)>>
    strip_tac>>
    first_x_assum(qspecl_then[`s0.compile_oracle`,`n`,`res`,`s1`]mp_tac)>>
    PURE_REWRITE_TAC[with_same_compile_oracle]>>
    impl_tac >- (
      qpat_assum`s0.compile_oracle = _` (fn th => PURE_REWRITE_TAC[th])>>
      rpt conj_tac >- first_assum ACCEPT_TAC >>
      rpt strip_tac>>REFL_TAC)>>
    strip_tac>>
    qpat_x_assum`_ ⇒ _ ∧ s1' = _ ∧ _` mp_tac>>
    impl_tac >- (disj1_tac>>first_assum ACCEPT_TAC)>>
    strip_tac>>
    qpat_x_assum`_ ⇒ _ ∧ s1 = _ ∧ _` mp_tac>>
    impl_tac >- (disj1_tac>>first_assum ACCEPT_TAC)>>
    strip_tac>>
    Cases_on`cont_loop res ∧ s1.clock ≠ 0`
    >- (
      qpat_x_assum`cont_loop res ∧ _ ⇒ _` mp_tac>>
      `s1.compile_oracle =
         shift_seq (LENGTH (ptr_eq_trace c s0) − 1) s0.compile_oracle` by
        (qpat_x_assum`s1 = s1 with compile_oracle := _` mp_tac>>
         simp[state_component_equality])>>
      qpat_x_assum`s1 = s1 with compile_oracle := _` kall_tac>>
      gvs[]>>
      `s1.ptr_eq_oracle = NONE` by (imp_res_tac evaluate_consts>>gvs[])>>
      `LENGTH (ptr_eq_trace c s0) ≠ 0` by simp[]>>
      disch_then(qspecl_then
        [`shift_seq (LENGTH (ptr_eq_trace c s0) − 1) co'`,
         `n + 1 - LENGTH (ptr_eq_trace c s0)`,`r2`,`s2`]mp_tac)>>
      impl_tac >- (
        rpt conj_tac
        >- gvs[dec_clock_def]
        >- first_assum ACCEPT_TAC
        >- (simp[shift_seq_def]>>rw[]>>first_x_assum irule>>simp[])
        >- (simp[shift_seq_def]>>
            `n + 1 - LENGTH (ptr_eq_trace c s0) +
               (LENGTH (ptr_eq_trace c s0) - 1) = n` by simp[]>>
            simp[]))>>
      strip_tac>>
      simp[TAKE_epoch_append_short,shift_seq_shift_seq]>>
      `n + 1 - LENGTH (ptr_eq_trace c s0) + 1 =
         n + 2 - LENGTH (ptr_eq_trace c s0)` by simp[]>>
      gvs[]>>
      gvs[shift_seq_shift_seq]>>
      `LENGTH (ptr_eq_trace c s0) ≠ 0 ∧
       LENGTH (ptr_eq_trace (STOP (Loop names c exit_names)) (dec_clock s1)) ≠ 0`
        by simp[LENGTH_NIL]>>
      `LENGTH (ptr_eq_trace c s0) - 1 +
         (LENGTH (ptr_eq_trace (STOP (Loop names c exit_names))
                    (dec_clock s1)) - 1) =
       LENGTH (ptr_eq_trace c s0) +
         LENGTH (ptr_eq_trace (STOP (Loop names c exit_names))
                    (dec_clock s1)) - 2` by simp[]>>
      gvs[dec_clock_def]>>
      strip_tac>>gvs[])
    >- (
      qpat_x_assum`cont_loop res ∧ _ ⇒ _` kall_tac>>
      `s1.compile_oracle =
         shift_seq (LENGTH (ptr_eq_trace c s0) − 1) s0.compile_oracle` by
        (qpat_x_assum`s1 = s1 with compile_oracle := _` mp_tac>>
         simp[state_component_equality])>>
      qpat_x_assum`s1 = s1 with compile_oracle := _` kall_tac>>
      Cases_on`cont_loop res`>>gvs[]>>
      Cases_on`res = SOME (Break 0)`>>gvs[]>>
      Cases_on`cut_state (exit_names,LN) s1`>>gvs[])) >>
  Cases_on`LENGTH (ptr_eq_trace c (s0 with compile_oracle := co')) ≤ n + 1 ∧
           res' ≠ SOME Error`
  >- (
    rpt (disch_then strip_assume_tac)>>
    qpat_x_assum`cont_loop res ∧ _ ⇒ _` kall_tac>>
    first_x_assum(qspecl_then[`co'`,`n`,`res'`,`s1'`]mp_tac)>>
    impl_tac >- (rpt conj_tac>>first_assum ACCEPT_TAC)>>
    strip_tac>>
    qpat_x_assum`_ ⇒ _ ∧ s1' = _ ∧ _` mp_tac>>
    impl_tac >- (disj2_tac>>first_assum ACCEPT_TAC)>>
    strip_tac>>
    gvs[])
  >- (
    rpt (disch_then strip_assume_tac)>>
    qpat_x_assum`cont_loop res ∧ _ ⇒ _` kall_tac>>
    first_x_assum(qspecl_then[`co'`,`n`,`res'`,`s1'`]mp_tac)>>
    impl_tac >- (rpt conj_tac>>first_assum ACCEPT_TAC)>>
    strip_tac>>
    Cases_on`cont_loop res ∧ s1.clock ≠ 0`>>
    Cases_on`cont_loop res' ∧ s1'.clock ≠ 0`>>gvs[]>>
    gvs[TAKE_epoch_append_long]>>
    qspecl_then[`STOP (Loop names c exit_names)`,`dec_clock s1`]assume_tac
      ptr_eq_trace_LENGTH_NOT_0>>
    qspecl_then[`STOP (Loop names c exit_names)`,`dec_clock s1'`]assume_tac
      ptr_eq_trace_LENGTH_NOT_0>>
    rw[]>>gvs[])
QED

Resume evaluate_compile_oracle_prefix[Call]:
  rpt(qpat_x_assum`∀a. _`mp_tac)>>
  Cases_on`get_vars args s`
  >- (
    qpat_assum`get_vars args s = _`(fn gv =>
      qpat_x_assum`evaluate (Call _ _ _ _,_ with compile_oracle := _) = _`
        (mp_tac o SIMP_RULE (srw_ss()) [Once evaluate_def, gv]))>>
    qpat_assum`get_vars args s = _`(fn gv =>
      qpat_x_assum`evaluate (Call _ _ _ _,_) = _`
        (mp_tac o SIMP_RULE (srw_ss()) [Once evaluate_def, gv]))>>
    `ptr_eq_trace (Call ret dest args handler) s = [[]]` by
      (irule ptr_eq_trace_Call_NONE>>simp[])>>
    `ptr_eq_trace (Call ret dest args handler)
       (s with compile_oracle := co') = [[]]` by
      (irule ptr_eq_trace_Call_NONE>>simp[])>>
    ntac 2 (pop_assum (fn th => PURE_REWRITE_TAC[th]))>>
    simp[]) >>
  rename1`get_vars args s = SOME xs`>>
  Cases_on`bad_dest_args dest args`
  >- (
    qpat_assum`get_vars args s = _`(fn gv =>
      qpat_assum`bad_dest_args dest args`(fn bd =>
        qpat_x_assum`evaluate (Call _ _ _ _,_ with compile_oracle := _) = _`
          (mp_tac o SIMP_RULE (srw_ss()) [Once evaluate_def, gv, bd])))>>
    qpat_assum`get_vars args s = _`(fn gv =>
      qpat_assum`bad_dest_args dest args`(fn bd =>
        qpat_x_assum`evaluate (Call _ _ _ _,_) = _`
          (mp_tac o SIMP_RULE (srw_ss()) [Once evaluate_def, gv, bd])))>>
    `ptr_eq_trace (Call ret dest args handler) s = [[]]` by
      (irule ptr_eq_trace_Call_bad>>simp[])>>
    `ptr_eq_trace (Call ret dest args handler)
       (s with compile_oracle := co') = [[]]` by
      (irule ptr_eq_trace_Call_bad>>simp[])>>
    ntac 2 (pop_assum (fn th => PURE_REWRITE_TAC[th]))>>
    simp[]) >>
  Cases_on`find_code dest (add_ret_loc ret xs) s.code s.stack_size`
  >- (
    qpat_assum`get_vars args s = _`(fn gv =>
      qpat_assum`¬bad_dest_args dest args`(fn bd =>
        qpat_assum`find_code _ _ _ _ = NONE`(fn fc =>
          qpat_x_assum`evaluate (Call _ _ _ _,_ with compile_oracle := _) = _`
            (mp_tac o SIMP_RULE (srw_ss()) [Once evaluate_def, gv, bd, fc]))))>>
    qpat_assum`get_vars args s = _`(fn gv =>
      qpat_assum`¬bad_dest_args dest args`(fn bd =>
        qpat_assum`find_code _ _ _ _ = NONE`(fn fc =>
          qpat_x_assum`evaluate (Call _ _ _ _,_) = _`
            (mp_tac o SIMP_RULE (srw_ss()) [Once evaluate_def, gv, bd, fc]))))>>
    `ptr_eq_trace (Call ret dest args handler) s = [[]]` by
      (irule ptr_eq_trace_Call_nocode>>simp[])>>
    `ptr_eq_trace (Call ret dest args handler)
       (s with compile_oracle := co') = [[]]` by
      (irule ptr_eq_trace_Call_nocode>>simp[])>>
    ntac 2 (pop_assum (fn th => PURE_REWRITE_TAC[th]))>>
    strip_tac>>strip_tac>>
    rpt (disch_then kall_tac)>>
    gvs[])
  >- (
    rename1`find_code dest (add_ret_loc ret xs) s.code s.stack_size = SOME v3`>>
    PairCases_on`v3`>>
    Cases_on`ret`
    >- (
      `ptr_eq_trace (Call NONE dest args handler) s =
         (if handler = NONE ∧ s.clock ≠ 0 then
            ptr_eq_trace v31 (call_env v30 v32 (dec_clock s))
          else [[]])` by
        (irule ptr_eq_trace_Call_tail>>simp[])>>
      `ptr_eq_trace (Call NONE dest args handler)
         (s with compile_oracle := co') =
         (if handler = NONE ∧ (s with compile_oracle := co').clock ≠ 0 then
            ptr_eq_trace v31
              (call_env v30 v32 (dec_clock (s with compile_oracle := co')))
          else [[]])` by
        (irule ptr_eq_trace_Call_tail>>simp[])>>
      ntac 2 (pop_assum (fn th => PURE_REWRITE_TAC[th]))>>
      Cases_on`handler = NONE ∧ s.clock ≠ 0`
      >- (
        qpat_x_assum`handler = NONE ∧ _`strip_assume_tac>>
        gvs[]>>
        `call_env v30 v32 (dec_clock (s with compile_oracle := co')) =
           call_env v30 v32 (dec_clock s) with compile_oracle := co'` by
          simp[call_env_def,dec_clock_def,state_component_equality]>>
        qpat_assum`get_vars args s = _`(fn gv =>
          qpat_assum`¬bad_dest_args dest args`(fn bd =>
            qpat_assum`find_code _ _ _ _ = _`(fn fc =>
              qpat_assum`s.clock ≠ 0`(fn ck =>
                qpat_x_assum`evaluate (Call _ _ _ _,_ with compile_oracle := _) = _`
                  (mp_tac o SIMP_RULE (srw_ss())
                     [Once evaluate_def, gv, bd, fc, ck])))))>>
        qpat_assum`get_vars args s = _`(fn gv =>
          qpat_assum`¬bad_dest_args dest args`(fn bd =>
            qpat_assum`find_code _ _ _ _ = _`(fn fc =>
              qpat_assum`s.clock ≠ 0`(fn ck =>
                qpat_x_assum`evaluate (Call _ _ _ _,_) = _`
                  (mp_tac o SIMP_RULE (srw_ss())
                     [Once evaluate_def, gv, bd, fc, ck])))))>>
        pop_assum (fn th => PURE_REWRITE_TAC[th])>>
        Cases_on`evaluate (v31,call_env v30 v32 (dec_clock s))`>>
        Cases_on`evaluate (v31,
          call_env v30 v32 (dec_clock s) with compile_oracle := co')`>>
        gvs[]>>
        rename1`evaluate (v31,call_env v30 v32 (dec_clock s)) = (res,st)`>>
        rename1`evaluate (v31,call_env v30 v32 (dec_clock s) with
                  compile_oracle := co') = (res2,st2)`>>
        strip_tac>>strip_tac>>
        disch_then assume_tac>>
        strip_tac>>
        qpat_x_assum`∀co'' n' r2' s2'. _`
          (qspecl_then[`co'`,`n`,`res2`,`st2`]mp_tac)>>
        impl_tac >- (rpt conj_tac>>first_assum ACCEPT_TAC)>>
        strip_tac>>
        Cases_on`bad_fun_return res`>>Cases_on`bad_fun_return res2`>>gvs[]>>
        rw[]>>CCONTR_TAC>>
        qpat_x_assum`_ ∨ _ ⇒ _`mp_tac>>
        impl_tac>>gvs[]>>
        strip_tac>>gvs[])
      >- (
        qpat_assum`get_vars args s = _`(fn gv =>
          qpat_assum`¬bad_dest_args dest args`(fn bd =>
            qpat_assum`find_code _ _ _ _ = _`(fn fc =>
              qpat_x_assum`evaluate (Call _ _ _ _,_ with compile_oracle := _) = _`
                (mp_tac o SIMP_RULE (srw_ss()) [Once evaluate_def, gv, bd, fc]))))>>
        qpat_assum`get_vars args s = _`(fn gv =>
          qpat_assum`¬bad_dest_args dest args`(fn bd =>
            qpat_assum`find_code _ _ _ _ = _`(fn fc =>
              qpat_x_assum`evaluate (Call _ _ _ _,_) = _`
                (mp_tac o SIMP_RULE (srw_ss()) [Once evaluate_def, gv, bd, fc]))))>>
        Cases_on`handler`>>gvs[]>>
        strip_tac>>strip_tac>>rpt (disch_then kall_tac)>>gvs[]))
    >- (
      PairCases_on`x`>>
      Cases_on`domain x1 = {} ∨ ¬ALL_DISTINCT x0`
      >- (
        qpat_assum`get_vars args s = _`(fn gv =>
          qpat_assum`¬bad_dest_args dest args`(fn bd =>
            qpat_assum`find_code _ _ _ _ = _`(fn fc =>
              qpat_assum`domain _ = ∅ ∨ _`(fn dc =>
                qpat_x_assum`evaluate (Call _ _ _ _,_ with compile_oracle := _) = _`
                  (mp_tac o SIMP_RULE (srw_ss())
                     [Once evaluate_def, gv, bd, fc, dc])))))>>
        qpat_assum`get_vars args s = _`(fn gv =>
          qpat_assum`¬bad_dest_args dest args`(fn bd =>
            qpat_assum`find_code _ _ _ _ = _`(fn fc =>
              qpat_assum`domain _ = ∅ ∨ _`(fn dc =>
                qpat_x_assum`evaluate (Call _ _ _ _,_) = _`
                  (mp_tac o SIMP_RULE (srw_ss())
                     [Once evaluate_def, gv, bd, fc, dc])))))>>
        `ptr_eq_trace (Call (SOME (x0,(x1,x2),x3,x4,x5)) dest args handler) s =
           [[]]` by
          (simp[Once ptr_eq_trace_def]>>gvs[])>>
        `ptr_eq_trace (Call (SOME (x0,(x1,x2),x3,x4,x5)) dest args handler)
           (s with compile_oracle := co') = [[]]` by
          (simp[Once ptr_eq_trace_def]>>gvs[])>>
        ntac 2 (pop_assum (fn th => PURE_REWRITE_TAC[th]))>>
        strip_tac>>strip_tac>>
        rpt (disch_then kall_tac)>>
        gvs[]) >>
      Cases_on`cut_envs (x1,x2) s.locals`
      >- (
        qpat_assum`get_vars args s = _`(fn gv =>
          qpat_assum`¬bad_dest_args dest args`(fn bd =>
            qpat_assum`find_code _ _ _ _ = _`(fn fc =>
              qpat_assum`¬(domain _ = ∅ ∨ _)`(fn dc =>
                qpat_assum`cut_envs _ _ = NONE`(fn ce =>
                  qpat_x_assum`evaluate (Call _ _ _ _,_ with compile_oracle := _) = _`
                    (mp_tac o SIMP_RULE (srw_ss())
                       [Once evaluate_def, gv, bd, fc, dc, ce]))))))>>
        qpat_assum`get_vars args s = _`(fn gv =>
          qpat_assum`¬bad_dest_args dest args`(fn bd =>
            qpat_assum`find_code _ _ _ _ = _`(fn fc =>
              qpat_assum`¬(domain _ = ∅ ∨ _)`(fn dc =>
                qpat_assum`cut_envs _ _ = NONE`(fn ce =>
                  qpat_x_assum`evaluate (Call _ _ _ _,_) = _`
                    (mp_tac o SIMP_RULE (srw_ss())
                       [Once evaluate_def, gv, bd, fc, dc, ce]))))))>>
        `ptr_eq_trace (Call (SOME (x0,(x1,x2),x3,x4,x5)) dest args handler) s =
           [[]]` by
          (simp[Once ptr_eq_trace_def]>>gvs[])>>
        `ptr_eq_trace (Call (SOME (x0,(x1,x2),x3,x4,x5)) dest args handler)
           (s with compile_oracle := co') = [[]]` by
          (simp[Once ptr_eq_trace_def]>>gvs[])>>
        ntac 2 (pop_assum (fn th => PURE_REWRITE_TAC[th]))>>
        strip_tac>>strip_tac>>
        rpt (disch_then kall_tac)>>
        gvs[]) >>
      rename1`cut_envs (x1,x2) s.locals = SOME envs`>>
      Cases_on`s.clock = 0`
      >- (
        qpat_assum`get_vars args s = _`(fn gv =>
          qpat_assum`¬bad_dest_args dest args`(fn bd =>
            qpat_assum`find_code _ _ _ _ = _`(fn fc =>
              qpat_assum`¬(domain _ = ∅ ∨ _)`(fn dc =>
                qpat_assum`cut_envs _ _ = SOME _`(fn ce =>
                  qpat_assum`s.clock = 0`(fn ck =>
                    qpat_x_assum
                      `evaluate (Call _ _ _ _,_ with compile_oracle := _) = _`
                      (mp_tac o SIMP_RULE (srw_ss())
                         [Once evaluate_def, gv, bd, fc, dc, ce, ck])))))))>>
        qpat_assum`get_vars args s = _`(fn gv =>
          qpat_assum`¬bad_dest_args dest args`(fn bd =>
            qpat_assum`find_code _ _ _ _ = _`(fn fc =>
              qpat_assum`¬(domain _ = ∅ ∨ _)`(fn dc =>
                qpat_assum`cut_envs _ _ = SOME _`(fn ce =>
                  qpat_assum`s.clock = 0`(fn ck =>
                    qpat_x_assum`evaluate (Call _ _ _ _,_) = _`
                      (mp_tac o SIMP_RULE (srw_ss())
                         [Once evaluate_def, gv, bd, fc, dc, ce, ck])))))))>>
        `ptr_eq_trace (Call (SOME (x0,(x1,x2),x3,x4,x5)) dest args handler) s =
           [[]]` by
          (simp[Once ptr_eq_trace_def]>>gvs[])>>
        `ptr_eq_trace (Call (SOME (x0,(x1,x2),x3,x4,x5)) dest args handler)
           (s with compile_oracle := co') = [[]]` by
          (simp[Once ptr_eq_trace_def]>>gvs[])>>
        ntac 2 (pop_assum (fn th => PURE_REWRITE_TAC[th]))>>
        strip_tac>>strip_tac>>
        rpt (disch_then kall_tac)>>
        gvs[shift_seq_0])
      >- (
        `call_env v30 v32
           (push_env envs handler (dec_clock (s with compile_oracle := co'))) =
           call_env v30 v32 (push_env envs handler (dec_clock s)) with
             compile_oracle := co'` by simp[dec_clock_def]>>
        qpat_assum`get_vars args s = _`(fn gv =>
          qpat_assum`¬bad_dest_args dest args`(fn bd =>
            qpat_assum`find_code _ _ _ _ = _`(fn fc =>
              qpat_assum`¬(domain _ = ∅ ∨ _)`(fn dc =>
                qpat_assum`cut_envs _ _ = SOME _`(fn ce =>
                  qpat_assum`s.clock ≠ 0`(fn ck =>
                    qpat_x_assum
                      `evaluate (Call _ _ _ _,_ with compile_oracle := _) = _`
                      (mp_tac o SIMP_RULE (srw_ss())
                         [Once evaluate_def, gv, bd, fc, dc, ce, ck])))))))>>
        qpat_assum`get_vars args s = _`(fn gv =>
          qpat_assum`¬bad_dest_args dest args`(fn bd =>
            qpat_assum`find_code _ _ _ _ = _`(fn fc =>
              qpat_assum`¬(domain _ = ∅ ∨ _)`(fn dc =>
                qpat_assum`cut_envs _ _ = SOME _`(fn ce =>
                  qpat_assum`s.clock ≠ 0`(fn ck =>
                    qpat_x_assum`evaluate (Call _ _ _ _,_) = _`
                      (mp_tac o SIMP_RULE (srw_ss())
                         [Once evaluate_def, gv, bd, fc, dc, ce, ck])))))))>>
        qpat_assum`call_env _ _ _ = _`(fn th => PURE_REWRITE_TAC[th])>>
        strip_tac>>strip_tac>>
        Cases_on`evaluate (v31,
          call_env v30 v32 (push_env envs handler (dec_clock s)))`>>
        Cases_on`evaluate (v31,
          call_env v30 v32 (push_env envs handler (dec_clock s)) with
            compile_oracle := co')`>>
        rename1`evaluate (v31,
          call_env v30 v32 (push_env envs handler (dec_clock s))) = (bres,bst)`>>
        rename1`evaluate (v31,
          call_env v30 v32 (push_env envs handler (dec_clock s)) with
            compile_oracle := co') = (bres2,bst2)`>>
        qpat_x_assum`¬(domain _ = ∅ ∨ _)`
          (strip_assume_tac o SIMP_RULE (srw_ss()) [])>>
        `(call_env v30 v32 (push_env envs handler (dec_clock s))).ptr_eq_oracle =
           s.ptr_eq_oracle` by simp[]>>
        `(call_env v30 v32 (push_env envs handler (dec_clock s))).compile_oracle =
           s.compile_oracle` by simp[]>>
        rpt (disch_then strip_assume_tac)>>
        qpat_assum`∀xs' v3 args1 v10 prog ss v1 n v6 names v9 ret_handler v11 l1
            l2 envs. _`
          (qspecl_then[`xs`,`(v30,v31,v32)`,`v30`,`(v31,v32)`,`v31`,`v32`,
            `(x0,(x1,x2),x3,x4,x5)`,`x0`,`((x1,x2),x3,x4,x5)`,`(x1,x2)`,
            `(x3,x4,x5)`,`x3`,`(x4,x5)`,`x4`,`x5`,`envs`]mp_tac)>>
        impl_tac >- (SIMP_TAC (srw_ss()) []>>rpt conj_tac>>first_assum ACCEPT_TAC)>>
        disch_then(qspecl_then[`bres`,`bst`,`co'`,`n`,`bres2`,`bst2`]mp_tac)>>
        impl_tac >- (
          qpat_assum`(call_env _ _ _).ptr_eq_oracle = _`(fn th1 =>
            qpat_assum`(call_env _ _ _).compile_oracle = _`(fn th2 =>
              PURE_REWRITE_TAC[th1,th2]))>>
          rpt conj_tac>>first_assum ACCEPT_TAC)>>
        strip_tac>>
        Cases_on`LENGTH (ptr_eq_trace v31
            (call_env v30 v32 (push_env envs handler (dec_clock s)))) ≤ n + 1 ∧
          bres ≠ SOME Error ∨
          LENGTH (ptr_eq_trace v31
            (call_env v30 v32 (push_env envs handler (dec_clock s)) with
             compile_oracle := co')) ≤ n + 1 ∧ bres2 ≠ SOME Error`
        >- (
          qpat_x_assum`_ ∨ _ ⇒ _`mp_tac>>
          impl_tac >- first_assum ACCEPT_TAC>>
          strip_tac>>
          qspecl_then[`args`,`s`,`xs`,`dest`,
            `x0`,`x1`,`x2`,`x3`,`x4`,`x5`,`v30`,`v31`,`v32`,`envs`,`handler`,`bres`,
            `bst`] mp_tac ptr_eq_trace_Call_ret>>
          impl_tac
          >- (rpt conj_tac>>first_assum ACCEPT_TAC)>>
          qspecl_then[`args`,`s with compile_oracle := co'`,`xs`,`dest`,
            `x0`,`x1`,`x2`,`x3`,`x4`,`x5`,`v30`,`v31`,`v32`,`envs`,`handler`,`bres`,
            `bst with compile_oracle :=
               shift_seq (LENGTH (ptr_eq_trace v31
                 (call_env v30 v32 (push_env envs handler (dec_clock s)))) − 1) co'`]
            mp_tac ptr_eq_trace_Call_ret>>
          impl_tac
          >- (qpat_assum`call_env _ _ _ = _`(fn th =>
                qpat_assum`bres2 = _`(fn e1 =>
                  qpat_assum`bst2 = _`(fn e2 =>
                    SIMP_TAC (srw_ss()) [th, GSYM e1, GSYM e2])))>>
              rpt conj_tac>>first_assum ACCEPT_TAC)>>
          strip_tac>>strip_tac>>
          Cases_on`bres`
          >- (
            rpt (qpat_x_assum`∀a. _`kall_tac)>>gvs[]) >>
          rename1`evaluate (v31,call_env v30 v32 (push_env envs handler (dec_clock s)))
                    = (SOME bx,bst)`>>
          Cases_on`bx`
          >- (
            Cases_on`w ≠ Loc x4 x5 ∨ LENGTH l ≠ LENGTH x0`
            >- (rpt (qpat_x_assum`∀a. _`kall_tac)>>gvs[]) >>
            Cases_on`pop_env bst`
            >- (rpt (qpat_x_assum`∀a. _`kall_tac)>>gvs[]) >>
            rename1`pop_env bst = SOME ps`>>
            Cases_on`domain ps.locals = domain (FST envs) ∪ domain (SND envs)`
            >- (
              qpat_assum`ptr_eq_trace v31 (_ with compile_oracle := _) = _`(fn th =>
                qpat_x_assum`_ ∨ _`(assume_tac o PURE_REWRITE_RULE[th]))>>
              Cases_on`LENGTH (ptr_eq_trace v31
                (call_env v30 v32 (push_env envs handler (dec_clock s)))) ≤ n + 1`
              >- (
                qpat_assum`∀xs' v3 args1 v10 prog ss v1 n v6 names v9 ret_handler v11 l1
                    l2 envs. _`
                  (qspecl_then[`xs`,`(v30,v31,v32)`,`v30`,`(v31,v32)`,`v31`,`v32`,
                    `(x0,(x1,x2),x3,x4,x5)`,`x0`,`((x1,x2),x3,x4,x5)`,`(x1,x2)`,
                    `(x3,x4,x5)`,`x3`,`(x4,x5)`,`x4`,`x5`,`envs`]mp_tac)>>
                impl_tac
                >- (SIMP_TAC (srw_ss()) []>>rpt conj_tac>>first_assum ACCEPT_TAC)>>
                disch_then(qspecl_then[`SOME (Result w l)`,`bst`,
                  `(call_env v30 v32 (push_env envs handler (dec_clock s))).compile_oracle`,
                  `n`,`SOME (Result w l)`,`bst`]mp_tac)>>
                PURE_REWRITE_TAC[with_same_compile_oracle]>>
                impl_tac
                >- (qpat_assum`(call_env _ _ _).ptr_eq_oracle = _`
                      (fn th => REWRITE_TAC[th])>>
                    rpt conj_tac>>first_assum ACCEPT_TAC)>>
                strip_tac>>
                qpat_x_assum`_ ∨ _ ⇒ _`mp_tac>>
                impl_tac
                >- (disj1_tac>>conj_tac
                    >- first_assum ACCEPT_TAC
                    >- SIMP_TAC (srw_ss()) [])>>
                strip_tac>>
                `bst.compile_oracle =
                   shift_seq (LENGTH (ptr_eq_trace v31
                     (call_env v30 v32 (push_env envs handler (dec_clock s)))) − 1)
                     s.compile_oracle` by
                  (qpat_x_assum`bst = bst with compile_oracle := _`mp_tac>>
                   qpat_assum`(call_env _ _ _).compile_oracle = _`
                     (fn th => REWRITE_TAC[th])>>
                   SIMP_TAC (srw_ss()) [state_component_equality])>>
                qpat_x_assum`¬(w ≠ _ ∨ _)`(strip_assume_tac o SIMP_RULE (srw_ss()) [])>>
                qpat_assum`pop_env bst = _`(fn pe =>
                  qpat_assum`domain ps.locals = _`(fn dm =>
                    qpat_assum`w = Loc _ _`(fn wq =>
                     qpat_assum`LENGTH l = _`(fn wf =>
                      qpat_x_assum`_ = (r,s')`
                        (assume_tac o SIMP_RULE (srw_ss()) [pe,dm,wq,wf])))))>>
                qpat_assum`pop_env bst = _`(fn pe =>
                  qpat_assum`domain ps.locals = _`(fn dm =>
                    qpat_assum`w = Loc _ _`(fn wq =>
                     qpat_assum`LENGTH l = _`(fn wf =>
                      qpat_assum`bres2 = _`(fn b2 =>
                        qpat_assum`bst2 = _`(fn t2 =>
                          qpat_x_assum`_ = (r2,s2)`
                            (assume_tac o
                               SIMP_RULE (srw_ss()) [b2,t2,pe,dm,wq,wf])))))))>>
                imp_res_tac pop_env_const>>
                sg`ps.compile_oracle =
                     shift_seq (LENGTH (ptr_eq_trace v31
                       (call_env v30 v32 (push_env envs handler (dec_clock s)))) − 1)
                       s.compile_oracle ∧ ps.ptr_eq_oracle = NONE`
                >- (rpt (qpat_x_assum`∀a. _`kall_tac)>>
                    imp_res_tac evaluate_consts>>
                    gvs[])>>
                qpat_x_assum`∀xs' v3 args1 v10 prog ss v1 n v6 names v9 ret_handler v11 l1
                    l2 envs v5 s2 v8 x ys s1. _`
                  (qspecl_then[`xs`,`(v30,v31,v32)`,`v30`,`(v31,v32)`,`v31`,`v32`,
                    `(x0,(x1,x2),x3,x4,x5)`,`x0`,`((x1,x2),x3,x4,x5)`,`(x1,x2)`,
                    `(x3,x4,x5)`,`x3`,`(x4,x5)`,`x4`,`x5`,`envs`,
                    `SOME (Result w l)`,`bst`,`Result w l`,`w`,`l`,`ps`]mp_tac)>>
                impl_tac
                >- (SIMP_TAC (srw_ss()) []>>rpt conj_tac>>first_assum ACCEPT_TAC)>>
                rpt (qpat_x_assum`∀a b c d e f. _`kall_tac)>>
                disch_then(qspecl_then[`r`,`s'`,
                  `shift_seq (LENGTH (ptr_eq_trace v31
                     (call_env v30 v32 (push_env envs handler (dec_clock s)))) − 1) co'`,
                  `n + 1 - LENGTH (ptr_eq_trace v31
                     (call_env v30 v32 (push_env envs handler (dec_clock s))))`,
                  `r2`,`s2`]mp_tac)>>
                impl_tac
                >- (
                  rpt conj_tac
                  >- first_assum ACCEPT_TAC
                  >- first_assum ACCEPT_TAC
                  >- simp[]
                  >- (rw[shift_seq_def]>>
                      qpat_x_assum`∀j. j < n ⇒ _`irule>>
                      qspecl_then[`v31`,
                        `call_env v30 v32 (push_env envs handler (dec_clock s))`]
                        assume_tac ptr_eq_trace_LENGTH_NOT_0>>
                      simp[])
                  >- (simp[shift_seq_def]>>
                      qspecl_then[`v31`,
                        `call_env v30 v32 (push_env envs handler (dec_clock s))`]
                        assume_tac ptr_eq_trace_LENGTH_NOT_0>>
                      `n + 1 −
                       LENGTH (ptr_eq_trace v31
                         (call_env v30 v32 (push_env envs handler (dec_clock s)))) +
                       (LENGTH (ptr_eq_trace v31
                         (call_env v30 v32
                            (push_env envs handler (dec_clock s)))) − 1) = n` by simp[]>>
                      simp[]))>>
                strip_tac>>
                qpat_assum`pop_env bst = _`(fn pe =>
                  qpat_assum`domain ps.locals = _`(fn dm =>
                    qpat_assum`w = Loc _ _`(fn wq =>
                      qpat_assum`LENGTH l = _`(fn wf =>
                        qpat_x_assum`ptr_eq_trace (Call _ _ _ _) s = _`
                          (assume_tac o SIMP_RULE (srw_ss()) [pe,dm,wq,wf])))))>>
                qpat_assum`pop_env bst = _`(fn pe =>
                  qpat_assum`domain ps.locals = _`(fn dm =>
                    qpat_assum`w = Loc _ _`(fn wq =>
                      qpat_assum`LENGTH l = _`(fn wf =>
                        qpat_assum`call_env _ _ _ = _`(fn ce =>
                          qpat_x_assum`ptr_eq_trace (Call _ _ _ _)
                                         (_ with compile_oracle := _) = _`
                            (assume_tac o SIMP_RULE (srw_ss()) [pe,dm,wq,wf,ce]))))))>>
                qpat_assum`ptr_eq_trace v31 (_ with compile_oracle := _) = _`(fn th =>
                  qpat_x_assum`ptr_eq_trace (Call _ _ _ _) (_ with compile_oracle := _) = _`
                    (assume_tac o PURE_REWRITE_RULE[th]))>>
                gvs[]>>
                simp[TAKE_epoch_append_short,shift_seq_shift_seq]>>
                qspecl_then[`v31`,`call_env v30 v32 (push_env envs handler (dec_clock s))`]
                  assume_tac ptr_eq_trace_LENGTH_NOT_0>>
                qspecl_then[`x3`,`set_vars x0 l ps`]assume_tac ptr_eq_trace_LENGTH_NOT_0>>
                strip_tac>>
                qpat_x_assum`_ ∨ _ ⇒ _`mp_tac>>
                impl_tac>>gvs[]>>
                strip_tac>>gvs[]>>
                gvs[shift_seq_shift_seq]>>
                qspecl_then[`v31`,`call_env v30 v32 (push_env envs handler (dec_clock s))`]
                  assume_tac ptr_eq_trace_LENGTH_NOT_0>>
                qspecl_then[`x3`,`set_vars x0 l ps`]assume_tac ptr_eq_trace_LENGTH_NOT_0>>
                simp[])>>
              rpt (qpat_x_assum`∀a. _`kall_tac)>>gvs[])
            >- (rpt (qpat_x_assum`∀a. _`kall_tac)>>gvs[]))
          >- (
            Cases_on`handler`
            >- (rpt (qpat_x_assum`∀a. _`kall_tac)>>gvs[]) >>
            rename1`push_env envs (SOME hnd) _`>>PairCases_on`hnd`>>
            Cases_on`w ≠ Loc hnd2 hnd3`
            >- (rpt (qpat_x_assum`∀a. _`kall_tac)>>gvs[]) >>
            Cases_on`domain bst.locals = domain (FST envs) ∪ domain (SND envs)`
            >- (
              qpat_assum`ptr_eq_trace v31 (_ with compile_oracle := _) = _`(fn th =>
                qpat_x_assum`_ ∨ _`(assume_tac o PURE_REWRITE_RULE[th]))>>
              Cases_on`LENGTH (ptr_eq_trace v31
                (call_env v30 v32
                  (push_env envs (SOME (hnd0,hnd1,hnd2,hnd3)) (dec_clock s)))) ≤ n + 1`
              >- (
                qpat_assum`∀xs' v3 args1 v10 prog ss v1 n v6 names v9 ret_handler v11 l1
                    l2 envs. _`
                  (qspecl_then[`xs`,`(v30,v31,v32)`,`v30`,`(v31,v32)`,`v31`,`v32`,
                    `(x0,(x1,x2),x3,x4,x5)`,`x0`,`((x1,x2),x3,x4,x5)`,`(x1,x2)`,
                    `(x3,x4,x5)`,`x3`,`(x4,x5)`,`x4`,`x5`,`envs`]mp_tac)>>
                impl_tac
                >- (SIMP_TAC (srw_ss()) []>>rpt conj_tac>>first_assum ACCEPT_TAC)>>
                disch_then(qspecl_then[`SOME (Exception w w0)`,`bst`,
                  `(call_env v30 v32
                     (push_env envs (SOME (hnd0,hnd1,hnd2,hnd3))
                        (dec_clock s))).compile_oracle`,
                  `n`,`SOME (Exception w w0)`,`bst`]mp_tac)>>
                PURE_REWRITE_TAC[with_same_compile_oracle]>>
                impl_tac
                >- (qpat_assum`(call_env _ _ _).ptr_eq_oracle = _`
                      (fn th => REWRITE_TAC[th])>>
                    rpt conj_tac>>first_assum ACCEPT_TAC)>>
                strip_tac>>
                qpat_x_assum`_ ∨ _ ⇒ _`mp_tac>>
                impl_tac
                >- (disj1_tac>>conj_tac
                    >- first_assum ACCEPT_TAC
                    >- SIMP_TAC (srw_ss()) [])>>
                strip_tac>>
                `bst.compile_oracle =
                   shift_seq (LENGTH (ptr_eq_trace v31
                     (call_env v30 v32
                       (push_env envs (SOME (hnd0,hnd1,hnd2,hnd3)) (dec_clock s)))) − 1)
                     s.compile_oracle` by
                  (qpat_x_assum`bst = bst with compile_oracle := _`mp_tac>>
                   qpat_assum`(call_env _ _ _).compile_oracle = _`
                     (fn th => REWRITE_TAC[th])>>
                   SIMP_TAC (srw_ss()) [state_component_equality])>>
                qpat_x_assum`¬(w ≠ Loc _ _)`(strip_assume_tac o SIMP_RULE (srw_ss()) [])>>
                qpat_assum`domain bst.locals = _`(fn dm =>
                  qpat_assum`w = Loc _ _`(fn wq =>
                    qpat_x_assum`_ = (r,s')`
                      (assume_tac o SIMP_RULE (srw_ss()) [dm,wq])))>>
                qpat_assum`domain bst.locals = _`(fn dm =>
                  qpat_assum`w = Loc _ _`(fn wq =>
                    qpat_assum`bres2 = _`(fn b2 =>
                      qpat_assum`bst2 = _`(fn t2 =>
                        qpat_x_assum`_ = (r2,s2)`
                          (assume_tac o SIMP_RULE (srw_ss()) [b2,t2,dm,wq])))))>>
                imp_res_tac evaluate_consts>>
                qpat_x_assum`∀xs' v3 args1 v10 prog ss v1 n v6 names v9 ret_handler v11 l1
                    l2 envs v5 s2 v8 x' y v n' v2 h v4 l1' l2'. _`
                  (qspecl_then[`xs`,`(v30,v31,v32)`,`v30`,`(v31,v32)`,`v31`,`v32`,
                    `(x0,(x1,x2),x3,x4,x5)`,`x0`,`((x1,x2),x3,x4,x5)`,`(x1,x2)`,
                    `(x3,x4,x5)`,`x3`,`(x4,x5)`,`x4`,`x5`,`envs`,
                    `SOME (Exception w w0)`,`bst`,`Exception w w0`,`w`,`w0`,
                    `(hnd0,hnd1,hnd2,hnd3)`,`hnd0`,`(hnd1,hnd2,hnd3)`,`hnd1`,
                    `(hnd2,hnd3)`,`hnd2`,`hnd3`]mp_tac)>>
                impl_tac
                >- (SIMP_TAC (srw_ss()) []>>rpt conj_tac>>first_assum ACCEPT_TAC)>>
                rpt (qpat_x_assum`∀a b c d e f. _`kall_tac)>>
                disch_then(qspecl_then[`r`,`s'`,
                  `shift_seq (LENGTH (ptr_eq_trace v31
                     (call_env v30 v32
                       (push_env envs (SOME (hnd0,hnd1,hnd2,hnd3))
                          (dec_clock s)))) − 1) co'`,
                  `n + 1 - LENGTH (ptr_eq_trace v31
                     (call_env v30 v32
                       (push_env envs (SOME (hnd0,hnd1,hnd2,hnd3)) (dec_clock s))))`,
                  `r2`,`s2`]mp_tac)>>
                impl_tac
                >- (
                  rpt conj_tac
                  >- first_assum ACCEPT_TAC
                  >- first_assum ACCEPT_TAC
                  >- simp[]
                  >- (rw[shift_seq_def]>>
                      qpat_x_assum`∀j. j < n ⇒ _`irule>>
                      qspecl_then[`v31`,`call_env v30 v32
                        (push_env envs (SOME (hnd0,hnd1,hnd2,hnd3)) (dec_clock s))`]
                        assume_tac ptr_eq_trace_LENGTH_NOT_0>>
                      simp[])
                  >- (simp[shift_seq_def]>>
                      qspecl_then[`v31`,`call_env v30 v32
                        (push_env envs (SOME (hnd0,hnd1,hnd2,hnd3)) (dec_clock s))`]
                        assume_tac ptr_eq_trace_LENGTH_NOT_0>>
                      `n + 1 −
                       LENGTH (ptr_eq_trace v31
                         (call_env v30 v32
                           (push_env envs (SOME (hnd0,hnd1,hnd2,hnd3)) (dec_clock s)))) +
                       (LENGTH (ptr_eq_trace v31
                         (call_env v30 v32
                           (push_env envs (SOME (hnd0,hnd1,hnd2,hnd3))
                              (dec_clock s)))) − 1) = n` by simp[]>>
                      simp[]))>>
                strip_tac>>
                qpat_assum`domain bst.locals = _`(fn dm =>
                  qpat_assum`w = Loc _ _`(fn wq =>
                    qpat_x_assum`ptr_eq_trace (Call _ _ _ _) s = _`
                      (assume_tac o SIMP_RULE (srw_ss()) [dm,wq])))>>
                qpat_assum`domain bst.locals = _`(fn dm =>
                  qpat_assum`w = Loc _ _`(fn wq =>
                    qpat_assum`call_env _ _ _ = _`(fn ce =>
                      qpat_x_assum`ptr_eq_trace (Call _ _ _ _)
                                     (_ with compile_oracle := _) = _`
                        (assume_tac o SIMP_RULE (srw_ss()) [dm,wq,ce]))))>>
                qpat_assum`ptr_eq_trace v31 (_ with compile_oracle := _) = _`(fn th =>
                  qpat_x_assum`ptr_eq_trace (Call _ _ _ _) (_ with compile_oracle := _) = _`
                    (assume_tac o PURE_REWRITE_RULE[th]))>>
                gvs[]>>
                simp[TAKE_epoch_append_short,shift_seq_shift_seq]>>
                strip_tac>>
                qpat_x_assum`_ ∨ _ ⇒ _`mp_tac>>
                impl_tac>>gvs[]>>
                strip_tac>>gvs[]>>
                gvs[shift_seq_shift_seq]>>
                qspecl_then[`v31`,`call_env v30 v32
                  (push_env envs (SOME (hnd0,hnd1,hnd2,hnd3)) (dec_clock s))`]
                  assume_tac ptr_eq_trace_LENGTH_NOT_0>>
                qspecl_then[`hnd1`,`set_var hnd0 w0 bst`]
                  assume_tac ptr_eq_trace_LENGTH_NOT_0>>
                simp[])>>
              rpt (qpat_x_assum`∀a. _`kall_tac)>>gvs[])
            >- (rpt (qpat_x_assum`∀a. _`kall_tac)>>gvs[]))
          >> rpt (qpat_x_assum`∀a. _`kall_tac)>>gvs[])
        >- (
          qspecl_then[`args`,`s`,`xs`,`dest`,`x0`,`x1`,`x2`,`x3`,`x4`,`x5`,
            `v30`,`v31`,`v32`,`envs`,`handler`,`bres`,`bst`]
            mp_tac ptr_eq_trace_Call_ret_bound>>
          impl_tac
          >- (rpt conj_tac>>first_assum ACCEPT_TAC)>>
          strip_tac>>
          qspecl_then[`args`,`s with compile_oracle := co'`,`xs`,`dest`,
            `x0`,`x1`,`x2`,`x3`,`x4`,`x5`,`v30`,`v31`,`v32`,`envs`,`handler`,
            `bres2`,`bst2`]
            mp_tac ptr_eq_trace_Call_ret_bound>>
          impl_tac
          >- (qpat_assum`call_env _ _ _ = _`(fn th => SIMP_TAC (srw_ss()) [th])>>
              rpt conj_tac>>first_assum ACCEPT_TAC)>>
          strip_tac>>
          qpat_assum`call_env _ _ _ = _`
            (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE[th]))>>
          qpat_x_assum`∀m. ¬(_ ∧ bres ≠ _) ⇒ _`(qspec_then`n`mp_tac)>>
          qpat_x_assum`∀m. ¬(_ ∧ bres2 ≠ _) ⇒ _`(qspec_then`n`mp_tac)>>
          rpt (qpat_x_assum`∀a. _`kall_tac)>>
          gvs[]))))
QED

Finalise evaluate_compile_oracle_prefix;

(* A family of answer lists that nest as the clock grows has one oracle above
   all of them. *)
Theorem oracle_of_limit_exists:
  ∀bs:num -> bool list.
    (∀k k'. k ≤ k' ⇒ bs k ≼ bs k') ⇒
    ∃po. ∀k i. i < LENGTH (bs k) ⇒ EL i (bs k) = po i
Proof
  rpt strip_tac>>
  qexists_tac`λi. if ∃k. i < LENGTH (bs k)
                  then EL i (bs (@k. i < LENGTH (bs k))) else F`>>
  rw[]
  >- (
    qabbrev_tac`k0 = @k. i < LENGTH (bs k)`>>
    `i < LENGTH (bs k0)` by
      (qunabbrev_tac`k0`>>SELECT_ELIM_TAC>>metis_tac[])>>
    `k ≤ k0 ∨ k0 ≤ k` by decide_tac>>
    metis_tac[rich_listTheory.is_prefix_el])>>
  metis_tac[]
QED

(* The answers of epoch i, as a limit over clocks, of the concrete run. *)
Definition epoch_limit_def:
  epoch_limit t start i =
    @a. ∀k. epoch_prefix
              (ptr_eq_trace (Call NONE (SOME start) [0] NONE) (t with clock := k))
              i a
End

(* Each epoch of the trace grows with the clock, so it has a limit, and
   epoch_limit is one. *)

Theorem ptr_eq_trace_prefix_EL:
  ∀t1 t2 i.
    ptr_eq_trace_prefix t1 t2 ∧ i < LENGTH t1 ⇒ i < LENGTH t2 ∧ EL i t1 ≼ EL i t2
Proof
  rw [ptr_eq_trace_prefix_def] >>
  Cases_on `i + 1 < LENGTH t1`
  >- (qpat_x_assum `∀e. _` (qspec_then `i` mp_tac) >> simp []) >>
  `i = LENGTH t1 - 1 ∧ t1 ≠ []` by (Cases_on `t1` >> gvs []) >>
  gvs [LAST_EL, PRE_SUB1]
QED

Theorem epoch_limit_exists[local]:
  ∀t start i.
    ∃a. ∀k. epoch_prefix
              (ptr_eq_trace (Call NONE (SOME start) [0] NONE)
                 (t with clock := k)) i a
Proof
  rpt strip_tac >>
  qspec_then
    `λk. if i < LENGTH (ptr_eq_trace (Call NONE (SOME start) [0] NONE)
                          (t with clock := k))
         then EL i (ptr_eq_trace (Call NONE (SOME start) [0] NONE)
                      (t with clock := k))
         else []` mp_tac oracle_of_limit_exists >>
  impl_tac >- (
    rw [] >>
    Cases_on`evaluate (Call NONE (SOME start) [0] NONE, t with clock := k)` >>
    drule ptr_eq_trace_mono >>
    disch_then(qspec_then`k' - k`mp_tac) >>
    `k + (k' - k) = k'` by simp [] >>
    strip_tac >> gvs [] >>
    metis_tac [ptr_eq_trace_prefix_EL]) >>
  strip_tac >> qexists_tac`po` >>
  rw [epoch_prefix_def] >>
  first_x_assum(qspecl_then[`k`,`k'`]mp_tac) >> simp []
QED

Theorem epoch_limit_spec:
  ∀t start i k.
    epoch_prefix
      (ptr_eq_trace (Call NONE (SOME start) [0] NONE) (t with clock := k))
      i (epoch_limit t start i)
Proof
  rw [epoch_limit_def] >>
  SELECT_ELIM_TAC >> rw [] >>
  metis_tac [epoch_limit_exists]
QED

Definition ptr_eq_pad_def:
  ptr_eq_pad es = (λi. if i < LENGTH es then EL i es else K F)
End

(* The epochs of the fixed point, built one at a time: the answers of epoch i
   are read off the concrete run whose compile oracle is fixed by the epochs
   already built. *)
Definition ptr_eq_epochs_def:
  ptr_eq_epochs Syn wst start 0 = [] ∧
  ptr_eq_epochs Syn wst start (SUC i) =
    (let es = ptr_eq_epochs Syn wst start i in
       es ++ [epoch_limit (wst (Syn (ptr_eq_pad es))) start i])
End

Definition ptr_eq_fix_def:
  ptr_eq_fix Syn wst start = (λi. EL i (ptr_eq_epochs Syn wst start (SUC i)))
End

(* The epochs already built never change as more are added, so padding out the
   first i of them agrees with the fixed point below i. *)

Theorem ptr_eq_epochs_LENGTH[local,simp]:
  ∀i Syn wst start. LENGTH (ptr_eq_epochs Syn wst start i) = i
Proof
  Induct >> rw [ptr_eq_epochs_def]
QED

Theorem ptr_eq_epochs_SUC_prefix[local]:
  ptr_eq_epochs Syn wst start i ≼ ptr_eq_epochs Syn wst start (SUC i)
Proof
  rw [ptr_eq_epochs_def]
QED

Theorem ptr_eq_epochs_prefix:
  ∀j i Syn wst start.
    i ≤ j ⇒ ptr_eq_epochs Syn wst start i ≼ ptr_eq_epochs Syn wst start j
Proof
  Induct >> rw [] >>
  Cases_on `i = SUC j` >> gvs [] >>
  `i ≤ j` by simp [] >>
  metis_tac [ptr_eq_epochs_SUC_prefix, rich_listTheory.IS_PREFIX_TRANS]
QED

Theorem ptr_eq_pad_prefix:
  ∀i j Syn wst start.
    j < i ⇒
    ptr_eq_pad (ptr_eq_epochs Syn wst start i) j = ptr_eq_fix Syn wst start j
Proof
  rw [ptr_eq_pad_def, ptr_eq_fix_def] >>
  irule (GSYM rich_listTheory.is_prefix_el) >>
  simp [ptr_eq_epochs_prefix]
QED

(* Two traces that agree on their first e+1 epochs agree on epoch e. *)
Theorem epoch_prefix_TAKE[local]:
  ∀tr1 tr2 e a.
    TAKE (e+1) tr1 = TAKE (e+1) tr2 ∧ epoch_prefix tr2 e a ⇒
    epoch_prefix tr1 e a
Proof
  rw [epoch_prefix_def] >>
  `EL e tr1 = EL e tr2` by
    (`EL e (TAKE (e+1) tr1) = EL e (TAKE (e+1) tr2)` by
       (qpat_assum `TAKE _ _ = TAKE _ _` (fn th => REWRITE_TAC [th])) >>
     gvs [EL_TAKE]) >>
  `e < LENGTH tr2` by
    (`LENGTH (TAKE (e+1) tr1) = LENGTH (TAKE (e+1) tr2)` by
       (qpat_assum `TAKE _ _ = TAKE _ _` (fn th => REWRITE_TAC [th])) >>
     pop_assum mp_tac >> simp [LENGTH_TAKE_EQ] >> rw []) >>
  gvs []
QED

Theorem ptr_eq_fix_thm:
  (∀po po' i. (∀j. j ≤ i ⇒ po j = po' j) ⇒ Syn po i = Syn po' i) ∧
  (∀syn. wst syn = t0 with compile_oracle := mkco syn) ∧
  t0.ptr_eq_oracle = NONE ∧ (∀m dm st w. t0.ptr_eq_rel m dm st w w) ∧
  (∀syn syn' i. (∀j. j ≤ i ⇒ syn j = syn' j) ⇒ mkco syn i = mkco syn' i) ∧
  (∀syn syn' i. (∀j. j < i ⇒ syn j = syn' j) ⇒ FST (mkco syn i) = FST (mkco syn' i)) ⇒
  ∀k. ∃rest.
    evaluate (Call NONE (SOME start) [0] NONE,
              wst (Syn (ptr_eq_fix Syn wst start)) with
                <|clock := k;
                  ptr_eq_oracle := SOME (ptr_eq_fix Syn wst start)|>) =
    (I ## (λt. t with ptr_eq_oracle := SOME rest))
      (evaluate (Call NONE (SOME start) [0] NONE,
                 wst (Syn (ptr_eq_fix Syn wst start)) with clock := k))
Proof
  rpt strip_tac>>
  Cases_on`evaluate (Call NONE (SOME start) [0] NONE,
                     wst (Syn (ptr_eq_fix Syn wst start)) with clock := k)`>>
  qspecl_then[`Call NONE (SOME start) [0] NONE`,
    `wst (Syn (ptr_eq_fix Syn wst start)) with clock := k`,`q`,`r`]
    mp_tac ptr_eq_trace_agrees>>
  impl_tac
  >- gvs[]>>
  disch_then(qspec_then`ptr_eq_fix Syn wst start`mp_tac)>>
  impl_tac
  >- (
    rw[trace_agrees_def]>>
    `∀m. m < e ⇒
       Syn (ptr_eq_fix Syn wst start) m =
       Syn (ptr_eq_pad (ptr_eq_epochs Syn wst start e)) m` by
      (rw[]>>
       qpat_assum`∀po po' i. _ ⇒ Syn _ _ = _`irule>>
       rw[]>>irule (GSYM ptr_eq_pad_prefix)>>simp[])>>
    `∀j. j < e ⇒
       mkco (Syn (ptr_eq_fix Syn wst start)) j =
       mkco (Syn (ptr_eq_pad (ptr_eq_epochs Syn wst start e))) j` by
      (rw[]>>
       qpat_assum`∀syn syn' i. _ ⇒ mkco _ _ = _`irule>>
       rw[]>>first_x_assum irule>>simp[])>>
    `FST (mkco (Syn (ptr_eq_fix Syn wst start)) e) =
     FST (mkco (Syn (ptr_eq_pad (ptr_eq_epochs Syn wst start e))) e)` by
      (qpat_assum`∀syn syn' i. _ ⇒ FST (mkco _ _) = _`irule>>
       rw[]>>first_x_assum irule>>simp[])>>
    `ptr_eq_fix Syn wst start e =
       epoch_limit (wst (Syn (ptr_eq_pad (ptr_eq_epochs Syn wst start e)))) start e` by
      simp[ptr_eq_fix_def,ptr_eq_epochs_def,rich_listTheory.EL_APPEND2]>>
    qspecl_then[`ptr_eq_trace (Call NONE (SOME start) [0] NONE)
       (t0 with <|compile_oracle := mkco (Syn (ptr_eq_fix Syn wst start));
                  clock := k|>)`,
      `ptr_eq_trace (Call NONE (SOME start) [0] NONE)
       (t0 with <|compile_oracle :=
                    mkco (Syn (ptr_eq_pad (ptr_eq_epochs Syn wst start e)));
                  clock := k|>)`,`e`,`ptr_eq_fix Syn wst start e`]
      mp_tac epoch_prefix_TAKE>>
    impl_tac
    >- (
      conj_tac
      >- (
        qspecl_then[`Call NONE (SOME start) [0] NONE`,
          `t0 with <|compile_oracle := mkco (Syn (ptr_eq_fix Syn wst start));
                     clock := k|>`,`q`,`r`,
          `mkco (Syn (ptr_eq_pad (ptr_eq_epochs Syn wst start e)))`,`e`,
          `FST (evaluate (Call NONE (SOME start) [0] NONE,
             t0 with <|compile_oracle :=
                         mkco (Syn (ptr_eq_pad (ptr_eq_epochs Syn wst start e)));
                       clock := k|>))`,
          `SND (evaluate (Call NONE (SOME start) [0] NONE,
             t0 with <|compile_oracle :=
                         mkco (Syn (ptr_eq_pad (ptr_eq_epochs Syn wst start e)));
                       clock := k|>))`]
          mp_tac evaluate_compile_oracle_prefix>>
        impl_tac
        >- (gvs[]>>rpt conj_tac>>simp[])>>
        strip_tac>>gvs[])>>
      qpat_assum`ptr_eq_fix Syn wst start e = _`
        (fn th => PURE_REWRITE_TAC[th])>>
      qspecl_then[`wst (Syn (ptr_eq_pad (ptr_eq_epochs Syn wst start e)))`,`start`,
        `e`,`k`] mp_tac epoch_limit_spec>>
      simp[])>>
    strip_tac>>first_assum ACCEPT_TAC)>>
  strip_tac>>
  gvs[]>>
  metis_tac[]
QED

(* semantics reads only the result and the ffi state, so an oracle that
   reproduces the concrete run at every clock leaves semantics alone. *)
Theorem semantics_ptr_eq_oracle:
  ∀s start po.
    (∀k. ∃rest.
       evaluate (Call NONE (SOME start) [0] NONE,
                 s with <|clock := k; ptr_eq_oracle := SOME po|>) =
       (I ## (λt. t with ptr_eq_oracle := SOME rest))
         (evaluate (Call NONE (SOME start) [0] NONE, s with clock := k))) ⇒
    semantics (s with ptr_eq_oracle := SOME po) start = semantics s start
Proof
  rw[]>>
  fs[SKOLEM_THM]>>
  simp[semantics_def,pairTheory.PAIR_MAP,
       quantHeuristicsTheory.PAIR_EQ_EXPAND]
QED

(* Discharging the oracle for the top-level call at every clock at once: for a
   state with no oracle and a reflexive attenuator, one oracle reproduces the
   concrete run at every clock.  This is the fixed point at a compile oracle
   that does not depend on the answers. *)
Theorem evaluate_ptr_eq_oracle_exists:
  ∀s start.
    s.ptr_eq_oracle = NONE ∧ (∀m dm st w. s.ptr_eq_rel m dm st w w) ⇒
    ∃po. ∀k. ∃rest.
      evaluate (Call NONE (SOME start) [0] NONE,
                s with <|clock := k; ptr_eq_oracle := SOME po|>) =
      (I ## (λt. t with ptr_eq_oracle := SOME rest))
        (evaluate (Call NONE (SOME start) [0] NONE, s with clock := k))
Proof
  rpt strip_tac>>
  qexists_tac`epoch_limit s start`>>
  rw[]>>
  Cases_on`evaluate (Call NONE (SOME start) [0] NONE, s with clock := k)`>>
  drule ptr_eq_trace_agrees>>
  disch_then(qspec_then`epoch_limit s start`mp_tac)>>
  impl_tac >- simp[trace_agrees_def,epoch_limit_spec]>>
  strip_tac>>
  qexists_tac`rest`>>
  gvs[]
QED

(* Discharging the oracle at the level of whole-program semantics. *)
Theorem ptr_eq_semantics:
  ∀s start.
    s.ptr_eq_oracle = NONE ∧ (∀m dm st w. s.ptr_eq_rel m dm st w w) ⇒
    ∃po. semantics (s with ptr_eq_oracle := SOME po) start = semantics s start
Proof
  rpt strip_tac>>
  drule_all evaluate_ptr_eq_oracle_exists>>
  disch_then(qspec_then`start`strip_assume_tac)>>
  qexists_tac`po`>>
  irule semantics_ptr_eq_oracle>>
  simp[]
QED

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

(**)
Theorem stack_size_eq:
  (stack_size (StackFrame n _ _ NONE::stack) = OPTION_MAP2 $+ n (stack_size stack)) /\
  (stack_size (StackFrame n _ _ (SOME handler)::stack) =
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

(*--Stack Swap Lemma--*)

(*Stacks look the same to the GC except for the keys (e.g. recoloured and in order)*)
Definition s_frame_val_eq_def:
  (s_frame_val_eq (StackFrame n ls1 ls NONE) (StackFrame n' ls1' ls' NONE) ⇔
     MAP SND ls = MAP SND ls' ∧ n = n') ∧
  (s_frame_val_eq (StackFrame n ls1 ls (SOME y)) (StackFrame n' ls1' ls' (SOME y')) ⇔
     MAP SND ls = MAP SND ls' ∧ y = y' ∧ n = n') ∧
  (s_frame_val_eq _ _ = F)
End

Theorem s_frame_val_eq_def2:
  (s_frame_val_eq (StackFrame n ls0 ls y) (StackFrame n' ls0' ls' y')
     ⇔ MAP SND ls = MAP SND ls' ∧ y = y' ∧ n = n')
Proof
  Cases_on `y` >> Cases_on `y'` >> fs[s_frame_val_eq_def]
QED

Definition s_val_eq_def:
  (s_val_eq [] [] = T) /\
  (s_val_eq (x::xs) (y::ys) = (s_val_eq xs ys /\
                                    s_frame_val_eq x y)) /\
  (s_val_eq _ _ = F)
End

(*Stacks look the same except for the values of the GC-ed cutsets (e.g. result of gc)*)
Definition s_frame_key_eq_def:
  (s_frame_key_eq (StackFrame n ls0 ls NONE) (StackFrame n' ls0' ls' NONE)
     <=> MAP FST ls = MAP FST ls' /\ ls0 = ls0' /\  n=n') /\
  (s_frame_key_eq (StackFrame n ls0 ls (SOME y)) (StackFrame n' ls0' ls' (SOME y'))
     <=> MAP FST ls = MAP FST ls' /\ y=y' /\ ls0 = ls0' /\ n=n') /\
  (s_frame_key_eq _ _ = F)
End

Theorem s_frame_key_eq_def2:
  (s_frame_key_eq (StackFrame n ls0 ls y) (StackFrame n' ls0' ls' y')
     <=> MAP FST ls = MAP FST ls' /\ y=y' /\ ls0 = ls0' /\ n=n')
Proof
  Cases_on `y` >> Cases_on `y'` >> fs[s_frame_key_eq_def]
QED

Definition s_key_eq_def:
  (s_key_eq [] [] = T) /\
  (s_key_eq (x::xs) (y::ys) = (s_key_eq xs ys /\
                                    s_frame_key_eq x y)) /\
  (s_key_eq _ _ = F)
End

Theorem s_key_eq_def2:
  !l1 l2.
  s_key_eq l1 l2 = LIST_REL s_frame_key_eq l1 l2
Proof
  recInduct s_key_eq_ind >> simp[s_key_eq_def] >>
  rpt strip_tac >> irule CONJ_COMM
QED

Theorem s_val_eq_def2:
  !l1 l2.
  s_val_eq l1 l2 = LIST_REL s_frame_val_eq l1 l2
Proof
  recInduct s_val_eq_ind >> simp[s_val_eq_def] >>
  rpt strip_tac >> irule CONJ_COMM
QED

(*Reflexive*)
Theorem s_frame_key_eq_refl:
   !ls.s_frame_key_eq ls ls = T
Proof
  rw[oneline s_frame_key_eq_def] >>
  every_case_tac >> fs[]
QED

Theorem s_frame_val_eq_refl:
   !ls.s_frame_val_eq ls ls = T
Proof
  rw[oneline s_frame_val_eq_def] >>
  every_case_tac >> fs[]
QED

Theorem s_key_eq_refl:
   !ls .s_key_eq ls ls = T
Proof
   rw[s_key_eq_def2] >>
   irule EVERY2_refl >>
   simp[s_frame_key_eq_refl]
QED

Theorem s_val_eq_refl:
   !ls.s_val_eq ls ls = T
Proof
   rw[s_val_eq_def2] >>
   irule EVERY2_refl >>
   simp[s_frame_val_eq_refl]
QED

(*transitive*)
Theorem s_frame_key_eq_trans[local]:
  !a b c. s_frame_key_eq a b /\ s_frame_key_eq b c ==>
            s_frame_key_eq a c
Proof
  simp[oneline s_frame_key_eq_def] >>
  rpt strip_tac >> every_case_tac >>
  fs[]
QED

Theorem s_key_eq_trans:
   !a b c. s_key_eq a b /\ s_key_eq b c ==>
            s_key_eq a c
Proof
  simp[s_key_eq_def2] >>
  HO_MATCH_MP_TAC EVERY2_trans >>
  ACCEPT_TAC s_frame_key_eq_trans
QED

Theorem s_frame_val_eq_trans[local]:
  !a b c. s_frame_val_eq a b /\ s_frame_val_eq b c ==>
            s_frame_val_eq a c
Proof
  simp[oneline s_frame_val_eq_def] >>
  rpt strip_tac >> every_case_tac >>
  fs[]
QED

Theorem s_val_eq_trans:
  !a b c. s_val_eq a b /\ s_val_eq b c ==>
            s_val_eq a c
Proof
  simp[s_val_eq_def2] >>
  HO_MATCH_MP_TAC EVERY2_trans >>
  ACCEPT_TAC s_frame_val_eq_trans
QED


(*Symmetric*)
Theorem s_frame_key_eq_sym[local]:
  !a b. s_frame_key_eq a b <=> s_frame_key_eq b a
Proof
  simp[oneline s_frame_key_eq_def] >>
  rpt strip_tac >> every_case_tac >>
  simp[]  >> EQ_TAC >> simp[]
QED


Theorem s_key_eq_sym:
   !a b. s_key_eq a b <=> s_key_eq b a
Proof
  rpt strip_tac >>
  simp[s_key_eq_def2] >>
  EQ_TAC >> rename1  `LIST_REL s_frame_key_eq x y` >>
  qid_spec_tac `y` >> qid_spec_tac `x` >>
  HO_MATCH_MP_TAC EVERY2_sym >>
  rpt strip_tac >> simp[Once s_frame_key_eq_sym]
QED

Theorem s_frame_val_eq_sym[local]:
  !a b. s_frame_val_eq a b <=> s_frame_val_eq b a
Proof
  simp[oneline s_frame_val_eq_def] >>
  rpt strip_tac >> every_case_tac >>
  simp[]  >> EQ_TAC >> simp[]
QED

Theorem s_val_eq_sym:
   !a b. s_val_eq a b <=> s_val_eq b a
Proof
  rpt strip_tac >>
  simp[s_val_eq_def2] >>
  EQ_TAC >> rename1  `LIST_REL s_frame_val_eq x y` >>
  qid_spec_tac `y` >> qid_spec_tac `x` >>
  HO_MATCH_MP_TAC EVERY2_sym >>
  rpt strip_tac >> simp[Once s_frame_val_eq_sym]
QED

Theorem s_frame_val_and_key_eq[local]:
  !s t. s_frame_val_eq s t /\ s_frame_key_eq s t ==> s = t
Proof
  recInduct s_frame_val_eq_ind >>
  simp[s_frame_val_eq_def,s_frame_key_eq_def,LIST_EQ_MAP_PAIR]
QED

Theorem LIST_REL_CONJ2:
  LIST_REL (λa b. P a b ∧ Q a b) l1 l2 ⇔
  LIST_REL P l1 l2 ∧ LIST_REL Q l1 l2
Proof
 fs[LIST_REL_CONJ] >>
 `(λa b. P a b) = P` by simp[EQ_EXT] >>
 `(λa b. Q a b) = Q` by simp[EQ_EXT] >>
 simp[]
QED

Theorem s_val_and_key_eq:
   !s t. s_val_eq s t /\ s_key_eq s t ==> s = t
Proof
  simp[s_val_eq_def2,s_key_eq_def2] >>
  simp[GSYM LIST_REL_CONJ2] >>
  Induct >> fs[] >>
  rpt strip_tac >>
  simp[s_frame_val_and_key_eq]
QED

Theorem dec_stack_stack_key_eq[local]:
  !wl st st'. dec_stack wl st = SOME st' ==> s_key_eq st st'
Proof
  ho_match_mp_tac dec_stack_ind>>simp[dec_stack_def]>>
  rpt strip_tac >> fs[s_key_eq_def2]>>
  every_case_tac>>full_simp_tac(srw_ss())[]>>srw_tac[][]>>full_simp_tac(srw_ss())[dec_stack_def]>>srw_tac[][]>>
  Cases_on `handler`>>
  full_simp_tac(srw_ss())[s_key_eq_def,s_frame_key_eq_def,MAP_ZIP,NOT_LESS]
QED

(*gc preserves the stack_key relation*)
Theorem gc_s_key_eq:
   !s x. gc s = SOME x ==> s_key_eq s.stack x.stack
Proof
  srw_tac[][gc_def] >>full_simp_tac(srw_ss())[LET_THM]>>every_case_tac>>full_simp_tac(srw_ss())[]>>
  IMP_RES_TAC dec_stack_stack_key_eq>>
  full_simp_tac(srw_ss())[state_component_equality]>>rev_full_simp_tac(srw_ss())[]
QED

Theorem s_val_eq_enc_stack[local]:
  !st st'. s_val_eq st st' ==> enc_stack st = enc_stack st'
Proof
  Induct>>Cases_on`st'`>>full_simp_tac(srw_ss())[s_val_eq_def2]>>
  Cases_on`h`>>Cases_on`h'`>>
  full_simp_tac(srw_ss())[s_frame_val_eq_def2,enc_stack_def]
QED

Theorem s_val_eq_dec_stack[local]:
  !q st st' x. s_val_eq st st' /\ dec_stack q st = SOME x ==>
    ?y. dec_stack q st' = SOME y /\ s_val_eq x y
Proof
  ho_match_mp_tac dec_stack_ind >> srw_tac[][] >>
   Cases_on`st'`>>full_simp_tac(srw_ss())[s_val_eq_def,s_val_eq_refl]>>
   Cases_on`h`>>full_simp_tac(srw_ss())[dec_stack_def]>>
   pop_assum mp_tac>>CASE_TAC >>
   first_x_assum(qspecl_then [`t`,`x'`] assume_tac)>> rev_full_simp_tac(srw_ss())[]>>
   strip_tac>>pop_assum (SUBST1_TAC o SYM)>>
   full_simp_tac(srw_ss())[s_frame_val_eq_def,s_val_eq_def]>>
   `LENGTH l0' = LENGTH l` by
    (Cases_on `handler` \\ Cases_on `o'` \\ Cases_on `o0` \\ full_simp_tac(srw_ss())[s_frame_val_eq_def]
     \\ metis_tac[LENGTH_MAP]) \\ full_simp_tac(srw_ss())[NOT_LESS]
   \\ Cases_on `handler` \\ Cases_on `o'` \\ Cases_on `o0` \\ full_simp_tac(srw_ss())[s_frame_val_eq_def,s_val_eq_def]
   \\ full_simp_tac(srw_ss())[MAP_ZIP,LENGTH_TAKE]
QED

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
   ∀ x b s t. s_key_eq (push_env x b s).stack t.stack ⇒
       ∃n l ls opt.
              t.stack = (StackFrame n (toAList (FST x)) l opt)::ls ∧
              ∃y. (pop_env t = SOME y ∧
                   y.locals = union  (fromAList l) (fromAList (toAList (FST x))) ∧
                   (domain (SND x)) ∪ (domain (FST x)) = domain y.locals ∧
                   s_key_eq s.stack y.stack)
Proof
  srw_tac[][]>>Cases_on`b`>>TRY(PairCases_on`x'`)>>full_simp_tac(srw_ss())[push_env_def]>>
  full_simp_tac(srw_ss())[LET_THM,env_to_list_def]>>Cases_on`t.stack`>>
  full_simp_tac(srw_ss())[s_key_eq_def,pop_env_def]>>BasicProvers.EVERY_CASE_TAC>>
  full_simp_tac(srw_ss())[domain_fromAList,s_frame_key_eq_def]>>
  rw[] >>
  simp[domain_union,domain_fromAList] >>
  qpat_x_assum `A = MAP FST l` (SUBST1_TAC o SYM)>>
  fs[EXTENSION,mem_list_rearrange,MEM_MAP,sort_MEM,MEM_toAList
    ,EXISTS_PROD,domain_lookup] >> METIS_TAC[]
QED

Theorem get_vars_stack_swap[local]:
  !l s t. s.locals = t.locals ==>
    get_vars l s = get_vars l t
Proof
  Induct>>full_simp_tac(srw_ss())[get_vars_def,get_var_def]>>
  srw_tac[][]>> every_case_tac>>
  metis_tac[NOT_NONE_SOME,SOME_11]
QED


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

Theorem s_val_eq_APPEND[local]:
  !s t x y. (s_val_eq s t /\ s_val_eq x y)==> s_val_eq (s++x) (t++y)
Proof
  ho_match_mp_tac (s_val_eq_ind)>>
  srw_tac[][]>>full_simp_tac(srw_ss())[s_val_eq_def]
QED

Theorem s_val_eq_REVERSE[local]:
  !s t. s_val_eq s t ==> s_val_eq (REVERSE s) (REVERSE t)
Proof
  ho_match_mp_tac (s_val_eq_ind)>>
  srw_tac[][]>>full_simp_tac(srw_ss())[s_val_eq_def,s_val_eq_APPEND]
QED

Theorem s_val_eq_TAKE[local]:
  !s t n. s_val_eq s t ==> s_val_eq (TAKE n s) (TAKE n t)
Proof
  ho_match_mp_tac (s_val_eq_ind)>>rw[]>>
  Cases_on`n`>>fs[s_val_eq_def]
QED

Theorem s_val_eq_LASTN[local]:
  !s t n. s_val_eq s t
    ==> s_val_eq (LASTN n s) (LASTN n t)
Proof
  ho_match_mp_tac (s_val_eq_ind)>>
  srw_tac[][LASTN_def]>>full_simp_tac(srw_ss())[s_val_eq_def]>>
  `s_val_eq [x] [y]` by full_simp_tac(srw_ss())[s_val_eq_def]>>
  `s_val_eq (REVERSE s ++ [x]) (REVERSE t ++[y])` by
    full_simp_tac(srw_ss())[s_val_eq_APPEND,s_val_eq_REVERSE]>>
  IMP_RES_TAC s_val_eq_TAKE>>
  metis_tac[s_val_eq_REVERSE]
QED

Theorem s_key_eq_APPEND[local]:
  !s t x y. (s_key_eq s t /\ s_key_eq x y)==> s_key_eq (s++x) (t++y)
Proof
  ho_match_mp_tac s_key_eq_ind>>
  srw_tac[][]>>full_simp_tac(srw_ss())[s_key_eq_def]
QED

Theorem s_key_eq_REVERSE[local]:
  !s t. s_key_eq s t ==> s_key_eq (REVERSE s) (REVERSE t)
Proof
  ho_match_mp_tac s_key_eq_ind>>
  srw_tac[][]>>full_simp_tac(srw_ss())[s_key_eq_def,s_key_eq_APPEND]
QED

Theorem s_key_eq_TAKE[local]:
  !s t n. s_key_eq s t ==> s_key_eq (TAKE n s) (TAKE n t)
Proof
  ho_match_mp_tac s_key_eq_ind>>
  rw[]>>Cases_on`n`>>fs[s_key_eq_def]
QED

Theorem s_key_eq_LASTN[local]:
  !s t n. s_key_eq s t
    ==> s_key_eq (LASTN n s) (LASTN n t)
Proof
  ho_match_mp_tac s_key_eq_ind>>
  srw_tac[][LASTN_def]>>full_simp_tac(srw_ss())[s_key_eq_def]>>
  `s_key_eq [x] [y]` by full_simp_tac(srw_ss())[s_key_eq_def]>>
  `s_key_eq (REVERSE s ++ [x]) (REVERSE t ++[y])` by
    full_simp_tac(srw_ss())[s_key_eq_APPEND,s_key_eq_REVERSE]>>
  IMP_RES_TAC s_key_eq_TAKE>>
  metis_tac[s_key_eq_REVERSE]
QED

Theorem s_key_eq_tail:
  !a b c d. s_key_eq (a::b) (c::d) ==> s_key_eq b d
Proof
  full_simp_tac(srw_ss())[s_key_eq_def]
QED

Theorem s_val_eq_tail[local]:
  !a b c d. s_val_eq (a::b) (c::d) ==> s_val_eq b d
Proof
  full_simp_tac(srw_ss())[s_val_eq_def]
QED

Theorem s_key_eq_LASTN_exists[local]:
  !s t n m e0 e y xs. s_key_eq s t /\
    LASTN n s = StackFrame m e0 e (SOME y)::xs
    ==> ?e' ls. LASTN n t = StackFrame m e0 e' (SOME y)::ls
        /\ MAP FST e' = MAP FST e
        /\ s_key_eq xs ls
Proof
  rpt strip_tac>>
   IMP_RES_TAC s_key_eq_LASTN>>
   first_x_assum (qspec_then `n` assume_tac)>> rev_full_simp_tac(srw_ss())[]>>
   Cases_on`LASTN n t`>>
   full_simp_tac(srw_ss())[s_key_eq_def]>>
   Cases_on`h`>>Cases_on`o'`>>Cases_on`o0`>>full_simp_tac(srw_ss())[s_frame_key_eq_def]
QED

Theorem s_val_eq_LASTN_exists:
   !s t n m e0 e y xs. s_val_eq s t /\
   LASTN n s = StackFrame m e0 e (SOME y)::xs
    ==> ?e0' e' ls. LASTN n t = StackFrame m e0' e' (SOME y)::ls
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

Theorem handler_eq[local]:
  x with handler := x.handler = x
Proof
  full_simp_tac(srw_ss())[state_component_equality]
QED

Theorem s_val_eq_stack_size:
  ∀xs ys.
   s_val_eq xs ys ==>
   stack_size xs = stack_size ys
Proof
  ho_match_mp_tac s_val_eq_ind >>
  rw[s_val_eq_def] >>
  rename1 `s_frame_val_eq x y` >>
  Cases_on `x` >> Cases_on `y` >>
  rename1 `s_frame_val_eq (StackFrame _ _ _ ss1) (StackFrame _ _ _ ss2)` >>
  Cases_on `ss1` >> Cases_on `ss2` >> fs[s_frame_val_eq_def,stack_size_eq]
QED


Theorem s_key_eq_stack_size:
  !xs ys. s_key_eq xs ys ⇒ stack_size xs = stack_size ys
Proof
  ho_match_mp_tac s_key_eq_ind >>
  rw[s_key_eq_def] >>
  rename1 `s_frame_key_eq x y` >>
  Cases_on `x` >> Cases_on `y` >>
  rename1 `s_frame_key_eq (StackFrame _ _ _ ss1) (StackFrame _ _ _ ss2)` >>
  Cases_on `ss1` >> Cases_on `ss2` >> fs[s_frame_key_eq_def,stack_size_eq]
QED

Theorem s_val_append_eq_stack_size:
  !stk stk' frm. s_val_eq stk stk' ==>
    stack_size (frm::stk) = stack_size (frm::stk')
Proof
  rw [] >>
  drule s_val_eq_stack_size >> rw [] >>
  fs [stack_size_def]
QED

(* Stack swap theorem for evaluate *)
Theorem evaluate_stack_swap:
  !c s.
    case evaluate (c,s) of
    | (SOME Error,s1) => T
    | (SOME (FinalFFI e),s1) => s1.stack = [] /\ s1.locals = LN /\
                           (!xs. s_val_eq s.stack xs ==>
                                 evaluate(c,s with stack := xs) =
                                      (SOME (FinalFFI e),s1))
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
          (?e0 e n ls m lss.
              (LASTN (s.handler+1) s.stack = StackFrame m e0 e (SOME n)::ls) /\
              Abbrev (m = s1.locals_size) /\
              (MAP FST e = MAP FST lss /\
                 s1.locals = union (fromAList lss) (fromAList e0)) /\
              (s_key_eq s1.stack ls) /\ (s1.handler = case n of(a,b,c)=>a) /\
              (!xs e0' e' ls'.
                         (LASTN (s.handler+1) xs =
                           StackFrame m e0' e' (SOME n):: ls') /\
                         (s_val_eq s.stack xs) ==> (*this implies n=n' and m=m' and MAP SND e0' = MAP SND e0 *)
                         ?st locs.
                         (evaluate (c,s with stack := xs) =
                            (SOME (Exception x y),
                             s1 with <| stack := st;
                                        handler := case n of (a,b,c) => a;
                                        locals := locs |>) /\
                          (?lss'. MAP FST e' = MAP FST lss' /\
                             locs = union (fromAList lss') (fromAList e0') /\
                             MAP SND lss = MAP SND lss')/\
                          s_val_eq s1.stack st /\ s_key_eq ls' st)))
    (*NONE, SOME Result cases*)
    | (res, s1) => (s_key_eq s.stack s1.stack) /\ (s1.handler = s.handler) /\
                  (!xs. s_val_eq s.stack xs ==>
                        ?st. evaluate (c,s with stack := xs) =
                              (res, s1 with stack := st)  /\
                              s_val_eq s1.stack st /\
                              s_key_eq xs st)
Proof
  simp_tac std_ss [LET_DEF,markerTheory.Abbrev_def]
  >> ho_match_mp_tac (evaluate_ind |> Q.SPEC`UNCURRY P` |> SIMP_RULE (srw_ss())[] |> Q.GEN`P`)
  >> srw_tac[][]
  >~[`Skip`] >- (
    fs [evaluate_def] >> fs[s_key_eq_refl])
  >~[`Alloc`] >- (
    fs[evaluate_def,alloc_def] >> every_case_tac >> fs[]
    >> (
    IMP_RES_TAC gc_s_key_eq>>
    IMP_RES_TAC push_env_pop_env_s_key_eq>>
    gvs[] >>
    TRY(CONJ_TAC>-(srw_tac[][] >>
      qpat_x_assum`gc a = SOME b` mp_tac>>
      qpat_x_assum`pop_env a = b` mp_tac>>
      fs[pop_env_def,gc_def,push_env_def,env_to_list_def]>>
      every_case_tac>>full_simp_tac(srw_ss())[s_key_eq_def,s_frame_key_eq_def]>>
      srw_tac[][]>>full_simp_tac(srw_ss())[])) >>
    TRY(fs[Once CONJ_ASSOC]>> CONJ_TAC >-
       (full_simp_tac(srw_ss())[call_env_def,flush_state_def]>>srw_tac[][])
       )) >>
    rpt strip_tac
    >> qmatch_goalsub_abbrev_tac `gc a` >>
    qmatch_asmsub_abbrev_tac `gc b = _`>>
    `s_val_eq b.stack a.stack /\
      a.stack = ((HD b.stack) :: xs) /\
      (TL b.stack) = s.stack /\
      b with stack:=a.stack = a` by
      (conj_asm1_tac >> TRY(drule s_val_eq_stack_size) >>
      full_simp_tac(srw_ss())[push_env_def,LET_THM,env_to_list_def]>>
      bossLib.UNABBREV_ALL_TAC>>
      full_simp_tac(srw_ss())[s_val_eq_def,s_key_eq_def,
      s_frame_key_eq_def, s_frame_val_eq_def,s_val_eq_sym])
    >> pop_assum (PURE_ONCE_REWRITE_TAC o single o GSYM) >>
    dxrule_all gc_s_val_eq>> rev_full_simp_tac(srw_ss())[]>>
    disch_tac >> fs[] >>
    Cases_on `z` >> fs[s_val_eq_def,s_key_eq_def] >>
    Cases_on `b.stack` >> fs[s_val_eq_def,s_key_eq_def] >>
    gvs[] >>
    `h = HD x'.stack`
        by(fs[] >>
       Cases_on `b.stack` >> fs[s_val_eq_def,s_key_eq_def] >>
       irule s_frame_val_and_key_eq >> CONJ_TAC
       >-(metis_tac[s_frame_key_eq_trans,s_frame_key_eq_sym])
       >-(metis_tac[s_frame_val_eq_trans,s_frame_val_eq_sym]))
    >> fs[]
    >> fs[pop_env_def] >> gvs[AllCaseEqs()]
    >> simp[state_component_equality]
    >> metis_tac[s_key_eq_trans,s_key_eq_sym])
  >~[`PtrEq`] >- (
    fs[evaluate_def]>>every_case_tac>>
    simp[]>>
    fs[s_key_eq_refl])
  >~[`StoreConsts`] >- (
    fs[evaluate_def]>>every_case_tac>>
    simp[]>>
    fs[s_key_eq_refl])
  >~[`Move`] >- (
    fs[evaluate_def]>>every_case_tac>>
    simp[]>>
    fs[s_key_eq_refl])
  >~[`Inst`] >- (
    fs[evaluate_def] >> every_case_tac >>
    simp[]>>
    drule inst_const_full >> fs[s_key_eq_refl])
  >~[`Assign`] >- (
    fs[evaluate_def]>>every_case_tac>>
    simp[]>>
    fs[s_key_eq_refl])
  >~[`Get`] >- (
    fs[evaluate_def]>>every_case_tac>>
    simp[]>>
    fs[s_key_eq_refl])
  >~[`Set`] >- (
    fs[evaluate_def]>>every_case_tac>>
    simp[]>>
    fs[s_key_eq_refl])
  >~[`OpCurrHeap`] >- (
    fs[evaluate_def]>>every_case_tac>>
    simp[]>>
    fs[s_key_eq_refl])
  >~[`Store`] >- (
    fs[evaluate_def]>>every_case_tac>>
    simp[]>>
    drule mem_store_const >> fs[s_key_eq_refl])
  >~[`Tick`] >- (
    fs[evaluate_def,dec_clock_def,flush_state_def]>>every_case_tac>>
    simp[]>>
    fs[s_key_eq_refl])
  >~[`MustTerminate`] >- (
    full_simp_tac(srw_ss())[evaluate_def]>>
    LET_ELIM_TAC >>
    rpt ( IF_CASES_TAC >> fs[]) >>
    EVERY_CASE_TAC >> fs[] >>
    TRY(rpt strip_tac >>res_tac>>gvs[]>> NO_TAC)
    >- (
      qexists_tac`lss`>>simp[]>>
      rpt strip_tac >>res_tac>> gvs[] >>
      simp[state_component_equality]>>
      qexists_tac`lss'`>>simp[]
    ))
  >~[`Seq`] >- (
    full_simp_tac(srw_ss())[evaluate_def]>>
    LET_ELIM_TAC >> IF_CASES_TAC>-
      (*q = NONE*)
      (
      fs[] >> every_case_tac >> fs[]
       (*6 subgoals*)
       >> TRY (TRY (CONJ_TAC>- imp_res_tac s_key_eq_trans)>>
        rpt strip_tac>>
        last_x_assum(qspec_then `xs` assume_tac)>>rev_full_simp_tac(srw_ss())[]>>
        last_x_assum(qspec_then `st` assume_tac)>>rev_full_simp_tac(srw_ss())[]>>
        imp_res_tac s_key_eq_trans >> fs[] >> NO_TAC)
        >-(
        `s_key_eq s1.stack s.stack` by srw_tac[][s_key_eq_sym]>>
        drule_all s_key_eq_LASTN_exists >>
        disch_tac >> gvs[] >>
        (*get the result stack from first eval*)
        IMP_RES_TAC s_key_eq_length>>full_simp_tac(srw_ss())[]>>
        Q.EXISTS_TAC`lss`>> simp[] >>
        CONJ_TAC>-metis_tac[s_key_eq_trans]>>
        rpt strip_tac>>
        last_x_assum(qspec_then `xs` assume_tac)>>
        gvs[] >>
        IMP_RES_TAC s_key_eq_LASTN_exists>>
        fs[] >> RES_TAC >> fs[] >>
        (*cleanup assms*)
        rpt (pop_assum mp_tac) >> gvs[]
        >> rpt (disch_tac>> gvs[]) >>
        fs[state_component_equality] >>
        gvs[] >>
        CONJ_TAC >-
        (Q.EXISTS_TAC `lss'` >> simp[]
        >> fs[]) >>
        imp_res_tac s_key_eq_trans)
      )
      >-(
        fs[] >> EVERY_CASE_TAC >> fs[] >>
        TRY(rw[] >> res_tac >> fs[] >> NO_TAC)
        >-(
        Q.EXISTS_TAC `lss` >> fs[] >>
        rw[] >> res_tac >> fs[] >>
        fs[state_component_equality] >>
        Q.EXISTS_TAC `lss'` >> fs[])))
  >~[`Return`] >- (
    fs[evaluate_def,flush_state_def]>>every_case_tac>>
    simp[state_component_equality]>>
    fs[s_key_eq_refl])
  >~[`Raise`] >- (
    full_simp_tac(srw_ss())[evaluate_def]>>every_case_tac>>
    full_simp_tac(srw_ss())[jump_exc_def]>> every_case_tac>>
    gvs[] >>
    Q.EXISTS_TAC `l0` >> fs[] >>
    CONJ_TAC >-fs[s_key_eq_refl] >>
    rpt strip_tac >>
    IMP_RES_TAC s_val_eq_length>>
    fs[state_component_equality]>>
    fs[s_key_eq_refl] >>
    IMP_RES_TAC s_val_eq_LASTN>>
    first_x_assum(qspec_then `s.handler+1` assume_tac)>>
    gvs[] >> fs[s_val_eq_def,s_frame_val_eq_def]>>
    Q.EXISTS_TAC `e'` >> fs[])
  >~[`Break`] >- (
    fs[evaluate_def,flush_state_def]>>every_case_tac>>
    fs[s_key_eq_refl])
  >~[`Continue`] >- (
    fs[evaluate_def,flush_state_def]>>every_case_tac>>
    fs[s_key_eq_refl])
  >~[`If`] >- (
    full_simp_tac(srw_ss())[evaluate_def] >> every_case_tac >>
    fs[] >>
    metis_tac [])
  >~[`Loop`] >- (
    fs[evaluate_def] >>
    Cases_on `cut_state (names,LN) s` >> gvs[AllCaseEqs()] >>
    Cases_on `evaluate(c',x)` >> gvs[] >>
    rename1 `evaluate(c',x) = (bres,bs)` >>
    `x.stack = s.stack ∧ x.handler = s.handler` by
      (gvs[cut_state_def, AllCaseEqs()]) >>
    Cases_on `bres` >> gvs[]
    >- (* bres = NONE: cont_loop *)
    (IF_CASES_TAC >> gvs[flush_state_def]
     >- (* clock=0: TimeOut *)
     (rpt strip_tac >>
      first_x_assum(qspec_then `xs` mp_tac) >> simp[] >> strip_tac >>
      gvs[flush_state_def, cut_state_def, AllCaseEqs()])
     >- (* clock>0: recursive *)
     (gvs[STOP_def] >>
      Cases_on `evaluate(Loop names c' exit_names, dec_clock bs)` >> gvs[] >>
      Cases_on `q` >> gvs[]
      >- (* recursive returns NONE *)
      (conj_tac >- metis_tac[s_key_eq_trans] >>
       gen_tac >> strip_tac >>
       `∃q' r'. evaluate(c', x with stack := xs) = (q',r')` by
          metis_tac[PAIR] >>
       qpat_x_assum `∀xs. s_val_eq s.stack xs ⇒ _`
         (qspec_then `xs` mp_tac) >>
       impl_tac >- simp[] >> strip_tac >> gvs[dec_clock_def] >>
       qpat_x_assum `∀xs. s_val_eq bs.stack xs ⇒ _`
         (qspec_then `st` mp_tac) >>
       simp[] >> strip_tac >>
       qexists_tac `st'` >> simp[] >>
       metis_tac[s_key_eq_trans])
      >- (* recursive returns SOME *)
      (Cases_on `x'` >> gvs[]
       >- (* Result *)
       (conj_tac >- metis_tac[s_key_eq_trans] >>
        gen_tac >> strip_tac >>
        `∃q' r'. evaluate(c', x with stack := xs) = (q',r')` by
           metis_tac[PAIR] >>
        qpat_x_assum `∀xs. s_val_eq s.stack xs ⇒ _`
          (qspec_then `xs` mp_tac) >>
        impl_tac >- simp[] >> strip_tac >> gvs[dec_clock_def] >>
        qpat_x_assum `∀xs. s_val_eq bs.stack xs ⇒ _`
          (qspec_then `st` mp_tac) >>
        simp[] >> strip_tac >>
        qexists_tac `st'` >> simp[] >>
        metis_tac[s_key_eq_trans])
       >- (* Exception: LASTN composition, following Seq pattern *)
       (`s_key_eq bs.stack s.stack` by fs[Once s_key_eq_sym] >>
        drule_all s_key_eq_LASTN_exists >> strip_tac >>
        CONJ_TAC >- (imp_res_tac s_key_eq_length >> fs[]) >>
        rename1 `LASTN _ s.stack = StackFrame _ _ e_s _ :: ls_s` >>
        qexistsl [`e0`, `e_s`, `(r.handler, v1)`, `ls_s`, `lss`] >> simp[] >>
        CONJ_TAC >- metis_tac[s_key_eq_trans] >>
        rpt strip_tac >>
        `∃q'' r''. evaluate(c', x with stack := xs) = (q'',r'')` by
           (Cases_on `evaluate(c', x with stack := xs)` >> simp[]) >>
        qpat_x_assum `∀xs. s_val_eq s.stack xs ⇒ _`
          (qspec_then `xs` mp_tac) >>
        impl_tac >- simp[] >> strip_tac >> gvs[dec_clock_def] >>
        imp_res_tac s_val_eq_LASTN_exists >>
        fs[] >> res_tac >> fs[] >>
        rpt (pop_assum mp_tac) >> gvs[] >>
        rpt (disch_tac >> gvs[]) >>
        fs[state_component_equality] >> gvs[] >>
        CONJ_TAC >-
        (qexists_tac `lss'` >> simp[] >>
         imp_res_tac s_key_eq_LASTN_exists >> fs[] >> metis_tac[]) >>
        imp_res_tac s_key_eq_trans >>
        first_x_assum match_mp_tac >>
        imp_res_tac s_key_eq_LASTN_exists >> fs[] >> metis_tac[])
       >- (* Break *)
       (conj_tac >- metis_tac[s_key_eq_trans] >>
        gen_tac >> strip_tac >>
        `∃q' r'. evaluate(c', x with stack := xs) = (q',r')` by
           metis_tac[PAIR] >>
        qpat_x_assum `∀xs. s_val_eq s.stack xs ⇒ _`
          (qspec_then `xs` mp_tac) >>
        impl_tac >- simp[] >> strip_tac >> gvs[dec_clock_def] >>
        qpat_x_assum `∀xs. s_val_eq bs.stack xs ⇒ _`
          (qspec_then `st` mp_tac) >>
        simp[] >> strip_tac >>
        qexists_tac `st'` >> simp[] >>
        metis_tac[s_key_eq_trans])
       >- (* Continue *)
       (conj_tac >- metis_tac[s_key_eq_trans] >>
        gen_tac >> strip_tac >>
        `∃q' r'. evaluate(c', x with stack := xs) = (q',r')` by
           metis_tac[PAIR] >>
        qpat_x_assum `∀xs. s_val_eq s.stack xs ⇒ _`
          (qspec_then `xs` mp_tac) >>
        impl_tac >- simp[] >> strip_tac >> gvs[dec_clock_def] >>
        qpat_x_assum `∀xs. s_val_eq bs.stack xs ⇒ _`
          (qspec_then `st` mp_tac) >>
        simp[] >> strip_tac >>
        qexists_tac `st'` >> simp[] >>
        metis_tac[s_key_eq_trans])
       >- (* TimeOut *)
       (gen_tac >> strip_tac >>
        `∃q' r'. evaluate(c', x with stack := xs) = (q',r')` by
           metis_tac[PAIR] >>
        qpat_x_assum `∀xs. s_val_eq s.stack xs ⇒ _`
          (qspec_then `xs` mp_tac) >>
        impl_tac >- simp[] >> strip_tac >> gvs[dec_clock_def] >>
        qpat_x_assum `∀xs. s_val_eq bs.stack xs ⇒ _`
          (qspec_then `st` mp_tac) >> simp[])
       >- (* NotEnoughSpace *)
       (gen_tac >> strip_tac >>
        `∃q' r'. evaluate(c', x with stack := xs) = (q',r')` by
           metis_tac[PAIR] >>
        qpat_x_assum `∀xs. s_val_eq s.stack xs ⇒ _`
          (qspec_then `xs` mp_tac) >>
        impl_tac >- simp[] >> strip_tac >> gvs[dec_clock_def] >>
        qpat_x_assum `∀xs. s_val_eq bs.stack xs ⇒ _`
          (qspec_then `st` mp_tac) >> simp[])
       >- (* FinalFFI *)
       (gen_tac >> strip_tac >>
        `∃q' r'. evaluate(c', x with stack := xs) = (q',r')` by
           metis_tac[PAIR] >>
        qpat_x_assum `∀xs. s_val_eq s.stack xs ⇒ _`
          (qspec_then `xs` mp_tac) >>
        impl_tac >- simp[] >> strip_tac >> gvs[dec_clock_def] >>
        qpat_x_assum `∀xs. s_val_eq bs.stack xs ⇒ _`
          (qspec_then `st` mp_tac) >> simp[])
       )))
    >- (* bres = SOME r: body returned SOME x' *)
    (Cases_on `x'` >> gvs[]
     >- (* Result: simple swap *)
     (gen_tac >> strip_tac >>
      `∃q' r'. evaluate(c', x with stack := xs) = (q',r')` by
           (Cases_on `evaluate(c', x with stack := xs)` >> simp[]) >>
      qpat_x_assum `∀xs. s_val_eq s.stack xs ⇒ _`
        (qspec_then `xs` mp_tac) >>
      impl_tac >- simp[] >> strip_tac >> gvs[] >>
      qexists_tac `st` >> simp[])
     >- (* Exception *)
     (qexists_tac `lss` >> simp[] >>
      rpt strip_tac >>
      `∃q' r'. evaluate(c', x with stack := xs) = (q',r')` by
           (Cases_on `evaluate(c', x with stack := xs)` >> simp[]) >>
      first_x_assum(qspecl_then [`xs`,`e0'`,`e'`,`ls'`] mp_tac) >>
      simp[] >> strip_tac >> gvs[] >>
      simp[state_component_equality] >>
      qexists_tac `lss'` >> simp[])
     >- (* Break *)
     (Cases_on `n = 0` >> gvs[]
      >- (* Break 0: cut_state exit_names *)
      (Cases_on `cut_state (exit_names,LN) bs` >> gvs[] >>
       `x'.stack = bs.stack ∧ x'.handler = bs.handler` by
         (qpat_x_assum `cut_state _ _ = SOME _` mp_tac >>
          simp[cut_state_def,AllCaseEqs()] >> strip_tac >> gvs[]) >>
       gvs[] >>
       gen_tac >> strip_tac >>
       `∃q' r'. evaluate(c', x with stack := xs) = (q',r')` by
           (Cases_on `evaluate(c', x with stack := xs)` >> simp[]) >>
       qpat_x_assum `∀xs. s_val_eq s.stack xs ⇒ _`
         (qspec_then `xs` mp_tac) >>
       impl_tac >- simp[] >> strip_tac >> gvs[] >>
       qpat_x_assum `cut_state _ _ = SOME _` mp_tac >>
       simp[cut_state_def,AllCaseEqs()] >> strip_tac >> gvs[] >>
       qexists_tac `st` >> gvs[state_component_equality])
      >- (* Break n>0 *)
      (gen_tac >> strip_tac >>
       `∃q' r'. evaluate(c', x with stack := xs) = (q',r')` by
           (Cases_on `evaluate(c', x with stack := xs)` >> simp[]) >>
       qpat_x_assum `∀xs. s_val_eq s.stack xs ⇒ _`
         (qspec_then `xs` mp_tac) >>
       impl_tac >- simp[] >> strip_tac >> gvs[] >>
       qexists_tac `st` >> simp[]))
     >- (* Continue *)
     (Cases_on `n = 0` >> gvs[]
      >- (* Continue 0: recursive *)
      (IF_CASES_TAC >> gvs[flush_state_def]
       >- (rpt strip_tac >>
           `∃q' r'. evaluate(c', x with stack := xs) = (q',r')` by
           (Cases_on `evaluate(c', x with stack := xs)` >> simp[]) >>
           qpat_x_assum `∀xs. s_val_eq s.stack xs ⇒ _`
             (qspec_then `xs` mp_tac) >>
           impl_tac >- simp[] >> strip_tac >>
           gvs[flush_state_def, cut_state_def, AllCaseEqs()])
       >- (gvs[STOP_def] >>
           Cases_on `evaluate(Loop names c' exit_names, dec_clock bs)` >>
           gvs[] >> Cases_on `q` >> gvs[]
           >- (conj_tac >- metis_tac[s_key_eq_trans] >>
               gen_tac >> strip_tac >>
               `∃q' r'. evaluate(c', x with stack := xs) = (q',r')` by
           (Cases_on `evaluate(c', x with stack := xs)` >> simp[]) >>
               qpat_x_assum `∀xs. s_val_eq s.stack xs ⇒ _`
                 (qspec_then `xs` mp_tac) >>
               impl_tac >- simp[] >> strip_tac >> gvs[dec_clock_def] >>
               qpat_x_assum `∀xs. s_val_eq bs.stack xs ⇒ _`
                 (qspec_then `st` mp_tac) >>
               simp[] >> strip_tac >>
               qexists_tac `st'` >> simp[] >>
               metis_tac[s_key_eq_trans])
           >- (* recursive SOME for Continue 0 — same as bres=NONE *)
           (Cases_on `x'` >> gvs[]
            >- (* Result *)
            (conj_tac >- metis_tac[s_key_eq_trans] >>
             gen_tac >> strip_tac >>
             `∃q' r'. evaluate(c', x with stack := xs) = (q',r')` by
                (Cases_on `evaluate(c', x with stack := xs)` >> simp[]) >>
             qpat_x_assum `∀xs. s_val_eq s.stack xs ⇒ _`
               (qspec_then `xs` mp_tac) >>
             impl_tac >- simp[] >> strip_tac >> gvs[dec_clock_def] >>
             qpat_x_assum `∀xs. s_val_eq bs.stack xs ⇒ _`
               (qspec_then `st` mp_tac) >>
             simp[] >> strip_tac >>
             qexists_tac `st'` >> simp[] >>
             metis_tac[s_key_eq_trans])
            >- (* Exception *)
            (`s_key_eq bs.stack s.stack` by fs[Once s_key_eq_sym] >>
             drule_all s_key_eq_LASTN_exists >> strip_tac >>
             CONJ_TAC >- (imp_res_tac s_key_eq_length >> fs[]) >>
             rename1 `LASTN _ s.stack = StackFrame _ _ e_s _ :: ls_s` >>
             qexistsl [`e0`, `e_s`, `(r.handler, v1)`, `ls_s`, `lss`] >> simp[] >>
             CONJ_TAC >- metis_tac[s_key_eq_trans] >>
             rpt strip_tac >>
             `∃q'' r''. evaluate(c', x with stack := xs) = (q'',r'')` by
                (Cases_on `evaluate(c', x with stack := xs)` >> simp[]) >>
             qpat_x_assum `∀xs. s_val_eq s.stack xs ⇒ _`
               (qspec_then `xs` mp_tac) >>
             impl_tac >- simp[] >> strip_tac >> gvs[dec_clock_def] >>
             imp_res_tac s_val_eq_LASTN_exists >>
             fs[] >> res_tac >> fs[] >>
             rpt (pop_assum mp_tac) >> gvs[] >>
             rpt (disch_tac >> gvs[]) >>
             fs[state_component_equality] >> gvs[] >>
             CONJ_TAC >-
             (qexists_tac `lss'` >> simp[] >>
              imp_res_tac s_key_eq_LASTN_exists >> fs[] >> metis_tac[]) >>
             imp_res_tac s_key_eq_trans >>
             first_x_assum match_mp_tac >>
             imp_res_tac s_key_eq_LASTN_exists >> fs[] >> metis_tac[])
            >- (* Break *)
            (conj_tac >- metis_tac[s_key_eq_trans] >>
             gen_tac >> strip_tac >>
             `∃q' r'. evaluate(c', x with stack := xs) = (q',r')` by
                (Cases_on `evaluate(c', x with stack := xs)` >> simp[]) >>
             qpat_x_assum `∀xs. s_val_eq s.stack xs ⇒ _`
               (qspec_then `xs` mp_tac) >>
             impl_tac >- simp[] >> strip_tac >> gvs[dec_clock_def] >>
             qpat_x_assum `∀xs. s_val_eq bs.stack xs ⇒ _`
               (qspec_then `st` mp_tac) >>
             simp[] >> strip_tac >>
             qexists_tac `st'` >> simp[] >>
             metis_tac[s_key_eq_trans])
            >- (* Continue *)
            (conj_tac >- metis_tac[s_key_eq_trans] >>
             gen_tac >> strip_tac >>
             `∃q' r'. evaluate(c', x with stack := xs) = (q',r')` by
                (Cases_on `evaluate(c', x with stack := xs)` >> simp[]) >>
             qpat_x_assum `∀xs. s_val_eq s.stack xs ⇒ _`
               (qspec_then `xs` mp_tac) >>
             impl_tac >- simp[] >> strip_tac >> gvs[dec_clock_def] >>
             qpat_x_assum `∀xs. s_val_eq bs.stack xs ⇒ _`
               (qspec_then `st` mp_tac) >>
             simp[] >> strip_tac >>
             qexists_tac `st'` >> simp[] >>
             metis_tac[s_key_eq_trans])
            >- (* TimeOut *)
            (gen_tac >> strip_tac >>
             `∃q' r'. evaluate(c', x with stack := xs) = (q',r')` by
                (Cases_on `evaluate(c', x with stack := xs)` >> simp[]) >>
             qpat_x_assum `∀xs. s_val_eq s.stack xs ⇒ _`
               (qspec_then `xs` mp_tac) >>
             impl_tac >- simp[] >> strip_tac >> gvs[dec_clock_def] >>
             qpat_x_assum `∀xs. s_val_eq bs.stack xs ⇒ _`
               (qspec_then `st` mp_tac) >> simp[])
            >- (* NotEnoughSpace *)
            (gen_tac >> strip_tac >>
             `∃q' r'. evaluate(c', x with stack := xs) = (q',r')` by
                (Cases_on `evaluate(c', x with stack := xs)` >> simp[]) >>
             qpat_x_assum `∀xs. s_val_eq s.stack xs ⇒ _`
               (qspec_then `xs` mp_tac) >>
             impl_tac >- simp[] >> strip_tac >> gvs[dec_clock_def] >>
             qpat_x_assum `∀xs. s_val_eq bs.stack xs ⇒ _`
               (qspec_then `st` mp_tac) >> simp[])
            >- (* FinalFFI *)
            (gen_tac >> strip_tac >>
             `∃q' r'. evaluate(c', x with stack := xs) = (q',r')` by
                (Cases_on `evaluate(c', x with stack := xs)` >> simp[]) >>
             qpat_x_assum `∀xs. s_val_eq s.stack xs ⇒ _`
               (qspec_then `xs` mp_tac) >>
             impl_tac >- simp[] >> strip_tac >> gvs[dec_clock_def] >>
             qpat_x_assum `∀xs. s_val_eq bs.stack xs ⇒ _`
               (qspec_then `st` mp_tac) >> simp[])
            )
           ))
      >- (* Continue n>0 *)
      (gen_tac >> strip_tac >>
       `∃q' r'. evaluate(c', x with stack := xs) = (q',r')` by
           (Cases_on `evaluate(c', x with stack := xs)` >> simp[]) >>
       qpat_x_assum `∀xs. s_val_eq s.stack xs ⇒ _`
         (qspec_then `xs` mp_tac) >>
       impl_tac >- simp[] >> strip_tac >> gvs[] >>
       qexists_tac `st` >> simp[]))
     (* TimeOut/NotEnoughSpace/FinalFFI: body gives stack=[], so result is same *)
     >> (gen_tac >> strip_tac >>
         `∃q' r'. evaluate(c', x with stack := xs) = (q',r')` by
             (Cases_on `evaluate(c', x with stack := xs)` >> simp[]) >>
         first_x_assum(qspec_then `xs` mp_tac) >>
         impl_tac >- simp[] >> strip_tac >> gvs[])))
  >~[`LocValue`] >- (
    fs[evaluate_def,flush_state_def]>>every_case_tac>>
    simp[]>>
    fs[s_key_eq_refl])
  >~[`Install`] >- (
    fs[evaluate_def]>> every_case_tac >>
    pairarg_tac >> fs[] >> every_case_tac>>
    gvs[] >>
    simp[state_component_equality] >>
    fs[s_key_eq_refl])
  >~[`CodeBufferWrite`] >- (
    fs[evaluate_def]>>every_case_tac>>
    simp[]>>
    fs[s_key_eq_refl])
  >~[`DataBufferWrite`] >- (
    fs[evaluate_def]>>every_case_tac>>
    simp[]>>
    fs[s_key_eq_refl])
  >~[`FFI`] >- (
    full_simp_tac(srw_ss())[evaluate_def,flush_state_def]>>
    every_case_tac >> gvs[state_component_equality] >>
    fs[s_key_eq_refl])
  >~[`ShareInst`] >- (
    fs[evaluate_def,oneline share_inst_def] >>
    Cases_on `word_exp s exp` >> fs[] >>
    Cases_on `x` >> fs[] >>
    Cases_on `op` >> fs[]
    (*Do not unfold sh_mem_load* *)
    >>~- ([`sh_mem_set_var`],
    fs[oneline sh_mem_set_var_def] >> every_case_tac >>
    fs[flush_state_def] >>
    fs[s_key_eq_refl])
    >-(fs[sh_mem_store_def] >> every_case_tac >>
    fs[flush_state_def] >>
    fs[s_key_eq_refl])
    >-(fs[sh_mem_store_byte_def] >> every_case_tac >>
    fs[flush_state_def] >>
    fs[s_key_eq_refl])
    >-(fs[sh_mem_store16_def] >> every_case_tac >>
    fs[flush_state_def] >>
    fs[s_key_eq_refl])
    >-(fs[sh_mem_store32_def] >> every_case_tac >>
    fs[flush_state_def] >>
    fs[s_key_eq_refl])
   )
  >~[`Call`] >- (
    full_simp_tac(srw_ss())[evaluate_def]>>
    Cases_on`get_vars args s`>> full_simp_tac(srw_ss())[]>>
    IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
    Cases_on`find_code dest (add_ret_loc ret x) s.code s.stack_size`>>
    full_simp_tac(srw_ss())[]>>
    Cases_on`x'`>>full_simp_tac(srw_ss())[]>>
    Cases_on`r`>>full_simp_tac(srw_ss())[]>>
    Cases_on`ret`>>full_simp_tac(srw_ss())[]
    >- ( (*Tail Call*)
      Cases_on`handler`>>full_simp_tac(srw_ss())[flush_state_def,dec_clock_def]>>
      every_case_tac>> fs[] >> every_case_tac>> fs[] >>
      full_simp_tac bool_ss [GSYM state_fupdcanon] >> fs[] >> gvs[] >>
      TRY (Q.EXISTS_TAC `lss` >> fs[]) >>
      rpt strip_tac >> fs[call_env_def] >>
      drule_then (simp o single o GSYM) s_val_eq_stack_size >>
      first_x_assum (drule_all_then (assume_tac)) >>
      fs[] >> simp[state_component_equality] >>
      Q.EXISTS_TAC `lss'` >> fs[])
    >>
    (*Returning call*)
    PairCases_on`x'`>> full_simp_tac(srw_ss())[]>>
    IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
    Cases_on`cut_envs (x'1,x'2) s.locals`>>full_simp_tac(srw_ss())[]>>
    IF_CASES_TAC >> gvs[]
    >- (
      gvs[AllCaseEqs()] >> fs[flush_state_def,call_env_def] >>
      Cases_on `handler` >-
        (
        gvs[push_env_def,env_to_list_def,state_component_equality
        ,stack_size_eq] >> rpt strip_tac >>
         imp_res_tac s_val_eq_stack_size >> rw[]) >>
      rename1 `push_env _ (SOME handler)` >>
      PairCases_on `handler` >>
      rw[push_env_def,ELIM_UNCURRY,stack_size_eq] >>
      imp_res_tac s_val_eq_stack_size >> rw[]
      )>>
    full_simp_tac(srw_ss())[]>>
    Cases_on`evaluate (q',call_env q r' (push_env x' handler (dec_clock s)))`>>
    Cases_on`q''`>>full_simp_tac(srw_ss())[]>>Cases_on`x''`>>full_simp_tac(srw_ss())[]
    >- ( (*Result*)
      full_simp_tac(srw_ss())[]>>
      IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
      Cases_on `pop_env r` >> fs[] >>
      IF_CASES_TAC>> fs[] >>
      IMP_RES_TAC push_env_pop_env_s_key_eq>>
      full_simp_tac(srw_ss())[dec_clock_def,SOME_11]>>
      Cases_on`evaluate(x'3,set_vars x'0 l x'')`>>full_simp_tac(srw_ss())[]>>
      Cases_on`q''`>>TRY(Cases_on`x'''`)>>full_simp_tac(srw_ss())[]>>rev_full_simp_tac(srw_ss())[]>>
      `s_key_eq s.stack x''.stack` by full_simp_tac(srw_ss())[EQ_SYM_EQ]>>full_simp_tac(srw_ss())[]>>
      (*Inductive Result and None*)
      TRY
      (qho_match_abbrev_tac`A ∧ B /\ C` >> unabbrev_all_tac>>
      CONJ_TAC
      >- metis_tac[s_key_eq_trans]>>
      CONJ_ASM1_TAC >-
      (
      gvs[] >> Cases_on`handler`>>
      full_simp_tac(srw_ss())[oneline push_env_def,LET_THM,env_to_list_def,pop_env_def]>>
      fs[Once (oneline s_key_eq_def),oneline s_frame_key_eq_def] >>
      gvs[AllCaseEqs()] >> PairCases_on `x'''` >> gvs[AllCaseEqs()]
      ) >>
      gvs[] >> rpt  strip_tac >>
      (*Pull out clock*)
      full_simp_tac bool_ss [GSYM state_fupdcanon] >> fs[] >>
      qpat_abbrev_tac `a = push_env x' handler _` >>
      qabbrev_tac `b = push_env x' handler s` >>
     `s_val_eq b.stack a.stack /\  a.stack = (HD b.stack :: xs) /\
       a = b with stack := a.stack` by
       (conj_asm1_tac >>
      bossLib.UNABBREV_ALL_TAC >>
      Cases_on `handler` >> TRY (PairCases_on `x'''`) >>
      fs[push_env_def,env_to_list_def] >>
      fs[s_val_eq_def,s_frame_val_eq_def] >>
      fs[state_component_equality] >>
      fs[stack_size_eq] >>
      TRY(drule s_val_eq_stack_size)>>
      fs[s_val_eq_length]) >>
      pop_assum (PURE_ONCE_REWRITE_TAC o single) >>
      `call_env q r' (b with stack := a.stack) = call_env q r' b with stack := a.stack`
         by (fs[call_env_def] >>
         drule_then assume_tac s_val_eq_stack_size >>
         fs[]) >>
      fs[] >>
      last_x_assum (dxrule) >>
      disch_tac >> fs[] >>
      Cases_on `st` >> fs [s_val_eq_def,s_key_eq_def] >>
      Cases_on `b.stack` >> fs[s_val_eq_def,s_key_eq_def] >>
      `(StackFrame n (toAList (FST x')) l' opt) = h` by
          (Cases_on `b.stack` >> fs[s_key_eq_def] >>
          irule s_frame_val_and_key_eq >> CONJ_TAC
          >- metis_tac[s_frame_key_eq_sym,s_frame_key_eq_trans]
          >- metis_tac[s_frame_val_eq_sym,s_frame_val_eq_trans]) >>
      fs[] >>
      `pop_env (r with stack := h ::t) =
      SOME (x'' with stack := t) /\ x''.stack = ls`
         by (fs[oneline pop_env_def] >> every_case_tac >> gvs[])
      >> fs[] >>
      last_x_assum (dxrule) >>
      disch_tac >> fs[] >>
      gvs[] >> metis_tac[s_key_eq_trans])
      (*Exceptions*)
        >- (
          `s.handler = x''.handler` by
          (
          fs[oneline push_env_def,pop_env_def,env_to_list_def]>>
          every_case_tac >> gvs[s_key_eq_def,s_frame_key_eq_def]) >>
        fs[] >>
        CONJ_ASM1_TAC >- metis_tac[s_key_eq_length]>>
        `s_key_eq x''.stack s.stack` by metis_tac[s_key_eq_sym]>>
        drule_all_then assume_tac s_key_eq_LASTN_exists>>
        full_simp_tac(srw_ss())[]>>
        (*check*)
        qexists_tac`lss`>>full_simp_tac(srw_ss())[]>>
        CONJ_TAC>- metis_tac[s_key_eq_trans] >>
        rpt strip_tac>>full_simp_tac(srw_ss())[]>>
        full_simp_tac bool_ss [GSYM state_fupdcanon] >> simp[] >>
        qpat_abbrev_tac `a = push_env x' handler _` >>
        qabbrev_tac `b = push_env x' handler s` >>
        `s_val_eq b.stack a.stack /\  a.stack = (HD b.stack :: xs) /\
         a = b with stack := a.stack` by
         (conj_asm1_tac >>
         bossLib.UNABBREV_ALL_TAC >>
         Cases_on `handler` >> TRY (PairCases_on `x'''`) >>
         fs[push_env_def,env_to_list_def] >>
         fs[s_val_eq_def,s_frame_val_eq_def] >>
         fs[state_component_equality] >>
         fs[stack_size_eq] >>
         TRY(drule s_val_eq_stack_size)>>
         fs[s_val_eq_length]) >>
         pop_assum (PURE_ONCE_REWRITE_TAC o single) >>
         `call_env q r' (b with stack := a.stack) = call_env q r' b with stack := a.stack`
           by (fs[call_env_def] >>
              drule_then assume_tac s_val_eq_stack_size >>
              fs[]) >>
         fs[] >>
         last_x_assum (drule_all) >>
         disch_tac >> fs[] >>
         Cases_on `st` >> fs [s_val_eq_def,s_key_eq_def] >>
         Cases_on `b.stack` >> fs[s_val_eq_def,s_key_eq_def] >>
         `(StackFrame n (toAList (FST x')) l' opt) = h` by
            (Cases_on `b.stack` >> fs[s_key_eq_def] >>
            irule s_frame_val_and_key_eq >> CONJ_TAC
            >- metis_tac[s_frame_key_eq_sym,s_frame_key_eq_trans]
            >- metis_tac[s_frame_val_eq_sym,s_frame_val_eq_trans]) >>
         fs[] >>
         `pop_env (r with stack := h ::t) =
          SOME (x'' with stack := t) /\ x''.stack = ls`
            by (fs[oneline pop_env_def] >> every_case_tac >> gvs[])
         >> fs[] >>
         drule_all s_key_eq_LASTN_exists>>
         disch_tac >> fs[] >>
         last_x_assum (drule_all) >>
         disch_tac >> fs[] >>
         simp[state_component_equality] >>
         (CONJ_TAC >- (Q.EXISTS_TAC `lss'` >> fs[] )
         >>metis_tac[s_key_eq_sym,s_key_eq_trans])
       )
      (*The rest*)
      >> (
      rpt strip_tac >> full_simp_tac bool_ss [GSYM state_fupdcanon] >> fs[] >>
      qpat_abbrev_tac `a = push_env x' handler _` >>
      qabbrev_tac `b = push_env x' handler s` >>
     `s_val_eq b.stack a.stack /\  a.stack = (HD b.stack :: xs) /\
       a = b with stack := a.stack` by
       (conj_asm1_tac >>
      bossLib.UNABBREV_ALL_TAC >>
      Cases_on `handler` >> TRY (PairCases_on `x'''`) >>
      fs[push_env_def,env_to_list_def] >>
      fs[s_val_eq_def,s_frame_val_eq_def] >>
      fs[state_component_equality] >>
      fs[stack_size_eq] >>
      TRY(drule s_val_eq_stack_size)>>
      fs[s_val_eq_length]) >>
      pop_assum (PURE_ONCE_REWRITE_TAC o single) >>
      `call_env q r' (b with stack := a.stack) = call_env q r' b with stack := a.stack`
         by (fs[call_env_def] >>
         drule_then assume_tac s_val_eq_stack_size >>
         fs[]) >>
      fs[] >>
      last_x_assum (dxrule) >>
      disch_tac >> fs[] >>
      Cases_on `st` >> fs[s_key_eq_def,s_val_eq_def] >>
     `(StackFrame n (toAList (FST x')) l' opt) = h` by
            (Cases_on `b.stack` >> fs[s_key_eq_def] >>
            irule s_frame_val_and_key_eq >> CONJ_TAC
            >- metis_tac[s_frame_key_eq_sym,s_frame_key_eq_trans]
            >- metis_tac[s_frame_val_eq_sym,s_frame_val_eq_trans]) >>
      fs[] >>
      `pop_env (r with stack := h ::t) =
       SOME (x'' with stack := t) /\ x''.stack = ls`
         by (fs[oneline pop_env_def] >> every_case_tac >> gvs[])
      >> fs[]))
     >- ( (*Exception*)
       Cases_on`handler` >> fs []
       >- (
         (*no handler*)
         fs [call_env_def,flush_state_def,push_env_def,env_to_list_def,dec_clock_def,LET_THM]>>
         CONJ_ASM1_TAC
         >- (
           IMP_RES_TAC prim_recTheory.LESS_LEMMA1>>
           qpat_x_assum `LASTN a as=b` mp_tac>>simp[]>>
           qpat_abbrev_tac `frame = StackFrame lsz _ _  _`>>
           `LENGTH s.stack+1 = LENGTH (frame::s.stack) ` by full_simp_tac(srw_ss())[arithmeticTheory.ADD1]>>
           pop_assum SUBST1_TAC>> fs [LASTN_LENGTH_ID]>>
           Q.UNABBREV_TAC`frame`>>fs[option_nchotomy]) >>
         fs[GEN_ALL LASTN_TL]>>
         Q.EXISTS_TAC`lss`>>full_simp_tac(srw_ss())[]>>rpt strip_tac>>
         fs[] >>
         qpat_abbrev_tac `frame = StackFrame lsz _ _ _`>>
         `s.handler < LENGTH xs` by (IMP_RES_TAC s_val_eq_length>>full_simp_tac(srw_ss())[])>>
         first_x_assum(qspecl_then [`frame::xs`,`e0'`,`e'`,`ls'`] assume_tac)>>
         rev_full_simp_tac(srw_ss())[]>>
         IMP_RES_TAC (GEN_ALL LASTN_TL)>>
         last_x_assum(qspec_then `frame` assume_tac)>>
         full_simp_tac(srw_ss())[]>> rev_full_simp_tac(srw_ss())[]>>
         `s_val_eq (frame::s.stack) (frame::xs)` by
           metis_tac[s_val_eq_def,s_frame_val_eq_def] >>
         drule s_val_eq_stack_size >> strip_tac >> fs []>>
         simp[state_component_equality] >>
         Q.EXISTS_TAC`lss'`>> fs []) >>
       (*handler*)
       PairCases_on`x''`>> fs[dec_clock_def] >>
       fs[call_env_def,push_env_def,env_to_list_def] >>
       IF_CASES_TAC >> fs[] >>
       IF_CASES_TAC >> fs[] >>
       every_case_tac>>fs[]>>
       `q'' = s.handler` by (
         `LENGTH s.stack +1 =
          LENGTH (StackFrame s.locals_size (toAList (FST x')) (list_rearrange (s.permute 0)
             (sort key_val_compare (toAList (SND x'))))
             (SOME (s.handler,x''2,x''3))::s.stack)` by fs [arithmeticTheory.ADD1]>>
           pop_assum SUBST_ALL_TAC>>         fs [LASTN_LENGTH_ID])>>
       TRY (
         qho_match_abbrev_tac`A ∧ B /\ C` >> unabbrev_all_tac>>
         ONCE_REWRITE_TAC[CONJ_ASSOC]>>CONJ_TAC
         >-
         (`LENGTH s.stack +1 =
           LENGTH (StackFrame s.locals_size  (toAList (FST x')) (list_rearrange (s.permute 0)
           (sort key_val_compare (toAList (SND x'))))
           (SOME (s.handler,x''2,x''3))::s.stack)` by full_simp_tac(srw_ss())[arithmeticTheory.ADD1]>>
         pop_assum SUBST_ALL_TAC>>
         full_simp_tac(srw_ss())[LASTN_LENGTH_ID]>>
         metis_tac[s_key_eq_trans,s_key_eq_sym])>>
         rpt strip_tac>>
         qpat_abbrev_tac`frame = StackFrame lsz _ _ _`>>
         `s_val_eq (frame::s.stack) (frame::xs)` by
           fs[s_val_eq_def,s_frame_val_eq_refl]>>
         drule_all_then assume_tac s_val_eq_stack_size >> fs[] >>
         drule_all_then assume_tac s_val_eq_LASTN_exists>> fs[] >>
         `LENGTH s.stack = LENGTH xs` by full_simp_tac(srw_ss())[s_val_eq_length] >>
         first_x_assum (drule_all_then assume_tac) >> gvs[] >>
         `LENGTH s.stack +1 = LENGTH (frame::s.stack) /\
          LENGTH s.stack +1 = LENGTH (frame::xs)` by
           full_simp_tac(srw_ss())[arithmeticTheory.ADD1,s_val_eq_length]>>
         full_simp_tac(srw_ss())[LASTN_LENGTH_cond]>>
         gvs[] >>
         `lss = lss'` by full_simp_tac(srw_ss())[LIST_EQ_MAP_PAIR]>>
         gvs[] >>
         qmatch_goalsub_abbrev_tac `set_var _ _ a` >>
         `a = r with stack := st`
           by fs[Abbr`a`, state_component_equality] >>
         fs[] >>
         first_x_assum drule_all >> fs[] >>
         disch_tac >> fs[] >>
         metis_tac[s_key_eq_trans])
       >- (
         CONJ_TAC >- (
          `LENGTH s.stack +1 =
           LENGTH (StackFrame s.locals_size (toAList (FST x')) (list_rearrange (s.permute 0)
           (sort key_val_compare (toAList (SND x'))))
           (SOME (s.handler,x''2,x''3))::s.stack)` by full_simp_tac(srw_ss())[arithmeticTheory.ADD1]>>
           pop_assum SUBST_ALL_TAC>>
           full_simp_tac(srw_ss())[LASTN_LENGTH_ID]>>
           `LENGTH ls = LENGTH r.stack` by full_simp_tac(srw_ss())[s_key_eq_length] >>
           full_simp_tac(srw_ss())[])>>
         gvs[] >>
         IMP_RES_TAC s_key_eq_LASTN_exists>> gvs[] >>
         `LASTN (s.handler + 1) ls = LASTN (s.handler + 1) s.stack` by (
           `LENGTH s.stack +1 =
           LENGTH (StackFrame s.locals_size (toAList(FST x')) (list_rearrange (s.permute 0)
           (sort key_val_compare (toAList (SND x'))))
           (SOME (s.handler,x''2,x''3))::s.stack)` by full_simp_tac(srw_ss())[arithmeticTheory.ADD1]>>
           pop_assum SUBST_ALL_TAC>>
           full_simp_tac(bool_ss)[LASTN_LENGTH_ID]>>
           `LENGTH ls = LENGTH r.stack` by full_simp_tac(srw_ss())[s_key_eq_length]>>
           full_simp_tac(srw_ss())[EQ_SYM_EQ] >> gvs[])>>
         gvs[] >>
         qexists_tac `lss'` >> gvs[] >>
         CONJ_TAC>- metis_tac[s_key_eq_trans]>>
         rpt strip_tac>> fs[] >>
         qpat_abbrev_tac`frame = StackFrame lsz b c d`>>
         `s_val_eq (frame::s.stack) (frame::xs)` by
           metis_tac[s_val_eq_def,s_frame_val_eq_def]>>
         drule s_val_eq_stack_size >> strip_tac >> fs [] >>
         IMP_RES_TAC s_val_eq_LASTN_exists>>
         pop_assum kall_tac>>
         first_x_assum drule_all >>
         disch_tac >> gvs[] >>
         `LENGTH s.stack = LENGTH xs` by full_simp_tac(srw_ss())[s_val_eq_length] >>
         gvs[] >>
         `LENGTH s.stack +1 = LENGTH (frame::s.stack) /\
          LENGTH s.stack +1 = LENGTH (frame::xs)` by
           full_simp_tac(srw_ss())[arithmeticTheory.ADD1,s_val_eq_length]>>
         full_simp_tac(srw_ss())[LASTN_LENGTH_cond]>>
         gvs[] >>
         `MAP FST lss = MAP FST lss''` by metis_tac[EQ_SYM_EQ]>>
         `lss'' = lss` by full_simp_tac(srw_ss())[LIST_EQ_MAP_PAIR]>>
         fs[]>> gvs[] >>
         qmatch_goalsub_abbrev_tac `set_var _ _ a` >>
         `a = r with stack := st`
          by fs[Abbr`a`, state_component_equality] >>
         fs[] >> gvs[] >>
         (*Clean assms*)
         gvs[s_val_eq_def,stack_size_eq2,s_frame_val_eq_def] >>
         IMP_RES_TAC s_key_eq_LASTN_exists>>
         qmatch_asmsub_rename_tac `LASTN _ st = StackFrame _ e00 e5 _::ls5` >>
         first_x_assum (qspecl_then [`st`,`e00`,`e5`,`ls5`] mp_tac)>>
         impl_tac >- gvs[]>>
         disch_tac >> gvs[] >>
         simp[state_component_equality] >>
         CONJ_TAC >- (Q.EXISTS_TAC `lss''` >> fs[]) >>
         metis_tac[s_key_eq_trans] ) >>
       (*TimeOut*)
       rpt strip_tac>> fs[] >>
       qpat_abbrev_tac`frame = StackFrame lsz _ _ _`>>
       `s_val_eq (frame::s.stack) (frame::xs)` by
         metis_tac[s_val_eq_def,s_frame_val_eq_def]>>
       drule s_val_eq_stack_size >> strip_tac >> fs [] >>
       IMP_RES_TAC s_val_eq_LASTN_exists>>
       `LENGTH s.stack = LENGTH xs` by full_simp_tac(srw_ss())[s_val_eq_length] >>
       first_x_assum(drule_all_then  assume_tac)>>rev_full_simp_tac(srw_ss())[]>>
       `LENGTH s.stack +1 = LENGTH (frame::s.stack) /\
        LENGTH s.stack +1 = LENGTH (frame::xs)` by
          full_simp_tac(srw_ss())[arithmeticTheory.ADD1,s_val_eq_length]>>
       full_simp_tac(srw_ss())[LASTN_LENGTH_cond]>>
       `MAP FST lss = MAP FST lss'` by metis_tac[EQ_SYM_EQ]>>
       `lss = lss'` by full_simp_tac(srw_ss())[LIST_EQ_MAP_PAIR]>>
       pop_assum (SUBST1_TAC o SYM)>>
       full_simp_tac(srw_ss())[]>>
       qmatch_goalsub_abbrev_tac `set_var _ _ a` >>
       `a = r with stack := st`
         by fs[Abbr`a`, state_component_equality] >>
       fs[] >>
       first_x_assum drule_all >> fs[]) >>
     (*Cleanup...*)
     rpt  strip_tac>> fs[call_env_def] >>
      Cases_on`handler`>> TRY(PairCases_on`x''`)>>
      fs [push_env_def,LET_THM,env_to_list_def,dec_clock_def]>>
      qpat_abbrev_tac `frame = StackFrame lsz _ _ _`>>
      `s_val_eq (frame::s.stack) (frame::xs)`
         by fs[s_val_eq_def,s_frame_val_eq_refl] >>
      drule s_val_eq_stack_size >> strip_tac >> fs [] >>
     `LENGTH xs = LENGTH s.stack` by full_simp_tac(srw_ss())[s_val_eq_length]>>
     full_simp_tac(srw_ss())[])
QED

(*--Stack Swap Lemma DONE--*)

(*--Permute Swap Lemma--*)
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
  ho_match_mp_tac (evaluate_ind |> Q.SPEC`UNCURRY P` |> SIMP_RULE (srw_ss())[] |> Q.GEN`P`) >> srw_tac[][]
  >~[`Alloc`]
  >-
   (qexists_tac`λx. if x = 0 then st.permute 0 else perm (x-1)`>>
    qpat_x_assum `_ = (res,rst)` mp_tac >>
    fs[evaluate_def,alloc_def,push_env_def,env_to_list_def] >>
    pure_rewrite_tac[GSYM state_fupdcanon] >> fs[] >>
    gvs[AllCaseEqs()] >>
    rw[] >> fs[] >>
    fs[has_space_def,flush_state_def] >>
    fs[state_component_equality,FUN_EQ_THM])
  >~[`MustTerminate`]
  >-(gvs[evaluate_def,AllCaseEqs()] >> simp[state_component_equality] >>
     pairarg_tac >> gvs[AllCaseEqs()] >>
    first_x_assum(qspec_then`perm` assume_tac)>>full_simp_tac(srw_ss())[]>>
     qexists_tac`perm'`>> gvs[AllCaseEqs()])
  >~[`Seq`]
  >- (gvs[evaluate_def,AllCaseEqs()] >> simp[state_component_equality] >>
     pairarg_tac >> gvs[AllCaseEqs()]
     >-(
     last_x_assum(qspec_then`perm` assume_tac)>>full_simp_tac(srw_ss())[]>>
     last_x_assum(qspec_then`perm'` assume_tac)>>full_simp_tac(srw_ss())[]>>
     qexists_tac`perm''`>> gvs[AllCaseEqs()]) >>
     last_x_assum(qspec_then`perm` assume_tac)>>full_simp_tac(srw_ss())[]>>
     qexists_tac`perm'`>> gvs[AllCaseEqs()])
  >~[`Install`]
  >- (gvs[evaluate_def,AllCaseEqs()] >> pairarg_tac >> gvs[AllCaseEqs()] >>
     simp[state_component_equality])
  >~[`Loop`]
  >- (
    qpat_x_assum `evaluate (Loop _ _ _, _) = _` mp_tac >>
    PURE_ONCE_REWRITE_TAC[evaluate_def] >>
    gvs[AllCaseEqs(),UNCURRY_EQ,flush_state_def,dec_clock_def] >>
    rpt strip_tac >> imp_res_tac cut_state_const >> gvs[]
    (* timeout: cont_loop, clock=0 *)
    >- (`res' ≠ SOME Error` by
          (Cases_on `res'` >> gvs[cont_loop_def] >>
           Cases_on `x` >> gvs[cont_loop_def]) >>
        last_x_assum(qspec_then`perm` assume_tac) >> gvs[] >>
        rename1 `evaluate (prog,_ with <|locals := _; permute := bp|>) = _` >>
        qexists_tac `bp` >> qexists_tac `res'` >>
        qexists_tac `s1 with permute := perm` >>
        gvs[flush_state_def,state_component_equality])
    (* recursive: cont_loop, clock≠0 *)
    >- (last_x_assum(qspec_then`perm` assume_tac) >> gvs[] >>
        `res' ≠ SOME Error` by
          (Cases_on `res'` >> gvs[cont_loop_def] >>
           Cases_on `x` >> gvs[cont_loop_def]) >>
        rename1 `evaluate (STOP _,_ with <|permute := rp; clock := _|>) = _` >>
        last_x_assum(qspec_then`rp` assume_tac) >> gvs[] >>
        rename1 `evaluate (prog,_ with <|locals := _; permute := bp|>) = _` >>
        qexists_tac `bp` >> qexists_tac `res'` >>
        qexists_tac `s1 with permute := rp` >>
        gvs[dec_clock_def,state_component_equality])
    (* break *)
    >- (last_x_assum(qspec_then`perm` assume_tac) >> gvs[] >>
        rename1 `evaluate (prog,_ with <|locals := _; permute := bp|>) = _` >>
        qexists_tac `bp` >> qexists_tac `SOME (Break 0)` >>
        qexists_tac `s1 with permute := perm` >>
        gvs[] >> imp_res_tac cut_state_const >> gvs[state_component_equality])
    (* exit_loop *)
    >- (`res' ≠ SOME Error` by
          (CCONTR_TAC >> gvs[exit_loop_def]) >>
        last_x_assum(qspec_then`perm` assume_tac) >> gvs[] >>
        rename1 `evaluate (prog,_ with <|locals := _; permute := bp|>) = _` >>
        qexists_tac `bp` >> qexists_tac `res'` >>
        qexists_tac `rst with permute := perm` >>
        gvs[exit_loop_def,state_component_equality])
  )
  >~[`Call`]
  >- (
    fs[evaluate_def,flush_state_def,dec_clock_def]>>
    ntac 6 (TOP_CASE_TAC>>full_simp_tac(srw_ss())[])
    >- (*Tail Call*)
      (gvs[evaluate_def,AllCaseEqs()] >> simp[state_component_equality])
    >>
      PairCases_on `x'` >> fs[] >>
      ntac 3 (TOP_CASE_TAC>>full_simp_tac(srw_ss())[])
      >-
        (gvs[] >> simp[state_component_equality] >>
        Cases_on `handler` >> TRY (PairCases_on  `x''`) >>
        fs[push_env_def,env_to_list_def] >>
        full_simp_tac bool_ss [GSYM state_fupdcanon] >> fs[] >>
        fs[call_env_def,stack_size_eq])
      >>
      qpat_x_assum `_ = (res,rst)` mp_tac >>
      ntac 3 (TOP_CASE_TAC >> fs[])
      >-(
        IF_CASES_TAC >> fs[] >>
        TOP_CASE_TAC >> fs[] >>
        IF_CASES_TAC >> fs[] >>
        rw[] >> fs[] >> gvs[] >>
        first_x_assum(qspec_then`perm`assume_tac)>>full_simp_tac(srw_ss())[]>>
        first_x_assum(qspec_then`perm'`assume_tac)>>full_simp_tac(srw_ss())[]>>
        qexists_tac`λx. if x = 0 then st.permute 0 else perm'' (x-1)`>>
        Cases_on `handler` >> TRY (PairCases_on  `x'''`) >>
        fs[push_env_def,env_to_list_def] >>
        fs[] >>
        `(λn. perm'' n) = perm''` by full_simp_tac(srw_ss())[FUN_EQ_THM]>>
        fs[] >>
        full_simp_tac bool_ss [GSYM state_fupdcanon] >> fs[]
        )
      >-(
        Cases_on `handler` >> TRY (PairCases_on  `x''`) >>
        fs[push_env_def,env_to_list_def] >>
        rw[] >> gvs[]
        >- (
            first_x_assum(qspec_then`perm`assume_tac)>>full_simp_tac(srw_ss())[]>>
            qexists_tac`λx. if x = 0 then st.permute 0 else perm' (x-1)`>>
            fs[] >>
            `(λn. perm' n) = perm'` by full_simp_tac(srw_ss())[FUN_EQ_THM]>>
            full_simp_tac bool_ss [GSYM state_fupdcanon] >> fs[])
        >- (
            first_x_assum(qspec_then`perm`assume_tac)>>full_simp_tac(srw_ss())[]>>
            first_x_assum(qspec_then`perm'`assume_tac)>>full_simp_tac(srw_ss())[]>>
            qexists_tac`λx. if x = 0 then st.permute 0 else perm'' (x-1)`>>
            fs[] >>
            `(λn. perm'' n) = perm''` by full_simp_tac(srw_ss())[FUN_EQ_THM]>>
            fs[] >>
            full_simp_tac bool_ss [GSYM state_fupdcanon] >> fs[]
            ))
      >>
        rw[] >> gvs[] >>
        first_x_assum(qspec_then`perm`assume_tac)>>full_simp_tac(srw_ss())[]>>
        qexists_tac`λx. if x = 0 then st.permute 0 else perm' (x-1)`>>
        Cases_on `handler` >> TRY (PairCases_on  `x''`) >>
        fs[push_env_def,env_to_list_def] >>
        fs[] >>
        `(λn. perm' n) = perm'` by full_simp_tac(srw_ss())[FUN_EQ_THM]>>
        fs[] >>
        full_simp_tac bool_ss [GSYM state_fupdcanon] >> fs[]
    )
  >> gvs[evaluate_def,AllCaseEqs()] >> simp[state_component_equality]
  >> simp[dec_clock_def]
QED

(* Locals extend lemma *)
Definition locals_rel_def:
  locals_rel temp (s:'a word_loc num_map) t ⇔ (∀x. x < temp ⇒ lookup x s = lookup x t)
End

Theorem the_words_EVERY_IS_SOME:
   ∀ls x.
  the_words ls = SOME x ⇒
  EVERY IS_SOME ls
Proof
  Induct>>fs[]>>Cases>>fs[the_words_def]>>
  TOP_CASE_TAC>>fs[]>>
  TOP_CASE_TAC>>fs[]
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

Theorem locals_rel_get_var_simp:
  r < temp ∧
  locals_rel temp st.locals loc ⇒
  get_var r (st with locals:=loc) = get_var r st
Proof
  full_simp_tac(srw_ss())[get_var_def,locals_rel_def]
QED

Theorem locals_rel_get_vars_simp:
  EVERY (λx. x < temp) l ∧
  locals_rel temp st.locals loc ⇒
  get_vars l (st with locals:=loc) = get_vars l st
Proof
   Induct_on `l` >> fs[get_vars_def] >>
   rpt strip_tac >>
   DEP_REWRITE_TAC[locals_rel_get_var_simp] >> fs[]
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

Theorem locals_rel_get_var_imm_simp:
  every_var_imm (λx.x<temp) r ∧
  locals_rel temp st.locals loc ⇒
  get_var_imm r (st with locals:=loc) = get_var_imm r st
Proof
  Cases_on`r`>>full_simp_tac(srw_ss())[get_var_imm_def,every_var_imm_def]>>
  rpt strip_tac >>
  DEP_REWRITE_TAC[locals_rel_get_var_simp] >> fs[]
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
  >-(gvs[get_var_def])
  >-
    (every_case_tac>>
    res_tac>>full_simp_tac(srw_ss())[])
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
  >-
    (every_case_tac>>
    res_tac>>full_simp_tac(srw_ss())[])
QED

Theorem locals_rel_word_exp_simp:
  ∀s exp w.
    every_var_exp (λx. x < temp) exp ∧
    locals_rel temp s.locals loc ⇒
    word_exp (s with locals:=loc) exp = word_exp s exp
Proof
  ho_match_mp_tac word_exp_ind>>srw_tac[][]>>
  full_simp_tac(srw_ss())[word_exp_def,every_var_exp_def]
  >-
  (DEP_REWRITE_TAC [locals_rel_get_var_simp] >> fs[])
  >-
    (qpat_abbrev_tac`ls = MAP A B`>>
    qpat_abbrev_tac`ls' = MAP A B`>>
    `ls = ls'` by
      (imp_res_tac the_words_EVERY_IS_SOME>>
      unabbrev_all_tac>>fs[MAP_EQ_f]>>
      fs[EVERY_MAP,EVERY_MEM]>>
      rw[]>>res_tac>>
      fs[IS_SOME_EXISTS])>>
    fs[])
QED

Theorem locals_rel_set_var[local]:
  ∀n s t.
  locals_rel temp s t ⇒
  locals_rel temp (insert n v s) (insert n v t)
Proof
  srw_tac[][]>>full_simp_tac(srw_ss())[locals_rel_def,lookup_insert]
QED

Theorem locals_rel_delete[local]:
  ∀n s t.
  locals_rel temp s t ⇒
  locals_rel temp (delete n s) (delete n t)
Proof
  rw[locals_rel_def,lookup_delete]
QED

Theorem locals_rel_cut_envs:
  locals_rel temp loc loc' ∧
  every_name (λx. x < temp) names ∧
  cut_envs names loc = SOME x ⇒
  cut_envs names loc' = SOME x
Proof
  rw[locals_rel_def,every_name_def,cut_envs_def,cut_names_def]>>
  full_simp_tac(srw_ss())[SUBSET_DEF,EVERY_MEM,toAList_domain] >>
  fs[cut_envs_def,cut_names_def]
    >- (
    simp[lookup_inter]>>
    rw[]>>every_case_tac>>fs[]>>
    fs[domain_lookup]>>
    res_tac >> fs[] >>
    res_tac >> fs[])
    >>
  res_tac >> fs[] >>
  PURE_REWRITE_TAC[GSYM NOT_EVERY,EVERY_MEM,toAList_domain] >>
  metis_tac[domain_lookup]
QED

Theorem locals_rel_cut_env:
  locals_rel temp loc loc' ∧
  every_name (λx. x < temp) names ∧
  cut_env names loc = SOME x ⇒
  cut_env names loc' = SOME x
Proof
  fs[cut_env_def] >>
  fs[option_case_eq,pair_case_eq] >>
  rpt strip_tac >>
  drule_all locals_rel_cut_envs >>
  fs[]
QED

(*Extra temporaries not mentioned in program
  do not affect evaluation
  TODO: theorem statement needs to be changed *)
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
      | SOME (Break _) => locals_rel temp rst.locals loc'
      | SOME (Continue _) => locals_rel temp rst.locals loc'
      | SOME _ => rst.locals = loc'
Proof
  completeInduct_on`prog_size (K 0) prog`>>
  rpt strip_tac>>
  Cases_on`prog` >> fs[every_var_def]
  >~[`Move`] >- suspend "Move"
  >~[`Inst`] >- suspend "Inst"
  >~[`Store`] >- suspend "Store"
  >~[`MustTerminate`] >- suspend "MustTerminate"
  >~[`Call`] >- suspend "Call"
  >~[`Seq`] >- suspend "Seq"
  >~[`If`] >- suspend "If"
  >~[`Loop`] >- suspend "Loop"
  >~[`Alloc`] >- suspend "Alloc"
  >~[`StoreConsts`] >- suspend "StoreConsts"
  >~[`Raise`] >- suspend "Raise"
  >~[`OpCurrHeap`] >- suspend "OpCurrHeap"
  >~[`Install`] >- suspend "Install"
  >~[`FFI`] >- suspend "FFI"
  >~[`ShareInst`] >- suspend "ShareInst"
  >~[`Break`] >- suspend "Break"
  >~[`Continue`] >- suspend "Continue"
  >~[`Return`] >- suspend "Return"
  >~[`Assign`] >- suspend "Assign"
  >~[`Get`] >- suspend "Get"
  >~[`Set`] >- suspend "Set"
  >~[`Tick`] >- suspend "Tick"
  >~[`LocValue`] >- suspend "LocValue"
  >~[`Skip`] >- suspend "Skip"
  >~[`CodeBufferWrite`] >- suspend "CodeBufferWrite"
  >~[`DataBufferWrite`] >- suspend "DataBufferWrite"
  >~[`PtrEq`] >- suspend "PtrEq"
QED

Resume locals_rel_evaluate_thm[Move]:
  fs[evaluate_def]>>
  DEP_REWRITE_TAC[locals_rel_get_vars_simp] >> fs[] >>
  gvs[AllCaseEqs()] >> fs[set_vars_def] >>
  irule locals_rel_alist_insert >> fs[]
QED

Resume locals_rel_evaluate_thm[Inst]:
  fs[evaluate_def] >>
  gvs[inst_def,every_var_def,every_var_inst_def,
  assign_def,AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs []) >>
  TRY (DEP_REWRITE_TAC[locals_rel_word_exp_simp] >> fs[every_var_exp_def]) >>
  TRY (rename1 `every_var_imm _ R` >> Cases_on `R` >>
  fs[every_var_imm_def,every_var_exp_def]) >>
  TRY (DEP_REWRITE_TAC[locals_rel_get_vars_simp] >> fs[]) >>
  TRY (DEP_REWRITE_TAC[locals_rel_get_var_simp] >> fs[]) >>
  simp[set_var_def] >>
  rpt (irule locals_rel_set_var >> fs[])
  >-(drule_then assume_tac mem_store_const >> gvs[])
QED

Resume locals_rel_evaluate_thm[Store]:
  fs[evaluate_def]>>
  DEP_REWRITE_TAC[locals_rel_word_exp_simp] >> fs[] >>
  DEP_REWRITE_TAC[locals_rel_get_var_simp] >> fs[] >>
  gvs[AllCaseEqs()] >> simp[set_var_def] >>
  drule mem_store_const >> fs[]
QED

Resume locals_rel_evaluate_thm[MustTerminate]:
  fs[evaluate_def] >>
  full_simp_tac(srw_ss())[PULL_FORALL,GSYM AND_IMP_INTRO]>>
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
  simp[]
QED

Resume locals_rel_evaluate_thm[Call]:
  fs[evaluate_def] >>
  DEP_REWRITE_TAC[locals_rel_get_vars_simp] >> fs[] >>
  TOP_CASE_TAC >- gvs[] >>
  TOP_CASE_TAC >- gvs[] >>
  TOP_CASE_TAC >- gvs[] >>
  PairCases_on `x'` >> fs[] >>
  TOP_CASE_TAC
  >-(
    gvs[AllCaseEqs()]
    >- fs[flush_state_def] >>
    gvs[call_env_def,flush_state_def,dec_clock_def,
      oneline bad_fun_return_def, AllCasePreds()]>>
    simp[state_component_equality]>>
    rename1`res = SOME _`>>
    Cases_on`res`>>gvs[locals_rel_def]>>
    Cases_on`x'`>>gvs[]
  )
  >>
    PairCases_on`x'`>>full_simp_tac(srw_ss())[]>>
    IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
    qmatch_goalsub_rename_tac`cut_envs (x1, x2)` >>
    Cases_on `cut_envs (x1, x2) st.locals` >>
    imp_res_tac locals_rel_cut_envs>>full_simp_tac(srw_ss())[]>>
    IF_CASES_TAC
     >-(gvs[] >> simp[state_component_equality]) >>
    full_simp_tac(srw_ss())[]>>
    fs[dec_clock_def] >> simp[state_component_equality] >>
    TOP_CASE_TAC >> gvs[locals_rel_def] >> every_case_tac
QED

Resume locals_rel_evaluate_thm[Seq]:
  fs[evaluate_def] >>
  full_simp_tac(srw_ss())[PULL_FORALL,GSYM AND_IMP_INTRO]>>
  Cases_on`evaluate (p,st)`>>full_simp_tac(srw_ss())[]>>
  first_assum(qspec_then`p` mp_tac)>>
  first_x_assum(qspec_then`p0` mp_tac)>>
  `q ≠ SOME Error` by (every_case_tac >> full_simp_tac(srw_ss())[])>>
  simp[prog_size_def]>>srw_tac[][]>>full_simp_tac(srw_ss())[every_var_def]>>res_tac>>
  simp[]>>IF_CASES_TAC>>full_simp_tac(srw_ss())[state_component_equality]>>
  Cases_on `q` >> gvs[]
QED

Resume locals_rel_evaluate_thm[If]:
  gvs[evaluate_def] >>
  DEP_REWRITE_TAC[locals_rel_get_var_simp,
  locals_rel_get_var_imm_simp] >> fs[] >>
  gvs[AllCaseEqs(),prog_size_def]
QED

Resume locals_rel_evaluate_thm[Loop]:
  simp[every_name_def] >>
  `every_name (\x. x < temp) (s0,LN)` by (simp[every_name_def] >> EVAL_TAC) >>
  `cut_env (s0,LN) loc = cut_env (s0,LN) st.locals` by (
    qpat_x_assum `evaluate _ = _` mp_tac >>
    simp[evaluate_def,cut_state_def] >>
    Cases_on `cut_env (s0,LN) st.locals` >> fs[] >>
    strip_tac >>
    imp_res_tac locals_rel_cut_env >> fs[]) >>
  `evaluate (Loop s0 p s, st with locals := loc) =
   evaluate (Loop s0 p s, st)` suffices_by (
    disch_then (fn th => rewrite_tac[th]) >> fs[] >>
    qexists_tac `rst.locals` >>
    fs[state_component_equality] >>
    every_case_tac >> simp[locals_rel_def]) >>
  simp[Once evaluate_def, cut_state_def] >>
  qpat_x_assum `evaluate (Loop _ _ _, st) = _` mp_tac >>
  simp[Once evaluate_def, cut_state_def] >>
  Cases_on `cut_env (s0,LN) st.locals` >> simp[]
QED

Resume locals_rel_evaluate_thm[Alloc]:
  gvs[evaluate_def] >>
  DEP_REWRITE_TAC[locals_rel_get_var_simp] >> fs[] >>
  gvs[AllCaseEqs()] >>
  fs[alloc_def] >> qpat_x_assum`A=(res,rst)` mp_tac>>
  ntac 6 (full_case_tac>>full_simp_tac(srw_ss())[])>>srw_tac[][]>>
  imp_res_tac  locals_rel_cut_envs>> fs[] >> gvs[] >>
  simp[state_component_equality] >>
  simp[locals_rel_def]
QED

Resume locals_rel_evaluate_thm[StoreConsts]:
  gvs[evaluate_def] >>
  DEP_REWRITE_TAC[locals_rel_get_var_simp] >> fs[] >>
  gvs[AllCaseEqs()] >> simp[set_var_def,unset_var_def] >>
  irule locals_rel_set_var >> fs[] >>
  irule locals_rel_set_var >> fs[] >>
  irule locals_rel_delete >> fs[] >>
  irule locals_rel_delete >> fs[]
QED

Resume locals_rel_evaluate_thm[Raise]:
  gvs[evaluate_def] >>
  DEP_REWRITE_TAC[locals_rel_get_var_simp] >> fs[] >>
  gvs[AllCaseEqs()] >>
  fs[jump_exc_def] >>
  simp[state_component_equality]
QED

Resume locals_rel_evaluate_thm[OpCurrHeap]:
  gvs[evaluate_def] >>
  DEP_REWRITE_TAC[locals_rel_word_exp_simp] >> fs[every_var_exp_def] >>
  gvs[AllCaseEqs()] >> fs[set_var_def] >>
  irule locals_rel_set_var >> fs[]
QED

Resume locals_rel_evaluate_thm[Install]:
  gvs[evaluate_def] >>
  DEP_REWRITE_TAC[locals_rel_get_var_simp] >> fs[] >>
  gvs[AllCaseEqs()] >>
  imp_res_tac locals_rel_cut_env>> fs[] >>
  pairarg_tac >> fs[] >>
  gvs[AllCaseEqs()] >>
  irule locals_rel_set_var >> fs[locals_rel_def]
QED

Resume locals_rel_evaluate_thm[FFI]:
  gvs[evaluate_def] >>
  DEP_REWRITE_TAC[locals_rel_get_var_simp] >> fs[] >>
  gvs[AllCaseEqs()] >>
  imp_res_tac locals_rel_cut_env>>
  simp[locals_rel_def,state_component_equality]
QED

Resume locals_rel_evaluate_thm[ShareInst]:
  gvs[evaluate_def,oneline share_inst_def] >>
  DEP_REWRITE_TAC[locals_rel_word_exp_simp] >> fs[] >>
  DEP_REWRITE_TAC[locals_rel_get_var_simp] >> fs[] >>
  gvs[AllCaseEqs()]
  >>~- ([`sh_mem_set_var`],
    fs[oneline sh_mem_set_var_def] >>
    gvs[AllCaseEqs()] >> fs[set_var_def]
    >-(irule locals_rel_set_var >> fs[]) >>
   simp[state_component_equality]) >>
  fs[sh_mem_store_def,sh_mem_store_byte_def,sh_mem_store32_def,
     sh_mem_store16_def] >>
  gvs[AllCaseEqs()] >> simp[state_component_equality]
QED

Resume locals_rel_evaluate_thm[Break]:
  fs[evaluate_def] >> gvs[]
QED

Resume locals_rel_evaluate_thm[Continue]:
  fs[evaluate_def] >> gvs[]
QED

Resume locals_rel_evaluate_thm[Get]:
  gvs[evaluate_def] >>
  gvs[AllCaseEqs()] >> simp[set_var_def] >>
  irule locals_rel_set_var >> fs[]
QED

Resume locals_rel_evaluate_thm[Set]:
  gvs[evaluate_def] >>
  DEP_REWRITE_TAC[locals_rel_word_exp_simp] >> fs[] >>
  gvs[AllCaseEqs(),state_component_equality]
QED

Resume locals_rel_evaluate_thm[Tick]:
  gvs[evaluate_def,AllCaseEqs(),dec_clock_def] >>
  simp[state_component_equality,flush_state_def]
QED

Resume locals_rel_evaluate_thm[Assign]:
  gvs[evaluate_def] >>
  DEP_REWRITE_TAC[locals_rel_word_exp_simp] >> fs[] >>
  gvs[AllCaseEqs()] >> simp[set_var_def] >>
  irule locals_rel_set_var >> fs[]
QED

Resume locals_rel_evaluate_thm[Return]:
  gvs[evaluate_def] >>
  DEP_REWRITE_TAC[locals_rel_get_var_simp,locals_rel_get_vars_simp] >> fs[] >>
  gvs[AllCaseEqs(),flush_state_def,state_component_equality]
QED

Resume locals_rel_evaluate_thm[LocValue]:
  gvs[evaluate_def,AllCaseEqs()] >> simp[set_var_def] >>
  irule locals_rel_set_var >> fs[]
QED

Resume locals_rel_evaluate_thm[Skip]:
  gvs[evaluate_def]
QED

Resume locals_rel_evaluate_thm[CodeBufferWrite]:
  gvs[evaluate_def] >>
  DEP_REWRITE_TAC[locals_rel_get_var_simp] >> fs[] >>
  gvs[AllCaseEqs(),state_component_equality]
QED

Resume locals_rel_evaluate_thm[DataBufferWrite]:
  gvs[evaluate_def] >>
  DEP_REWRITE_TAC[locals_rel_get_var_simp] >> fs[] >>
  gvs[AllCaseEqs(),state_component_equality]
QED

Resume locals_rel_evaluate_thm[PtrEq]:
  gvs[evaluate_def] >>
  DEP_REWRITE_TAC[locals_rel_get_var_simp] >> fs[] >>
  gvs[AllCaseEqs()] >> fs[set_var_def] >>
  irule locals_rel_set_var >> fs[]
QED

Finalise locals_rel_evaluate_thm;

Definition gc_fun_ok_def:
  gc_fun_ok (f:'a gc_fun_type) =
    !wl m d s wl1 m1 s1.
      Handler IN FDOM s /\
      (f (wl,m,d,s \\ Handler) = SOME (wl1,m1,s1)) ==>
      (LENGTH wl = LENGTH wl1) /\
      ~(Handler IN FDOM s1) /\
      (f (wl,m,d,s) = SOME (wl1,m1,s1 |+ (Handler,s ' Handler)))
End

Theorem push_env_dec_clock_stack:
  (push_env y opt (wordSem$dec_clock t)).stack_max =
  (push_env y opt t).stack_max /\
  (push_env y opt (wordSem$dec_clock t)).stack =
  (push_env y opt t).stack
Proof
  fs[dec_clock_def]
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
  qmatch_asmsub_rename_tac `s.stack = StackFrame lsz _ _ _ :: tlstk` >>
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

(*I'm pretty sure this is defined somewhere else too
MOVE THIS to backend props.*)
Theorem OPTION_MAP2_ADD_0:
 OPTION_MAP2 $+ m (SOME 0n) = m /\
 OPTION_MAP2 $+ (SOME 0n) m = m
Proof
  Cases_on `m` >> fs[]
QED

Theorem option_le_stack_size_nil[local]:
  option_le (stack_size []) (OPTION_MAP2 $+ (stack_size xs) opt)
Proof
  rw[OPTION_MAP2_DEF,IS_SOME_EXISTS]>>
  drule stack_size_some_at_least_one>>
  rw[stack_size_def]
QED

Theorem evaluate_option_le_stack_max_preserved:
  !p s r t. evaluate (p, s) = (r, t) /\
     option_le (OPTION_MAP2 $+ (stack_size s.stack) s.locals_size) s.stack_max ==>
     option_le (OPTION_MAP2 $+ (stack_size t.stack) t.locals_size) t.stack_max
Proof
  recInduct evaluate_ind >>
  rw[]
  >~[`Call`]
  >- (
    ntac 4 (last_x_assum mp_tac)>>
    PURE_REWRITE_TAC[AND_IMP_INTRO]>>
    qmatch_goalsub_abbrev_tac`FOO ⇒ _`>>
    disch_then (fn th => EQT_INTRO th |> PURE_ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def] |> assume_tac)>>
    qpat_x_assum`evaluate _ = _` mp_tac>>
    simp[evaluate_def] >>
    PURE_TOP_CASE_TAC >>gvs[]
    >- metis_tac[]>>
    PURE_TOP_CASE_TAC >>gvs[]
    >- metis_tac[]>>
    PURE_TOP_CASE_TAC >>gvs[]
    >- metis_tac[]>>
    rename1`find_code dest _ _ _ = SOME xx`>>
    PairCases_on`xx`>> gvs[]>>
    rename1 `find_code dest _ _ _ = SOME (clargs,exp,lsz)`>>
    TOP_CASE_TAC
    >- (
      (* tail call *)
      rpt IF_CASES_TAC >> gvs []
      >- (
        strip_tac >> fs [flush_state_def] >> rveq >> fs[state_fn_updates, stack_size_eq2] >>
        Cases_on `s.locals_size` >> Cases_on `stack_size s.stack` >> Cases_on `s.stack_max` >>
        fs [OPTION_MAP_DEF] >> drule stack_size_some_at_least_one >> DECIDE_TAC)
     >- (
       TOP_CASE_TAC >> TOP_CASE_TAC >>
       strip_tac >> rveq >> rfs [] >> fs [call_env_def] >>
       Cases_on `stack_size s.stack` >> Cases_on `lsz` >> Cases_on ` s.stack_max` >> fs [] >>
       fs [option_le_def]) >>
       strip_tac >>rveq >> fs []) >>
    (* returning call *)
    rename1`find_code dest (add_ret_loc (SOME retarg) vargs) _ _ = _` >>
    PairCases_on`retarg`>>
    rename1`find_code _ (add_ret_loc (SOME (n,names,ret_handler,l1,l2)) vargs) _ _ = _` >>
    simp[]>>
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
    gvs[]>>
    ntac 2 TOP_CASE_TAC
    >- (
      strip_tac >> rveq >>
      PRED_ASSUM is_forall kall_tac >>
      qmatch_asmsub_rename_tac  `push_env env handler _` >>
      qmatch_asmsub_rename_tac  `evaluate (exp,_)= (_,stnew)` >>
      gvs[]>>
      assume_tac push_call_option_le_stack_max_preserved >>
      res_tac >> rfs []) >>
    TOP_CASE_TAC >>
    qmatch_asmsub_rename_tac  `push_env env handler _` >>
    qmatch_asmsub_rename_tac  `evaluate (exp,_)= (_,stnew)`
    >- ( (*  SOME result *)
      gvs[]>>
      TOP_CASE_TAC
      >- (
        rw[]>>
        assume_tac push_call_option_le_stack_max_preserved >>
        res_tac >> rfs []) >>
      TOP_CASE_TAC
      >- (
        rw[]>>
        assume_tac push_call_option_le_stack_max_preserved >>
        res_tac >> rfs [])>>
      IF_CASES_TAC
      >- (
        rw[]>>gvs[]>>
        rename1`pop_env stnew = SOME popst` >>
        assume_tac push_call_option_le_stack_max_preserved >>
        res_tac >> fs [] >>
        pop_assum kall_tac >>
        drule pop_env_option_le_stack_max_preserved >>
        disch_then drule >>
        rw []) >>
      rw[]>>gvs[]>>
      assume_tac push_call_option_le_stack_max_preserved >>
      res_tac >> fs [] >>
      pop_assum kall_tac >>
      drule pop_env_option_le_stack_max_preserved >>
      disch_then drule >>
      rw [])
    >> ( (* All cases *)
      gvs[]>>every_case_tac>>gvs[]>>rw[]>>
      assume_tac push_call_option_le_stack_max_preserved >>
      res_tac >> rfs []))
  (*This case*)
  >~[`Alloc`]
  >- (
     (*  Alloc *)
     gvs[evaluate_def,alloc_def,AllCaseEqs()]
     >- (
       fs [gc_def, flush_state_def, set_store_def] >>
       irule option_le_trans >> pop_assum $ irule_at Any >>
       fs [OPTION_MAP2_ADD_0,option_le_stack_size_nil])
     >- (
       fs [gc_def, flush_state_def, set_store_def] >>
       irule option_le_trans >> pop_assum $ irule_at Any >>
       fs [OPTION_MAP2_ADD_0,option_le_stack_size_nil]) >>
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
     gvs[gc_def,AllCaseEqs()] >>
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
  >~[`Inst`]
  >- (
     gvs[evaluate_def,AllCaseEqs()] >> imp_res_tac inst_const_full >> fs[])
  >~[`Store`]
  >- (
     gvs[evaluate_def,AllCaseEqs()] >> imp_res_tac mem_store_const >> fs[])
  >~[`Tick`]
  >- (
   gvs[evaluate_def,flush_state_def,AllCaseEqs()] >>
   fs [flush_state_def] >> fs [stack_size_eq2] >>
   Cases_on `s.locals_size` >> Cases_on `stack_size s.stack` >> Cases_on `s.stack_max` >>
   fs [OPTION_MAP_DEF] >> drule stack_size_some_at_least_one >> DECIDE_TAC)
 >~[`MustTerminate`]
 >-(
   gvs[evaluate_def,flush_state_def,AllCaseEqs()] >>
   rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs()])
 >~[`Seq`]
 >- (
  gvs[evaluate_def,flush_state_def,AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs()])
 >~[`Return`]
 >- (
   gvs[evaluate_def,flush_state_def,AllCaseEqs()] >> fs[OPTION_MAP2_ADD_0] >>
   irule option_le_trans >> first_x_assum (irule_at Any) >>
   fs[option_le_add] )
  >~[`Raise`]
  >- (
   gvs[evaluate_def,jump_exc_def,AllCaseEqs()] >>fs[state_fn_updates] >>
   Cases_on `stack_size s.stack` >>  Cases_on `s.locals_size` >>  Cases_on `s.stack_max` >>
   fs [OPTION_MAP2_DEF, option_le_def] >>
   `s.handler + 1 <= LENGTH s.stack` by DECIDE_TAC >>
   drule LASTN_stack_size_SOME >>
   disch_then drule >> strip_tac >> rfs [] >>
   fs[stack_size_eq2, stack_size_frame_def])
  >~[`Loop`]
  >- (
    gvs[evaluate_def,flush_state_def,AllCaseEqs()] >>
    qpat_x_assum` _ = (_,_)` mp_tac>>
    pairarg_tac>>gvs[]>>
    reverse IF_CASES_TAC>>gvs[]
    >- (
      rw[]>>gvs[AllCaseEqs()]>>
      imp_res_tac cut_state_const>>gvs[])>>
    IF_CASES_TAC>>gvs[]
    >- (
      rw[]>>gvs[AllCaseEqs()]>>
      imp_res_tac cut_state_const>>gvs[]>>
      Cases_on `stack_size s1.stack` >>
      Cases_on `s1.stack_max` >>
      gvs[OPTION_MAP2_DEF,option_le_def] >>
      drule stack_size_some_at_least_one >>
      Cases_on `s1.locals_size` >>
      gvs[]>>EVAL_TAC>>gvs[]) >>
    rw[]>>gvs[]>>
    imp_res_tac cut_state_const>>gvs[]>>
    rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs()])
  >~[`Install`]
  >- (
     gvs[evaluate_def,flush_state_def,AllCaseEqs()] >>
     rpt (pairarg_tac >> gvs []) >> gvs[AllCaseEqs()] )
  >~[`FFI`]
  >- (
    gvs [evaluate_def,AllCaseEqs(),state_fn_updates, flush_state_def, stack_size_eq2] >>
    Cases_on `s.locals_size` >> Cases_on `stack_size s.stack` >> Cases_on `s.stack_max` >>
    fs [OPTION_MAP_DEF] >> drule stack_size_some_at_least_one >> DECIDE_TAC)
  >~[`ShareInst`]
  >- ( (* ShareInst *)
    gvs[evaluate_def,(oneline share_inst_def),AllCaseEqs()] >>
    gvs[sh_mem_store_def,sh_mem_load_def,sh_mem_store_byte_def,
        sh_mem_load16_def,sh_mem_store16_def,
        sh_mem_load_byte_def,sh_mem_load32_def,sh_mem_store32_def]
    >>~- ([`sh_mem_set_var`],
      every_case_tac
      >- (
        qmatch_asmsub_abbrev_tac `sh_mem_set_var (SOME x)` >>
        Cases_on `x` >>
        gvs[sh_mem_set_var_def,flush_state_def,state_fn_updates,stack_size_eq2] >>
        Cases_on `stack_size s.stack` >>
        Cases_on `s.stack_max` >>
        gvs[OPTION_MAP2_DEF,option_le_def] >>
        drule stack_size_some_at_least_one >>
        Cases_on `s.locals_size` >>
        gvs[]
      ) >>
      gvs[sh_mem_set_var_def]
    ) >>
    gvs[AllCaseEqs(),flush_state_def,state_fn_updates,stack_size_eq2] >>
    Cases_on `stack_size s.stack` >>
    Cases_on `s.stack_max` >>
    gvs[OPTION_MAP2_DEF,option_le_def] >>
    drule stack_size_some_at_least_one >>
    Cases_on `s.locals_size` >>
    gvs[] )
  >> TRY (gvs[evaluate_def,AllCaseEqs()] >> NO_TAC)
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
Theorem  call_env_option_le_stack_max[local]:
  option_le s.stack_max (call_env args1 ss s).stack_max
Proof
  fs[call_env_def,env_to_list_def,option_le_max_right]
QED
Theorem call_push_env_option_le_stack_max[local]:
        option_le s.stack_max
          (call_env args1 ss (push_env envs handler s)).stack_max
Proof
  gvs[call_env_def,env_to_list_def,oneline push_env_def] >>
  namedCases_on `handler` ["","whll"] >>
  TRY (PairCases_on `whll`) >> fs[option_le_max_right]
QED

Theorem evaluate_stack_max_le:
  !c s1 res s2.
  evaluate (c, s1) = (res,s2) ==>
  option_le s1.stack_max s2.stack_max
Proof
  recInduct wordSemTheory.evaluate_ind >> rpt strip_tac
  >~ [`Alloc`]
  >-(
    gvs[evaluate_def,alloc_def,flush_state_def,AllCaseEqs()] >>
    imp_res_tac gc_const >> fs[] >>
    imp_res_tac pop_env_const >> fs[] >>
    fs[push_env_def,env_to_list_def] >>
    gvs[option_le_max_right])
  >~ [`Inst`]
  >-(
    gvs[evaluate_def,AllCaseEqs()] >>
    imp_res_tac inst_const_full >> fs[])
  >~[`Store`]
  >- (
    gvs[evaluate_def,AllCaseEqs()] >>
    imp_res_tac mem_store_const >> fs[])
  >~[`Raise`]
  >- (
    gvs[evaluate_def,AllCaseEqs()] >>
    imp_res_tac jump_exc_const>> fs[])
  >~ [`ShareInst`]
  >- (
    gvs[evaluate_def,AllCaseEqs()] >>
    imp_res_tac share_inst_const >> fs[])
  >~ [`MustTerminate`]
  >- (
    gvs[evaluate_def,AllCaseEqs()] >>
    pairarg_tac >> gvs[AllCaseEqs()])
  >~ [`Seq`]
  >- (
    gvs[evaluate_def,AllCaseEqs()] >>
    pairarg_tac >> gvs[AllCaseEqs()] >>
    drule_all option_le_trans >> fs[])
  >~ [`Loop`]
  >- (
    gvs[evaluate_def,AllCaseEqs(),UNCURRY_EQ, flush_state_def] >>
    imp_res_tac cut_state_const>>rw[]>>gvs[]>>
    drule_all option_le_trans >> fs[]
   )
  >~ [`Call`]
  >-(
   pop_assum mp_tac >>
   gvs[evaluate_def,AllCaseEqs(),dec_clock_def,flush_state_def] >>
   rpt strip_tac >> gvs[] >>
   imp_res_tac pop_env_const >> fs[] >>
   fs[call_env_option_le_stack_max,call_push_env_option_le_stack_max] >>
   rpt (irule option_le_trans >>
   first_x_assum (irule_at Any) >>
   fs[call_env_option_le_stack_max,call_push_env_option_le_stack_max])
   )
  >>
  gvs[evaluate_def,AllCaseEqs(),flush_state_def] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs()]
QED

Theorem evaluate_stack_max:
  !c s1 res s2.
  evaluate (c,s1) = (res,s2) ==>
  case s1.stack_max of
    NONE => s2.stack_max = NONE
  | SOME stack_max =>
      the stack_max s2.stack_max >= stack_max
Proof
  rpt gen_tac >>
  disch_then (mp_tac o HO_MATCH_MP evaluate_stack_max_le) >>
  gvs[oneline miscTheory.the_def,oneline option_le_def] >>
  every_case_tac >> fs[]
QED

Theorem evaluate_stack_max_IS_SOME:
  ∀c s1 res s2.
    evaluate (c,s1) = (res,s2) /\ IS_SOME s2.stack_max ⇒
    IS_SOME s1.stack_max
Proof
  rw[] >> dxrule_then assume_tac evaluate_stack_max >>
  PURE_FULL_CASE_TAC >> fs[]
QED

Theorem evaluate_stack_limit:
  !c s1 res s2.
  evaluate (c,s1) = (res,s2) ==>
  s2.stack_limit = s1.stack_limit
Proof
  recInduct wordSemTheory.evaluate_ind >>
  rw[]
  >~[`Loop`] >- (
    gvs[evaluate_def,AllCaseEqs(),UNCURRY_EQ]>>
    imp_res_tac cut_state_const>>fs[]
  )
  >~[`Call`] >- (
    gvs[evaluate_def]>>
    fs[CaseEq "bool",CaseEq"option",CaseEq"prod",CaseEq"wordSem$result"] >>
    rveq >> simp[call_env_def] >>
    rpt(first_x_assum (drule_then strip_assume_tac)) >>
    fs[] >> rpt(first_x_assum (drule_then strip_assume_tac)) >>
    fs[pop_env_def,CaseEq "list",CaseEq"stack_frame",CaseEq"option",CaseEq"prod"] >>
    rveq >> fs[])>>
  gvs[evaluate_def,AllCaseEqs(),UNCURRY_EQ]>>
  drulel [alloc_const,inst_const_full,
    mem_store_const,jump_exc_const, share_inst_const] >> gvs[]
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

Definition inc_clock_def:
  inc_clock n (t:('a,'c,'ffi) wordSem$state) = t with clock := t.clock + n
End

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
  recInduct evaluate_ind >> (rpt strip_tac)
  >~ [`Call`]
  >- (
    ntac 4 (last_x_assum mp_tac)>>
    PURE_REWRITE_TAC[AND_IMP_INTRO]>>
    qmatch_goalsub_abbrev_tac`FOO ⇒ _`>>
    disch_then (fn th => EQT_INTRO th |> PURE_ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def] |> assume_tac)>>
    rpt (qpat_x_assum `evaluate _ = _` mp_tac) >>
    rpt disch_tac >>
    fs[evaluate_def,inc_clock_def] >>
    Cases_on `get_vars args s` >> fs[] >> rveq >> fs[] >>
    Cases_on `bad_dest_args dest args` >> fs[] >> rveq >> fs[] >>
    Cases_on `find_code dest (add_ret_loc ret x) s.code s.stack_size` >> fs[] >> rveq >> fs[] >>
    fs[CaseEq"prod"] >> rveq >> fs[] >> rveq >>
    Cases_on `ret`
    >- (
      fs[] >> fs[Abbr `FOO`] >>
      Cases_on `handler` >> fs[] >> rveq >> fs[] >>
      reverse(Cases_on `s.clock`) >- (
        fs[dec_clock_def,ADD1] >>
        gvs[AllCaseEqs()] >> rveq >> fs[] >>
        res_tac) >>
      fs[] >> rveq >>
      Cases_on `ck = 0` >> fs[flush_state_def] >> rveq >> fs[] >>
      gvs[AllCaseEqs()] >> rveq >> fs[] >>
      imp_res_tac evaluate_stack_max_le >>
      fs[call_env_def,option_le_max]) >>
    (* Returning calls *)
    fs[CaseEq"prod"] >> rveq >> fs[] >> rveq >> fs[] >>
    Cases_on `domain (FST names) = ∅` >> fs[] >> rveq >> fs[] >>
    Cases_on `cut_envs names s.locals` >> fs[] >> rveq >> fs[] >>
    reverse(Cases_on `s.clock`) >- (
      fs[dec_clock_def,ADD1] >>
      fs[CaseEq"prod",CaseEq"option",
         CaseEq"bool"]>> rveq >> fs[] >>
      fs[Abbr `FOO`] >> res_tac >>
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
  >~[`Seq`]
  >-(
    fs[evaluate_def,inc_clock_def] >>
    rpt (pairarg_tac >> gvs[]) >>
    first_x_assum drule_all >>
    EVERY_CASE_TAC >> gvs[] >>
    drule_then (qspec_then `ck` mp_tac) evaluate_add_clock >>
    rw[] >> gvs[]
    >- (first_x_assum drule_all >> gvs[])
    >> imp_res_tac evaluate_stack_max_le >> gvs[]
    >> (PROVE_TAC[option_le_trans]))
  >~[`Loop`]
  >-(
    gvs[evaluate_def,AllCaseEqs(),inc_clock_def,UNCURRY_EQ,flush_state_def] >>
    imp_res_tac cut_state_const>>gvs[]>>
    first_x_assum drule_all >> gvs[]
    >> imp_res_tac evaluate_stack_max_le >> gvs[]
    >> imp_res_tac evaluate_add_clock_body >> gvs[]
    >> imp_res_tac cut_state_const >> gvs[]
    >> rpt strip_tac
    >> imp_res_tac evaluate_stack_max_le >> gvs[]
    >> drule_all option_le_trans >> fs[]
    >> strip_tac
    >> last_x_assum (qspec_then `ck` mp_tac) >> gvs[dec_clock_def]
  )
  >> (* Every case except call *)
  fs[inc_clock_def, evaluate_clock_with_const] >> gvs[] >>
  gvs[evaluate_def,inc_clock_def,AllCaseEqs(),flush_state_def] >>
  rpt (pairarg_tac >> gvs[]) >> EVERY_CASE_TAC >> res_tac >> gvs[]
QED

Theorem evaluate_code_only_grows:
  !p s r t. evaluate (p,s) = (r,t) ==> subspt s.code t.code
Proof
  recInduct evaluate_ind \\ rpt conj_tac \\ rpt gen_tac \\ rpt strip_tac
  >~[`Alloc`]
  >-(gvs[evaluate_def,AllCaseEqs()]
    \\ imp_res_tac alloc_const \\ fs [])
  >~[`Inst`]
  >-(gvs[evaluate_def,AllCaseEqs()]
    \\ imp_res_tac inst_const_full \\ fs [])
  >~[`Store`]
  >-(gvs[evaluate_def,AllCaseEqs()]
    \\ imp_res_tac mem_store_const \\ fs [])
  >~[`Seq`]
  >- (
    gvs[evaluate_def,AllCaseEqs()] >>
    pairarg_tac >> gvs[AllCaseEqs()] >>
    drule_all subspt_trans >> fs[])
  >~[`Loop`]
  >- (
    gvs[evaluate_def,AllCaseEqs(),UNCURRY_EQ] >>
    imp_res_tac cut_state_const>>gvs[]>>
    metis_tac[subspt_trans])
  >~[`Raise`]
  >-(gvs[evaluate_def,AllCaseEqs()]
    \\ imp_res_tac jump_exc_const \\ fs [])
  >~[`ShareInst`]
  >-(gvs[evaluate_def,AllCaseEqs()]
    \\ imp_res_tac share_inst_const \\ fs [])
  >~[`Call`]
  >-(
    gvs[evaluate_def,AllCaseEqs()]
    \\ imp_res_tac subspt_trans \\ fs []
    \\ imp_res_tac pop_env_const \\ fs [])
  >> gvs [evaluate_def,AllCaseEqs()] >>
   rpt (pairarg_tac >> gvs[])
   >> gvs[AllCaseEqs()]
QED

(* ---- code that leaves the pointer-equality oracle alone ---- *)

Definition code_ptr_eq_free_def:
  code_ptr_eq_free ns (code : (num # 'a wordLang$prog) num_map) ⇔
    ∀n. n ∈ ns ⇒ ∃a p. lookup n code = SOME (a,p) ∧ ptr_eq_free ns p
End

Theorem code_ptr_eq_free_subspt:
  code_ptr_eq_free ns code ∧ subspt code code' ⇒ code_ptr_eq_free ns code'
Proof
  rw [code_ptr_eq_free_def, subspt_lookup] \\ metis_tac []
QED

Theorem ptr_eq_free_find_code:
  code_ptr_eq_free ns code ∧ n ∈ ns ∧
  find_code (SOME n) args code lsize = SOME (args1,expr,ps) ⇒
  ptr_eq_free ns expr
Proof
  rw [code_ptr_eq_free_def] \\ res_tac \\ gvs [find_code_def, AllCaseEqs()]
QED

Theorem evaluate_ptr_eq_free:
  ∀p s r s'.
    evaluate (p,s) = (r,s') ∧ ptr_eq_free ns p ∧ code_ptr_eq_free ns s.code ⇒
    s'.ptr_eq_oracle = s.ptr_eq_oracle
Proof
  recInduct evaluate_ind \\ rpt conj_tac \\ rpt gen_tac \\ rpt strip_tac
  >~ [`Alloc`]
  >- (gvs [evaluate_def, AllCaseEqs()] \\ imp_res_tac alloc_const \\ fs [])
  >~ [`Inst`]
  >- (gvs [evaluate_def, AllCaseEqs()] \\ imp_res_tac inst_const_full \\ fs [])
  >~ [`Store`]
  >- (gvs [evaluate_def, AllCaseEqs()] \\ imp_res_tac mem_store_const \\ fs [])
  >~ [`Raise`]
  >- (gvs [evaluate_def, AllCaseEqs()] \\ imp_res_tac jump_exc_const \\ fs [])
  >~ [`ShareInst`]
  >- (gvs [evaluate_def, AllCaseEqs()] \\ imp_res_tac share_inst_const \\ fs [])
  >~ [`PtrEq`]
  >- gvs [ptr_eq_free_def]
  >~ [`Seq`]
  >- (
    gvs [evaluate_def, AllCaseEqs(), ptr_eq_free_def]
    \\ pairarg_tac \\ gvs [AllCaseEqs()]
    \\ imp_res_tac evaluate_code_only_grows
    \\ imp_res_tac code_ptr_eq_free_subspt
    \\ gvs [])
  >~ [`Loop`]
  >- (
    gvs [evaluate_def, AllCaseEqs(), UNCURRY_EQ, ptr_eq_free_def]
    \\ imp_res_tac cut_state_const
    \\ imp_res_tac evaluate_code_only_grows
    \\ imp_res_tac code_ptr_eq_free_subspt
    \\ gvs [STOP_def, ptr_eq_free_def])
  >~ [`Call`]
  >- (
    Cases_on `dest` >- gvs [ptr_eq_free_def]
    \\ gvs [evaluate_def, AllCaseEqs(), ptr_eq_free_def]
    \\ imp_res_tac ptr_eq_free_find_code
    \\ imp_res_tac evaluate_code_only_grows
    \\ imp_res_tac code_ptr_eq_free_subspt
    \\ imp_res_tac pop_env_const
    \\ gvs [])
  \\ gvs [evaluate_def, AllCaseEqs(), ptr_eq_free_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ gvs [AllCaseEqs()]
QED

Theorem evaluate_NONE_stack_size_const:
  !p s t. evaluate (p,s) = (NONE,t) ==>
          stack_size t.stack = stack_size s.stack
Proof
  rw [] \\ qspecl_then [`p`,`s`] mp_tac evaluate_stack_swap \\ fs [] \\ rw []
  \\ imp_res_tac s_key_eq_stack_size \\ fs []
QED

Theorem env_to_list_lookup_equiv:
   env_to_list y f = (q,r) ==>
    (!n. ALOOKUP q n = lookup n y) /\
    (!x1 x2. MEM (x1,x2) q ==> lookup x1 y = SOME x2)
Proof
  fs[wordSemTheory.env_to_list_def,LET_DEF] \\ srw_tac[][]
  \\ `ALL_DISTINCT (MAP FST (toAList y))` by fs[ALL_DISTINCT_MAP_FST_toAList]
  \\ imp_res_tac (MATCH_MP PERM_ALL_DISTINCT_MAP
        (sort_PERM |> Q.ISPEC `key_val_compare` |> SPEC_ALL))
  \\ `ALL_DISTINCT (sort key_val_compare (toAList y))`
        by imp_res_tac ALL_DISTINCT_MAP
  \\ pop_assum (assume_tac o Q.SPEC `f (0:num)` o MATCH_MP PERM_list_rearrange)
  \\ imp_res_tac PERM_ALL_DISTINCT_MAP
  \\ rpt (qpat_x_assum `!x. pp ==> qq` (K all_tac))
  \\ rpt (qpat_x_assum `!x y. pp ==> qq` (K all_tac)) \\ rfs[]
  \\ rpt (pop_assum (mp_tac o Q.GEN `x` o SPEC_ALL))
  \\ rpt (pop_assum (mp_tac o SPEC ``f:num->num->num``))
  \\ Q.ABBREV_TAC `xs =
       (list_rearrange (f 0) (sort key_val_compare (toAList y)))`
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
  \\ `PERM (toAList y) l` by fs [Abbr`l`,sort_PERM]
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

Theorem env_to_list_ALL_DISTINCT_FST:
   ALL_DISTINCT (MAP FST (FST(env_to_list y perm)))
Proof
  Cases_on ‘env_to_list y perm’ >>
  metis_tac[env_to_list_ALL_DISTINCT,FST]
QED

Definition no_alloc_code_def:
  no_alloc_code (code : (num # ('a wordLang$prog)) num_map) ⇔
  ∀ k n p . lookup k code = SOME (n, p) ⇒ no_alloc p
End

Theorem no_alloc_find_code:
  ∀ code dest args lsize args1 expr ps.
    wordSem$find_code dest args code lsize = SOME (args1, expr, ps) ∧
    no_alloc_code code ⇒
    no_alloc expr
Proof
  rw[no_alloc_code_def] >> Cases_on `dest` >>
  fs[find_code_def] >>
  EVERY_CASE_TAC >> fs [] >> rveq >>
  metis_tac[]
QED

Definition no_install_code_def:
    no_install_code (code : (num # ('a wordLang$prog)) num_map) ⇔
        ∀ k n p . lookup k code = SOME (n, p) ⇒ no_install p
End

Theorem no_install_find_code:
     ∀ code dest args lsize args1 expr ps.
    no_install_code code ∧ find_code dest args code lsize = SOME (args1, expr, ps)
    ⇒ no_install expr
Proof
  rw[no_install_code_def] >> Cases_on `dest` >> fs[find_code_def] >>
  EVERY_CASE_TAC >> fs [] >> rveq >>
  metis_tac[]
QED

Theorem no_install_evaluate_const_code:
  ∀ prog s result s1 .
    evaluate (prog, s) = (result, s1) ∧
    no_install prog ∧ no_install_code s.code
    ⇒ s.code = s1.code
Proof
  recInduct evaluate_ind >> rw[] >> qpat_x_assum `evaluate _ = _` mp_tac
  >~[`MustTerminate`]
  >-(gvs[evaluate_def,AllCaseEqs()]
     >> rpt strip_tac >> gvs[no_install_def] >>
     pairarg_tac >> fs[] >> every_case_tac >> gvs[])
  >~[`Seq`]
  >- (gvs[evaluate_def,AllCaseEqs()]
     >> rpt strip_tac >> gvs[no_install_def] >>
     pairarg_tac >> fs[] >> every_case_tac >> gvs[])
  >~[`Loop`]
  >- (
    gvs[evaluate_def,no_install_def] >>
    every_case_tac >> gvs[UNCURRY_EQ]>>
    rw[]>>gvs[AllCaseEqs()]>>
    imp_res_tac cut_state_const>>
    gvs[STOP_def,no_install_def]
  )
  >~[`Call`]
  >-(
  gvs[evaluate_def,AllCaseEqs()]
  >> rpt strip_tac >> gvs[no_install_def]
  >> imp_res_tac no_install_find_code >> fs[]
  >> imp_res_tac pop_env_const >>  gvs[])
  >> gvs[evaluate_def,AllCaseEqs()]
  >> rpt strip_tac >> gvs[no_install_def]
  >- (drule alloc_const >> fs[])
  >- (drule inst_const_full >> fs[])
  >- (drule mem_store_const >> fs[])
  >- (drule jump_exc_const >> fs[])
  >- (drule share_inst_const >> fs[])
QED

Theorem get_code_labels_not_created:
  !p x. (x IN get_code_labels p) <=>
  (~ (not_created_subprogs (\sp. sp <> (wordLang$Call NONE (SOME x) [] NONE) /\
    sp <> LocValue 0 x) p))
Proof
  ho_match_mp_tac get_code_labels_ind
  \\ fs [not_created_subprogs_def]
  \\ rw []
  \\ every_case_tac \\ fs []
  \\ EQ_TAC \\ rw [] \\ fs []
QED

Definition no_mt_code_def:
  no_mt_code (code : (num # ('a wordLang$prog)) num_map) <=>
  ! k n p . lookup k code = SOME (n, p) ==> no_mt p
End

Theorem no_mt_find_code:
  ! code dest args lsize args1 expr ps.
    wordSem$find_code dest args code lsize = SOME (args1, expr, ps) /\
    no_mt_code code ==>
    no_mt expr
Proof
  rw[no_mt_code_def] >> Cases_on `dest` >>
  fs[wordSemTheory.find_code_def] >>
  EVERY_CASE_TAC >> fs [] >> rveq >>
  metis_tac[]
QED


(*** permute_swap for no_install & no_alloc ***)

Overload PERM_STACK = “λs1 s2. case (s1,s2) of
                                 (StackFrame ss l env h,StackFrame ss' l' env' h') =>
                                   ss = ss' ∧ h = h' ∧ l = l'∧  PERM env env' ∧ ALL_DISTINCT (MAP FST env)
                      ”
Theorem PERM_fromAList:
  ∀l1 l2.
    PERM l1 l2 ∧
    ALL_DISTINCT (MAP FST l1) ⇒
    fromAList l1 = fromAList l2
Proof
  rw[] >>
  dep_rewrite.DEP_REWRITE_TAC[spt_eq_thm] >>
  simp[wf_fromAList] >>
  simp[lookup_fromAList] >>
  rw[] >>
  Cases_on ‘ALOOKUP l2 n’
  >- (dxrule MEM_PERM >> strip_tac >> gvs[ALOOKUP_NONE,MEM_MAP]) >>
  drule_then assume_tac ALOOKUP_MEM >>
  match_mp_tac ALOOKUP_ALL_DISTINCT_MEM >>
  metis_tac[MEM_PERM]
QED

Theorem stack_size_perm:
  ∀l1 l2.
  LIST_REL PERM_STACK l1 l2 ⇒
  stack_size l1 = stack_size l2
Proof
  ho_match_mp_tac LIST_REL_ind >>
  rw[] >>
  rpt(PURE_FULL_CASE_TAC >> gvs[]) >>
  fs[stack_size_eq2] >>
  rename1 ‘StackFrame _ _ _ handler’ >>
  Cases_on ‘handler’ >>
  gvs[stack_size_frame_def]
QED

Theorem env_to_list_PERM:
  PERM (FST (env_to_list env perm)) (FST (env_to_list env perm'))
Proof
  rw[env_to_list_def] \\
  match_mp_tac PERM_TRANS \\
  qspec_then ‘env’ assume_tac ALL_DISTINCT_MAP_FST_toAList \\
  drule_then assume_tac ALL_DISTINCT_MAP \\
  irule_at (Pos last) PERM_list_rearrange \\
  ‘PERM (toAList env) (sort key_val_compare (toAList env))’
    by(MATCH_ACCEPT_TAC sort_PERM) \\
  conj_asm1_tac THEN1 metis_tac[ALL_DISTINCT_PERM] \\
  simp[Once PERM_SYM] \\
  match_mp_tac PERM_list_rearrange \\
  simp[]
QED

Theorem permute_swap_lemma2:
  ∀prog st perm stack.
  let (res,rst) = evaluate(prog,st) in
    res ≠ SOME Error ∧ no_alloc_code st.code ∧ no_alloc prog ∧
    no_install_code st.code ∧ no_install prog ∧
    LIST_REL PERM_STACK stack st.stack
    ⇒
    ∃perm' stack'.
      wordSem$evaluate(prog,st with <|permute := perm; stack := stack|>) = (res,rst with <|permute:=perm'; stack := stack'|>) ∧
      LIST_REL PERM_STACK stack' rst.stack
Proof
  ho_match_mp_tac (evaluate_ind |> Q.SPEC`UNCURRY P` |> SIMP_RULE (srw_ss())[] |> Q.GEN`P`) >>
  rw[] >> pairarg_tac >> rw[no_alloc_def,no_install_def]
  >~ [‘Inst’]
  >- (gvs[evaluate_def,inst_def,assign_def,word_exp_def,AllCaseEqs()] >>
      rpt (pairarg_tac >> gvs []) >>
      simp[state_component_equality]
      >-(drule mem_store_const >> fs[]))
  >~ [‘MustTerminate’]
  >- (
      gvs[evaluate_def, AllCaseEqs()] >>
      rpt (pairarg_tac >> gvs[AllCaseEqs()]) >>
      first_x_assum drule_all >>
      disch_then (qspec_then `perm` assume_tac) >>
      gvs[] >> simp[state_component_equality])
  >~ [‘Seq’]
  >- (gvs[evaluate_def, AllCaseEqs()] >>
      ntac 2 (pairarg_tac >> gvs[]) >>
      gvs[AllCaseEqs()] >>
      first_x_assum drule >>
      disch_then(qspec_then ‘perm’ mp_tac) >>
      rw[] >>
      fs[]>>
      drule_then drule no_install_evaluate_const_code >>
      simp[] >>
      disch_then $ ASSUME_TAC o GSYM >>
      simp[state_component_equality])
  >~ [‘Loop’] >- suspend "Loop"
  >~ [‘Raise’]
  >- (gvs[evaluate_def,get_var_def,AllCaseEqs(),jump_exc_def,PULL_EXISTS] >>
      imp_res_tac LIST_REL_LENGTH >>
      Cases_on ‘LASTN (st.handler + 1) stack’
      >- (‘LENGTH $ LASTN(st.handler + 1) st.stack = st.handler + 1’
            by(match_mp_tac LENGTH_LASTN >> simp[]) >>
          ‘LENGTH $ LASTN(st.handler + 1) stack = st.handler + 1’
            by(match_mp_tac LENGTH_LASTN >> simp[]) >>
          gvs[]) >>
      rename [‘LASTN _ stack = fr::ys’] >>
      drule_at (Pos last) list_rel_lastn >>
      disch_then (qspec_then ‘st.handler + 1’ mp_tac) >>
      rw[] >>
      Cases_on ‘fr’ >>
      gvs[] >>
      first_x_assum(irule_at $ Pos last) >>
      simp[state_component_equality] >>
      metis_tac[PERM_fromAList])
  >~ [‘If’]
  >- (gvs[evaluate_def, AllCaseEqs()] >>
      first_x_assum drule >>
      disch_then(qspec_then ‘perm’ mp_tac) >>
      rw[] >> simp[state_component_equality])
  >~ [`ShareInst`]
  >- (
    gvs[evaluate_def, oneline share_inst_def ,AllCaseEqs()] >>
    gvs[oneline sh_mem_set_var_def,oneline sh_mem_store_def,
        oneline sh_mem_load16_def,oneline sh_mem_store16_def,
        oneline sh_mem_store_byte_def,oneline sh_mem_store32_def,
        AllCaseEqs()] >>
    simp[state_component_equality,flush_state_def])
  >~ [‘Call’]
  >- (gvs[evaluate_def] >>
      PURE_TOP_CASE_TAC >> gvs[] >>
      IF_CASES_TAC >> gvs[] >>
      PURE_TOP_CASE_TAC >> gvs[] >>
      ntac 3 (PURE_TOP_CASE_TAC >> gvs[])
      >- (
          gvs[AllCaseEqs(),flush_state_def] >>
          simp[state_component_equality] >>
          gvs[call_env_def,dec_clock_def] >>
          ‘stack_size stack = stack_size st.stack’ by gvs[stack_size_perm] >>
          gvs[] >>
          first_x_assum match_mp_tac >>
          simp[] >>
          metis_tac[no_alloc_find_code,no_install_find_code]) >>
      PairCases_on `x'` >> gvs[] >>
      IF_CASES_TAC >> gvs[] >>
      TOP_CASE_TAC >- gvs[] >>
      IF_CASES_TAC >> gvs[]
      >- (gvs[push_env_def,call_env_def] >>
          simp[flush_state_def,state_component_equality] >>
          Cases_on ‘handler’
          >- (simp[push_env_def,ELIM_UNCURRY,stack_size_eq] >>
              ‘stack_size stack = stack_size st.stack’ by gvs[stack_size_perm] >>
              gvs[AC OPTION_MAP2_MAX_COMM OPTION_MAP2_MAX_ASSOC])
          >- (PairCases_on ‘x''’ >>
              simp[push_env_def,ELIM_UNCURRY,stack_size_eq] >>
              ‘stack_size stack = stack_size st.stack’ by gvs[stack_size_perm] >>
              gvs[AC OPTION_MAP2_MAX_COMM OPTION_MAP2_MAX_ASSOC])) >>
      qpat_x_assum ‘_ = (_,_)’ mp_tac >>
      ntac 2 $ simp[SimpL “$==>”, Once $ AllCaseEqs()] >>
      strip_tac >> gvs[] >>
      rename1 ‘evaluate _ = (SOME call_res,_)’ >>
      Cases_on ‘call_res’ >> gvs[]
      >~ [‘evaluate _ = (SOME TimeOut,_)’]
      >- (drule_all_then strip_assume_tac no_alloc_find_code >>
          drule_all_then strip_assume_tac $ ONCE_REWRITE_RULE [CONJ_SYM] no_install_find_code >>
          first_x_assum drule >>
          qmatch_goalsub_abbrev_tac ‘evaluate (_,aenv)’ >>
          disch_then(qspec_then ‘aenv.permute’ mp_tac) >>
          disch_then(qspec_then ‘aenv.stack’ mp_tac) >>
          qunabbrev_tac ‘aenv’ >>
          impl_tac >-
           (Cases_on ‘handler’ >> gvs[call_env_def,push_env_def,ELIM_UNCURRY]
            >- (simp[env_to_list_PERM,env_to_list_ALL_DISTINCT_FST]) >>
            PairCases_on ‘x''’ >> (* TODO: generated names *)
            gvs[call_env_def,push_env_def,ELIM_UNCURRY,dec_clock_def] >>
            simp[env_to_list_PERM,env_to_list_ALL_DISTINCT_FST]) >>
          rw[] >>
          ‘stack_size stack = stack_size st.stack’ by gvs[stack_size_perm] >>
          Cases_on ‘handler’ >>
          gvs[call_env_def,push_env_def,ELIM_UNCURRY,dec_clock_def,stack_size_eq]
          >- simp[state_component_equality] >>
          PairCases_on ‘x''’ >> (* TODO: generated names *)
          imp_res_tac LIST_REL_LENGTH >>
          gvs[call_env_def,push_env_def,ELIM_UNCURRY,dec_clock_def,stack_size_eq] >>
          simp[state_component_equality])
      >~ [‘evaluate _ = (SOME NotEnoughSpace,_)’]
      >- (drule_all_then strip_assume_tac no_alloc_find_code >>
          drule_all_then strip_assume_tac $ ONCE_REWRITE_RULE [CONJ_SYM] no_install_find_code >>
          first_x_assum drule >>
          qmatch_goalsub_abbrev_tac ‘evaluate (_,aenv)’ >>
          disch_then(qspec_then ‘aenv.permute’ mp_tac) >>
          disch_then(qspec_then ‘aenv.stack’ mp_tac) >>
          qunabbrev_tac ‘aenv’ >>
          impl_tac >-
           (Cases_on ‘handler’ >> gvs[call_env_def,push_env_def,ELIM_UNCURRY]
            >- simp[env_to_list_PERM,env_to_list_ALL_DISTINCT_FST] >>
            PairCases_on ‘x''’ >> (* TODO: generated names *)
            gvs[call_env_def,push_env_def,ELIM_UNCURRY,dec_clock_def] >>
            simp[env_to_list_PERM,env_to_list_ALL_DISTINCT_FST]) >>
          rw[] >>
          ‘stack_size stack = stack_size st.stack’ by gvs[stack_size_perm] >>
          Cases_on ‘handler’ >>
          gvs[call_env_def,push_env_def,ELIM_UNCURRY,dec_clock_def,stack_size_eq]
          >- simp[state_component_equality] >>
          PairCases_on ‘x''’ >> (* TODO: generated names *)
          imp_res_tac LIST_REL_LENGTH >>
          gvs[call_env_def,push_env_def,ELIM_UNCURRY,dec_clock_def,stack_size_eq] >>
          simp[state_component_equality])
      >~ [‘evaluate _ = (SOME(FinalFFI _),_)’]
      >- (drule_all_then strip_assume_tac no_alloc_find_code >>
          drule_all_then strip_assume_tac $ ONCE_REWRITE_RULE [CONJ_SYM] no_install_find_code >>
          first_x_assum drule >>
          qmatch_goalsub_abbrev_tac ‘evaluate (_,aenv)’ >>
          disch_then(qspec_then ‘aenv.permute’ mp_tac) >>
          disch_then(qspec_then ‘aenv.stack’ mp_tac) >>
          qunabbrev_tac ‘aenv’ >>
          impl_tac >-
           (Cases_on ‘handler’ >> gvs[call_env_def,push_env_def,ELIM_UNCURRY]
            >- simp[env_to_list_PERM,env_to_list_ALL_DISTINCT_FST] >>
            PairCases_on ‘x''’ >> (* TODO: generated names *)
            gvs[call_env_def,push_env_def,ELIM_UNCURRY,dec_clock_def] >>
            simp[env_to_list_PERM,env_to_list_ALL_DISTINCT_FST]) >>
          rw[] >>
          ‘stack_size stack = stack_size st.stack’ by gvs[stack_size_perm] >>
          Cases_on ‘handler’ >>
          gvs[call_env_def,push_env_def,ELIM_UNCURRY,dec_clock_def,stack_size_eq]
          >- simp[state_component_equality] >>
          PairCases_on ‘x''’ >> (* TODO: generated names *)
          imp_res_tac LIST_REL_LENGTH >>
          gvs[call_env_def,push_env_def,ELIM_UNCURRY,dec_clock_def,stack_size_eq] >>
          simp[state_component_equality])
      >~ [‘evaluate _ = (SOME(Result _ _),_)’]
      >- (gvs[call_env_def,dec_clock_def] >>
          ‘stack_size stack = stack_size st.stack’ by gvs[stack_size_perm] >>
          Cases_on ‘handler’
          >- (gvs[set_vars_def,PULL_EXISTS,push_env_def,env_to_list_def] >>
              drule_all no_alloc_find_code >>
              drule_all_then strip_assume_tac $ ONCE_REWRITE_RULE [CONJ_SYM] no_install_find_code >>
              strip_tac >>
              first_x_assum drule >>
              disch_then(drule_at $ Pos last) >>
              disch_then(qspec_then ‘λn. perm (n + 1)’ mp_tac) >>
              qmatch_goalsub_abbrev_tac ‘st1 :: stack’ >>
              disch_then(qspec_then ‘st1’ mp_tac) >>
              simp[Abbr ‘st1’] >>
              impl_tac >-
               (simp $ map (SIMP_RULE (srw_ss()) [env_to_list_def,LET_DEF]) [env_to_list_PERM,env_to_list_ALL_DISTINCT_FST]) >>
              strip_tac >>
              simp[stack_size_eq] >>
              gvs[AC OPTION_MAP2_MAX_COMM OPTION_MAP2_MAX_ASSOC,stack_size_eq,PULL_EXISTS] >>
              gvs[pop_env_def,AllCaseEqs(),PULL_EXISTS,cut_env_def] >>
              PURE_FULL_CASE_TAC >>
              gvs[PULL_EXISTS] >>
              drule_all PERM_fromAList >>
              strip_tac >>
              gvs[]
              >- (first_x_assum match_mp_tac >>
                  simp[] >>
                  drule_then drule no_install_evaluate_const_code >>
                  simp[] >>
                  disch_then $ ASSUME_TAC o GSYM >>
                  simp[] >>
                  gvs[no_alloc_def,no_install_def])
              >- (first_x_assum match_mp_tac >>
                  simp[] >>
                  drule_then drule no_install_evaluate_const_code >>
                  simp[] >>
                  disch_then $ ASSUME_TAC o GSYM >>
                  simp[] >>
                  gvs[no_alloc_def,no_install_def])) >>
          PairCases_on ‘x''’ >>
          gvs[set_vars_def,PULL_EXISTS,push_env_def,env_to_list_def] >>
          drule_all no_alloc_find_code >>
          drule_all_then strip_assume_tac $ ONCE_REWRITE_RULE [CONJ_SYM] no_install_find_code >>
          strip_tac >>
          first_x_assum drule >>
          disch_then(drule_at $ Pos last) >>
          disch_then(qspec_then ‘λn. perm (n + 1)’ mp_tac) >>
          qmatch_goalsub_abbrev_tac ‘st1 :: stack’ >>
          disch_then(qspec_then ‘st1’ mp_tac) >>
          simp[Abbr ‘st1’] >>
          impl_tac >-
            (simp $ map (SIMP_RULE (srw_ss()) [env_to_list_def,LET_DEF]) [env_to_list_PERM,env_to_list_ALL_DISTINCT_FST]) >>
          strip_tac >>
          simp[stack_size_eq] >>
          gvs[AC OPTION_MAP2_MAX_COMM OPTION_MAP2_MAX_ASSOC,stack_size_eq,PULL_EXISTS] >>
          gvs[pop_env_def,AllCaseEqs(),PULL_EXISTS,cut_env_def] >>
          PURE_FULL_CASE_TAC >>
          gvs[PULL_EXISTS] >>
          drule_all PERM_fromAList >>
          strip_tac >>
          imp_res_tac LIST_REL_LENGTH >>
          gvs[]
          >- (first_x_assum match_mp_tac >>
              simp[] >>
              drule_then drule no_install_evaluate_const_code >>
              simp[] >>
              disch_then $ ASSUME_TAC o GSYM >>
              simp[] >>
              gvs[no_alloc_def,no_install_def])
          >- (first_x_assum match_mp_tac >>
              simp[] >>
              drule_then drule no_install_evaluate_const_code >>
              simp[] >>
              disch_then $ ASSUME_TAC o GSYM >>
              simp[] >>
              gvs[no_alloc_def,no_install_def]))
      >~ [‘evaluate _ = (SOME(Exception _ _),_)’]
      >- (gvs[call_env_def,dec_clock_def] >>
          ‘stack_size stack = stack_size st.stack’ by gvs[stack_size_perm] >>
          Cases_on ‘handler’
          >- (gvs[set_var_def,PULL_EXISTS,push_env_def,env_to_list_def] >>
              drule_all no_alloc_find_code >>
              drule_all_then strip_assume_tac $ ONCE_REWRITE_RULE [CONJ_SYM] no_install_find_code >>
              strip_tac >>
              first_x_assum drule >>
              disch_then(drule_at $ Pos last) >>
              disch_then(qspec_then ‘λn. perm (n + 1)’ mp_tac) >>
              qmatch_goalsub_abbrev_tac ‘st1 :: stack’ >>
              disch_then(qspec_then ‘st1’ mp_tac) >>
              simp[Abbr ‘st1’] >>
              impl_tac >-
               (simp $ map (SIMP_RULE (srw_ss()) [env_to_list_def,LET_DEF]) [env_to_list_PERM,env_to_list_ALL_DISTINCT_FST]) >>
              strip_tac >>
              simp[stack_size_eq] >>
              gvs[AC OPTION_MAP2_MAX_COMM OPTION_MAP2_MAX_ASSOC,stack_size_eq,PULL_EXISTS] >>
              gvs[pop_env_def,AllCaseEqs(),PULL_EXISTS,cut_env_def] >>
              simp[state_component_equality]) >>
          PairCases_on ‘x''’ >>
          gvs[set_var_def,PULL_EXISTS,push_env_def,env_to_list_def] >>
          drule_all no_alloc_find_code >>
          drule_all_then strip_assume_tac $ ONCE_REWRITE_RULE [CONJ_SYM] no_install_find_code >>
          strip_tac >>
          first_x_assum drule >>
          disch_then(drule_at $ Pos last) >>
          disch_then(qspec_then ‘λn. perm (n + 1)’ mp_tac) >>
          qmatch_goalsub_abbrev_tac ‘st1 :: stack’ >>
          disch_then(qspec_then ‘st1’ mp_tac) >>
          simp[Abbr ‘st1’] >>
          impl_tac >-
           (simp $ map (SIMP_RULE (srw_ss()) [env_to_list_def,LET_DEF]) [env_to_list_PERM,env_to_list_ALL_DISTINCT_FST]) >>
          strip_tac >>
          simp[stack_size_eq] >>
          imp_res_tac LIST_REL_LENGTH >>
          gvs[AC OPTION_MAP2_MAX_COMM OPTION_MAP2_MAX_ASSOC,stack_size_eq,PULL_EXISTS] >>
          gvs[pop_env_def,AllCaseEqs(),PULL_EXISTS,cut_env_def] >>
          first_x_assum match_mp_tac >>
          simp[] >>
          drule_then drule no_install_evaluate_const_code >>
          simp[] >>
          disch_then $ ASSUME_TAC o GSYM >>
          simp[] >>
          gvs[no_alloc_def,no_install_def])
     )
  (* else *)
  >> gvs[evaluate_def,AllCaseEqs(),mem_store_def,flush_state_def,
      dec_clock_def]>>
  full_simp_tac bool_ss [GSYM state_fupdcanon] >> fs[] >>
  simp[state_component_equality]
QED

Resume permute_swap_lemma2[Loop]:
  fs[evaluate_def] >>
  Cases_on `cut_state (names,LN) st` >> fs[] >>
  `cut_state (names,LN) (st with <|permute := perm; stack := stack|>) =
   SOME (x with <|permute := perm; stack := stack|>)` by
    (fs[cut_state_def] >> every_case_tac >> gvs[]) >>
  Cases_on `evaluate(prog,x)` >> fs[STOP_def] >>
  first_x_assum(qspecl_then [`perm`,`stack`] mp_tac) >>
  impl_tac >- (conj_tac >- (strip_tac >> gvs[]) >>
               fs[cut_state_def] >> every_case_tac >> gvs[]) >>
  strip_tac >>
  qpat_x_assum `LIST_REL _ _ r.stack` mp_tac >>
  gvs[AllCaseEqs(),flush_state_def,dec_clock_def,cut_state_def] >>
  strip_tac >>
  simp[state_component_equality] >>
  TRY (first_x_assum(irule_at $ Pos last) >> simp[]) >>
  last_x_assum(qspecl_then [`perm'`,`stack'`] mp_tac) >>
  impl_tac >- (fs[] >> imp_res_tac no_install_evaluate_const_code >>
               gvs[no_alloc_def,no_install_def]) >>
  strip_tac >> gvs[dec_clock_def] >> simp[state_component_equality]
QED

Finalise permute_swap_lemma2;

Theorem permute_swap_lemma3:
  ∀prog st perm stack.
  let (res,rst) = evaluate(prog,st) in
    res ≠ SOME Error ∧ no_alloc_code st.code ∧ no_alloc prog ∧
    no_install_code st.code ∧ no_install prog ∧
    EVERY (λst. case st of StackFrame _ _ vs handler => ALL_DISTINCT(MAP FST vs)) st.stack
    ⇒
    ∃perm' stack'.
      wordSem$evaluate(prog,st with <|permute := perm|>) = (res,rst with <|permute:=perm'; stack := stack'|>) ∧
      LIST_REL PERM_STACK stack' rst.stack
Proof
  rw[] >>
  pairarg_tac >>
  rw[] >>
  qspecl_then [‘prog’,‘st’,‘perm’,‘st.stack’] assume_tac permute_swap_lemma2 >>
  gvs[] >>
  pop_assum mp_tac >> impl_tac
  >- (rename1 ‘LIST_REL _ l’ >> Induct_on ‘l’ >>
      rw[] >> TOP_CASE_TAC >> gvs[]) >>
  qmatch_goalsub_abbrev_tac ‘evaluate (_,st1)’ >>
  strip_tac >>
  qmatch_goalsub_abbrev_tac ‘evaluate (_,st2)’ >>
  ‘st1 = st2’ by rw[Abbr ‘st1’, Abbr ‘st2’, state_component_equality] >>
  gvs[] >>
  simp[state_component_equality]
QED

Theorem word_cmp_Word_Word[simp]:
  word_cmp cmp (Word c) (Word c') = SOME (word_cmp cmp c c')
Proof
  Cases_on `cmp` \\ rw [wordSemTheory.word_cmp_def,word_cmp_def]
QED
