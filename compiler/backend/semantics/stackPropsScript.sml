(*
  Properties about stackLang and its semantics
*)
Theory stackProps
Libs
  preamble
Ancestors
  stackSem stack_names backendProps


Theorem case_eq_thms =
  (pair_case_eq::
   bool_case_eq::
   map (TypeBase.case_eq_of)
        [``:'a option``,``:'a list``,``:'a word_loc``,``:'a inst``, ``:binop``,
         ``:'a reg_imm`` ,``:'a arith``,``:'a addr``,``:memop``,``:'a result``,
         ``:'a ffi_result``])
    |> LIST_CONJ

Theorem set_store_const[simp]:
   (set_store x y z).ffi = z.ffi ∧
   (set_store x y z).clock = z.clock ∧
   (set_store x y z).use_alloc = z.use_alloc ∧
   (set_store x y z).use_store = z.use_store ∧
   (set_store x y z).use_stack = z.use_stack ∧
   (set_store x y z).code = z.code ∧
   (set_store x y z).be = z.be ∧
   (set_store x y z).gc_fun = z.gc_fun ∧
   (set_store x y z).memory = z.memory ∧
   (set_store x y z).mdomain = z.mdomain ∧
   (set_store x y z).sh_mdomain = z.sh_mdomain ∧
   (set_store x y z).bitmaps = z.bitmaps ∧
   (set_store x y z).data_buffer = z.data_buffer ∧
   (set_store x y z).code_buffer = z.code_buffer ∧
   (set_store x y z).compile = z.compile ∧
   (set_store x y z).compile_oracle = z.compile_oracle ∧
   (set_store x y z).stack_space = z.stack_space ∧
   (set_store x y z).stack = z.stack
Proof
  EVAL_TAC
QED

Theorem set_store_with_const[simp]:
   set_store x y (z with clock := a) = set_store x y z with clock := a
Proof
  EVAL_TAC
QED

Theorem set_var_const[simp]:
   (set_var x y z).ffi = z.ffi ∧
   (set_var x y z).clock = z.clock ∧
   (set_var x y z).use_alloc = z.use_alloc ∧
   (set_var x y z).use_store = z.use_store ∧
   (set_var x y z).use_stack = z.use_stack ∧
   (set_var x y z).code = z.code ∧
   (set_var x y z).be = z.be ∧
   (set_var x y z).fp_regs = z.fp_regs ∧
   (set_var x y z).data_buffer = z.data_buffer ∧
   (set_var x y z).code_buffer = z.code_buffer ∧
   (set_var x y z).gc_fun = z.gc_fun ∧
   (set_var x y z).memory = z.memory ∧
   (set_var x y z).mdomain = z.mdomain ∧
   (set_var x y z).sh_mdomain = z.sh_mdomain ∧
   (set_var x y z).bitmaps = z.bitmaps ∧
   (set_var x y z).compile = z.compile ∧
   (set_var x y z).compile_oracle = z.compile_oracle ∧
   (set_var x y z).store = z.store ∧
   (set_var x y z).stack = z.stack ∧
   (set_var x y z).stack_space = z.stack_space
Proof
  EVAL_TAC
QED

Theorem set_var_with_const[simp]:
   set_var x y (z with clock := clk) = set_var x y z with clock := clk ∧
   set_var x y (z with memory := m) = set_var x y z with memory := m ∧
   set_var x y (z with ffi := ffi) = set_var x y z with ffi := ffi /\
   set_var x y (z with stack := stk) = set_var x y z with stack := stk /\
   set_var x y (z with stack_space := stk_space) = set_var x y z with stack_space := stk_space
Proof
  EVAL_TAC
QED

Theorem set_fp_var_with_const[local,simp]:
   set_fp_var x y (z with clock := k) = set_fp_var x y z with clock := k
Proof
  EVAL_TAC
QED

Theorem set_fp_var_const[local,simp]:
   (set_fp_var x y z).ffi = z.ffi ∧
   (set_fp_var x y z).clock = z.clock ∧
   (set_fp_var x y z).use_alloc = z.use_alloc ∧
   (set_fp_var x y z).use_store = z.use_store ∧
   (set_fp_var x y z).use_stack = z.use_stack ∧
   (set_fp_var x y z).code = z.code ∧
   (set_fp_var x y z).be = z.be ∧
   (set_fp_var x y z).gc_fun = z.gc_fun ∧
   (set_fp_var x y z).mdomain = z.mdomain ∧
   (set_fp_var x y z).sh_mdomain = z.sh_mdomain ∧
   (set_fp_var x y z).bitmaps = z.bitmaps ∧
   (set_fp_var x y z).compile = z.compile ∧
   (set_fp_var x y z).compile_oracle = z.compile_oracle ∧
   (set_fp_var x y z).stack = z.stack ∧
   (set_fp_var x y z).stack_space = z.stack_space
Proof
  EVAL_TAC
QED

Theorem get_fp_var_with_const[local,simp]:
   get_fp_var x (y with clock := k) = get_fp_var x y
Proof
  EVAL_TAC
QED

Theorem get_var_with_const[simp]:
  get_var r (t with clock := clk) =
  (get_var r t) /\
  get_var r (t with stack_space := stk_space) =
  (get_var r t)
Proof
  EVAL_TAC
QED

Theorem get_vars_with_const[local,simp]:
   get_vars xs (y with clock := k) = get_vars xs y
Proof
  Induct_on `xs` >> EVAL_TAC >> simp[]
QED

Theorem get_var_imm_with_const[simp]:
   get_var_imm x (y with clock := k) = get_var_imm x y
Proof
  Cases_on`x`>>EVAL_TAC
QED

Theorem set_fp_var_const[simp]:
  (set_fp_var x y z).stack_space = z.stack_space /\
  (set_fp_var x y z).stack = z.stack
Proof
  EVAL_TAC
QED

Theorem empty_env_const[simp]:
   (empty_env x).ffi = x.ffi ∧
   (empty_env x).clock = x.clock ∧
   (empty_env z).use_alloc = z.use_alloc ∧
   (empty_env z).use_store = z.use_store ∧
   (empty_env z).use_stack = z.use_stack ∧
   (empty_env z).code = z.code ∧
   (empty_env z).be = z.be ∧
   (empty_env z).gc_fun = z.gc_fun ∧
   (empty_env z).mdomain = z.mdomain ∧
   (empty_env z).sh_mdomain = z.sh_mdomain ∧
   (empty_env z).bitmaps = z.bitmaps ∧
   (empty_env z).data_buffer = z.data_buffer ∧
   (empty_env z).code_buffer = z.code_buffer ∧
   (empty_env z).compile = z.compile ∧
   (empty_env z).compile_oracle = z.compile_oracle
Proof
  EVAL_TAC
QED

Theorem empty_env_with_const[simp]:
   empty_env (x with clock := y) = empty_env x with clock := y
Proof
  EVAL_TAC
QED

Theorem alloc_const:
   alloc w s = (r,t) ⇒ t.ffi = s.ffi ∧
    t.clock = s.clock ∧
    t.use_alloc = s.use_alloc ∧
    t.use_store = s.use_store ∧
    t.use_stack = s.use_stack ∧
    t.code = s.code ∧
    t.be = s.be ∧
    t.gc_fun = s.gc_fun ∧
    t.mdomain = s.mdomain ∧
    t.sh_mdomain = s.sh_mdomain ∧
    t.bitmaps = s.bitmaps ∧
    t.compile = s.compile ∧
    t.data_buffer = s.data_buffer ∧
    t.code_buffer = s.code_buffer ∧
    t.compile_oracle = s.compile_oracle
Proof
  srw_tac[][alloc_def,gc_def,LET_THM] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][]
QED

Theorem store_const_sem_const:
   store_const_sem t1 t2 s = (r,t) ⇒ t.ffi = s.ffi ∧
    t.clock = s.clock ∧
    t.use_alloc = s.use_alloc ∧
    t.use_store = s.use_store ∧
    t.use_stack = s.use_stack ∧
    t.code = s.code ∧
    t.be = s.be ∧
    t.gc_fun = s.gc_fun ∧
    t.mdomain = s.mdomain ∧
    t.sh_mdomain = s.sh_mdomain ∧
    t.bitmaps = s.bitmaps ∧
    t.compile = s.compile ∧
    t.store = s.store ∧
    t.data_buffer = s.data_buffer ∧
    t.code_buffer = s.code_buffer ∧
    t.compile_oracle = s.compile_oracle
Proof
  gvs[store_const_sem_def,gc_def,LET_THM,AllCaseEqs()]
  \\ rw [] \\ gvs [unset_var_def,set_var_def]
QED

Theorem gc_with_const[simp]:
   gc (x with clock := k) = OPTION_MAP (λs. s with clock := k) (gc x)
Proof
   srw_tac[][gc_def] >> every_case_tac >> full_simp_tac(srw_ss())[]
QED

Theorem alloc_with_const[simp]:
   alloc x (y with clock := z) = (I ## (λs. s with clock := z))(alloc x y)
Proof
  srw_tac[][alloc_def] >> every_case_tac >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[]
QED

Theorem store_const_sem_with_const[simp]:
   store_const_sem t1 t2 (y with clock := z) =
   (I ## (λs. s with clock := z))(store_const_sem t1 t2 y)
Proof
  srw_tac[][store_const_sem_def,get_var_def] >> every_case_tac >>
  fs [unset_var_def,set_var_def]
QED

Theorem mem_load_with_const[simp]:
   mem_store x y (z with clock := k) = OPTION_MAP(λs. s with clock := k)(mem_store x y z)
Proof
  EVAL_TAC >> srw_tac[][]
QED

Theorem sh_mem_load_with_const[simp]:
  (sh_mem_load r x (y with clock := k)) = (I ## (\s. s with clock := k)) (sh_mem_load r x y)
Proof
  simp[sh_mem_load_def,ffiTheory.call_FFI_def]>>every_case_tac>>
  fs[]
QED

Theorem sh_mem_store_with_const[simp]:
  (sh_mem_store x y (z with clock := k)) = (I ## (\s. s with clock := k)) (sh_mem_store x y z)
Proof
  gs[sh_mem_store_def,ffiTheory.call_FFI_def]>>every_case_tac>>
  gs[]
QED

Theorem sh_mem_load32_with_const[simp]:
  (sh_mem_load32 r x (y with clock := k)) = (I ## (\s. s with clock := k)) (sh_mem_load32 r x y)
Proof
  simp[sh_mem_load32_def,ffiTheory.call_FFI_def]>>every_case_tac>>
  fs[]
QED

Theorem sh_mem_store32_with_const[simp]:
  (sh_mem_store32 x y (z with clock := k)) = (I ## (\s. s with clock := k)) (sh_mem_store32 x y z)
Proof
  gs[sh_mem_store32_def,ffiTheory.call_FFI_def]>>every_case_tac>>
  gs[]
QED

Theorem sh_mem_load16_with_const[simp]:
  (sh_mem_load16 r x (y with clock := k)) = (I ## (\s. s with clock := k)) (sh_mem_load16 r x y)
Proof
  simp[sh_mem_load16_def,ffiTheory.call_FFI_def]>>every_case_tac>>
  fs[]
QED

Theorem sh_mem_store16_with_const[simp]:
  (sh_mem_store16 x y (z with clock := k)) = (I ## (\s. s with clock := k)) (sh_mem_store16 x y z)
Proof
  gs[sh_mem_store16_def,ffiTheory.call_FFI_def]>>every_case_tac>>
  gs[]
QED

Theorem sh_mem_load_byte_with_const[simp]:
   (sh_mem_load_byte r x (y with clock := k)) = (I ## (\s. s with clock := k)) (sh_mem_load_byte r x y)
Proof
  simp[sh_mem_load_byte_def,ffiTheory.call_FFI_def]>>every_case_tac>>
  fs[]
QED

Theorem sh_mem_store_byte_with_const[simp]:
  (sh_mem_store_byte x y (z with clock := k)) = (I ## (\s. s with clock := k)) (sh_mem_store_byte x y z)
Proof
  gs[sh_mem_store_byte_def,ffiTheory.call_FFI_def]>>every_case_tac>>
  gs[]
QED

Theorem sh_mem_op_with_const[local,simp]:
   (sh_mem_op op x y (z with clock := k)) = (I ## (\s. s with clock := k)) (sh_mem_op op x y z)
Proof
  gs[oneline sh_mem_op_def] >>
  TOP_CASE_TAC >> gs[]
QED

Theorem word_exp_with_const[simp]:
   ∀s y k. word_exp (s with clock := k) y = word_exp s y
Proof
  ho_match_mp_tac word_exp_ind >> srw_tac[][word_exp_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[EVERY_MEM,EXISTS_MEM] >>
  unabbrev_all_tac >>
  full_simp_tac(srw_ss())[MEM_MAP,PULL_EXISTS] >>
  res_tac >> full_simp_tac(srw_ss())[IS_SOME_EXISTS] >> full_simp_tac(srw_ss())[] >>
  rpt AP_TERM_TAC >>
  simp[MAP_EQ_f] >>
  gvs [mem_load_def]
QED

Theorem assign_with_const[simp]:
   assign x y (s with clock := k) = OPTION_MAP (λs. s with clock := k) (assign x y s)
Proof
  srw_tac[][assign_def] >> every_case_tac >> full_simp_tac(srw_ss())[]
QED


Theorem inst_const:
   inst i s = SOME t ⇒
    t.ffi = s.ffi ∧
    t.clock = s.clock ∧
    t.use_alloc = s.use_alloc ∧
    t.use_store = s.use_store ∧
    t.use_stack = s.use_stack ∧
    t.code = s.code ∧
    t.be = s.be ∧
    t.gc_fun = s.gc_fun ∧
    t.mdomain = s.mdomain ∧
    t.sh_mdomain = s.sh_mdomain ∧
    t.bitmaps = s.bitmaps ∧
    t.compile = s.compile ∧
    t.compile_oracle = s.compile_oracle
Proof
  Cases_on`i`>> strip_tac >>
  gvs[inst_def,assign_def,word_exp_def,
  mem_store_def,AllCaseEqs(),UNCURRY_EQ]
QED

Theorem inst_with_const[simp]:
   inst i (s with clock := k) = OPTION_MAP (λs. s with clock := k) (inst i s)
Proof
  srw_tac[][inst_def]
  >> rpt (TOP_CASE_TAC >> gvs[mem_load_def])
QED

Theorem dec_clock_const[simp]:
   (dec_clock s).ffi = s.ffi ∧
   (dec_clock z).use_alloc = z.use_alloc ∧
   (dec_clock z).use_store = z.use_store ∧
   (dec_clock z).use_stack = z.use_stack ∧
   (dec_clock z).stack = z.stack ∧
   (dec_clock z).store = z.store ∧
   (dec_clock z).code = z.code ∧
   (dec_clock z).data_buffer = z.data_buffer ∧
   (dec_clock z).code_buffer = z.code_buffer ∧
   (dec_clock z).fp_regs = z.fp_regs ∧
   (dec_clock z).be = z.be ∧
   (dec_clock z).gc_fun = z.gc_fun ∧
   (dec_clock z).memory = z.memory ∧
   (dec_clock z).mdomain = z.mdomain ∧
   (dec_clock z).sh_mdomain = z.sh_mdomain ∧
   (dec_clock z).bitmaps = z.bitmaps ∧
   (dec_clock z).stack_space = z.stack_space ∧
   (dec_clock z).compile = z.compile ∧
   (dec_clock z).compile_oracle = z.compile_oracle
Proof
  EVAL_TAC
QED


Theorem sh_mem_op_const[simp]:
   sh_mem_op op a r s = (res,t) ⇒
    t.clock = s.clock ∧
    t.use_alloc = s.use_alloc ∧
    t.use_store = s.use_store ∧
    t.use_stack = s.use_stack ∧
    t.code = s.code ∧
    t.be = s.be ∧
    t.gc_fun = s.gc_fun ∧
    t.mdomain = s.mdomain ∧
    t.sh_mdomain = s.sh_mdomain ∧
    t.bitmaps = s.bitmaps ∧
    t.compile = s.compile ∧
    t.compile_oracle = s.compile_oracle
Proof
  strip_tac>>Cases_on`op` >>
  fs[sh_mem_op_def,sh_mem_load_def,sh_mem_store_def,
     sh_mem_load_byte_def,sh_mem_store_byte_def,
     sh_mem_load16_def,sh_mem_store16_def,
     sh_mem_load32_def,sh_mem_store32_def,
     ffiTheory.call_FFI_def] >>
  every_case_tac >> gvs[get_var_def]
QED

Theorem evaluate_consts:
   !c s r s1.
      evaluate (c,s) = (r,s1) ==>
      s1.use_alloc = s.use_alloc /\
      s1.use_store = s.use_store /\
      s1.use_stack = s.use_stack /\
      s1.be = s.be /\
      s1.gc_fun = s.gc_fun /\
      s1.mdomain = s.mdomain /\
      s1.sh_mdomain = s.sh_mdomain /\
      s1.compile = s.compile
Proof
  recInduct evaluate_ind >>
  rpt conj_tac >>
  simp[evaluate_def] >>
  rpt (gen_tac ORELSE disch_tac) >>
  gvs[AllCaseEqs(),UNCURRY_EQ] >>
  map_every imp_res_tac [alloc_const,inst_const,store_const_sem_const,sh_mem_op_const] >>
  fs[]
QED

Theorem evaluate_code_bitmaps:
   ∀c s r s1.
   evaluate (c,s) = (r,s1) ⇒
   ∃n.
    s1.compile_oracle = shift_seq n s.compile_oracle ∧
    s1.code = FOLDL union s.code (MAP (fromAList o FST o SND) (GENLIST s.compile_oracle n)) ∧
    s1.bitmaps = s.bitmaps ++ FLAT (MAP (SND o SND) (GENLIST s.compile_oracle n))
Proof
  recInduct evaluate_ind >>
  rpt conj_tac >>
  simp[evaluate_def] >>
  rpt (gen_tac ORELSE disch_tac) >>
  gvs[AllCaseEqs(),UNCURRY_EQ] >>
  map_every imp_res_tac [alloc_const,inst_const,store_const_sem_const,sh_mem_op_const] >>
  fs[shift_seq_def] >>
  TRY(qexists_tac`0` \\ fsrw_tac[ETA_ss][] \\ NO_TAC) >>
  PURE_REWRITE_TAC[GSYM FLAT_APPEND,GSYM MAP_APPEND,GSYM GENLIST_APPEND,GSYM FOLDL_APPEND] >>
  TRY ( qmatch_goalsub_abbrev_tac `s.compile_oracle (_ + N)`>>
  qexists_tac `N` >> fsrw_tac[ETA_ss][Abbr`N`] \\ NO_TAC)
QED

Theorem evaluate_mono:
    ∀c s r s1.
  evaluate (c,s) = (r,s1) ⇒
  isPREFIX s.bitmaps s1.bitmaps ∧
  subspt s.code s1.code
Proof
  rw[] \\
  imp_res_tac evaluate_code_bitmaps \\
  rw[] \\
  irule subspt_FOLDL_union
QED

Theorem evaluate_io_events_mono:
   !exps s1 res s2.
    evaluate (exps,s1) = (res, s2)
    ⇒
    s1.ffi.io_events ≼ s2.ffi.io_events
Proof
  recInduct evaluate_ind >>
  rpt conj_tac >>
  simp[evaluate_def] >>
  rpt (gen_tac ORELSE disch_tac) >>
  gvs[AllCaseEqs(),UNCURRY_EQ] >>
  map_every imp_res_tac [alloc_const,inst_const,store_const_sem_const] >>
  fs[] >> rpt (drule_then MATCH_MP_TAC IS_PREFIX_TRANS) >> fs[]
  >~[`sh_mem_op`]
  >-(
    gvs[oneline sh_mem_op_def,sh_mem_load_def,sh_mem_store_def,
    sh_mem_load32_def,sh_mem_store32_def,sh_mem_load_byte_def,
    sh_mem_load16_def,sh_mem_store16_def,
    sh_mem_store_byte_def,ffiTheory.call_FFI_def,AllCaseEqs()])
  >-(gvs[ffiTheory.call_FFI_def,AllCaseEqs()])
QED

Theorem pair_map_eq:
   (f ## g) p = (x,y) <=> (∃q r. p = (q,r) /\ x = (f q) /\ y = (g r))
Proof
  Cases_on `p` >> simp[] >>
  EQ_TAC >> simp[]
QED

Theorem evaluate_add_clock:
   ∀p s r s'.
    evaluate (p,s) = (r,s') ∧ r ≠ SOME TimeOut ⇒
    evaluate (p,s with clock := s.clock + extra) = (r,s' with clock := s'.clock + extra)
Proof
  recInduct evaluate_ind >> rpt conj_tac
  >~[`Call`]
  >-(srw_tac[][evaluate_def] >> full_simp_tac(srw_ss())[LET_THM] >>
    gvs[AllCaseEqs(),UNCURRY_EQ] >>
    fsrw_tac[ARITH_ss][dec_clock_def] >>
    rev_full_simp_tac(arith_ss)[] >>
    fs[])
  >~[`RawCall`]
  >-(srw_tac[][evaluate_def] >> full_simp_tac(srw_ss())[LET_THM] >>
    gvs[AllCaseEqs(),UNCURRY_EQ] >>
    fsrw_tac[ARITH_ss][dec_clock_def] >>
    rev_full_simp_tac(arith_ss)[] >>
    fs[])
  >~[`While`]
  >-(srw_tac[][evaluate_def] >> full_simp_tac(srw_ss())[LET_THM] >>
    gvs[AllCaseEqs(),UNCURRY_EQ] >>
    fsrw_tac[ARITH_ss][dec_clock_def] >>
    irule pair_CASES)
  >~[`Tick`]
  >-(srw_tac[][evaluate_def] >> full_simp_tac(srw_ss())[LET_THM] >>
    gvs[AllCaseEqs(),UNCURRY_EQ] >>
    fsrw_tac[ARITH_ss][dec_clock_def] >>
    rev_full_simp_tac(arith_ss)[] >>
    fs[])
  >> srw_tac[][evaluate_def] >> full_simp_tac(srw_ss())[LET_THM]
  >> gvs[AllCaseEqs(),UNCURRY_EQ]
  >> map_every imp_res_tac [alloc_const,inst_const,store_const_sem_const,sh_mem_op_const]
  >> fs[]
  >> fsrw_tac[ARITH_ss][dec_clock_def]
  >> fs[pair_map_eq]
QED

Theorem with_clock_ffi:
   (s with clock := k).ffi = s.ffi
Proof
  EVAL_TAC
QED

Theorem evaluate_add_clock_io_events_mono:
   ∀e s.
     (SND(evaluate(e,s))).ffi.io_events ≼
     (SND(evaluate(e,s with clock := s.clock + extra))).ffi.io_events
Proof
  rw[oneline SND] >> ntac 2 (TOP_CASE_TAC >> fs[]) >>
  reverse $ Cases_on `q = (SOME TimeOut)` >> gvs[]
  >- (
     drule_all evaluate_add_clock >>
     strip_tac >> gvs[]) >>
  rpt (pop_assum mp_tac) >>
  map_every qid_spec_tac (rev [`e`,`s`,`r`,`q'`,`r'`]) >>
  recInduct evaluate_ind >> rpt conj_tac
  >~ [`Seq`]
  >-
    (rpt strip_tac >> pop_assum mp_tac >>
    gvs[evaluate_def,UNCURRY_EQ,AllCaseEqs()]
    >-(imp_res_tac evaluate_add_clock >> fs[]) >>
    strip_tac >> gvs[] >>
    imp_res_tac evaluate_io_events_mono >> fs[] >>
    METIS_TAC[IS_PREFIX_TRANS])
  >~ [`While`]
  >-
    (rpt strip_tac >>
    gvs[evaluate_def,Ntimes (CONJ UNCURRY_EQ (AllCaseEqs())) 7]
    >-(
      gvs[AllCaseEqs(),UNCURRY_EQ] >>
      imp_res_tac evaluate_io_events_mono >> fs[] >>
      METIS_TAC[IS_PREFIX_TRANS]) >>
    imp_res_tac evaluate_add_clock >> fs[] >>
    gvs[AllCaseEqs()]
    >-(
    imp_res_tac evaluate_io_events_mono >> fs[] >>
    METIS_TAC[IS_PREFIX_TRANS]) >>
    fsrw_tac[ARITH_ss][dec_clock_def])
  >~ [`JumpLower`]
  >- (rpt strip_tac >>
    gvs[evaluate_def,Ntimes (CONJ UNCURRY_EQ (AllCaseEqs())) 7]
    >-(
      gvs[AllCaseEqs(),UNCURRY_EQ] >>
      imp_res_tac evaluate_io_events_mono >> fs[] >>
      METIS_TAC[IS_PREFIX_TRANS]) >>
    gvs[AllCaseEqs()]
    >- (fsrw_tac[ARITH_ss][dec_clock_def])
    >- (fsrw_tac[ARITH_ss][dec_clock_def]))
  >~ [`RawCall`]
  >- (rpt strip_tac >>
    gvs[evaluate_def,Ntimes (CONJ UNCURRY_EQ (AllCaseEqs())) 7]
    >-(
      gvs[AllCaseEqs(),UNCURRY_EQ] >>
      imp_res_tac evaluate_io_events_mono >> fs[] >>
      METIS_TAC[IS_PREFIX_TRANS]) >>
    gvs[AllCaseEqs()]
    >- fsrw_tac[ARITH_ss][dec_clock_def]
    >- fsrw_tac[ARITH_ss][dec_clock_def])
  >~ [`Call`]
  >- (rpt strip_tac >>
    gvs[evaluate_def,Ntimes (CONJ UNCURRY_EQ (AllCaseEqs())) 2]
    >- (
      gvs[Ntimes (CONJ UNCURRY_EQ (AllCaseEqs())) 2]
      >-(
        gvs[AllCaseEqs(),UNCURRY_EQ] >>
        imp_res_tac evaluate_io_events_mono >> fs[] >>
        METIS_TAC[IS_PREFIX_TRANS]) >>
      gvs[AllCaseEqs()]
      >- fsrw_tac[ARITH_ss][dec_clock_def]
      >- fsrw_tac[ARITH_ss][dec_clock_def])
    >- (
      gvs[Ntimes (CONJ UNCURRY_EQ (AllCaseEqs())) 5]
      >-(
        gvs[AllCaseEqs(),UNCURRY_EQ] >>
        imp_res_tac evaluate_io_events_mono >> fs[] >>
        METIS_TAC[IS_PREFIX_TRANS]) >>
      gvs[Ntimes (CONJ UNCURRY_EQ (AllCaseEqs())) 3]
      >-(
        imp_res_tac evaluate_add_clock >> fs[] >>
        fsrw_tac[ARITH_ss][dec_clock_def] >>
        gvs[] >> gvs[AllCaseEqs()])
      >-(
        imp_res_tac evaluate_add_clock >> fs[] >>
        fsrw_tac[ARITH_ss][dec_clock_def] >>
        gvs[] >> gvs[AllCaseEqs()]) >>
      fsrw_tac[ARITH_ss][dec_clock_def] >>
      gvs[Ntimes (CONJ UNCURRY_EQ (AllCaseEqs())) 3]
      >-(
        gvs[AllCaseEqs(),UNCURRY_EQ] >>
        imp_res_tac evaluate_io_events_mono >> fs[] >>
        METIS_TAC[IS_PREFIX_TRANS])
      >-(
        gvs[AllCaseEqs(),UNCURRY_EQ] >>
        imp_res_tac evaluate_io_events_mono >> fs[] >>
        METIS_TAC[IS_PREFIX_TRANS])))
  >~ [`ShMemOp`]
  >- (rpt strip_tac >>
     imp_res_tac evaluate_io_events_mono >>
     gvs[evaluate_def,AllCaseEqs()] >>
     fsrw_tac[ARITH_ss][dec_clock_def] >>
     gvs[pair_map_eq])
  >> (rpt (strip_tac) >> gvs[evaluate_def,AllCaseEqs(),UNCURRY_EQ] >>
  NO_TAC)
QED

Definition clock_neutral_def:
  (clock_neutral (Seq p1 p2) <=> clock_neutral p1 /\ clock_neutral p2) /\
  (clock_neutral (LocValue _ _ _) <=> T) /\
  (clock_neutral (Halt _) <=> T) /\
  (clock_neutral (Inst _) <=> T) /\
  (clock_neutral (Skip) <=> T) /\
  (clock_neutral (If _ _ _ p1 p2) <=> clock_neutral p1 /\ clock_neutral p2) /\
  (clock_neutral r <=> F)
End

Theorem inst_clock_neutral[local]:
  (inst i s = SOME t ==> inst i (s with clock := k) = SOME (t with clock := k)) /\
    (inst i s = NONE ==> inst i (s with clock := k) = NONE)
Proof
  Cases_on `i` \\ full_simp_tac(srw_ss())[inst_def,assign_def,word_exp_def,set_var_def,LET_DEF,set_fp_var_def]
  \\ srw_tac[][state_component_equality]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[word_exp_def]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[word_exp_def]
  \\ full_simp_tac(srw_ss())[mem_load_def,get_var_def,mem_store_def,get_fp_var_def]
  \\ srw_tac[][state_component_equality]
QED

Theorem inst_clock_neutral_ffi[local]:
  (inst i s = SOME t ==> inst i (s with ffi := k) = SOME (t with ffi := k)) /\
    (inst i s = NONE ==> inst i (s with ffi := k) = NONE)
Proof
  Cases_on `i` \\ full_simp_tac(srw_ss())[inst_def,assign_def,word_exp_def,set_var_def,LET_DEF,state_component_equality,set_fp_var_def]>>
  reverse full_case_tac>>fs[]>>
  TRY
    (qmatch_goalsub_abbrev_tac`get_vars _ _`>>
    fs[get_vars_def,get_var_def]>>
    rpt (BasicProvers.TOP_CASE_TAC>>fs[state_component_equality]))
  \\ rpt (srw_tac[][state_component_equality]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[word_exp_def]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[word_exp_def]
  \\ full_simp_tac(srw_ss())[mem_load_def,get_var_def,mem_store_def,get_fp_var_def]
  \\ srw_tac[][state_component_equality])
QED

Theorem evaluate_clock_neutral:
   !prog s res t.
      evaluate (prog,s) = (res,t) /\ clock_neutral prog ==>
      evaluate (prog,s with clock := c) = (res,t with clock := c)
Proof
  recInduct evaluate_ind \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[evaluate_def,get_var_def,clock_neutral_def]
  THEN1 (every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[])
  THEN1 (every_case_tac \\ imp_res_tac inst_clock_neutral \\ full_simp_tac(srw_ss())[])
  THEN1 (Cases_on `evaluate (c1,s)` \\ full_simp_tac(srw_ss())[LET_THM] \\ every_case_tac \\ full_simp_tac(srw_ss())[])
  \\ `get_var_imm ri (s with clock := c) = get_var_imm ri s` by
         (Cases_on `ri` \\ full_simp_tac(srw_ss())[get_var_imm_def,get_var_def])
  \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[set_var_def]
QED

Theorem evaluate_ffi_neutral:
   !prog s res t.
      evaluate (prog,s) = (res,t) /\ clock_neutral prog ==>
      evaluate (prog,s with ffi := c) = (res,t with ffi := c)
Proof
  recInduct evaluate_ind \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[evaluate_def,get_var_def,clock_neutral_def]
  THEN1 (every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[empty_env_def])
  THEN1 (every_case_tac \\ imp_res_tac inst_clock_neutral_ffi \\ full_simp_tac(srw_ss())[])
  THEN1 (Cases_on `evaluate (c1,s)` \\ full_simp_tac(srw_ss())[LET_THM] \\ every_case_tac \\ full_simp_tac(srw_ss())[])
  \\ `get_var_imm ri (s with ffi := c) = get_var_imm ri s` by
         (Cases_on `ri` \\ full_simp_tac(srw_ss())[get_var_imm_def,get_var_def])
  \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[set_var_def]
QED

Theorem semantics_Terminate_IMP_PREFIX:
   semantics start s1 = Terminate x l ==> isPREFIX s1.ffi.io_events l
Proof
  full_simp_tac(srw_ss())[semantics_def,LET_DEF] \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[]
  \\ DEEP_INTRO_TAC some_intro \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ imp_res_tac evaluate_io_events_mono \\ full_simp_tac(srw_ss())[]
QED

Theorem semantics_Diverge_IMP_LPREFIX:
   semantics start s1 = Diverge l ==> LPREFIX (fromList s1.ffi.io_events) l
Proof
  simp[semantics_def] >> IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
  DEEP_INTRO_TAC some_intro >> srw_tac[][] >>
  qmatch_abbrev_tac`LPREFIX l1 (build_lprefix_lub l2)` >>
  `l1 ∈ l2 ∧ lprefix_chain l2` suffices_by metis_tac[build_lprefix_lub_thm,lprefix_lub_def] >>
  conj_tac >- (
    unabbrev_all_tac >> simp[] >>
    qexists_tac`0`>>full_simp_tac(srw_ss())[evaluate_def] >>
    CASE_TAC >> full_simp_tac(srw_ss())[] ) >>
  simp[Abbr`l2`] >>
  simp[Once(GSYM o_DEF),IMAGE_COMPOSE] >>
  match_mp_tac prefix_chain_lprefix_chain >>
  simp[prefix_chain_def,PULL_EXISTS] >>
  qx_genl_tac[`k1`,`k2`] >>
  qspecl_then[`k1`,`k2`]mp_tac LESS_EQ_CASES >>
  simp[LESS_EQ_EXISTS] >>
  metis_tac[evaluate_add_clock_io_events_mono,
            EVAL``(s with clock := k).clock``,
            EVAL``((s with clock := k) with clock := k2) = (s with clock := k2)``]
QED

Theorem map_bitmap_length:
    ∀a b c x y z.
  map_bitmap a b c = SOME(x,y,z) ⇒
  LENGTH c = LENGTH x + LENGTH z ∧
  LENGTH x = LENGTH a
Proof
  Induct>>rw[]>>
  Cases_on`b`>>TRY(Cases_on`h`)>>Cases_on`c`>>
  fs[map_bitmap_def]>>
  TRY(qpat_x_assum`A=x` (SUBST_ALL_TAC o SYM))>>
  TRY(qpat_x_assum`A=y` (SUBST_ALL_TAC o SYM))>>
  fs[LENGTH_NIL]>>
  pop_assum mp_tac>>every_case_tac>>rw[]>>res_tac>>
  fs[]>>DECIDE_TAC
QED

Theorem dec_stack_length:
    ∀bs enc orig_stack new_stack.
  dec_stack bs enc orig_stack = SOME new_stack ⇒
  LENGTH orig_stack = LENGTH new_stack
Proof
  ho_match_mp_tac stackSemTheory.dec_stack_ind>>
  fs[stackSemTheory.dec_stack_def,LENGTH_NIL]>>rw[]>>
  pop_assum mp_tac>>
  Cases_on`w`>>fs[full_read_bitmap_def]>>
  every_case_tac>>fs[]>>
  rw[]>>
  imp_res_tac map_bitmap_length>>
  simp[]>>metis_tac[]
QED

Definition extract_labels_def:
  (extract_labels (Call ret dest h) =
    (case ret of
      NONE => []
    | SOME (ret_handler,_,l1,l2) =>
      let ret_rest = extract_labels ret_handler in
    (case h of
      NONE => [(l1,l2)] ++ ret_rest
    | SOME (prog,l1',l2') =>
      let h_rest = extract_labels prog in
      [(l1,l2);(l1',l2')]++ret_rest++h_rest))) ∧
  (extract_labels (While _ _ _ s1) = extract_labels s1) ∧
  (extract_labels (Seq s1 s2) =
    extract_labels s1 ++ extract_labels s2) ∧
  (extract_labels (If cmp r1 ri e2 e3) =
    (extract_labels e2 ++ extract_labels e3)) ∧
  (extract_labels _ = [])
End

Theorem find_code_IMP_get_labels:
   find_code d r code = SOME e ==>
    get_labels e SUBSET loc_check code
Proof
  Cases_on `d`
  \\ fs [stackSemTheory.find_code_def,SUBSET_DEF,IN_DEF,
         loc_check_def,FORALL_PROD]
  \\ every_case_tac \\ fs []
  \\ metis_tac []
QED

Definition addr_ok_def:
  addr_ok op (Addr a w) c ⇔
  (reg_ok a c ∧
   if op ∈ {Load; Store; Load32; Store32}
   then addr_offset_ok c w
   else if op IN {Load16; Store16}
   then hw_offset_ok c w ∧ c.ISA ≠ Ag32 else byte_offset_ok c w)
End

(* TODO: This is not updated for Install, CBW and DBW *)
(* asm_ok out of stack_names *)
Definition stack_asm_ok_def:
  (stack_asm_ok c ((Inst i):'a stackLang$prog) ⇔ asm$inst_ok i c) ∧
  (stack_asm_ok c (ShMemOp op r ad) ⇔ reg_ok r c ∧ addr_ok op ad c) ∧
  (stack_asm_ok c (CodeBufferWrite r1 r2) ⇔ r1 < c.reg_count ∧ r2 < c.reg_count ∧ ¬MEM r1 c.avoid_regs ∧ ¬MEM r2 c.avoid_regs) ∧
  (stack_asm_ok c (Seq p1 p2) ⇔ stack_asm_ok c p1 ∧ stack_asm_ok c p2) ∧
  (stack_asm_ok c (If cmp n r p p') ⇔ stack_asm_ok c p ∧ stack_asm_ok c p') ∧
  (stack_asm_ok c (While cmp n r p) ⇔ stack_asm_ok c p) ∧
  (stack_asm_ok c (Raise n) ⇔ n < c.reg_count ∧ ¬MEM n c.avoid_regs) ∧
  (stack_asm_ok c (Return n) ⇔ n < c.reg_count ∧ ¬MEM n c.avoid_regs) ∧
  (stack_asm_ok c (Call r tar h) ⇔
    (case tar of INR r => r < c.reg_count ∧ ¬MEM r c.avoid_regs | _ => T) ∧
    case r of
      (SOME (p,_,_,_) => stack_asm_ok c p ∧
      case h of
      SOME (p',_,_) => stack_asm_ok c p'
      | _ => T)
    | _ => T) ∧
  (stack_asm_ok c _ ⇔  T)
End

Definition reg_name_def:
  reg_name r c ⇔
  r < c.reg_count - LENGTH (c.avoid_regs)
End

(* inst requirements just before stack_names *)

Definition reg_imm_name_def:
  (reg_imm_name b (Reg r) c ⇔ reg_name r c) ∧
  (reg_imm_name b (Imm w) c ⇔ c.valid_imm b w)
End

Definition arith_name_def:
  (arith_name (Binop b r1 r2 ri) (c:'a asm_config) ⇔
    (c.two_reg_arith ⇒ r1 = r2 ∨ b = Or ∧ ri = Reg r2) ∧ reg_name r1 c ∧
    reg_name r2 c ∧ reg_imm_name (INL b) ri c) ∧
  (arith_name (Shift l r1 r2 (Imm i)) c ⇔
    (c.two_reg_arith ⇒ r1 = r2) ∧ reg_name r1 c ∧ reg_name r2 c ∧
    (i = 0w ⇒ l = Lsl) ∧ w2n i < dimindex (:α)) ∧
  (arith_name (Shift l r1 r2 (Reg r3)) c ⇔
    (c.two_reg_arith ⇒ r1 = r2) ∧ reg_name r1 c ∧
     reg_name r2 c ∧ reg_name r3 c ∧ (c.ISA = x86_64 ⇒ r3 = 4)) ∧
  (arith_name (Div r1 r2 r3) c ⇔
    (reg_name r1 c ∧ reg_name r2 c ∧ reg_name r3 c ∧
    c.ISA ∈ {ARMv8; MIPS; RISC_V})) ∧
  (arith_name (LongMul r1 r2 r3 r4) c ⇔
    reg_name r1 c ∧ reg_name r2 c ∧ reg_name r3 c ∧ reg_name r4 c ∧
    (c.ISA = x86_64 ⇒ r1 = 3 ∧ r2 = 0 ∧ r3 = 0) ∧
    (c.ISA = ARMv7 ⇒ r1 ≠ r2) ∧
    (c.ISA = ARMv8 ∨ c.ISA = RISC_V ∨ c.ISA = Ag32 ⇒ r1 ≠ r3 ∧ r1 ≠ r4)) ∧
  (arith_name (LongDiv r1 r2 r3 r4 r5) c ⇔
    c.ISA = x86_64 ∧ r1 = 0 ∧ r2 = 3 ∧ r3 = 3 ∧ r4 = 0 ∧
    reg_name r5 c) ∧
  (arith_name (AddCarry r1 r2 r3 r4) c ⇔
    (c.two_reg_arith ⇒ r1 = r2) ∧ reg_name r1 c ∧ reg_name r2 c ∧
    reg_name r3 c ∧ reg_name r4 c ∧
    (c.ISA = MIPS ∨ c.ISA = RISC_V ⇒ r1 ≠ r3 ∧ r1 ≠ r4)) ∧
  (arith_name (AddOverflow r1 r2 r3 r4) c ⇔
    (c.two_reg_arith ⇒ r1 = r2) ∧ reg_name r1 c ∧ reg_name r2 c ∧
    reg_name r3 c ∧ reg_name r4 c ∧
    (c.ISA = MIPS ∨ c.ISA = RISC_V ⇒ r1 ≠ r3)) ∧
  (arith_name (SubOverflow r1 r2 r3 r4) c ⇔
    (c.two_reg_arith ⇒ r1 = r2) ∧ reg_name r1 c ∧ reg_name r2 c ∧
    reg_name r3 c ∧ reg_name r4 c ∧
    (c.ISA = MIPS ∨ c.ISA = RISC_V ⇒ r1 ≠ r3))
End

(* We could actually almost use fp_ok, except this needs to check reg_ok for
   some registers as well *)
Definition fp_name_def:
  (fp_name (FPLess r d1 d2) c <=>
      reg_name r c /\ fp_reg_ok d1 c /\ fp_reg_ok d2 c) /\
  (fp_name (FPLessEqual r d1 d2) c <=>
      reg_name r c /\ fp_reg_ok d1 c /\ fp_reg_ok d2 c) /\
  (fp_name (FPEqual r d1 d2) c <=>
      reg_name r c /\ fp_reg_ok d1 c /\ fp_reg_ok d2 c) /\
  (fp_name (FPAbs d1 d2) c <=>
      (c.two_reg_arith ==> (d1 <> d2)) /\ fp_reg_ok d1 c /\ fp_reg_ok d2 c) /\
  (fp_name (FPNeg d1 d2) c <=>
      (c.two_reg_arith ==> (d1 <> d2)) /\ fp_reg_ok d1 c /\ fp_reg_ok d2 c) /\
  (fp_name (FPSqrt d1 d2) c <=> fp_reg_ok d1 c /\ fp_reg_ok d2 c) /\
  (fp_name (FPAdd d1 d2 d3) c <=>
      (c.two_reg_arith ==> (d1 = d2)) /\
      fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c) /\
  (fp_name (FPSub d1 d2 d3) c <=>
      (c.two_reg_arith ==> (d1 = d2)) /\
      fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c) /\
  (fp_name (FPMul d1 d2 d3) c <=>
      (c.two_reg_arith ==> (d1 = d2)) /\
      fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c) /\
  (fp_name (FPDiv d1 d2 d3) c <=>
      (c.two_reg_arith ==> (d1 = d2)) /\
      fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c) /\
  (fp_name (FPFma d1 d2 d3) c <=>
      (c.ISA = ARMv7) /\
      2 < c.fp_reg_count /\
      fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c) /\
  (fp_name (FPMov d1 d2) c <=> fp_reg_ok d1 c /\ fp_reg_ok d2 c) /\
  (fp_name (FPMovToReg r1 r2 d) (c : 'a asm_config) <=>
      reg_name r1 c /\ ((dimindex(:'a) = 32) ==> r1 <> r2 /\ reg_name r2 c) /\
      fp_reg_ok d c) /\
  (fp_name (FPMovFromReg d r1 r2) (c : 'a asm_config) <=>
      reg_name r1 c /\ ((dimindex(:'a) = 32) ==> r1 <> r2 /\ reg_name r2 c) /\
      fp_reg_ok d c) /\
  (fp_name (FPToInt d1 d2) c <=> fp_reg_ok d1 c /\ fp_reg_ok d2 c) /\
  (fp_name (FPFromInt d1 d2) c <=> fp_reg_ok d1 c /\ fp_reg_ok d2 c)
End

Definition addr_name_def:
  addr_name m (Addr r w) c ⇔
  reg_name r c ∧
  (if m IN {Load; Store; Load32; Store32}
   then addr_offset_ok c w
   else if m IN {Load16; Store16}
   then hw_offset_ok c w ∧ c.ISA ≠ Ag32
   else byte_offset_ok c w)
End

Definition inst_name_def:
  (inst_name c (Const r w) ⇔ reg_name r c) ∧
  (inst_name c (Mem m r a) ⇔ reg_name r c ∧ addr_name m a c) ∧
  (inst_name c (Arith x) ⇔ arith_name x c) ∧
  (inst_name c (FP f) ⇔ fp_name f c) ∧
  (inst_name _ _ = T)
End

Definition stack_asm_name_def:
  (stack_asm_name c ((Inst i):'a stackLang$prog) ⇔ inst_name c i) ∧
  (stack_asm_name c (OpCurrHeap b r1 r2) ⇔
    (c.two_reg_arith ⇒ r1 = r2) ∧ reg_name r1 c ∧ reg_name r2 c) ∧
  (stack_asm_name c (ShMemOp op r a) ⇔ reg_name r c ∧ addr_name op a c) ∧
  (stack_asm_name c (CodeBufferWrite r1 r2) ⇔ reg_name r1 c ∧ reg_name r2 c) ∧
  (stack_asm_name c (DataBufferWrite r1 r2) ⇔ reg_name r1 c ∧ reg_name r2 c) ∧
  (stack_asm_name c (Seq p1 p2) ⇔ stack_asm_name c p1 ∧ stack_asm_name c p2) ∧
  (stack_asm_name c (If cmp n r p p') ⇔ stack_asm_name c p ∧ stack_asm_name c p') ∧
  (stack_asm_name c (While cmp n r p) ⇔ stack_asm_name c p) ∧
  (stack_asm_name c (Raise n) ⇔ reg_name n c) ∧
  (stack_asm_name c (Return n) ⇔ reg_name n c) ∧
  (stack_asm_name c (Call r tar h) ⇔
    (case tar of INR r => reg_name r c | _ => T) ∧
    case r of
      (SOME (p,_,_,_) => stack_asm_name c p ∧
      case h of
      SOME (p',_,_) => stack_asm_name c p'
      | _ => T)
    | _ => T) ∧
  (stack_asm_name c _ ⇔  T)
End

Definition fixed_names_def:
  fixed_names names c =
  if c.ISA = x86_64 then
    find_name names 3 = 2 ∧
    find_name names 4 = 1 ∧
    find_name names 0 = 0
  else T
End

Definition stack_asm_remove_def:
  (stack_asm_remove c ((Get n s):'a stackLang$prog) ⇔ reg_name n c) ∧
  (stack_asm_remove c (OpCurrHeap binop v src) ⇔ reg_name v c ∧ reg_name src c) ∧
  (stack_asm_remove c (Set s n) ⇔ reg_name n c) ∧
  (stack_asm_remove c (StackStore n n0) ⇔ reg_name n c) ∧
  (stack_asm_remove c (StackStoreAny n n0) ⇔ reg_name n c ∧ reg_name n0 c) ∧
  (stack_asm_remove c (StackLoad n n0) ⇔ reg_name n c) ∧
  (stack_asm_remove c (StackLoadAny n n0) ⇔ reg_name n c ∧ reg_name n0 c) ∧
  (stack_asm_remove c (StackGetSize n) ⇔ reg_name n c) ∧
  (stack_asm_remove c (StackSetSize n) ⇔ reg_name n c) ∧
  (stack_asm_remove c (BitmapLoad n n0) ⇔ reg_name n c ∧ reg_name n0 c) ∧
  (stack_asm_remove c (StoreConsts n n0 _) ⇔ reg_name n c ∧ reg_name n0 c) ∧
  (stack_asm_remove c (Seq p1 p2) ⇔ stack_asm_remove c p1 ∧ stack_asm_remove c p2) ∧
  (stack_asm_remove c (If cmp n r p p') ⇔ stack_asm_remove c p ∧ stack_asm_remove c p') ∧
  (stack_asm_remove c (While cmp n r p) ⇔ stack_asm_remove c p) ∧
  (stack_asm_remove c (Call r tar h) ⇔
    (case r of
      (SOME (p,_,_,_) => stack_asm_remove c p ∧
      case h of
      SOME (p',_,_) => stack_asm_remove c p'
      | _ => T)
    | _ => T)) ∧
  (stack_asm_remove c _ ⇔  T)
End

(* Various syntactic properties required for correctness of the stackLang passes
  All of these are trivially preserved from word_to_stack until the pass that
  they are used.
*)

(* stack_alloc requires that Allocs have a fixed argument
   TODO: this can also be a semantic check...
*)

Definition alloc_arg_def:
  (alloc_arg (Alloc v) <=> (v = 1)) /\
  (alloc_arg ((Seq p1 p2):'a stackLang$prog) <=>
     alloc_arg p1 /\ alloc_arg p2) /\
  (alloc_arg ((If c r ri p1 p2):'a stackLang$prog) <=>
     alloc_arg p1 /\ alloc_arg p2) /\
  (alloc_arg (While c r ri p1) <=>
     alloc_arg p1) /\
  (alloc_arg (Call x1 _ x2) <=>
     (case x1 of | SOME (y,r,_,_) => alloc_arg y | NONE => T) /\
     (case x2 of SOME (y,_,_) => alloc_arg y | NONE => T)) /\
  (alloc_arg _ <=> T)
End

(* stack_remove requires that all register arguments are bounded by k *)

Definition reg_bound_exp_def[simp]:
  (reg_bound_exp (Var n) k ⇔ n < k) ∧
  (reg_bound_exp (Load e) k ⇔ reg_bound_exp e k) ∧
  (reg_bound_exp (Shift _ e _) k ⇔ reg_bound_exp e k) ∧
  (reg_bound_exp (Lookup _) _ ⇔ F) ∧
  (reg_bound_exp (Op _ es) k ⇔ EVERY (λe. reg_bound_exp e k) es) ∧
  (reg_bound_exp _ _ ⇔ T)
Termination
  WF_REL_TAC`measure ((exp_size ARB) o FST)` \\ simp[]
   \\ Induct \\ simp[wordLangTheory.exp_size_def]
   \\ srw_tac[][] \\ res_tac \\ simp[]
End

Definition reg_bound_inst_def[simp]:
  (reg_bound_inst (Mem _ n (Addr a _)) k ⇔ n < k ∧ a < k) ∧
  (reg_bound_inst (Const n _) k ⇔ n < k) ∧
  (reg_bound_inst (Arith (Shift _ n r2 _)) k ⇔ r2 < k ∧ n < k) ∧
  (reg_bound_inst (Arith (Binop _ n r2 ri)) k ⇔ r2 < k ∧ n < k ∧ (case ri of Reg r1 => r1 < k | _ => T)) ∧
  (reg_bound_inst (Arith (Div r1 r2 r3)) k ⇔ r1 < k ∧ r2 < k ∧ r3 < k) ∧
  (reg_bound_inst (Arith (AddCarry r1 r2 r3 r4)) k ⇔ r1 < k ∧ r2 < k ∧ r3 < k ∧ r4 < k) ∧
  (reg_bound_inst (Arith (AddOverflow r1 r2 r3 r4)) k ⇔ r1 < k ∧ r2 < k ∧ r3 < k ∧ r4 < k) ∧
  (reg_bound_inst (Arith (SubOverflow r1 r2 r3 r4)) k ⇔ r1 < k ∧ r2 < k ∧ r3 < k ∧ r4 < k) ∧
  (reg_bound_inst (Arith (LongMul r1 r2 r3 r4)) k ⇔ r1 < k ∧ r2 < k ∧ r3 < k ∧ r4 < k) ∧
  (reg_bound_inst (Arith (LongDiv r1 r2 r3 r4 r5)) k ⇔ r1 < k ∧ r2 < k ∧ r3 < k ∧ r4 < k ∧ r5 < k) ∧
  (reg_bound_inst (FP (FPLess r f1 f2)) k ⇔ r < k) ∧
  (reg_bound_inst (FP (FPLessEqual r f1 f2)) k ⇔ r < k) ∧
  (reg_bound_inst (FP (FPEqual r f1 f2)) k ⇔ r < k) ∧
  (reg_bound_inst (FP (FPMovToReg r1 r2 d)) k ⇔ r1 < k ∧ r2 < k) ∧
  (reg_bound_inst (FP (FPMovFromReg d r1 r2)) k ⇔ r1 < k ∧ r2 < k) ∧
  (reg_bound_inst _ _ ⇔ T)
End

Definition reg_bound_def:
  (reg_bound (Halt v1) k <=>
     v1 < k) /\
  (reg_bound (Raise v1) k <=>
     v1 < k) /\
  (reg_bound (Get v1 n) k <=>
     v1 < k) /\
  (reg_bound (OpCurrHeap op v1 v2) k <=>
     v1 < k ∧ v2 < k) /\
  (reg_bound (Set n v1) k <=>
     v1 < k /\ n <> BitmapBase) /\
  (reg_bound (LocValue v1 l1 l2) k <=>
     v1 < k) /\
  (reg_bound (StoreConsts t1 t2 _) k <=>
     3 < k ∧ t1 < k ∧ t2 < k) /\
  (reg_bound (Return v1) k <=>
     v1 < k) /\
  (reg_bound (JumpLower v1 v2 dest) k <=>
     v1 < k /\ v2 < k) /\
  (reg_bound ((Seq p1 p2):'a stackLang$prog) k <=>
     reg_bound p1 k /\ reg_bound p2 k) /\
  (reg_bound ((If c r ri p1 p2):'a stackLang$prog) k <=>
     r < k /\ (case ri of Reg n => n < k | _ => T) /\
     reg_bound p1 k /\ reg_bound p2 k) /\
  (reg_bound (While c r ri p1) k <=>
     r < k /\ (case ri of Reg n => n < k | _ => T) /\
     reg_bound p1 k) /\
  (reg_bound (Halt n) k <=> n < k) /\
  (reg_bound (FFI ffi_index ptr' len' ptr2' len2' ret') k <=>
     ptr' < k /\ len' < k /\ ptr2' < k /\ len2' < k /\ ret' < k) /\
  (reg_bound (Call x1 dest x2) k <=>
     (case dest of INR i => i < k | _ => T) /\
     (case x1 of
      | NONE => T
      | SOME (y,r,_,_) => reg_bound y k /\ r < k /\
                          (case x2 of SOME (y,_,_) => reg_bound y k | NONE => T))) /\
  (reg_bound (Install ptr len dptr dlen ret) k ⇔
    ptr < k ∧ len < k ∧ dptr < k ∧ dlen < k ∧ ret < k) ∧
  (reg_bound (ShMemOp op r (Addr a _)) k ⇔ r < k ∧ a < k) ∧
  (reg_bound (CodeBufferWrite r1 r2) k ⇔
    r1 < k ∧ r2 < k) ∧
  (reg_bound (DataBufferWrite r1 r2) k ⇔
    r1 < k ∧ r2 < k) ∧
  (reg_bound (BitmapLoad r v) k <=> r < k /\ v < k) /\
  (reg_bound (Inst i) k <=> reg_bound_inst i k) /\
  (reg_bound (StackStore r _) k <=> r < k) /\
  (reg_bound (StackSetSize r) k <=> r < k) /\
  (reg_bound (StackGetSize r) k <=> r < k) /\
  (reg_bound (StackLoad r n) k <=> r < k) /\
  (reg_bound (StackLoadAny r r2) k <=> r < k /\ r2 < k) /\
  (reg_bound (StackStore r n) k <=> r < k) /\
  (reg_bound (StackStoreAny r r2) k <=> r < k /\ r2 < k) /\
  (reg_bound _ k <=> T)
End

(* Finally, stack_to_lab requires correct arguments for Call/FFI/Install calls *)
Definition call_args_def:
  (call_args ((Seq p1 p2):'a stackLang$prog) ptr len ptr2 len2 ret <=>
     call_args p1 ptr len ptr2 len2 ret /\
     call_args p2 ptr len ptr2 len2 ret) /\
  (call_args ((If c r ri p1 p2):'a stackLang$prog) ptr len ptr2 len2 ret <=>
     call_args p1 ptr len ptr2 len2 ret /\
     call_args p2 ptr len ptr2 len2 ret) /\
  (call_args (While c r ri p1) ptr len ptr2 len2 ret <=>
     call_args p1 ptr len ptr2 len2 ret) /\
  (call_args (Halt n) ptr len ptr2 len2 ret <=> (n = ptr)) /\
  (call_args (FFI ffi_index ptr' len' ptr2' len2' ret') ptr len ptr2 len2 ret <=>
     ptr' = ptr /\ len' = len /\ ptr2' = ptr2 /\ len2' = len2 /\ ret' = ret) /\
  (call_args (Call x1 _ x2) ptr len ptr2 len2 ret <=>
     (case x1 of
      | NONE => T
      | SOME (y,r,_,_) =>
          call_args y ptr len ptr2 len2 ret /\ r = ret /\
          (case x2 of SOME (y,_,_) => call_args y ptr len ptr2 len2 ret | NONE => T))) /\
  (call_args (Install ptr' len' _ _ ret') ptr len ptr2 len2 ret <=>
     ptr' = ptr /\ len' = len /\ ret' = ret) /\
  (call_args _ ptr len ptr2 len2 ret <=> T)
End

(* TODO: remove "stack_" prefix from these functions *)

Definition stack_get_handler_labels_def[simp]:
  (stack_get_handler_labels n (Call r d h) =
    (case r of SOME (x,_,_) => stack_get_handler_labels n x  ∪
      (case h of SOME (x,l1,l2) => (if l1 = n then {(l1,l2)} else {}) ∪ (stack_get_handler_labels n x) | _ => {})
    | _ => {})
  ) ∧
  (stack_get_handler_labels n (Seq p1 p2) = stack_get_handler_labels n p1 ∪ stack_get_handler_labels n p2) ∧
  (stack_get_handler_labels n (If _ _ _ p1 p2) = stack_get_handler_labels n p1 ∪ stack_get_handler_labels n p2) ∧
  (stack_get_handler_labels n (While _ _ _ p) = stack_get_handler_labels n p) ∧
  (stack_get_handler_labels n _ = {})
End

Definition get_code_labels_def[simp]:
  (get_code_labels (Call r d h) =
    (case d of INL x => {(x,0n)} | _ => {}) ∪
    (case r of SOME (x,_,_) => get_code_labels x | _ => {}) ∪
    (case h of SOME (x,_,_) => get_code_labels x | _ => {})) ∧
  (get_code_labels (Seq p1 p2) = get_code_labels p1 ∪ get_code_labels p2) ∧
  (get_code_labels (If _ _ _ p1 p2) = get_code_labels p1 ∪ get_code_labels p2) ∧
  (get_code_labels (While _ _ _ p) = get_code_labels p) ∧
  (get_code_labels (JumpLower _ _ t) = {(t,0)}) ∧
  (get_code_labels (RawCall t) = {(t,1)}) ∧
  (get_code_labels (LocValue _ l1 l2) = {(l1,l2)}) ∧
  (get_code_labels (StoreConsts _ _ (SOME l)) = {(l,0)}) ∧
  (get_code_labels _ = {})
End

(* elabs gives a set of existing code labels *)
Definition stack_good_code_labels_def:
  stack_good_code_labels p elabs ⇔
  BIGUNION (IMAGE get_code_labels (set (MAP SND p))) ⊆
  BIGUNION (set (MAP (λ(n,pp). stack_get_handler_labels n pp) p)) ∪
  IMAGE (λn. n,0) (set (MAP FST p)) ∪ IMAGE (λn. n,0) elabs ∪
  IMAGE (λn. n,1) (set (MAP FST p)) ∪ IMAGE (λn. n,1) elabs
End

Definition stack_good_handler_labels_def:
  stack_good_handler_labels p ⇔
  restrict_nonzero (BIGUNION (IMAGE get_code_labels (set (MAP SND p)))) ⊆
  BIGUNION (set (MAP (λ(n,pp). stack_get_handler_labels n pp) p)) ∪
  IMAGE (λn. n,1) (set (MAP FST p))
End

Definition no_install_def:
  (no_install (Call r d h) =
    ((case r of SOME (x,_,_) => no_install x | _ => T) /\
    (case h of SOME (x,_,_) => no_install x | _ => T))) /\
  (no_install (Seq p1 p2) = (no_install p1 /\ no_install p2)) /\
  (no_install (If _ _ _ p1 p2) = (no_install p1 /\ no_install p2)) /\
  (no_install (While _ _ _ p) = no_install p) /\
  (no_install (Install _ _ _ _ _) = F) /\
  (no_install _ = T)
End

Definition no_shmemop_def:
  (no_shmemop (Call r d h) =
    ((case r of SOME (x,_,_) => no_shmemop x | _ => T) /\
    (case h of SOME (x,_,_) => no_shmemop x | _ => T))) /\
  (no_shmemop (Seq p1 p2) = (no_shmemop p1 /\ no_shmemop p2)) /\
  (no_shmemop (If _ _ _ p1 p2) = (no_shmemop p1 /\ no_shmemop p2)) /\
  (no_shmemop (While _ _ _ p) = no_shmemop p) /\
  (no_shmemop (ShMemOp _ _ _) = F) /\
  (no_shmemop _ = T)
End
