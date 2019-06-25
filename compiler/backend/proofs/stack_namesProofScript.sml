(*
  Correctness proof for stack_names
*)
open preamble
     stack_namesTheory
     stackSemTheory stackPropsTheory
local open dep_rewrite in end

val _ = bring_to_front_overload"prog_comp"{Name="prog_comp",Thy="stack_names"};
val _ = bring_to_front_overload"comp"{Name="comp",Thy="stack_names"};

val _ = new_theory"stack_namesProof";

val rename_state_def = Define `
  rename_state compile_rest f s =
   s with
   <| regs := MAP_KEYS (find_name f) s.regs
    ; code := fromAList (compile f (toAList s.code))
    ; compile := compile_rest
    ; compile_oracle := (I ## compile f ## I) o s.compile_oracle
    ; ffi_save_regs := IMAGE (find_name f) s.ffi_save_regs
    |>`

Theorem rename_state_with_clock:
   rename_state c f (s with clock := k) = rename_state c f s with clock := k
Proof
  EVAL_TAC
QED

Theorem rename_state_const[simp]:
   (rename_state c f s).memory = s.memory ∧
   (rename_state c f s).be = s.be ∧
   (rename_state c f s).mdomain = s.mdomain ∧
   (rename_state c f s).code_buffer = s.code_buffer ∧
   (rename_state c f s).clock = s.clock ∧
   (rename_state c f s).compile = c ∧
   (rename_state c f s).use_stack = s.use_stack ∧
   (rename_state c f s).fp_regs = s.fp_regs
Proof
  EVAL_TAC
QED

Theorem rename_state_with_memory:
   rename_state c f (s with memory := k) = rename_state c f s with memory := k
Proof
  EVAL_TAC
QED

Theorem dec_clock_rename_state:
   dec_clock (rename_state c x y) = rename_state c x (dec_clock y)
Proof
  EVAL_TAC >> simp[state_component_equality]
QED

Theorem mem_load_rename_state[simp]:
   mem_load x (rename_state c f s) = mem_load x s
Proof
  EVAL_TAC
QED

Theorem mem_store_rename_state[simp]:
   mem_store x y (rename_state c f s) = OPTION_MAP (rename_state c f) (mem_store x y s)
Proof
  EVAL_TAC >> rw[] >> EVAL_TAC >> rw[]
QED

Theorem get_var_find_name[simp]:
   BIJ (find_name f) UNIV UNIV ==>
    get_var (find_name f v) (rename_state c f s) = get_var v s
Proof
  fs [get_var_def,rename_state_def,FLOOKUP_DEF,MAP_KEYS_def]
  \\ rpt strip_tac \\ imp_res_tac BIJ_IMP_11 \\ fs []
  \\ rw [] \\ fs [] \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ match_mp_tac (MAP_KEYS_def |> SPEC_ALL |> CONJUNCT2 |> MP_CANON)
  \\ fs [INJ_DEF]
QED

Theorem get_var_imm_find_name[simp]:
   BIJ (find_name f) UNIV UNIV ⇒
   get_var_imm (ri_find_name f ri) (rename_state c f s) =
   get_var_imm ri s
Proof
  Cases_on`ri`>>EVAL_TAC>>strip_tac>>
  dep_rewrite.DEP_REWRITE_TAC[FLOOKUP_MAP_KEYS] >>
  conj_tac >- metis_tac[INJ_DEF,BIJ_IMP_11,IN_UNIV] >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  fs[GSYM tlookup_def] >>
  metis_tac[BIJ_DEF,INJ_DEF,IN_UNIV,FLOOKUP_DEF]
QED

Theorem FLOOKUP_rename_state_find_name[simp]:
   BIJ (find_name f) UNIV UNIV ⇒
   FLOOKUP (rename_state c f s).regs (find_name f k) = FLOOKUP s.regs k
Proof
  rw[BIJ_DEF] >>
  rw[rename_state_def] >>
  simp[FLOOKUP_MAP_KEYS_MAPPED]
QED

val prog_comp_eta = Q.prove(
  `prog_comp f = λ(x,y). (x,comp f y)`,
  rw[prog_comp_def,FUN_EQ_THM,FORALL_PROD])

Theorem find_code_rename_state[simp]:
   BIJ (find_name f) UNIV UNIV ⇒
   find_code (dest_find_name f dest) (rename_state c f s).regs (rename_state c f s).code =
   OPTION_MAP (comp f) (find_code dest s.regs s.code)
Proof
  strip_tac >>
  Cases_on`dest`>>rw[find_code_def,rename_state_def,dest_find_name_def] >- (
    simp[lookup_fromAList,compile_def,prog_comp_eta,ALOOKUP_MAP,ALOOKUP_toAList] >>
    metis_tac[] ) >>
  dep_rewrite.DEP_REWRITE_TAC[FLOOKUP_MAP_KEYS] >>
  conj_tac >- metis_tac[BIJ_IMP_11,INJ_DEF,IN_UNIV] >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  reverse conj_tac >- (
    rw[] >> simp[FLOOKUP_DEF] >> rw[] >> metis_tac[] ) >>
  rw[] >>
  `x = y` by metis_tac[BIJ_IMP_11] >>
  rw[FLOOKUP_DEF] >>
  simp[lookup_fromAList,compile_def,prog_comp_eta,ALOOKUP_MAP,ALOOKUP_toAList] >>
  CASE_TAC >> simp[] >>
  CASE_TAC >> simp[] >>
  metis_tac[]
QED

Theorem set_var_find_name:
   BIJ (find_name f) UNIV UNIV ⇒
   rename_state c f (set_var x y z) =
   set_var (find_name f x) y (rename_state c f z)
Proof
  rw[set_var_def,rename_state_def,state_component_equality] >>
  match_mp_tac MAP_KEYS_FUPDATE >>
  metis_tac[BIJ_IMP_11,INJ_DEF,IN_UNIV]
QED

Theorem set_fp_var_find_name:
    rename_state c f (set_fp_var x y z) =
   set_fp_var x y (rename_state c f z)
Proof
  rw[set_fp_var_def,rename_state_def,state_component_equality]
QED

Theorem inst_rename:
   BIJ (find_name f) UNIV UNIV ⇒
   inst (inst_find_name f i) (rename_state c f s) =
   OPTION_MAP (rename_state c f) (inst i s)
Proof
  rw[inst_def] >>
  rw[inst_find_name_def] >>
  CASE_TAC >> fs[] >- (
    EVAL_TAC >>
    simp[state_component_equality] >>
    dep_rewrite.DEP_REWRITE_TAC[MAP_KEYS_FUPDATE] >>
    conj_tac >- (
      fs[BIJ_IFF_INV,INJ_DEF] >>
      metis_tac[] ) >>
    simp[fmap_eq_flookup,FLOOKUP_UPDATE] >>
    gen_tac >>
    `INJ (find_name f) (FDOM s.regs) UNIV` by
      metis_tac[BIJ_IMP_11,INJ_DEF,IN_UNIV] >>
    simp[FLOOKUP_MAP_KEYS] >>
    DEEP_INTRO_TAC some_intro >> simp[] >>
    simp[tlookup_def] ) >>
  CASE_TAC >> fs[assign_def,word_exp_def] >>
  CASE_TAC >> rfs[get_vars_def,get_fp_var_def] >>
  every_case_tac >> fs[LET_THM,word_exp_def,ri_find_name_def] >>
  rw[] >> fs[] >> rfs[] >> rw[set_var_find_name,set_fp_var_find_name]
  \\ every_case_tac \\ fs [wordLangTheory.word_op_def]
  \\ rw [] \\ fs [] \\ fs [BIJ_DEF,INJ_DEF] \\ res_tac
  \\ fs [rename_state_with_memory]
QED

Theorem MAP_FST_compile[simp]:
   MAP FST (stack_names$compile f c) = MAP FST c
Proof
  rw[compile_def,MAP_MAP_o,MAP_EQ_f,prog_comp_def,FORALL_PROD]
QED

Theorem domain_rename_state_code[simp]:
   domain (rename_state c f s).code = domain s.code
Proof
  rw[rename_state_def,domain_fromAList,toAList_domain,EXTENSION]
QED

val comp_STOP_While = Q.prove(
  `comp f (STOP (While cmp r1 ri c1)) =
    STOP (While cmp (find_name f r1) (ri_find_name f ri) (comp f c1))`,
  simp [Once comp_def] \\ fs [STOP_def]);

val get_labels_comp = Q.prove(
  `!f p. get_labels (comp f p) = get_labels p`,
  HO_MATCH_MP_TAC stack_namesTheory.comp_ind \\ rw []
  \\ Cases_on `p` \\ once_rewrite_tac [comp_def] \\ fs [get_labels_def]
  \\ every_case_tac \\ fs []);

val loc_check_rename_state = Q.prove(
  `loc_check (rename_state c f s).code (l1,l2) =
    loc_check s.code (l1,l2)`,
  fs [loc_check_def,rename_state_def,lookup_fromAList,compile_def,prog_comp_def]
  \\ simp[lookup_fromAList,compile_def,prog_comp_eta,ALOOKUP_MAP,ALOOKUP_toAList]
  \\ fs [PULL_EXISTS,get_labels_comp]);

val comp_correct = Q.prove(
  `!p s r t.
     evaluate (p,s) = (r,t) /\ BIJ (find_name f) UNIV UNIV /\
     ~s.use_alloc /\ ~s.use_store /\ ~s.use_stack /\
     s.compile = (λcfg. c cfg o (stack_names$compile f))
     ==>
     evaluate (comp f p, rename_state c f s) = (r, rename_state c f t)`,
  recInduct evaluate_ind \\ rpt strip_tac
  THEN1 (fs [evaluate_def,comp_def] \\ rpt var_eq_tac)
  THEN1 (fs [evaluate_def,comp_def] \\ rpt var_eq_tac \\ CASE_TAC \\ fs []
         \\ rw [] \\ fs [rename_state_def,empty_env_def])
  THEN1 (fs [evaluate_def,comp_def,rename_state_def] \\ rpt var_eq_tac \\ fs [])
  THEN1 (fs [evaluate_def,comp_def] >>
    every_case_tac >> fs[] >> rveq >> fs[] >>
    imp_res_tac inst_rename >> fs[])
  THEN1 (fs [evaluate_def,comp_def,rename_state_def] >> rveq >> fs[])
  THEN1 (fs [evaluate_def,comp_def,rename_state_def] >> rveq >> fs[])
  THEN1 (fs [evaluate_def,comp_def,rename_state_def] \\ rw []
         \\ fs [] \\ rw [] \\ fs [empty_env_def,dec_clock_def])
  THEN1
   (simp [Once evaluate_def,Once comp_def]
    \\ fs [evaluate_def,LET_DEF] \\ rpt (pairarg_tac \\ fs [])
    \\ rw [] \\ fs [] \\ rfs [] \\ fs []
    \\ imp_res_tac evaluate_consts \\ fs [])
  THEN1 (fs [evaluate_def,comp_def] \\ rpt var_eq_tac \\ every_case_tac \\ fs [])
  THEN1 (fs [evaluate_def,comp_def] \\ rpt var_eq_tac \\ every_case_tac \\ fs [])
  THEN1 (
    fs[evaluate_def] >>
    simp[Once comp_def] >>
    simp[evaluate_def] >>
    BasicProvers.TOP_CASE_TAC >> fs[] >>
    BasicProvers.TOP_CASE_TAC >> fs[] >>
    BasicProvers.TOP_CASE_TAC >> fs[] >>
    BasicProvers.TOP_CASE_TAC >> fs[] >>
    BasicProvers.TOP_CASE_TAC >> fs[] )
  THEN1 (* While *)
   (simp [Once comp_def] \\ fs [evaluate_def,get_var_def]
    \\ reverse every_case_tac
    \\ fs [LET_THM]
    \\ qpat_x_assum`(λ(x,y). _) _ = _`mp_tac
    \\ pairarg_tac \\ fs []
    \\ Cases_on `res = NONE` \\ fs []
    \\ Cases_on `s1.clock = 0` \\ fs []
    \\ strip_tac
    THEN1 (rpt var_eq_tac \\ fs [rename_state_def,empty_env_def])
    \\ `(rename_state c f s1).clock <> 0` by fs [rename_state_def] \\ fs []
    \\ fs [comp_STOP_While] \\ rfs []
    \\ fs [dec_clock_def,rename_state_def]
    \\ imp_res_tac evaluate_consts \\ fs [])
  (* JumpLower *)
  THEN1 (
    simp[Once comp_def] >>
    fs[evaluate_def] >>
    BasicProvers.TOP_CASE_TAC >> fs[] >>
    BasicProvers.TOP_CASE_TAC >> fs[] >>
    BasicProvers.TOP_CASE_TAC >> fs[] >>
    BasicProvers.TOP_CASE_TAC >> fs[] >>
    BasicProvers.TOP_CASE_TAC >> fs[] >>
    fs[find_code_def] >>
    simp[Once rename_state_def] >>
    simp[lookup_fromAList] >>
    BasicProvers.TOP_CASE_TAC >> fs[] >- (
      imp_res_tac ALOOKUP_FAILS >>
      qpat_x_assum`_ = (r,_)`mp_tac >>
      BasicProvers.TOP_CASE_TAC >> fs[] >>
      `dest ∈ domain s.code` by metis_tac[domain_lookup] >>
      `¬MEM dest (MAP FST (compile f (toAList s.code)))` by (
        simp[MEM_MAP,EXISTS_PROD] ) >>
      fs[] >>
      metis_tac[toAList_domain] ) >>
    simp[Once rename_state_def] >>
    imp_res_tac ALOOKUP_MEM >>
    `MEM dest (MAP FST (compile f (toAList s.code)))` by (
      simp[MEM_MAP,EXISTS_PROD] >> metis_tac[]) >>
    fs[] >>
    `dest ∈ domain s.code` by metis_tac[toAList_domain] >>
    fs[domain_lookup] >> fs[] >>
    IF_CASES_TAC >> fs[] >- (rveq >> EVAL_TAC >> simp[state_component_equality] ) >>
    qpat_x_assum`_ = (r,_)`mp_tac >>
    BasicProvers.TOP_CASE_TAC >> fs[] >>
    fs[compile_def,MEM_MAP,EXISTS_PROD,prog_comp_def] >>
    fs[MEM_toAList] >> rveq >>
    fs[dec_clock_rename_state] >>
    BasicProvers.TOP_CASE_TAC >> fs[])
  (* Call *)
  THEN1 (
    simp[Once comp_def] >>
    fs[evaluate_def] >>
    BasicProvers.TOP_CASE_TAC >> fs[] >- (
      pop_assum mp_tac >>
      reverse BasicProvers.TOP_CASE_TAC >> fs[] >- (
        BasicProvers.TOP_CASE_TAC >> simp[] >>
        BasicProvers.TOP_CASE_TAC >> simp[] >>
        BasicProvers.TOP_CASE_TAC >> simp[] ) >>
      qpat_x_assum`_ = (r,_)`mp_tac >>
      BasicProvers.TOP_CASE_TAC >> fs[] >>
      reverse(Cases_on`handler`)>>fs[]>-(
        split_pair_case_tac >> simp[] ) >>
      simp[Once rename_state_def] >>
      IF_CASES_TAC >> fs[] >- (
        rw[] >> EVAL_TAC >> simp[state_component_equality] ) >>
      simp[dec_clock_rename_state] >>
      BasicProvers.TOP_CASE_TAC >> fs[] >>
      BasicProvers.TOP_CASE_TAC >> fs[] ) >>
    split_pair_case_tac >> simp[] >>
    rveq >> pop_assum mp_tac >>
    BasicProvers.TOP_CASE_TAC >> fs[] >>
    split_pair_case_tac >> simp[] >>
    strip_tac >> rveq >> fs[] >>
    simp[Once rename_state_def] >>
    simp[DOMSUB_MAP_KEYS] >>
    simp[
      find_code_rename_state
      |> Q.GEN`s` |> Q.SPEC`s with regs := s.regs \\ lr`
      |> SIMP_RULE (std_ss)[Once rename_state_def] |> SIMP_RULE (srw_ss())[]
      |> SIMP_RULE std_ss [EVAL``(rename_state c f (s with regs := x)).code = (rename_state c f s).code``|>EQT_ELIM]] >>
    qpat_x_assum`_ = (r,_)`mp_tac >>
    BasicProvers.TOP_CASE_TAC >> fs[] >>
    simp[Once rename_state_def] >>
    IF_CASES_TAC >> fs[] >- (
      rw[] >> EVAL_TAC >> simp[state_component_equality] ) >>
    simp[GSYM set_var_find_name,dec_clock_rename_state] >>
    BasicProvers.TOP_CASE_TAC >> fs[] >>
    BasicProvers.TOP_CASE_TAC >> fs[] >>
    BasicProvers.TOP_CASE_TAC >> fs[] >- (
      rw[] >> rfs[] >>
      first_x_assum match_mp_tac >>
      imp_res_tac evaluate_consts >>
      fs[rename_state_def] ) >>
    BasicProvers.TOP_CASE_TAC >> fs[] >>
    BasicProvers.TOP_CASE_TAC >> fs[] >>
    BasicProvers.TOP_CASE_TAC >> fs[] >>
    BasicProvers.TOP_CASE_TAC >> fs[] >>
    strip_tac >> fs[] >>
    first_x_assum match_mp_tac >>
    imp_res_tac evaluate_consts >>
    fs[rename_state_def] )
  THEN1 (
  (* Install *)
    simp[Once comp_def] >>
    fs[evaluate_def] >>
    ntac 8 (TOP_CASE_TAC \\ fs[]) \\
    pairarg_tac>>fs[]>>
    pairarg_tac>>fs[]>>
    qpat_x_assum`(rename_state c f s).compile_oracle _ = _`mp_tac>>
    simp[Once rename_state_def]>> strip_tac>>fs[]>>
    ntac 2 (TOP_CASE_TAC>>fs[])>>
    qpat_x_assum`_ = (r,t)` mp_tac>>
    TOP_CASE_TAC \\
    rveq>>fs[compile_def]>>
    ntac 2 (TOP_CASE_TAC>>fs[])>>
    TOP_CASE_TAC>>simp[prog_comp_eta]>>
    fs[rename_state_def,shift_seq_def]>>
    TOP_CASE_TAC>>fs[]>>strip_tac>>
    fs[state_component_equality]>>
    CONJ_TAC>-(
      qpat_x_assum`_=t.regs` sym_sub_tac>>
      dep_rewrite.DEP_REWRITE_TAC[DRESTRICT_MAP_KEYS_IMAGE] >>
      conj_tac >- metis_tac[BIJ_DEF] \\
      dep_rewrite.DEP_REWRITE_TAC[MAP_KEYS_FUPDATE] \\
      fs[INJ_DEF,BIJ_DEF])>>
    CONJ_TAC>-(
      qpat_x_assum`_ = t.compile_oracle` sym_sub_tac>>
      simp[FUN_EQ_THM])>>
    qpat_x_assum`_ = t.code` sym_sub_tac>>
    simp[compile_def,GSYM prog_comp_eta] \\
    dep_rewrite.DEP_REWRITE_TAC[spt_eq_thm] \\
    simp[wf_union,wf_fromAList] \\
    simp[lookup_union,lookup_fromAList,ALOOKUP_MAP,prog_comp_eta,ALOOKUP_toAList] \\
    gen_tac \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[] )
  THEN1 (
  (* CodeBufferWrite *)
    simp[Once comp_def] \\
    fs[evaluate_def] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[] \\ rw[] \\
    EVAL_TAC)
  THEN1 (
  (* DataBufferWrite is not needed anymore *)
    simp[Once comp_def] \\
    fs[evaluate_def])
  (* FFI *)
  THEN1 (
    simp[Once comp_def] >>
    fs[evaluate_def] >>
    rpt(BasicProvers.TOP_CASE_TAC >> fs[]) >>
    simp[Once rename_state_def] >>
    simp[Once rename_state_def] >>
    simp[Once rename_state_def] >>
    fs[LET_THM] >>
    simp[EVAL``(rename_state c f s).ffi``] >>
    fs[] >> rveq >> fs[rename_state_def,state_component_equality] >>
    dep_rewrite.DEP_REWRITE_TAC[DRESTRICT_MAP_KEYS_IMAGE] >>
    metis_tac[BIJ_DEF])
  THEN1 (
    simp[Once comp_def] >> fs[evaluate_def,loc_check_rename_state] >>
    rw[] >> fs[] >> rveq >> fs[set_var_find_name] )
  \\ (
    simp[Once comp_def] >> fs[evaluate_def] >>
    simp[Once rename_state_def] >> rveq >> simp[] ));

Theorem compile_semantics:
   BIJ (find_name f) UNIV UNIV /\
    ~s.use_alloc /\ ~s.use_store /\ ~s.use_stack /\
    s.compile = (λcfg. c cfg o (compile f)) ==>
    semantics start (rename_state c f s) = semantics start s
Proof
  simp[GSYM AND_IMP_INTRO] >> ntac 4 strip_tac >>
  simp[semantics_def] >>
  simp[
    comp_correct
    |> Q.SPEC`Call NONE (INL start) NONE`
    |> SIMP_RULE(srw_ss())[comp_def,dest_find_name_def]
    |> Q.SPEC`s with clock := k`
    |> SIMP_RULE(srw_ss()++QUANT_INST_ss[pair_default_qp])[GSYM AND_IMP_INTRO]
    |> SIMP_RULE std_ss [rename_state_with_clock]
    |> UNDISCH_ALL] >>
  simp[rename_state_def] >>
  srw_tac[QUANT_INST_ss[pair_default_qp]][]
QED

val compile_semantics_alt = Q.prove(
  `!s t.
      BIJ (find_name f) UNIV UNIV /\ (rename_state t.compile f s = t) /\
      s.compile = (λc. t.compile c o (compile f)) /\
      ~s.use_alloc /\ ~s.use_store /\ ~s.use_stack ==>
      semantics start t = semantics start s`,
  metis_tac [compile_semantics]);

val make_init_def = Define `
  make_init f code oracle (s:('a,'c,'ffi) stackSem$state) =
    s with
     <| code := code;
        regs := MAP_KEYS (LINV (find_name f) UNIV) s.regs;
        compile := (λcfg. s.compile cfg o (compile f));
        compile_oracle := oracle;
(*
        code_buffer := <| position := 0w; buffer := []; space_left := 0 |>;
        data_buffer := <| position := 0w; buffer := []; space_left := 0 |>;
*)
        ffi_save_regs := IMAGE (LINV (find_name f) UNIV) s.ffi_save_regs|>`

Theorem make_init_semantics:
   ~s.use_alloc /\ ~s.use_store /\ ~s.use_stack /\
   BIJ (find_name f) UNIV UNIV /\ ALL_DISTINCT (MAP FST code) /\
   s.code = fromAList (compile f code) /\
   s.compile_oracle = (I ## compile f ## I) o oracle
   ==>
   semantics start s = semantics start (make_init f (fromAList code) oracle s)
Proof
  fs [make_init_def] \\ rw []
  \\ match_mp_tac compile_semantics_alt \\ fs []
  \\ fs [rename_state_def,state_component_equality]
  \\ `find_name f o LINV (find_name f) UNIV = I` by
   (imp_res_tac BIJ_LINV_INV \\ fs [FUN_EQ_THM])
  \\ fs [GSYM IMAGE_COMPOSE] \\ fs [MAP_KEYS_BIJ_LINV]
  \\ fs [spt_eq_thm,wf_fromAList,lookup_fromAList,compile_def]
  \\ rw[prog_comp_eta,ALOOKUP_MAP_2,ALOOKUP_toAList,lookup_fromAList]
QED

Theorem stack_names_lab_pres:
    ∀f p.
  extract_labels p = extract_labels (comp f p)
Proof
  HO_MATCH_MP_TAC comp_ind>>Cases_on`p`>>rw[]>>
  once_rewrite_tac [comp_def]>>fs[extract_labels_def]>>
  BasicProvers.EVERY_CASE_TAC>>fs[]
QED

val names_ok_imp = Q.prove(`
  names_ok f c.reg_count c.avoid_regs ⇒
  ∀n. reg_name n c ⇒
  reg_ok (find_name f n) c`,
  fs[names_ok_def,EVERY_GENLIST,reg_name_def,asmTheory.reg_ok_def])

val names_ok_imp2 = Q.prove(`
  names_ok f c.reg_count c.avoid_regs ∧
  n ≠ n' ∧
  reg_name n c ∧ reg_name n' c ⇒
  find_name f n ≠ find_name f n'`,
  rw[names_ok_def]>>fs[ALL_DISTINCT_GENLIST,reg_name_def]>>
  metis_tac[])

val stack_names_comp_stack_asm_ok = Q.prove(`
  ∀f p.
  stack_asm_name c p ∧ names_ok f c.reg_count c.avoid_regs ∧
  fixed_names f c ⇒
  stack_asm_ok c (stack_names$comp f p)`,
  ho_match_mp_tac comp_ind>>
  Cases_on`p`>>rw[]>>
  simp[Once comp_def]>>fs[stack_asm_ok_def,stack_asm_name_def]
  >-
    (simp[Once inst_find_name_def]>>every_case_tac>>
    fs[asmTheory.inst_ok_def,inst_name_def,arith_name_def,asmTheory.arith_ok_def,addr_name_def,asmTheory.fp_ok_def,fp_name_def,asmTheory.fp_reg_ok_def,asmTheory.fp_reg_ok_def]>>
    (* Some of these are extremely annoying to prove with the separation of
       stack_names and configs... *)
    TRY(metis_tac[names_ok_imp,names_ok_imp2])
    >-
      (rw[]>>
      TRY(metis_tac[names_ok_imp])
      >-
        (Cases_on`r`>>fs[ri_find_name_def])
      >>
        Cases_on`r`>>
        fs[reg_imm_name_def,asmTheory.reg_imm_ok_def,ri_find_name_def]>>
        metis_tac[names_ok_imp])
    >>
      rw[]>>
      fs[fixed_names_def]>>
      metis_tac[names_ok_imp,names_ok_imp2])
  >-
    (every_case_tac>>fs[dest_find_name_def]>>
    metis_tac[names_ok_imp,asmTheory.reg_ok_def])
  >- metis_tac[names_ok_imp,asmTheory.reg_ok_def]
  >- metis_tac[names_ok_imp,asmTheory.reg_ok_def]
  >- metis_tac[names_ok_imp,asmTheory.reg_ok_def]);

Theorem stack_names_stack_asm_ok:
    EVERY (λ(n,p). stack_asm_name c p) prog ∧
  names_ok f c.reg_count c.avoid_regs ∧
  fixed_names f c ⇒
  EVERY (λ(n,p). stack_asm_ok c p) (compile f prog)
Proof
  fs[EVERY_MAP,EVERY_MEM,FORALL_PROD,prog_comp_def,compile_def,MEM_MAP,EXISTS_PROD]>>
  rw[]>>
  metis_tac[stack_names_comp_stack_asm_ok]
QED

Theorem stack_names_call_args:
    compile f p = p' ∧
  EVERY (λp. call_args p 1 2 3 4 0) (MAP SND p) ==>
  EVERY (λp. call_args p (find_name f 1)
                           (find_name f 2)
                           (find_name f 3)
                           (find_name f 4)
                           (find_name f 0)) (MAP SND p')
Proof
  rw[]>>fs[compile_def]>>
  fs[EVERY_MAP,EVERY_MEM,FORALL_PROD,prog_comp_def]>>
  rw[]>>res_tac>> pop_assum mp_tac>> rpt (pop_assum kall_tac)>>
  map_every qid_spec_tac[`p_2`,`f`]>>
  ho_match_mp_tac comp_ind>>
  Cases_on`p_2`>>rw[]>>
  ONCE_REWRITE_TAC [comp_def]>>
  fs[call_args_def]>>
  BasicProvers.EVERY_CASE_TAC>>fs[]
QED

val _ = export_theory();
