(*
  Syntactic properties of the code produced by data_to_word
*)
Theory data_to_word_syntaxProof
Ancestors
  data_to_word wordConvs wordConvsProof word_to_wordProof dataProps
  word_bignum backend[qualified]
Libs
  preamble

val _ = augment_srw_ss [rewrites [CONJUNCT2 data_to_wordTheory.arch_size]];

val _ = temp_delsimps ["NORMEQ_CONV"]
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]
val _ = diminish_srw_ss ["ABBREV"]

val assign_def =
  data_to_wordTheory.assign_def
  |> REWRITE_RULE [data_to_wordTheory.arg1_def,
                   data_to_wordTheory.arg2_def,
                   data_to_wordTheory.arg3_def,
                   data_to_wordTheory.arg4_def,
                   data_to_wordTheory.all_assign_defs];

val assign_def_extras =
  LIST_CONJ
  [LoadWord64_def,WriteWord64_def,BignumHalt_def,LoadBignum_def,
   AnyArith_code_def,Add_code_def,Sub_code_def,Mul_code_def,
   SmallDivMod_def,SmallnumCompare_def,SmallnumMul_def,SmallnumDivLoop_def,
   SmallnumUnsignedDiv_def,SmallnumDiv_def,SmallnumDivCall_def,
   Div_code_def,Mod_code_def, Compare1_code_def, Compare_code_def,
   Equal1_code_def, Equal_code_def, LongDiv1_code_def, LongDiv_code_def,
   ShiftVar_def, generated_bignum_stubs_eq, DivCode_def,
   AddNumSize_def, AnyHeader_def, WriteWord64_on_32_def,
   WriteWord32_on_32_def, AllocVar_def, SilentFFI_def,
   WordOp64_on_32_def, WordShift64_on_32_def, Make_ptr_bits_code_def,
   ShiftW8_def, WordShiftVar64_def, WordShiftVar64_on_32_def];

Theorem adjust_var_NEQ[local,simp]:
  adjust_var n <> 0 /\ adjust_var n <> 1 /\ adjust_var n <> 3 /\
  adjust_var n <> 5 /\ adjust_var n <> 7 /\ adjust_var n <> 9 /\
  adjust_var n <> 11 /\ adjust_var n <> 13
Proof
  rw [adjust_var_def] \\ intLib.COOPER_TAC
QED

Theorem extract_labels_SmallDivMod[simp]:
  extract_labels (SmallDivMod is_mod v1 v2) = []
Proof
  Cases_on `is_mod`
  \\ simp [SmallDivMod_def, list_Seq_def, wordConvsTheory.extract_labels_def]
QED

Theorem no_share_inst_SmallDivMod[local]:
  no_share_inst (SmallDivMod is_mod v1 v2)
Proof
  Cases_on `is_mod` >>
  simp [SmallDivMod_def, list_Seq_def, no_share_inst_def]
QED

val _ = (max_print_depth := 15);

(* Integer payloads need not be evaluated when checking program structure. *)
val EVAL = computeLib.RESTR_EVAL_CONV
  [``int_bitwise$int_or``,``int_bitwise$int_and``,``int_bitwise$int_xor``];
val EVAL_TAC = CONV_TAC EVAL;

val extract_labels_def = wordConvsTheory.extract_labels_def;

Theorem extract_labels_MemEqList[simp]:
  ∀a x. extract_labels (MemEqList c a x) = []
Proof
  Induct_on `x`
  \\ asm_rewrite_tac [MemEqList_def,extract_labels_def,APPEND]
QED

Theorem extract_labels_StoreEach:
  ∀xs a d. extract_labels (StoreEach c a xs d) = []
Proof
  Induct \\ fs [StoreEach_def,extract_labels_def]
QED

Theorem extract_labels_StoreAnyConsts:
  ∀r1 r2 r3 ws w. extract_labels (StoreAnyConsts r1 r2 r3 ws w) = []
Proof
  rpt gen_tac >> Cases_on `w` >> rw[StoreAnyConsts_def,extract_labels_def]
QED

(* TODO: goes away on inlineenc branch *)
Theorem extract_labels_WordOp64_on_32[local]:
  extract_labels (WordOp64_on_32 f) = []
Proof
  simp[WordOp64_on_32_def]>>Cases_on`f`>>simp[]>>
  EVAL_TAC
QED

Theorem extract_labels_WordShift64_on_32[local]:
  extract_labels (WordShift64_on_32 f g) = []
Proof
  simp[WordShift64_on_32_def]>>
  Cases_on`f`>>simp[]>>
  IF_CASES_TAC>>EVAL_TAC
QED

Theorem extract_labels_assignWordOp[local]:
  assign a b c d (WordOp (WordOpw e f)) g h = (i,j) ⇒
  extract_labels i = [] ∧ c ≤ j
Proof
  simp[assign_def]>>
  Cases_on`arch_width_bits a.arch_width = 64`>> simp[]
  >- (every_case_tac>>rw[]>> EVAL_TAC)
  >>
    every_case_tac>>rw[]>>
    simp[extract_labels_def,list_Seq_def,extract_labels_WordOp64_on_32]>>
    EVAL_TAC
QED

Theorem extract_labels_assignWordShift[local]:
  assign a b c d (WordOp (WordShift e f k)) g h = (i,j) ⇒
  extract_labels i = [] ∧ c ≤ j
Proof
  simp[assign_def]>>
  Cases_on`arch_width_bits a.arch_width >= 64`>> simp[]
  >- (every_case_tac>>rw[]>> EVAL_TAC)
  >>
    every_case_tac>>rw[]>>
    simp[extract_labels_def,list_Seq_def,extract_labels_WordShift64_on_32]>>
    EVAL_TAC
QED

Theorem extract_labels_SmallnumDivCall[simp]:
  extract_labels (SmallnumDivCall is_mod secn l dest names v1 v2) = [(secn,l)]
Proof
  simp [SmallnumDivCall_def,list_Seq_def,extract_labels_def]
QED

Theorem data_to_word_lab_pres_lem:
  ∀c n l p.
    l ≠ 0 ⇒
    let (cp,l') = comp c n l p in
    l ≤ l' ∧
    EVERY (λ(l1,l2). l1 = n ∧ l ≤ l2 ∧ l2 < l') (extract_labels cp) ∧
    ALL_DISTINCT (extract_labels cp)
Proof
  HO_MATCH_MP_TAC comp_ind>>Cases_on`p`>>rw[]>>
  once_rewrite_tac[comp_def]>>fs[extract_labels_def]
  >-
    (BasicProvers.EVERY_CASE_TAC>>fs[]>>rveq>>fs[extract_labels_def]>>
    rpt(pairarg_tac>>fs[])>>rveq>>fs[extract_labels_def]>>
    fs[EVERY_MEM,FORALL_PROD]>>rw[]>>
    res_tac>>fs[]>>
    CCONTR_TAC>>fs[]>>res_tac>>fs[])
  >- (
    qmatch_goalsub_rename_tac `assign _ _ _ _ opname _ _`
    \\ Cases_on `c.arch_width`
    \\ fs [asmTheory.arch_width_bits_def,asmTheory.arch_bytes_def]
    \\ Cases_on `opname`
    >>> SELECT_LT_THEN (Q.RENAME_TAC [`Label label`])
          (Cases_on `label`)
    >>> SELECT_LT_THEN (Q.RENAME_TAC [`FFI ffi_name`])
          (Cases_on `ffi_name`)
    >>> SELECT_LT_THEN (Q.RENAME_TAC [`IntOp integer_op`])
          (Cases_on `integer_op`)
    >>> SELECT_LT_THEN (Q.RENAME_TAC [`WordOp word_op`])
          (Cases_on `word_op`)
    >>> SELECT_LT_THEN (Q.RENAME_TAC [`BlockOp block_op`])
          (Cases_on `block_op`)
    >>> SELECT_LT_THEN (Q.RENAME_TAC [`GlobOp global_op`])
          (Cases_on `global_op`)
    >>> SELECT_LT_THEN (Q.RENAME_TAC [`MemOp memory_op`])
          (Cases_on `memory_op`)
    >>> SELECT_LT_THEN (Q.RENAME_TAC [`ThunkOp thunk_op`])
          (Cases_on `thunk_op`)
    >>~- ([`assign _ _ _ _ (WordOp (WordOpw _ _)) _ _`],
      pairarg_tac \\ drule extract_labels_assignWordOp \\ simp [])
    >>~- ([`assign _ _ _ _ (WordOp (WordShift _ _ _)) _ _`],
      pairarg_tac \\ drule extract_labels_assignWordShift \\ simp [])
    \\ fs [extract_labels_def,GiveUp_def,assign_def,assign_def_extras,
           oneline AssignCmp_def,SetBool_def,
           asmTheory.arch_width_bits_def,asmTheory.arch_bytes_def]
    \\ BasicProvers.EVERY_CASE_TAC
    \\ fs [extract_labels_def,list_Seq_def,extract_labels_StoreEach,
           extract_labels_StoreAnyConsts,Maxout_bits_code_def]
  )
  >~ [‘force_thunk’] >- (
    pairarg_tac \\ gvs [force_thunk_def, AllCaseEqs()]
    >- gvs [GiveUp_def, extract_labels_def]
    \\ gvs [extract_labels_def]
    \\ CASE_TAC \\ gvs [list_Seq_def, extract_labels_def]
    \\ CASE_TAC \\ gvs [extract_labels_def])
  >>
    (rpt (pairarg_tac>>fs[])>>rveq>>
          fs[extract_labels_def,EVERY_MEM,FORALL_PROD,ALL_DISTINCT_APPEND,
             SilentFFI_def,list_Seq_def]>>
    rw[]>> res_tac>>fs[]>>
    CCONTR_TAC>>fs[]>>res_tac>>fs[] >>
    fs[extract_labels_def,EVERY_MEM,FORALL_PROD,ALL_DISTINCT_APPEND,
       SilentFFI_def,list_Seq_def]>>
    every_case_tac >> fs [] >>
    fs[extract_labels_def,EVERY_MEM,FORALL_PROD,ALL_DISTINCT_APPEND,
       SilentFFI_def,list_Seq_def])
QED

Theorem labels_rel_emp[local]:
  labels_rel [] ls ⇒ ls = []
Proof
  fs[wordConvsTheory.labels_rel_def]
QED

Theorem stub_labels:
    EVERY (λ(n,m,p,md).
    EVERY (λ(l1,l2). l1 = n ∧ l2 ≠ 0 ∧ l2 ≠ 1) (extract_labels p)  ∧
                     ALL_DISTINCT (extract_labels p))
    (stubs_md data_conf)
Proof
  Cases_on `data_conf.arch_width` >>
  simp[data_to_wordTheory.stubs_def,generated_bignum_stubs_eq,
       asmTheory.arch_width_bits_def,asmTheory.arch_bytes_def,
       extract_labels_def,list_Seq_def]>>
  rpt conj_tac >>
  rpt (EVAL_TAC \\ rw [] \\ fs [extract_labels_def,list_Seq_def]
       \\ EVAL_TAC \\ NO_TAC) >>
  CONV_TAC (RAND_CONV EVAL) >>
  CONV_TAC ((RATOR_CONV o RAND_CONV) EVAL)
QED

Theorem stubs_with_has_fp_ops[simp]:
   stubs (data_conf with has_fp_ops := b) = stubs data_conf
Proof
  EVAL_TAC \\ fs []
QED

Theorem stubs_with_has_fp_tern[simp]:
  stubs (data_conf with has_fp_tern := b) = stubs data_conf
Proof
  EVAL_TAC \\ fs []
QED

Theorem stubs_md_with_has_fp_ops[simp]:
   stubs_md (data_conf with has_fp_ops := b) = stubs_md data_conf
Proof
  simp [stubs_md_def]
QED

Theorem stubs_md_with_has_fp_tern[simp]:
   stubs_md (data_conf with has_fp_tern := b) = stubs_md data_conf
Proof
  simp [stubs_md_def]
QED

(* no ShareInst in the compiled program *)

Theorem list_Seq_no_share_inst:
  !xs. no_share_inst (list_Seq xs) = EVERY no_share_inst xs
Proof
  ho_match_mp_tac list_Seq_ind >>
  rw[list_Seq_def,no_share_inst_def]
QED

Theorem StoreEach_no_share_inst:
  !v xs offset. no_share_inst (StoreEach c v xs offset)
Proof
  Induct_on `xs` >>
  gvs[StoreEach_def,no_share_inst_def]
QED

Theorem MemEqList_no_share_inst:
  !a xs. no_share_inst (MemEqList c a xs)
Proof
  Induct_on `xs` >>
  gvs[MemEqList_def,no_share_inst_def]
QED

Theorem StoreAnyConsts_no_share_inst:
  !r1 r2 r3 vs v.
    no_share_inst (StoreAnyConsts r1 r2 r3 vs v)
Proof
  rpt gen_tac >> Cases_on `v` >> rw[StoreAnyConsts_def,no_share_inst_def]
QED

Theorem stubs_no_share_inst:
  EVERY (\x. no_share_inst (FST $ SND $ SND x)) (stubs_md data_conf)
Proof
  simp [stubs_md_def,EVERY_MAP,LAMBDA_PROD] >>
  EVAL_TAC >>
  rw [] >>
  EVAL_TAC >>
  Cases_on `data_conf.arch_width` >>
  fs [asmTheory.arch_width_bits_def] >>
  EVAL_TAC
QED

Theorem comp_no_share_inst:
  !c secn l prog prog' l'.
  data_to_word$comp c secn l prog = (prog',l') ==>
  no_share_inst prog'
Proof
  ho_match_mp_tac comp_ind >>
  Cases_on `prog` >>
  rw []
  >- suspend "Skip"
  >- suspend "Move"
  >- suspend "Call"
  >- suspend "Assign"
  >- suspend "Seq"
  >- suspend "If"
  >- suspend "MakeSpace"
  >- suspend "Raise"
  >- suspend "Return"
  >- suspend "Tick"
  >- suspend "Force"
QED

Resume comp_no_share_inst[Skip]:
  gvs[comp_def,no_share_inst_def]
QED

Resume comp_no_share_inst[Move]:
  gvs[comp_def,no_share_inst_def]
QED

Resume comp_no_share_inst[Call]:
  first_x_assum mp_tac >>
  rw[Once comp_def,AllCaseEqs()] >>
  simp[no_share_inst_def] >>
  gvs[ELIM_UNCURRY,no_share_inst_def] >>
  metis_tac[FST_EQ_EQUIV]
QED

Resume comp_no_share_inst[Assign]:
  gvs[comp_def,AllCaseEqs(),assign_def,all_assign_defs,
    arg1_def,arg2_def,arg3_def,arg4_def] >>
  simp[no_share_inst_def,oneline AssignCmp_def, SetBool_def,
    GiveUp_def,BignumHalt_def,AllocVar_def,SilentFFI_def,
    list_Seq_no_share_inst,StoreEach_no_share_inst,
    Make_ptr_bits_code_def,StoreAnyConsts_no_share_inst,
    Maxout_bits_code_def,MemEqList_no_share_inst,no_share_inst_SmallDivMod,
    SmallnumCompare_def,SmallnumMul_def,SmallnumDiv_def,SmallnumDivCall_def,
    WriteWord64_def,WordOp64_on_32_def,WriteWord64_on_32_def,
    LoadWord64_def,WordShift64_on_32_def,LoadBignum_def,
    WriteWord32_on_32_def,WordShiftVar64_def,WordShiftVar64_on_32_def] >>
  rpt (
    TOP_CASE_TAC >>
    simp[no_share_inst_def,list_Seq_no_share_inst,no_share_inst_SmallDivMod])
QED

Resume comp_no_share_inst[Seq]:
  first_x_assum mp_tac >>
  rw[Once comp_def] >>
  gvs[ELIM_UNCURRY,no_share_inst_def] >>
  metis_tac[FST_EQ_EQUIV,SND_EQ_EQUIV]
QED

Resume comp_no_share_inst[If]:
  first_x_assum mp_tac >>
  rw[Once comp_def] >>
  gvs[ELIM_UNCURRY,no_share_inst_def] >>
  metis_tac[FST_EQ_EQUIV,SND_EQ_EQUIV]
QED

Resume comp_no_share_inst[MakeSpace]:
  gvs[comp_def,no_share_inst_def,list_Seq_no_share_inst,SilentFFI_def] >>
  IF_CASES_TAC >>
  simp[comp_def,no_share_inst_def,list_Seq_no_share_inst]
QED

Resume comp_no_share_inst[Raise]:
  gvs[comp_def,no_share_inst_def]
QED

Resume comp_no_share_inst[Return]:
  gvs[comp_def,no_share_inst_def]
QED

Resume comp_no_share_inst[Tick]:
  gvs[comp_def,no_share_inst_def]
QED

Resume comp_no_share_inst[Force]:
  gvs [comp_def, force_thunk_def, AllCaseEqs()]
  >- gvs [GiveUp_def, no_share_inst_def]
  \\ gvs [no_share_inst_def]
  \\ CASE_TAC \\ gvs [no_share_inst_def, list_Seq_no_share_inst]
  \\ CASE_TAC \\ gvs [no_share_inst_def]
QED

Finalise comp_no_share_inst;

Theorem MAP_FST_ZIP[local]:
  !xs ys. MAP FST (ZIP (xs, ys)) = TAKE (LENGTH ys) xs
Proof
  Induct \\ simp [ZIP_def]
  \\ gen_tac
  \\ Cases \\ simp [ZIP_def]
QED

Theorem compile_no_share_inst:
  data_to_word$compile data_conf word_conf asm_conf prog = (xx,prog') ⇒
  EVERY (λ(n,m,pp,md). no_share_inst pp) prog'
Proof
  rw[data_to_wordTheory.compile_def] >>
  gvs[ELIM_UNCURRY,word_to_wordTheory.compile_def,
    EVERY_MAP,word_to_wordTheory.full_compile_single_def,
    remove_must_terminate_no_share_inst] >>
  irule MONO_EVERY >>
  simp[] >>
  qexists `no_share_inst o FST o SND o SND o FST` >>
  conj_tac
  >- (rw[] >>
      irule remove_must_terminate_no_share_inst >>
      pop_assum mp_tac>>
      simp [FORALL_PROD, no_share_inst_subprogs_def]
      \\ simp [compile_single_not_created_subprogs |> GEN_ALL |> SIMP_RULE std_ss [PAIR_FST_SND_EQ]]
  )
  >>
  REWRITE_TAC [combinTheory.o_ASSOC] >>
  REWRITE_TAC [GSYM rich_listTheory.ALL_EL_MAP] >>
  simp [MAP_FST_ZIP] >>
  simp [EVERY_MAP] >>
  irule EVERY_TAKE >>
  simp[stubs_no_share_inst,EVERY_MAP] >>
  rw [EVERY_MEM, FORALL_PROD, compile_part_def] >>
  simp [comp_no_share_inst |> SIMP_RULE std_ss [PAIR_FST_SND_EQ]]
QED

(***)

Theorem data_to_word_compile_lab_pres:
    let (c,p) = compile data_conf word_conf asm_conf prog in
    MAP FST p = MAP FST (stubs_md data_conf) ++ MAP FST prog ∧
    EVERY (λ(n,m,(p:wordLang$prog),md).
      let labs = extract_labels p in
      EVERY (λ(l1,l2).l1 = n ∧ l2 ≠ 0 ∧ l2 ≠ 1) labs ∧
      ALL_DISTINCT labs) p
Proof
  fs[data_to_wordTheory.compile_def]>>
  qpat_abbrev_tac`datap = _ ++ MAP (A B) prog`>>
  qspecl_then [`word_conf`,`datap`,`asm_conf`] mp_tac
    (GEN_ALL compile_to_word_conventions)>>
  impl_tac>-
   (fs[Abbr‘datap’]>>
    irule_at Any EVERY_MONOTONIC>>
    qexists ‘λx. no_share_inst (FST $ SND $ SND x)’>>simp[FORALL_PROD]>>
    irule_at Any stubs_no_share_inst>>
    fs[EVERY_MAP,LAMBDA_PROD]>>
    simp[compile_part_def]>>
    simp[EVERY_MEM]>>rw[]>>
    pairarg_tac>>fs[]>>irule OR_INTRO_THM1>>
    irule comp_no_share_inst>>metis_tac[PAIR])>>
  rw[]>>
  pairarg_tac>>fs[Abbr`datap`]>>
  fs[EVERY_MEM]>>rw[]
  >-
    (match_mp_tac LIST_EQ>>rw[EL_MAP]>>
    Cases_on`EL x prog`>>PairCases_on`r`>>fs[compile_part_def]) >>
  qmatch_assum_abbrev_tac`MAP FST p = MAP FST p1 ++ MAP FST p2`>>
  full_simp_tac std_ss [GSYM MAP_APPEND]>>
  qabbrev_tac`pp = p1 ++ p2` >>
  fs[EL_MAP,MEM_EL,FORALL_PROD]>>
  `EVERY (λ(n,m,p,md).
    EVERY (λ(l1,l2). l1 = n ∧ l2 ≠ 0 ∧ l2 ≠ 1) (extract_labels p)  ∧ ALL_DISTINCT (extract_labels p)) pp` by
    (unabbrev_all_tac>>fs[EVERY_MEM]>>CONJ_TAC
    >-
      (assume_tac stub_labels>>
      fs[EVERY_MEM])
    >>
      fs[MEM_MAP,MEM_EL,EXISTS_PROD]>>rw[]>>fs[compile_part_def]>>
      qmatch_goalsub_abbrev_tac `comp data_conf2` >>
      Q.SPECL_THEN [`data_conf2`,`p_1`,`2n`,`p_1''`]assume_tac
        data_to_word_lab_pres_lem>>
      fs[]>>pairarg_tac>>fs[EVERY_EL,PULL_EXISTS]>>
      rw[]>>res_tac>>
      pairarg_tac>>fs[])>>
  fs[LIST_REL_EL_EQN,EVERY_EL]>>
  rpt (first_x_assum(qspec_then`n` assume_tac))>>rfs[]>>
  rfs[EL_MAP]>>
  pairarg_tac>>fs[]>>
  pairarg_tac>>fs[]>>
  rw[] >>fs[wordConvsTheory.labels_rel_def,SUBSET_DEF,MEM_EL,PULL_EXISTS]>>
  first_x_assum(qspec_then`n'''` assume_tac)>>rfs[]>>
  res_tac>>fs[]>>
  pairarg_tac>>fs[]>>
  qpat_x_assum`A=MAP FST pp` mp_tac>>simp[Once LIST_EQ_REWRITE,EL_MAP]>>
  disch_then(qspec_then`n` assume_tac)>>rfs[]
QED

Theorem StoreEach_no_inst[local]:
  ∀a ls off.
  every_inst (inst_ok_less ac) (StoreEach c a ls off)
Proof
  Induct_on`ls`>>rw[StoreEach_def,every_inst_def]
QED

Theorem MemEqList_no_inst[local]:
  ∀a x.
  every_inst (inst_ok_less ac) (MemEqList c a x)
Proof
  Induct_on `x` \\ fs [MemEqList_def,every_inst_def]
QED

Theorem StoreAnyConsts_no_inst[local]:
  ∀r1 r2 r3 ws w. every_inst (inst_ok_less ac) (StoreAnyConsts r1 r2 r3 ws w)
Proof
  rpt gen_tac >> Cases_on `w` >> rw[StoreAnyConsts_def,every_inst_def]
QED

Theorem every_inst_SmallDivMod[local]:
  every_inst P (SmallDivMod is_mod v1 v2) ⇔
  P (Arith (IDiv 1 3 (adjust_var v1) (adjust_var v2)))
Proof
  Cases_on `is_mod` >>
  simp [SmallDivMod_def, list_Seq_def, every_inst_def]
QED

Theorem assign_no_inst[local]:
  isa_bits ac = dimindex (:'a) ∧
  arch_width_bits a.arch_width = isa_bits ac ∧
  ((a.has_longdiv ⇒ (ac.ISA = x86_64)) ∧
   (a.has_div ⇒ (ac.ISA ∈ {ARMv8; MIPS;RISC_V})) ∧
   (a.has_imul ⇒ (ac.ISA ∈ {x86_64; ARMv7; ARMv8; MIPS; RISC_V})) ∧
   (a.has_idiv ⇒ (ac.ISA ∈ {x86_64; ARMv8; MIPS; RISC_V})) ∧
   (a.has_fp_ops ⇒ 1 < ac.fp_reg_count) ∧
   (a.has_fp_tern ==> 2 < ac.fp_reg_count /\ ac.ISA = ARMv7) /\
  addr_offset_ok ac 0 /\ byte_offset_ok ac 0) ⇒
  every_inst (inst_ok_less ac) (FST(assign a b c d e f g) :wordLang$prog)
Proof
  Cases_on `e`
  >- suspend "Label"
  >- suspend "FFI"
  >- suspend "IntOp"
  >- suspend "WordOp"
  >- suspend "BlockOp"
  >- suspend "GlobOp"
  >- suspend "MemOp"
  >- suspend "Install"
  >- suspend "ThunkOp"
QED

Resume assign_no_inst[Label]:
  simp [assign_def, every_inst_def]
QED

Resume assign_no_inst[FFI]:
  simp [assign_def] >>
  every_case_tac >>
  simp [every_inst_def, list_Seq_def]
QED

Resume assign_no_inst[IntOp]:
  strip_tac >>
  qmatch_goalsub_rename_tac `IntOp integer_op` >>
  Cases_on `integer_op` >>
  simp [assign_def,SmallnumCompare_def,SmallnumMul_def,
    SmallnumDiv_def,SmallnumDivCall_def] >>
  every_case_tac >>
  simp [every_inst_SmallDivMod, every_inst_def, list_Seq_def,
    GiveUp_def, oneline AssignCmp_def, SetBool_def, inst_ok_less_def,
    adjust_var_NEQ]
QED

Resume assign_no_inst[WordOp]:
  strip_tac >>
  qmatch_goalsub_rename_tac `closLang$WordOp word_operation` >>
  Cases_on `word_operation` >>
  simp [assign_def] >>
  every_case_tac >>
  simp [every_inst_def, list_Seq_def, StoreEach_no_inst,
    Maxout_bits_code_def, GiveUp_def, StoreAnyConsts_no_inst,
    inst_ok_less_def, assign_def_extras, MemEqList_no_inst,
    asmTheory.fp_reg_ok_def, fp_uop_inst_def, fp_cmp_inst_def,
    fp_bop_inst_def, fp_top_inst_def, oneline AssignCmp_def,
    SetBool_def, adjust_var_NEQ] >>
  fs [oneline fp_uop_inst_def, oneline fp_cmp_inst_def,
    oneline fp_bop_inst_def, oneline fp_top_inst_def,
    inst_ok_less_def, asmTheory.fp_reg_ok_def] >>
  rpt (
    TOP_CASE_TAC >>
    fs [every_inst_def, list_Seq_def, inst_ok_less_def,
      asmTheory.fp_reg_ok_def])
QED

Resume assign_no_inst[BlockOp]:
  strip_tac >>
  qmatch_goalsub_rename_tac `closLang$BlockOp block_operation` >>
  Cases_on `block_operation` >>
  simp [assign_def] >>
  every_case_tac >>
  simp [every_inst_def, list_Seq_def, StoreEach_no_inst,
    Maxout_bits_code_def, GiveUp_def, StoreAnyConsts_no_inst,
    inst_ok_less_def, assign_def_extras, MemEqList_no_inst,
    oneline AssignCmp_def, SetBool_def, adjust_var_NEQ] >>
  Cases_on `a.call_empty_ffi` >> simp [every_inst_def]
QED

Resume assign_no_inst[GlobOp]:
  strip_tac >>
  qmatch_goalsub_rename_tac `closLang$GlobOp global_operation` >>
  Cases_on `global_operation` >>
  simp [assign_def] >>
  every_case_tac >>
  simp [every_inst_def, list_Seq_def, assign_def_extras, GiveUp_def]
QED

Resume assign_no_inst[MemOp]:
  strip_tac >>
  qmatch_goalsub_rename_tac `closLang$MemOp memory_operation` >>
  Cases_on `memory_operation` >>
  simp [assign_def] >>
  every_case_tac >>
  simp [every_inst_def, list_Seq_def, StoreEach_no_inst,
    Maxout_bits_code_def, GiveUp_def, StoreAnyConsts_no_inst,
    inst_ok_less_def, assign_def_extras, MemEqList_no_inst,
    oneline AssignCmp_def, SetBool_def, adjust_var_NEQ] >>
  rpt (
    TOP_CASE_TAC >>
    simp [every_inst_def, list_Seq_def])
QED

Resume assign_no_inst[Install]:
  simp [assign_def] >>
  every_case_tac >>
  simp [every_inst_def, list_Seq_def, GiveUp_def, BignumHalt_def]
QED

Resume assign_no_inst[ThunkOp]:
  strip_tac >>
  qmatch_goalsub_rename_tac `closLang$ThunkOp thunk_operation` >>
  Cases_on `thunk_operation` >>
  simp [assign_def] >>
  every_case_tac >>
  simp [every_inst_def, list_Seq_def, StoreEach_no_inst, GiveUp_def]
QED

Finalise assign_no_inst;

(*
inst_ok_less_def
*)

Theorem comp_no_inst:
    ∀c n m p.
  isa_bits ac = dimindex (:'a) ∧
  arch_width_bits c.arch_width = isa_bits ac ∧
  ((c.has_longdiv ⇒ (ac.ISA = x86_64)) ∧
   (c.has_div ⇒ (ac.ISA ∈ {ARMv8; MIPS;RISC_V})) ∧
   (c.has_imul ⇒ (ac.ISA ∈ {x86_64; ARMv7; ARMv8; MIPS; RISC_V})) ∧
   (c.has_idiv ⇒ (ac.ISA ∈ {x86_64; ARMv8; MIPS; RISC_V})) ∧
   (c.has_fp_ops ⇒ 1 < ac.fp_reg_count) ∧
   (c.has_fp_tern ==> 2 < ac.fp_reg_count /\ ac.ISA = ARMv7)) /\
  addr_offset_ok ac 0 /\ byte_offset_ok ac 0 ⇒
  every_inst (inst_ok_less ac) (FST(comp c n m p) :wordLang$prog)
Proof
  ho_match_mp_tac comp_ind>>Cases_on`p`>>rw[]>>
  simp[Once comp_def,every_inst_def,force_thunk_def]>>
  every_case_tac>>fs[]>>
  rpt(pairarg_tac>>fs[])>>
  fs[assign_no_inst]>>
  EVAL_TAC>>fs[] >>
  IF_CASES_TAC >> EVAL_TAC >> fs []
QED

Theorem bounds_lem[local]:
  (w:int = -3 ∨
  w = -2 ∨
  w = -1 ∨
  w = 0 ∨
  w = 1 ∨
  w = 2 ∨
  w = 3 ∨
  w = 4 ∨
  w = 5 ∨
  w = 6 ∨
  w = 7)
  ⇒
  -8 ≤ w ∧ w ≤ 8
Proof
  strip_tac >> gvs[]
QED

Theorem data_to_word_compile_conventions:
    good_dimindex(:'a) ==>
  let (c,p) = compile data_conf wc ac prog in
  EVERY (λ(n,m,prog,md).
    flat_exp_conventions (prog:wordLang$prog) ∧
    post_alloc_conventions (isa_bits ac) (ac.reg_count - (5+LENGTH ac.avoid_regs)) prog ∧
    (isa_bits ac = dimindex (:'a) ∧
    arch_width_bits data_conf.arch_width = isa_bits ac ∧
    (data_conf.has_longdiv ⇒ (ac.ISA = x86_64)) ∧
    (data_conf.has_div ⇒ (ac.ISA ∈ {ARMv8; MIPS;RISC_V})) ∧
    (data_conf.has_imul ⇒ (ac.ISA ∈ {x86_64; ARMv7; ARMv8; MIPS; RISC_V})) ∧
    (data_conf.has_idiv ⇒ (ac.ISA ∈ {x86_64; ARMv8; MIPS; RISC_V})) ∧
    addr_offset_ok ac 0 /\
    hw_offset_ok ac 0 /\
    (* NOTE: this condition is
       stricter than necessary, but we have much more byte_offset space
       anyway on all the targets *)
    (∀w. -8 <= w ∧ w <= 8 ==> byte_offset_ok ac w)
    ⇒ full_inst_ok_less ac prog) ∧
    (ac.two_reg_arith ⇒ every_inst two_reg_inst prog) ∧
    (no_share_inst prog ∨ ac.ISA ≠ Ag32)) p
Proof
 fs[data_to_wordTheory.compile_def]>>
 qpat_abbrev_tac`p= stubs_md data_conf ++B`>>
 pairarg_tac>>fs[]>>
 Q.SPECL_THEN [`wc`,`p`,`ac`] mp_tac (GEN_ALL word_to_wordProofTheory.compile_to_word_conventions)>>
 impl_tac >-
  (fs[Abbr‘p’]>>
   irule_at Any EVERY_MONOTONIC>>
   qexists ‘λx. no_share_inst (FST $ SND $ SND x)’>>simp[FORALL_PROD]>>
   irule_at Any stubs_no_share_inst>>
   fs[EVERY_MAP,LAMBDA_PROD]>>
   simp[compile_part_def]>>
   simp[EVERY_MEM]>>rw[]>>
   pairarg_tac>>fs[]>>irule OR_INTRO_THM1>>
   irule comp_no_share_inst>>metis_tac[PAIR])>>
 rw[]>>fs[EVERY_MEM,LAMBDA_PROD,FORALL_PROD]>>rw[]>>
 res_tac>>fs[]>>
 first_assum irule>>
 simp[Abbr`p`]>>(rw[]
 >-
   (pop_assum mp_tac>>
   qpat_x_assum`data_conf.has_longdiv ⇒ P` mp_tac>>
   qpat_x_assum`data_conf.has_div⇒ P` mp_tac>>
   qpat_x_assum`∀w. _ ==> byte_offset_ok _ _ ` mp_tac>>
   qpat_x_assum`addr_offset_ok _ _` mp_tac>>
   qpat_x_assum`good_dimindex _` mp_tac>>
   qpat_x_assum`isa_bits ac = _` mp_tac>>
   qpat_x_assum`arch_width_bits data_conf.arch_width = _` mp_tac>>
   rpt(pop_assum kall_tac)>>
   Cases_on `data_conf.arch_width` >>
   fs[stubs_md_def,stubs_def,generated_bignum_stubs_eq,
      asmTheory.arch_width_bits_def,asmTheory.arch_bytes_def]>>rw[]>>
   TRY(rename1`ByteCopySub_code`>>
   fs[good_dimindex_def,ByteCopySub_code_def,every_inst_def,list_Seq_def,inst_ok_less_def]>>rw[]>>
   fs[]>>
   first_assum match_mp_tac>>
   metis_tac[bounds_lem])>>
   EVAL_TAC>>rw[]>>
   fs[good_dimindex_def,every_inst_def,list_Seq_def,inst_ok_less_def]
   \\ gvs[] \\ EVAL_TAC \\ fs[dimword_def] >>
   rw[] >> EVAL_TAC >> simp[]>>
   pairarg_tac \\ fs[]>>
   qmatch_goalsub_abbrev_tac `min ≤ ww ∧ ww ≤ max`>>
   first_x_assum(qspecl_then[`ww`] mp_tac)>>simp[Abbr`ww`]>>
   simp[asmTheory.int_offset_ok_def])
 >-
   (fs[MEM_MAP]>>PairCases_on`y`>>fs[compile_part_def]>>
   match_mp_tac comp_no_inst>>fs[]>>
   first_x_assum match_mp_tac>>
   fs[good_dimindex_def]>>
   metis_tac[bounds_lem])
 >>
   first_x_assum irule >>
   fs[WORD_LE,miscTheory.good_dimindex_def,word_2comp_n2w,
     dimword_def,word_msb_n2w])
QED

Theorem data_to_word_names:
   word_to_word$compile c1 c2
     (stubs_md c.data_conf ++ MAP (compile_part c3) prog) = (col,p) ==>
    MAP FST p = (MAP FST (stubs_md c.data_conf))++MAP FST prog
Proof
  rw[]>>assume_tac(GEN_ALL word_to_wordProofTheory.compile_to_word_conventions)>>
  pop_assum (qspecl_then [`c1`,`stubs_md c.data_conf++(MAP (compile_part c3) prog)`,`c2`] mp_tac)>>impl_tac
  >- (irule_at Any EVERY_MONOTONIC>>
      qexists ‘λx. no_share_inst (FST $ SND $ SND x)’>>simp[FORALL_PROD]>>
      irule_at Any stubs_no_share_inst>>
      fs[EVERY_MAP,LAMBDA_PROD]>>
      simp[compile_part_def]>>
      simp[EVERY_MEM]>>rw[]>>
      pairarg_tac>>fs[]>>
      irule comp_no_share_inst>>metis_tac[PAIR])>>
  rfs[]>>
  fs[MAP_MAP_o,MAP_EQ_f,FORALL_PROD,data_to_wordTheory.compile_part_def]
QED

Theorem ALL_DISTINCT_MAP_FST_stubs:
   ALL_DISTINCT (MAP FST (data_to_word$stubs c))
Proof
  EVAL_TAC
QED

Theorem MAP_FST_stubs_bound:
   MEM n (MAP FST (data_to_word$stubs c)) ⇒ n < data_num_stubs
Proof
  EVAL_TAC
  \\ strip_tac \\ rveq \\ EVAL_TAC
QED

Theorem max_heap_limit_has_fp_ops[simp]:
   max_heap_limit (dimindex (:α)) (conf with has_fp_ops := b) =
    max_heap_limit (dimindex (:α)) conf
Proof
  EVAL_TAC
QED

Theorem FST_compile_part[simp]:
   FST (compile_part a b) = (FST b)
Proof
  PairCases_on`b` \\ EVAL_TAC
QED

Overload data_get_code_labels = ``dataProps$get_code_labels``
Overload data_good_code_labels = ``dataProps$good_code_labels``

Theorem word_get_code_labels_StoreEach[local]:
  ∀ls off.
  word_get_code_labels (StoreEach c v ls off) = {}
Proof
  Induct>>fs[StoreEach_def]
QED

Theorem word_get_code_labels_MemEqList[local]:
  ∀x b.
  word_get_code_labels (MemEqList c b x) = {}
Proof
  Induct>>fs[MemEqList_def]
QED

Theorem word_get_code_labels_StoreAnyConsts[local]:
  const_parts_to_words c ps = SOME (w,ws) ⇒
  word_get_code_labels (StoreAnyConsts r1 r2 r3 ws w) = EMPTY
Proof
  rpt gen_tac >> Cases_on `w` >> rw[StoreAnyConsts_def,wordConvsTheory.get_code_labels_def]
QED

Theorem const_parts_to_words_labels:
  const_parts_to_words c bs = SOME (q,r) ⇒
  word_get_code_labels (StoreAnyConsts (adjust_var w) 1 3 r q) ⊆
  closLang$assign_get_code_label (BlockOp (Build bs))
Proof
  rw [] \\ drule word_get_code_labels_StoreAnyConsts \\ fs []
QED

(* semi-slow... *)
Theorem word_get_code_labels_assign[local]:
  ∀x.
    assign c secn v w x y z = (res1,res2) ⇒
    word_get_code_labels (res1:wordLang$prog) SUBSET
    closLang$assign_get_code_label x ∪ (set(MAP FST (stubs c : (num # num # wordLang$prog) list)))
Proof
  ho_match_mp_tac closLangTheory.assign_get_code_label_ind>>
  rw[assign_def,all_assign_defs,arg1_def,arg2_def,arg3_def,arg4_def,
     closLangTheory.assign_get_code_label_def, oneline AssignCmp_def, SetBool_def]>>
  fs[list_Seq_def,word_get_code_labels_StoreEach,word_get_code_labels_MemEqList]>>
  gvs[AllCaseEqs()]>>
  rw[]>>
  simp[stubs_def,list_Seq_def,wordConvsTheory.get_code_labels_def,
    word_get_code_labels_StoreEach,word_get_code_labels_MemEqList,
    closLangTheory.assign_get_code_label_def,GiveUp_def]>>
  EVAL_TAC>>
  rw[]>>simp[list_Seq_def]>>
  every_case_tac>>fs[list_Seq_def]>>
  drule const_parts_to_words_labels>>
  simp[adjust_var_def]>>
  strip_tac>>
  irule SUBSET_TRANS >>
  pop_assum (irule_at Any)>>
  EVAL_TAC
QED

Theorem data_to_word_comp_code_labels[local]:
  ∀c secn l p.
  word_get_code_labels ((FST (comp c secn l p)):wordLang$prog) SUBSET
  data_get_code_labels p ∪ set(MAP FST (stubs c : (num # num # wordLang$prog) list))
Proof
  ho_match_mp_tac comp_ind>>
  rw[]>>Cases_on`p`>>fs[]>>
  simp[Once comp_def]>>
  rpt(pairarg_tac>>fs[])
  >- (
    every_case_tac>>fs[]>>
    rpt(pairarg_tac>>fs[])>>
    fs[SUBSET_DEF]>>fs[]>>
    metis_tac[])
  >- (
    simp[Once (GSYM FST_pair)]>> pairarg_tac>>
    drule word_get_code_labels_assign>>
    simp[])
  >-
    (fs[SUBSET_DEF]>>metis_tac[])
  >-
    (fs[SUBSET_DEF]>>metis_tac[])
  >~ [‘force_thunk’] >- (
    gvs [force_thunk_def]
    \\ every_case_tac \\ gvs [GiveUp_def, SUBSET_DEF]
    \\ EVAL_TAC \\ rpt strip_tac \\ disj1_tac \\ gvs []) >>
  EVAL_TAC>>rw[]>>fs[]
QED

Theorem word_good_handlers_StoreEach[local]:
  ∀ls off.
  word_good_handlers secn (StoreEach c v ls off)
Proof
  Induct>>fs[StoreEach_def]
QED

Theorem word_good_handlers_MemEqList[local]:
  ∀x b.
  word_good_handlers secn (MemEqList c b x)
Proof
  Induct>>fs[MemEqList_def]
QED

Theorem word_good_handlers_StoreAnyConsts[local]:
  ∀r1 r2 r3 ws w. word_good_handlers secn (StoreAnyConsts r1 r2 r3 ws w)
Proof
  rpt gen_tac >> Cases_on `w` >> rw[StoreAnyConsts_def,wordConvsTheory.good_handlers_def]
QED

(* slow... *)
Theorem word_good_handlers_assign[local]:
  ∀x.
    assign c secn v w x y z = (res1,res2) ⇒
    word_good_handlers secn res1
Proof
  ho_match_mp_tac closLangTheory.assign_get_code_label_ind>>
  rw[assign_def,all_assign_defs,arg1_def,arg2_def,arg3_def,arg4_def,
     closLangTheory.assign_get_code_label_def, oneline AssignCmp_def, SetBool_def]>>
  fs[list_Seq_def,word_good_handlers_StoreEach,word_good_handlers_MemEqList]>>
  gvs[AllCaseEqs()]>>
  rw[]>>
  simp[stubs_def,list_Seq_def,wordConvsTheory.good_handlers_def,
    word_good_handlers_StoreEach,word_good_handlers_MemEqList,
    closLangTheory.assign_get_code_label_def,GiveUp_def,word_good_handlers_StoreAnyConsts]>>
  EVAL_TAC>>
  rw[]>>simp[list_Seq_def]>>
  every_case_tac>>fs[list_Seq_def]
QED

Theorem data_to_word_comp_good_handlers[local]:
  ∀c secn l p.
  word_good_handlers secn ((FST (comp c secn l p)):wordLang$prog)
Proof
  ho_match_mp_tac comp_ind>>
  rw[]>>Cases_on`p`>>fs[]>>
  simp[Once comp_def]>>
  rpt(pairarg_tac>>fs[])
  >- (
    every_case_tac>>fs[]>>
    rpt(pairarg_tac>>fs[])>>
    fs[SUBSET_DEF]>>fs[]>>
    metis_tac[])
  >- (
    simp[Once (GSYM FST_pair)]>> pairarg_tac>>
    drule word_good_handlers_assign>>
    simp[])
  >~ [‘force_thunk’] >- (
    gvs [force_thunk_def]
    \\ every_case_tac \\ gvs [GiveUp_def]
    \\ EVAL_TAC)
  >>
    EVAL_TAC>>rw[]>>fs[]
QED

Theorem stubs_labels[local]:
  BIGUNION (set (MAP (λ(n,m,pp,md). word_get_code_labels pp)
                   (stubs_md dc)))
  ⊆ set (MAP FST (stubs_md dc))
Proof
  rpt (EVAL_TAC >> IF_CASES_TAC >> simp []) >>
  Cases_on `dc.arch_width` >>
  fs [asmTheory.arch_width_bits_def] >>
  EVAL_TAC
QED

Theorem stubs_good_handlers[local]:
  EVERY (λ(n,m,pp,md). word_good_handlers n pp) (stubs_md dc)
Proof
  EVAL_TAC >> rw [] >>
  Cases_on `dc.arch_width` >>
  fs [asmTheory.arch_width_bits_def] >>
  EVAL_TAC
QED

Theorem data_to_word_good_code_labels:
  (data_to_word$compile data_conf word_conf asm_conf prog) = (xx,prog') ∧
  data_good_code_labels prog elabs ⇒
  word_good_code_labels prog' elabs
Proof
  fs[data_to_wordTheory.compile_def]>>rw[]>>
  qmatch_asmsub_abbrev_tac`stubs_md dc`>>
  pop_assum kall_tac>>
  qmatch_asmsub_abbrev_tac`LHS = _`>>
  `prog' = SND LHS` by (unabbrev_all_tac>>fs[])>>
  pop_assum SUBST_ALL_TAC>>
  fs[Abbr`LHS`]>>
  match_mp_tac word_good_code_labels_word_to_word>>
  fs[wordConvsTheory.good_code_labels_def,dataPropsTheory.good_code_labels_def]>>rw[]
  >- irule stubs_good_handlers
  >-
    (simp[EVERY_MAP,LAMBDA_PROD,compile_part_def,data_to_word_comp_good_handlers]>>
    fs[EVERY_MEM,FORALL_PROD])
  >-
    (assume_tac stubs_labels>>
    match_mp_tac SUBSET_TRANS>>
    asm_exists_tac>>fs[]>>
    metis_tac[SUBSET_TRANS,SUBSET_UNION])
  >>
    fs[MAP_MAP_o,o_DEF,LAMBDA_PROD,compile_part_def]>>
    fs[SUBSET_DEF,PULL_EXISTS,Once MEM_MAP,FORALL_PROD]>>
    rw[]>>
    drule (data_to_word_comp_code_labels |> SIMP_RULE std_ss [SUBSET_DEF])>>
    rw[]
    >-
      (first_x_assum drule>>
      disch_then drule>>fs[MEM_MAP,EXISTS_PROD]>>
      metis_tac[])
    >>
      fs[MEM_MAP,EXISTS_PROD]>>
      fs[stubs_md_def,MEM_MAP,EXISTS_PROD]>>metis_tac[]
QED

val th = EVAL``MAP FST (stubs c)``;

(* TODO: move somewhere better *)
Definition stubs_fst_def:
  stubs_fst = ^(rconc th)
End

Theorem stubs_fst_eq =
  th |> REWRITE_RULE [GSYM stubs_fst_def]

(* The incremental version ONLY does data_to_word
  TODO: MAP FST stubs is independent of the data conf,
  not sure if generality is needed
*)
Theorem data_to_word_good_code_labels_incr:
  set stubs_fst ⊆ elabs ∧
  data_good_code_labels progs elabs ⇒
  word_good_code_labels (MAP (compile_part dc) progs) elabs
Proof
  fs[wordConvsTheory.good_code_labels_def,dataPropsTheory.good_code_labels_def]>>rw[]
  >-
    (simp[EVERY_MAP,LAMBDA_PROD,compile_part_def,data_to_word_comp_good_handlers]>>
    fs[EVERY_MEM,FORALL_PROD])
  >>
  fs[SUBSET_DEF,PULL_EXISTS,FORALL_PROD,MEM_MAP]>>
  rw[]>>
  fs[EXISTS_PROD,compile_part_def]>>
  drule (data_to_word_comp_code_labels |> SIMP_RULE std_ss [SUBSET_DEF])>>
  rw[]
  >-
    metis_tac[]
  >>
    fs[stubs_fst_eq]
QED

Theorem data_to_word_good_handlers:
  (data_to_word$compile data_conf word_conf asm_conf prog) = (xx,prog') ⇒
  EVERY (λ(n,m,pp,md). good_handlers n pp) prog'
Proof
  fs[data_to_wordTheory.compile_def]>>
  rw[]>>
  qmatch_asmsub_abbrev_tac`stubs_md dc`>>
  pop_assum kall_tac>>
  qmatch_asmsub_abbrev_tac`LHS = _`>>
  `prog' = SND LHS` by (unabbrev_all_tac>>fs[])>>
  pop_assum SUBST_ALL_TAC>>
  fs[Abbr`LHS`]>>
  match_mp_tac word_good_handlers_word_to_word>>
  fs[wordConvsTheory.good_code_labels_def,dataPropsTheory.good_code_labels_def]>>rw[]
  >- irule stubs_good_handlers
  >-
    (simp[EVERY_MAP,LAMBDA_PROD,compile_part_def,data_to_word_comp_good_handlers]>>
    fs[EVERY_MEM,FORALL_PROD])
QED

Theorem data_to_word_good_handlers_incr:
  EVERY (λ(n,m,pp,md). good_handlers n pp) (MAP (compile_part dc) progs)
Proof
  simp[EVERY_MAP,LAMBDA_PROD,compile_part_def,data_to_word_comp_good_handlers]>>
  fs[EVERY_MEM,FORALL_PROD]
QED
