open preamble primSemEnvTheory semanticsPropsTheory
     backendTheory
     source_to_modProofTheory
     mod_to_conProofTheory
     con_to_decProofTheory
     dec_to_exhProofTheory
     exh_to_patProofTheory
     pat_to_closProofTheory
     clos_to_bvlProofTheory
     bvl_to_bviProofTheory
     bvi_to_dataProofTheory
     data_to_wordProofTheory
     word_to_stackProofTheory
     stack_to_labProofTheory
     lab_to_targetProofTheory
     backend_commonTheory
local open compilerComputeLib dataPropsTheory in end
open word_to_stackTheory

val _ = new_theory"backendProof";

(* TODO: move *)

fun Abbrev_intro th =
  EQ_MP (SYM(SPEC(concl th)markerTheory.Abbrev_def)) th

val pair_CASE_eq = Q.store_thm("pair_CASE_eq",
  `pair_CASE p f = a ⇔ ∃x y. p = (x,y) ∧ f x y = a`,
  Cases_on`p`>>rw[]);

(* -- *)


(* --- composing data-to-target --- *)

(* TODO: this section is full of stuff that needs to be moved *)

val from_stack = let
  val lemma1 = lab_to_targetProofTheory.semantics_compile |> UNDISCH_ALL
    |> Q.INST [`code`|->`code2`]
  val lemma2 = stack_to_labProofTheory.full_make_init_semantics |> UNDISCH
    |> Q.INST [`code`|->`code1`]
  in simple_match_mp (MATCH_MP implements_trans lemma2) lemma1
     |> INST_TYPE [``:'state``|->``:'b``] end

val from_stack_fail = let
  val lemma1 = lab_to_targetProofTheory.semantics_compile |> UNDISCH_ALL
    |> Q.INST [`code`|->`code2`]
  val lemma2 = stack_to_labProofTheory.full_make_init_semantics_fail |> UNDISCH
    |> Q.INST [`code`|->`code1`]
  val th = EVAL ``(make_init mc_conf ffi save_regs io_regs t m dm ms code2).ffi``
  in simple_match_mp (MATCH_MP implements_trans lemma2) lemma1
     |> REWRITE_RULE [th]
     |> INST_TYPE [``:'state``|->``:'b``] end

val from_word = let
  val lemma1 = word_to_stackProofTheory.compile_semantics
    |> REWRITE_RULE [CONJ_ASSOC]
    |> MATCH_MP implements_intro_ext
    |> REWRITE_RULE [GSYM CONJ_ASSOC] |> UNDISCH_ALL
    |> Q.INST [`code`|->`code3`]
    |> INST_TYPE [``:'b``|->``:'a``]
  in simple_match_mp (MATCH_MP implements_trans lemma1) from_stack end

val full_make_init_ffi = Q.prove(
  `(full_make_init
         (bitmaps,c1,code,f,k,max_heap,off,regs,
          make_init mc_conf ffi save_regs io_regs t m dm ms code2,
          save_regs)).ffi = ffi`,
  fs [full_make_init_def,stack_allocProofTheory.make_init_def,
      stack_removeProofTheory.make_init_any_ffi] \\ EVAL_TAC);

val from_data = let
  val lemma1 = data_to_wordProofTheory.compile_semantics
    |> REWRITE_RULE [CONJ_ASSOC]
    |> MATCH_MP (GSYM implements_intro_ext)
    |> REWRITE_RULE [GSYM CONJ_ASSOC] |> UNDISCH_ALL
    |> Q.INST [`code`|->`code4`]
    |> INST_TYPE [``:'b``|->``:'a``]
  in simple_match_mp (MATCH_MP implements_trans lemma1) from_word
     |> SIMP_RULE (srw_ss()) [full_make_init_ffi,
          word_to_stackProofTheory.make_init_def] end;

val from_data_fail = let
  val th = dataPropsTheory.Resource_limit_hit_implements_semantics
  val th = MATCH_MP implements_trans th
  val th = MATCH_MP th from_stack_fail
  val target = from_data |> concl
  val curr = concl th
  val i = fst (match_term curr target)
  in INST i th end;

val full_make_init_code =
  ``(^(full_make_init_def |> SPEC_ALL |> concl |> dest_eq |> fst)).code``
  |> SIMP_CONV (srw_ss()) [full_make_init_def,stack_allocProofTheory.make_init_def];

fun define_abbrev name tm = let
  val vs = free_vars tm |> sort
    (fn v1 => fn v2 => fst (dest_var v1) <= fst (dest_var v2))
  val vars = foldr mk_pair (last vs) (butlast vs)
  val n = mk_var(name,mk_type("fun",[type_of vars, type_of tm]))
  in Define `^n ^vars = ^tm` end;

val machine_sem_implements_data_sem = save_thm("machine_sem_implements_data_sem",let
  val th = from_data |> DISCH_ALL
           |> REWRITE_RULE [AND_IMP_INTRO,GSYM CONJ_ASSOC,full_make_init_code]
           |> Q.INST [`code1`|->`SND (compile asm_conf code3)`]
           |> REWRITE_RULE [GSYM AND_IMP_INTRO] |> UNDISCH_ALL
  val th_fail = from_data_fail |> DISCH_ALL
           |> REWRITE_RULE [AND_IMP_INTRO,GSYM CONJ_ASSOC,full_make_init_code]
           |> Q.INST [`code1`|->`codeN`]
           |> REWRITE_RULE [GSYM AND_IMP_INTRO] |> UNDISCH_ALL
  val hs1 = hyp th
  val hs2 = hyp th_fail
  fun inter xs ys = filter (fn y => mem y ys) xs
  fun diff xs ys = filter (fn y => not (mem y ys)) xs
  val hs = inter hs1 hs2
  fun disch_assums thi =
    foldr (fn (tm,th) => DISCH tm th) thi (diff (hyp thi) hs)
     |> PURE_REWRITE_RULE [AND_IMP_INTRO,GSYM CONJ_ASSOC]
  val th1 = disch_assums th
  val th2 = disch_assums th_fail
  val lemma = METIS_PROVE [] ``(b1 ==> x) /\ (b2 ==> x) ==> (b1 \/ b2 ==> x)``
  val lemma2 = METIS_PROVE [] ``(P ==> R ==> Q) ==> P /\ R ==> R ==> Q``
  val th = simple_match_mp lemma (CONJ th1 th2)
           |> DISCH_ALL
           |> PURE_REWRITE_RULE [AND_IMP_INTRO,GSYM CONJ_ASSOC]
           |> UNDISCH_ALL
           |> Q.INST [`c`|->`c1`,`start`|->`InitGlobals_location`]
           |> DISCH ``from_data (c:'a backend$config) prog = SOME (bytes,ffis)``
           |> DISCH_ALL
           |> INST_TYPE [``:'state``|->``:'a``]
           |> MATCH_MP lemma2
  val (lhs,rhs) = dest_imp (concl th)
  fun diff xs ys = filter (fn x => not (mem x ys)) xs
  val vs = diff (free_vars lhs) (free_vars rhs) |> sort
    (fn v1 => fn v2 => fst (dest_var v1) <= fst (dest_var v2))
  val lemma = METIS_PROVE [] ``(!x. P x ==> Q) <=> ((?x. P x) ==> Q)``
  val th = GENL vs th |> SIMP_RULE std_ss [lemma]
  val def = define_abbrev "data_to_word_precond"
               (th |> concl |> dest_imp |> fst)
  val th = th |> REWRITE_RULE [GSYM def]
              |> SIMP_RULE std_ss [PULL_FORALL] |> SPEC_ALL
  in th end);

val data_to_word_precond_def = fetch "-" "data_to_word_precond_def" |> SPEC_ALL

val full_make_init_gc_fun = Q.store_thm("full_make_init_gc_fun",
  `(full_make_init
         (bitmaps,c1,code,f,k,max_heap,off,regs, xx,
          save_regs)).gc_fun = word_gc_fun c1`,
  fs [full_make_init_def,stack_allocProofTheory.make_init_def]);

val full_make_init_bitmaps = Q.prove(
  `full_init_pre
         (bitmaps,c1,SND (compile asm_conf code3),f,k,max_heap,off,regs,
          make_init mc_conf ffi save_regs io_regs t m dm ms code2,
          save_regs) ==>
    (full_make_init
         (bitmaps,c1,SND (compile asm_conf code3),f,k,max_heap,off,regs,
          make_init mc_conf ffi save_regs io_regs t m dm ms code2,
          save_regs)).bitmaps = bitmaps`,
  fs [full_make_init_def,stack_allocProofTheory.make_init_def,
      stack_removeProofTheory.make_init_any_bitmaps]
  \\ every_case_tac \\ fs [] \\ fs [full_init_pre_def]);

val full_init_pre_IMP_init_store_ok = Q.prove(
  `max_heap = 2 * max_heap_limit (:'a) c1 -1 ==>
    init_store_ok c1
      ((full_make_init
          (bitmaps,c1,code3,f,k,max_heap,off,regs,(s:('a,'ffi)labSem$state),
             save_regs)).store \\ Handler)
       (full_make_init
          (bitmaps,c1,code3,f,k,max_heap,off,regs,s,save_regs)).memory
       (full_make_init
          (bitmaps,c1,code3,f,k,max_heap,off,regs,s,save_regs)).mdomain`,
  fs [full_make_init_def,stack_allocProofTheory.make_init_def,
      stack_removeProofTheory.make_init_any_def]
  \\ CASE_TAC \\ fs [] THEN1
   (fs [init_store_ok_def,FUPDATE_LIST,stack_removeTheory.store_list_def,
        FLOOKUP_DEF,DOMSUB_FAPPLY_THM,FAPPLY_FUPDATE_THM]
    \\ rw [] \\ qexists_tac `0` \\ fs [word_list_exists_def]
    \\ fs [set_sepTheory.SEP_EXISTS_THM,set_sepTheory.cond_STAR,LENGTH_NIL]
    \\ fs [word_list_def,set_sepTheory.emp_def,set_sepTheory.fun2set_def]
    \\ EVAL_TAC)
  \\ fs [stack_removeProofTheory.make_init_opt_def]
  \\ every_case_tac \\ fs [] \\ NTAC 2 (pop_assum kall_tac) \\ rw []
  \\ fs [init_store_ok_def,stack_removeProofTheory.init_prop_def]
  \\ rewrite_tac [DECIDE ``2 * n = n + n:num``,
       stack_removeProofTheory.word_list_exists_ADD]
  \\ qexists_tac`len`
  \\ fs [FLOOKUP_DEF,DOMSUB_FAPPLY_THM,FAPPLY_FUPDATE_THM]);

val full_init_pre_IMP_init_state_ok = Q.prove(
  `4 < asm_conf.reg_count − (LENGTH asm_conf.avoid_regs + 5) /\
    (case bitmaps of [] => F | h::_ => 4w = h) /\
    good_dimindex (:α) ==>
    init_state_ok
      (asm_conf.reg_count − (LENGTH (asm_conf:'a asm_config).avoid_regs + 5))
      (full_make_init
        (bitmaps:'a word list,c1,code3,f,k,max_heap,off,regs,s,save_regs))`,
  fs [full_make_init_def,stack_allocProofTheory.make_init_def,
      stack_removeProofTheory.make_init_any_def] \\ strip_tac
  \\ CASE_TAC \\ fs [] THEN1
   (fs [init_state_ok_def,gc_fun_ok_word_gc_fun] \\ strip_tac
    \\ fs [FUPDATE_LIST,stack_removeTheory.store_list_def,FLOOKUP_UPDATE]
    \\ fs [labPropsTheory.good_dimindex_def,dimword_def])
  \\ fs [] \\ every_case_tac \\ fs [] \\ rw []
  \\ fs [init_state_ok_def,gc_fun_ok_word_gc_fun]
  \\ conj_tac THEN1 fs [labPropsTheory.good_dimindex_def]
  \\ `init_prop max_heap x /\ x.bitmaps = 4w::t` by
        (fs [stack_removeProofTheory.make_init_opt_def]
         \\ every_case_tac \\ fs [stack_removeProofTheory.init_reduce_def] \\ rw [])
  \\ fs [stack_removeProofTheory.init_prop_def]
  \\ `x.stack <> []` by (rpt strip_tac \\ fs [])
  \\ `?t1 t2. x.stack = SNOC t1 t2` by metis_tac [SNOC_CASES]
  \\ fs [] \\ rpt var_eq_tac \\ fs[ADD1]
  \\ qpat_x_assum `LENGTH t2 = x.stack_space` (assume_tac o GSYM)
  \\ fs [DROP_LENGTH_APPEND] \\ fs [FLOOKUP_DEF]);

val sr_gs_def = stack_removeProofTheory.good_syntax_def
val sa_gs_def = stack_allocProofTheory.good_syntax_def
val sl_gs_def = stack_to_labProofTheory.good_syntax_def
val convs = [sr_gs_def,sa_gs_def,sl_gs_def,wordPropsTheory.post_alloc_conventions_def,wordPropsTheory.call_arg_convention_def,wordLangTheory.every_var_def,wordLangTheory.every_stack_var_def,wordPropsTheory.inst_arg_convention_def];

val code_and_locs = [
  data_to_wordTheory.FromList_code_def,data_to_wordTheory.FromList_location_def,
  data_to_wordTheory.FromList1_code_def,data_to_wordTheory.FromList1_location_def,
  data_to_wordTheory.RefByte_code_def,data_to_wordTheory.RefByte_location_def,
  data_to_wordTheory.RefArray_code_def,data_to_wordTheory.RefArray_location_def,
  data_to_wordTheory.Replicate_code_def,data_to_wordTheory.Replicate_location_def,
  data_to_wordTheory.AnyArith_code_def,data_to_wordTheory.AnyArith_location_def,
  data_to_wordTheory.Add_code_def,data_to_wordTheory.Add_location_def,
  data_to_wordTheory.Sub_code_def,data_to_wordTheory.Sub_location_def,
  data_to_wordTheory.Mul_code_def,data_to_wordTheory.Mul_location_def,
  data_to_wordTheory.Div_code_def,data_to_wordTheory.Div_location_def,
  data_to_wordTheory.Mod_code_def,data_to_wordTheory.Mod_location_def,
  data_to_wordTheory.Compare1_code_def,data_to_wordTheory.Compare1_location_def,
  data_to_wordTheory.Compare_code_def,data_to_wordTheory.Compare_location_def,
  data_to_wordTheory.Equal1_code_def,data_to_wordTheory.Equal1_location_def,
  data_to_wordTheory.Equal_code_def,data_to_wordTheory.Equal_location_def,
  stackLangTheory.gc_stub_location_def,
  wordLangTheory.raise_stub_location_def
  ];

val stack_move_sa_gs = Q.store_thm("stack_move_sa_gs",`
  ∀n st off i p.
  good_syntax p ⇒
  good_syntax (stack_move n st off i p)`,
  Induct>>rw[stack_move_def,sa_gs_def]);

val word_to_stack_sa_gs = Q.store_thm("word_to_stack_sa_gs",`
  ∀p n args.
  good_syntax (FST(word_to_stack$comp p n args))`,
  recInduct comp_ind >>fs[comp_def,sa_gs_def,FORALL_PROD,wRegWrite1_def,wLive_def]>>rw[]>>fs convs
  >-
    (fs[wMove_def]>>qpat_abbrev_tac`ls = MAP f A`>>
    pop_assum kall_tac>>
    qid_spec_tac`ls`>>Induct>>fs[wMoveAux_def,sa_gs_def]>>
    Cases_on`ls`>>fs[FORALL_PROD,wMoveAux_def,wMoveSingle_def]>>rw[]>>
    BasicProvers.EVERY_CASE_TAC>>fs convs)
  >-
    (Cases_on`i`>>TRY(Cases_on`a`)>>TRY(Cases_on`m`)>>TRY(Cases_on`r`)>>
    fs[wInst_def,wRegWrite1_def,wReg1_def,wReg2_def]>>
    BasicProvers.EVERY_CASE_TAC>>
    fs[wStackLoad_def,sa_gs_def])
  >- (fs[wReg1_def,SeqStackFree_def]>>BasicProvers.EVERY_CASE_TAC>>fs[sa_gs_def,wStackLoad_def])
  >- rpt (pairarg_tac>>fs[sa_gs_def])
  >- (rpt (pairarg_tac>>fs[sa_gs_def])>>
  Cases_on`ri`>>fs[wReg1_def,wRegImm2_def,wReg2_def]>>BasicProvers.EVERY_CASE_TAC>>fs[]>>rveq>>fs[wStackLoad_def,sa_gs_def])
  >- (fs[wReg1_def]>>BasicProvers.EVERY_CASE_TAC>>fs[sa_gs_def,wStackLoad_def])
  >-
    (Cases_on`ret`>>fs[]
    >-
    (Cases_on`dest`>>fs[call_dest_def,wReg2_def,SeqStackFree_def]>>
    BasicProvers.EVERY_CASE_TAC>>
    fs convs>>
    BasicProvers.EVERY_CASE_TAC>>
    fs[wStackLoad_def,sa_gs_def])
    >>
    (PairCases_on`x`>>
    Cases_on`dest`>>fs[call_dest_def,wReg2_def,SeqStackFree_def]>>
    BasicProvers.EVERY_CASE_TAC>>
    fs convs>>
    rpt(pairarg_tac>>fs[StackArgs_def,sa_gs_def,wStackLoad_def,PushHandler_def,StackHandlerArgs_def,PopHandler_def])>>
    rveq>>fs convs>>
    match_mp_tac stack_move_sa_gs>>fs convs))
  >>
    rpt(pairarg_tac>>fs[sa_gs_def])>>rveq>>fs[sa_gs_def]);

val stack_move_sr_gs = Q.store_thm("stack_move_sr_gs",`
  ∀n st off i p k.
  i < k ∧
  good_syntax p k ⇒
  good_syntax (stack_move n st off i p) k`,
  Induct>>rw[stack_move_def,sr_gs_def]);

val word_to_stack_sr_gs = Q.store_thm("word_to_stack_sr_gs",`
  ∀p n args.
  post_alloc_conventions (FST args) p ∧
  4 ≤ FST args ⇒
  good_syntax (FST(word_to_stack$comp p n args)) (FST args+2)`,
  recInduct comp_ind >>fs[comp_def,sa_gs_def,FORALL_PROD,wRegWrite1_def,wLive_def]>>rw[]>> fs convs
  >-
    (fs[wMove_def]>>
    qpat_abbrev_tac`ls = parmove A`>>
    pop_assum kall_tac>>
    qid_spec_tac`ls`>>Induct>>fs[wMoveAux_def,sr_gs_def]>>
    Cases_on`ls`>>
    fs[FORALL_PROD,wMoveAux_def,wMoveSingle_def]>>rw[]>>
    Cases_on`p_1''`>>Cases_on`p_2'`>>fs[format_var_def]>>
    BasicProvers.EVERY_CASE_TAC>>fs convs)
  >-
    (Cases_on`i`>>TRY(Cases_on`a`)>>TRY(Cases_on`m`)>>TRY(Cases_on`r`)>>
    fs[wInst_def,wRegWrite1_def,wReg1_def,wReg2_def]>>
    BasicProvers.EVERY_CASE_TAC>>
    fs[wStackLoad_def,sr_gs_def]>>fs convs)
  >- (fs[wReg1_def,SeqStackFree_def]>>BasicProvers.EVERY_CASE_TAC>>fs[sr_gs_def,wStackLoad_def])
  >- rpt (pairarg_tac>>fs convs)
  >- (rpt (pairarg_tac>>fs convs)>>
  Cases_on`ri`>>fs[wReg1_def,wRegImm2_def,wReg2_def]>>BasicProvers.EVERY_CASE_TAC>>fs[]>>rveq>>fs[wStackLoad_def,sr_gs_def])
  >-
    (fs[wReg1_def]>>BasicProvers.EVERY_CASE_TAC>>
    fs[sr_gs_def,wStackLoad_def])
  >-
    (Cases_on`ret`>>fs[]
    >-
    (Cases_on`dest`>>fs[call_dest_def,wReg2_def,SeqStackFree_def]>>
    rpt (IF_CASES_TAC>>fs convs)>>
    fs[wStackLoad_def,sr_gs_def])
    >>
    (PairCases_on`x`>>
    Cases_on`dest`>>fs[call_dest_def,wReg2_def,SeqStackFree_def]>>
    rpt (IF_CASES_TAC>>fs convs)>>
    Cases_on`handler`>>TRY(PairCases_on`x`)>>TRY(PairCases_on`x'`)>>
    fs convs>>
    rpt(pairarg_tac>>fs[StackArgs_def,sa_gs_def,wStackLoad_def,PushHandler_def,StackHandlerArgs_def,PopHandler_def])>>
    rveq>>fs convs>>
    match_mp_tac stack_move_sr_gs>>fs convs))
  >- (rpt(pairarg_tac>>fs[sr_gs_def])>>rveq>>fs[sr_gs_def]));

val stack_move_sl_gs = Q.store_thm("stack_move_sl_gs",`
  ∀n st off i p.
  good_syntax p 1 2 0 ⇒
  good_syntax (stack_move n st off i p) 1 2 0`,
  Induct>>rw[stack_move_def,sl_gs_def]);

val word_to_stack_sl_gs = Q.store_thm("word_to_stack_sl_gs",`
  ∀p n args.
  post_alloc_conventions (FST args) p ⇒
  good_syntax (FST(word_to_stack$comp p n args)) 1 2 0`,
  ho_match_mp_tac comp_ind >>fs[comp_def,sl_gs_def,FORALL_PROD,wRegWrite1_def,wLive_def]>>rw[]>>fs convs
  >-
    (fs[wMove_def]>>
    qpat_abbrev_tac`ls = MAP f A`>>
    pop_assum kall_tac>>
    qid_spec_tac`ls`>>Induct>>fs[wMoveAux_def,sl_gs_def]>>
    Cases_on`ls`>>
    fs[FORALL_PROD,wMoveAux_def,wMoveSingle_def]>>rw[]>>
    BasicProvers.EVERY_CASE_TAC>>fs convs)
  >-
    (Cases_on`i`>>TRY(Cases_on`a`)>>TRY(Cases_on`m`)>>TRY(Cases_on`r`)>>
    fs[wInst_def,wRegWrite1_def,wReg1_def,wReg2_def]>>
    BasicProvers.EVERY_CASE_TAC>>
    fs[wStackLoad_def,sl_gs_def]>>fs convs)
  >- (fs[wReg1_def,SeqStackFree_def]>>BasicProvers.EVERY_CASE_TAC>>fs[sl_gs_def,wStackLoad_def])
  >- rpt (pairarg_tac>>fs convs)
  >- (rpt (pairarg_tac>>fs convs)>>
  Cases_on`ri`>>fs[wReg1_def,wRegImm2_def,wReg2_def]>>BasicProvers.EVERY_CASE_TAC>>fs[]>>rveq>>fs[wStackLoad_def,sl_gs_def])
  >- (fs[wReg1_def]>>BasicProvers.EVERY_CASE_TAC>>fs[sl_gs_def,wStackLoad_def])
  >-
    (Cases_on`ret`>>fs[]
    >-
    (Cases_on`dest`>>fs[call_dest_def,wReg2_def,SeqStackFree_def]>>
    rpt (IF_CASES_TAC>>fs convs)>>
    fs[wStackLoad_def,sl_gs_def])
    >>
    (PairCases_on`x`>>
    Cases_on`dest`>>fs[call_dest_def,wReg2_def,SeqStackFree_def]>>
    rpt (IF_CASES_TAC>>fs convs)>>
    Cases_on`handler`>>TRY(PairCases_on`x`)>>TRY(PairCases_on`x'`)>>
    fs convs>>
    rpt(pairarg_tac>>fs[StackArgs_def,sl_gs_def,wStackLoad_def,PushHandler_def,StackHandlerArgs_def,PopHandler_def])>>
    rveq>>fs convs>>
    match_mp_tac stack_move_sl_gs>>fs convs))
  >- (rpt(pairarg_tac>>fs[sl_gs_def])>>rveq>>fs[sl_gs_def]));

val data_to_word_compile_imp = Q.store_thm("data_to_word_compile_imp",
  `LENGTH mc_conf.target.config.avoid_regs + 9 ≤ mc_conf.target.config.reg_count ∧
    EVERY (λn. data_num_stubs ≤ n) (MAP FST prog) ∧
    compile (c:'a backend$config).word_to_word_conf mc_conf.target.config
        (stubs(:'a) c.data_conf ++ MAP (compile_part c.data_conf) prog) = (col,p) ==>
    code_rel c.data_conf (fromAList prog)
      (fromAList (stubs(:α) c.data_conf ++ MAP ((compile_part c.data_conf) :
         num # num # dataLang$prog -> num # num # 'a wordLang$prog) prog)) /\
    code_rel_ext
      (fromAList (stubs(:α) c.data_conf ++ MAP ((compile_part c.data_conf) :
         num # num # dataLang$prog -> num # num # 'a wordLang$prog) prog),fromAList p) /\
    EVERY
    (λ(n,m,prog').
       flat_exp_conventions prog' ∧
       post_alloc_conventions
         (mc_conf.target.config.reg_count −
          (LENGTH mc_conf.target.config.avoid_regs + 5)) prog' ∧
       (addr_offset_ok 0w mc_conf.target.config ⇒
        full_inst_ok_less mc_conf.target.config prog') ∧
       (mc_conf.target.config.two_reg_arith ⇒ every_inst two_reg_inst prog')) p /\
    (compile mc_conf.target.config p = (c2,prog1) ==>
     EVERY (\p. stack_to_labProof$good_syntax p 1 2 0) (MAP SND prog1) /\
     EVERY stack_allocProof$good_syntax (MAP SND prog1) /\
     EVERY (\p. stack_removeProof$good_syntax p (mc_conf.target.config.reg_count - (LENGTH mc_conf.target.config.avoid_regs +3)))
       (MAP SND prog1))`,
  fs[code_rel_def,code_rel_ext_def]>>strip_tac>>
  CONJ_TAC >-
    (fs[lookup_fromAList]
     \\ simp[ALOOKUP_APPEND]
     \\ conj_tac THEN1
      (`ALL_DISTINCT (MAP FST (stubs (:α) c.data_conf))` by EVAL_TAC
       \\ pop_assum mp_tac
       \\ qspec_tac (`stubs (:α) c.data_conf`,`xs`)
       \\ Induct \\ fs [FORALL_PROD]
       \\ rw [] \\ fs []
       \\ fs [EVERY_MEM,MEM_MAP,FORALL_PROD]
       \\ rw [] \\ fs [] \\ rfs [])
     \\ gen_tac
     \\ reverse BasicProvers.TOP_CASE_TAC
     >- (rw[] \\ imp_res_tac ALOOKUP_MEM
         \\ `EVERY (\n. FST n < data_num_stubs) (stubs (:α) c.data_conf)` by EVAL_TAC
         \\ rpt (pop_assum mp_tac)
         \\ rewrite_tac[EVERY_MAP,EVERY_MEM,MEM]
         \\ rpt strip_tac
         \\ res_tac \\ fs []) >>
     ntac 4 (last_x_assum kall_tac)>>
     qid_spec_tac`n` >>
     Induct_on`prog`>>rw[]>>PairCases_on`h`>>
     fs[data_to_wordTheory.compile_part_def]>>
     IF_CASES_TAC>>fs[]) >>
  CONJ_TAC>-
    (fs[lookup_fromAList,word_to_wordTheory.compile_def]>>
    pairarg_tac>>fs[]>>rveq>>
    qmatch_goalsub_abbrev_tac`ALOOKUP ls` >>
    `LENGTH ls = LENGTH n_oracles` by
      (fs[word_to_wordTheory.next_n_oracle_def,Abbr`ls`]>>
      metis_tac[LENGTH_GENLIST]) >>
    qpat_x_assum`Abbrev(ls = _)`kall_tac >>
    pop_assum mp_tac>>
    ntac 3 (pop_assum kall_tac)>>
    qid_spec_tac`n_oracles`>>
    qid_spec_tac`ls`>>
    Induct>>fs[]>>rw[]>>
    Cases_on`n_oracles`>>fs[]>>
    PairCases_on`h`>>fs[]>>
    fs[word_to_wordTheory.full_compile_single_def,word_to_wordTheory.compile_single_def,data_to_wordTheory.compile_part_def]>>
    IF_CASES_TAC \\ fs[] \\ rw[] >>
    metis_tac[]) >>
  CONJ_ASM1_TAC>-
    (assume_tac(GEN_ALL data_to_wordProofTheory.data_to_word_compile_conventions)>>
    pop_assum (qspecl_then [`c.word_to_word_conf`,`prog`,`c.data_conf`,`mc_conf.target.config`] assume_tac)>>
    rfs[data_to_wordTheory.compile_def])>>
  qpat_x_assum`EVERY _ (MAP FST _)`kall_tac >>
  qmatch_assum_rename_tac`_ pprog = _` >>
  rw[]>>fs[word_to_stackTheory.compile_def]>>pairarg_tac>>fs[]>>rveq>>
  fs[word_to_stackTheory.raise_stub_def,sr_gs_def,sa_gs_def,sl_gs_def]>>
  fs[word_to_stackTheory.compile_word_to_stack_def]>>
  qabbrev_tac`b=[4w]`>>pop_assum kall_tac>>
  qpat_x_assum`A=(col,p)` kall_tac>>
  rpt (pop_assum mp_tac)>>
  map_every qid_spec_tac [`progs`,`bitmaps`,`p`,`b`]>>
  Induct_on`p`>>
  fs[compile_word_to_stack_def,FORALL_PROD]>>rw[]>>
  pairarg_tac>>fs[]>>
  pairarg_tac>>fs[]>>
  rveq>>fs[]>>
  (reverse CONJ_TAC>-metis_tac[])>>
  qpat_x_assum`A=(prog',bitmaps')` mp_tac>>
  FULL_SIMP_TAC std_ss [compile_prog_def,LET_THM]>>
  qpat_abbrev_tac`m = MAX A B`>>
  pairarg_tac>>fs[]>>strip_tac>>
  rveq>>fs[]>>
  pop_assum (assume_tac o SYM o Q.AP_TERM`FST`)>>fs convs
  >-
    (match_mp_tac word_to_stack_sl_gs>>fs convs)
  >-
    metis_tac[word_to_stack_sa_gs]
  >>
    qpat_abbrev_tac`rc = A - B:num`>>
    qpat_abbrev_tac`rc2 = A - B:num`>>
    qpat_abbrev_tac`arg = (A,B,C)`>>
    `rc2 = FST arg + 2` by
      (unabbrev_all_tac>>fs[])>>
    simp[]>>
    match_mp_tac word_to_stack_sr_gs>>
    fs convs>>
    unabbrev_all_tac>>fs[]);

val stack_alloc_syntax = Q.store_thm("stack_alloc_syntax",
  `10 ≤ sp ∧ (* I think 10 has to do with the number of vars used by the gc implementation *)
    EVERY (λp. good_syntax p 1 2 0) (MAP SND prog1) /\
    EVERY (\p. stack_removeProof$good_syntax p sp)
       (MAP SND prog1) ==>
    EVERY (λp. good_syntax p 1 2 0) (MAP SND (compile c.data_conf prog1)) /\
    EVERY (\p. stack_removeProof$good_syntax p sp)
       (MAP SND (compile c.data_conf prog1))`,
  fs[stack_allocTheory.compile_def]>>
  EVAL_TAC>>fs[]>>
  qid_spec_tac`prog1`>>Induct>>
  fs[stack_allocTheory.prog_comp_def,FORALL_PROD]>>
  ntac 3 strip_tac>>fs[]>>
  qpat_abbrev_tac`l = next_lab A 1` >> pop_assum kall_tac>>
  qpat_x_assum`good_syntax p_2 1 2 0` mp_tac>>
  qpat_x_assum`good_syntax p_2 sp` mp_tac>>
  qpat_x_assum`10 ≤ sp` mp_tac>>
  rpt (pop_assum kall_tac)>>
  map_every qid_spec_tac [`p_2`,`l`,`p_1`]>>
  ho_match_mp_tac stack_allocTheory.comp_ind>>
  Cases_on`p_2`>>rw[]>>
  simp[Once stack_allocTheory.comp_def]>>fs convs>>
  TRY(ONCE_REWRITE_TAC [stack_allocTheory.comp_def]>>
    Cases_on`o'`>>TRY(PairCases_on`x`)>>fs convs>>
    BasicProvers.EVERY_CASE_TAC)>>
  rpt(pairarg_tac>>fs convs));

val word_to_stack_compile_imp = Q.store_thm("word_to_stack_compile_imp",
  `word_to_stack$compile c p = (c2,prog1) ==>
    (case c2.bitmaps of [] => F | h::v1 => 4w = h)`,
  fs [word_to_stackTheory.compile_def] \\ pairarg_tac \\ fs [] \\ rw [] \\ fs []
  \\ imp_res_tac compile_word_to_stack_isPREFIX
  \\ Cases_on `bitmaps` \\ fs []);

val make_init_opt_imp_bitmaps_limit = Q.store_thm("make_init_opt_imp_bitmaps_limit",
  `make_init_opt max_heap bitmaps k code s = SOME x ==>
    LENGTH (bitmaps:'a word list) < dimword (:'a) − 1`,
  fs [stack_removeProofTheory.make_init_opt_def]
  \\ every_case_tac \\ fs [] \\ rw []
  \\ fs [stack_removeProofTheory.init_prop_def,
         stack_removeProofTheory.init_reduce_def]);

val data_to_word_names = Q.store_thm("data_to_word_names",
  `word_to_word$compile c1 c2 (stubs(:α)c.data_conf ++ MAP (compile_part c3) prog) = (col,p) ==>
    MAP FST p = (MAP FST (stubs(:α)c.data_conf))++MAP FST prog`,
  rw[]>>assume_tac(GEN_ALL word_to_wordProofTheory.compile_to_word_conventions)>>
  pop_assum (qspecl_then [`c1`,`stubs(:α)c.data_conf++(MAP (compile_part c3) prog)`,`c2`] assume_tac)>>rfs[]>>
  fs[MAP_MAP_o,MAP_EQ_f,FORALL_PROD,data_to_wordTheory.compile_part_def]);

val word_to_stack_names = Q.prove(
  `word_to_stack$compile c1 p = (c2,prog1) ==>
    MAP FST prog1 = raise_stub_location::MAP FST p`,
  fs [word_to_stackTheory.compile_def] \\ pairarg_tac \\ fs []
  \\ rw [] \\ fs []>>
  pop_assum mp_tac>>
  qabbrev_tac`b=[4w]`>>pop_assum kall_tac>>
  map_every qid_spec_tac [`progs`,`bitmaps`,`p`,`b`]>>
  Induct_on`p`>>fs[FORALL_PROD,word_to_stackTheory.compile_word_to_stack_def]>>
  rw[]>>rpt (pairarg_tac>>fs[])>>
  rveq>>fs[]>>
  metis_tac[]);

val stack_alloc_names = Q.store_thm("stack_alloc_names",
  `stack_alloc$compile c1 p = prog1 ==>
    MAP FST prog1 = gc_stub_location::MAP FST p`,
  fs [stack_allocTheory.compile_def,stack_allocTheory.stubs_def] \\ rw []
  \\ fs [MAP_MAP_o,MAP_EQ_f,FORALL_PROD,stack_allocTheory.prog_comp_def]);

val code_installed'_def = Define `
  (code_installed' n [] code ⇔ T) /\
  (code_installed' n (x::xs) code ⇔
     if is_Label x then code_installed' n xs code
     else asm_fetch_aux n code = SOME x ∧ code_installed' (n + 1) xs code)`;

val code_installed'_cons_label = Q.store_thm("code_installed'_cons_label",
  `!lines pos.
      is_Label h ==>
      code_installed' pos lines (Section n (h::xs)::other) =
      code_installed' pos lines (Section n xs::other)`,
  Induct \\ fs [code_installed'_def]
  \\ rw [] \\ fs [labSemTheory.asm_fetch_aux_def]);

val code_installed'_cons_non_label = Q.store_thm("code_installed'_cons_non_label",
  `!lines pos.
      ~is_Label h ==>
      code_installed' (pos+1) lines (Section n (h::xs)::other) =
      code_installed' pos lines (Section n xs::other)`,
  Induct \\ fs [code_installed'_def]
  \\ rw [] \\ fs [labSemTheory.asm_fetch_aux_def])
  |> Q.SPECL [`lines`,`0`] |> SIMP_RULE std_ss [];

val code_installed'_simp = Q.store_thm("code_installed'_simp",
  `!lines. code_installed' 0 lines (Section n (lines ++ rest)::other)`,
  Induct \\ fs [code_installed'_def]
  \\ fs [labSemTheory.asm_fetch_aux_def]
  \\ rpt strip_tac \\ IF_CASES_TAC
  \\ fs [code_installed'_cons_label,code_installed'_cons_non_label]);

val loc_to_pc_skip_section = Q.store_thm("loc_to_pc_skip_section",
  `!lines.
      n <> p ==>
      loc_to_pc n 0 (Section p lines :: xs) =
      case loc_to_pc n 0 xs of
      | NONE => NONE
      | SOME k => SOME (k + LENGTH (FILTER (\x. ~(is_Label x)) lines))`,
  Induct \\ once_rewrite_tac [labSemTheory.loc_to_pc_def] \\ fs []
  THEN1 (every_case_tac \\ fs [])
  \\ strip_tac \\ IF_CASES_TAC \\ fs [] \\ CASE_TAC \\ fs []);

val asm_fetch_aux_add = Q.store_thm("asm_fetch_aux_add",
  `!ys pc rest.
      asm_fetch_aux (pc + LENGTH (FILTER (λx. ¬is_Label x) ys))
        (Section pos ys::rest) = asm_fetch_aux pc rest`,
  Induct \\ fs [labSemTheory.asm_fetch_aux_def,ADD1]);

val labs_correct_def = Define `
  (labs_correct n [] code ⇔ T) /\
  (labs_correct n (x::xs) code ⇔
     if is_Label x then labs_correct n xs code /\
       (case x of
        | Label l1 l2 v2 => loc_to_pc l1 l2 code = SOME n
        | _ => T)
     else labs_correct (n + 1) xs code)`

val is_Label_def = labSemTheory.is_Label_def

val code_installed_eq = Q.store_thm("code_installed_eq",
  `!pc xs code.
      code_installed pc xs code <=>
      code_installed' pc xs code /\ labs_correct pc xs code`,
  Induct_on `xs`
  \\ fs [code_installed_def,code_installed'_def,labs_correct_def]
  \\ ntac 3 strip_tac \\ fs []
  \\ IF_CASES_TAC \\ fs []
  \\ Cases_on `h` \\ fs [is_Label_def]
  \\ rw [] \\ eq_tac \\ fs []);

val code_installed_cons = Q.store_thm("code_installed_cons",
  `!xs ys pos pc.
      code_installed' pc xs rest ==>
      code_installed' (pc + LENGTH (FILTER (λx. ¬is_Label x) ys)) xs
        (Section pos ys :: rest)`,
  Induct \\ fs [] \\ fs [code_installed'_def]
  \\ ntac 4 strip_tac \\ IF_CASES_TAC \\ fs []
  \\ rw [] \\ res_tac \\ fs [asm_fetch_aux_add]);

val code_installed_prog_to_section_lemma = Q.prove(
  `!prog4 n prog3.
      ALOOKUP prog4 n = SOME prog3 ==>
      ?pc.
        code_installed' pc (append (FST (flatten prog3 n (next_lab prog3 1))))
          (MAP prog_to_section prog4) /\
        loc_to_pc n 0 (MAP prog_to_section prog4) = SOME pc`,
  Induct_on `prog4` \\ fs [] \\ Cases \\ fs [ALOOKUP_def] \\ rw []
  THEN1
   (fs [stack_to_labTheory.prog_to_section_def] \\ pairarg_tac \\ fs []
    \\ once_rewrite_tac [labSemTheory.loc_to_pc_def]
    \\ fs [code_installed'_simp])
  \\ res_tac \\ fs [stack_to_labTheory.prog_to_section_def] \\ pairarg_tac
  \\ fs [loc_to_pc_skip_section,code_installed_cons]);

val extract_labels_def = labPropsTheory.extract_labels_def
val extract_labels_append = labPropsTheory.extract_labels_append

val labs_correct_hd = Q.store_thm("labs_correct_hd",`
  ∀extra l.
  ALL_DISTINCT (extract_labels (extra++l)) ∧
  EVERY (λ(l1,l2). l1 = n ∧ l2 ≠ 0) (extract_labels (extra++l)) ⇒
  labs_correct (LENGTH (FILTER (\x. ~(is_Label x)) extra)) l (Section n (extra++l) ::code)`,
  Induct_on`l`>>fs[labs_correct_def]>>rw[]
  >-
    (first_x_assum(qspec_then `extra++[h]` mp_tac)>>
    Cases_on`h`>>fs[extract_labels_def,labSemTheory.is_Label_def,FILTER_APPEND]>>
    metis_tac[APPEND_ASSOC,APPEND])
  >-
    (Cases_on`h`>>fs[]>>
    ntac 2 (pop_assum mp_tac)>>
    rpt (pop_assum kall_tac)>>
    Induct_on`extra`>>fs[extract_labels_def]>>rw[]
    >-
      (once_rewrite_tac [labSemTheory.loc_to_pc_def]>>
      fs[])
    >>
    `n = n' ∧ n0 ≠ 0` by
      (Cases_on`h`>>fs[extract_labels_append,extract_labels_def])>>
    once_rewrite_tac [labSemTheory.loc_to_pc_def]>>
    Cases_on`h`>>fs[extract_labels_def]>>
    IF_CASES_TAC>>fs[extract_labels_append,extract_labels_def])
  >>
    first_x_assum(qspec_then `extra++[h]` mp_tac)>>
    Cases_on`h`>>fs[extract_labels_def,FILTER_APPEND]>>
    metis_tac[APPEND_ASSOC,APPEND]);

val labels_ok_imp = Q.store_thm("labels_ok_imp",
  `∀code.
   labels_ok code ⇒
   EVERY sec_labels_ok code ∧
   ALL_DISTINCT (MAP Section_num code) ∧
   EVERY (ALL_DISTINCT o extract_labels o Section_lines) code`,
  Induct_on`code` \\ simp[]
  \\ Cases \\ simp[]
  \\ fs[labels_ok_def]
  \\ strip_tac \\ fs[]
  \\ reverse conj_tac
  >- (
    strip_tac \\ fs[MEM_MAP,EXISTS_PROD] \\ fs[]
    \\ qmatch_assum_rename_tac`MEM sec code`
    \\ first_x_assum(qspec_then`sec`mp_tac) \\ simp[]
    \\ CASE_TAC \\ fs[] )
  \\ Induct_on`l` \\ fs[]
  \\ Cases \\ fs[]);

val labels_ok_labs_correct = Q.store_thm("labels_ok_labs_correct",`
  ∀code.
  labels_ok code ⇒
  EVERY ( λs. case s of Section n lines =>
      case loc_to_pc n 0 code of
       SOME pc => labs_correct pc lines code
      | _ => T) code`,
  Induct>>fs[labels_ok_def]>>Cases_on`h`>>fs[]>>
  rw[]
  >-
    (once_rewrite_tac[labSemTheory.loc_to_pc_def]>>fs[]>>
    assume_tac (Q.SPEC `[]` labs_correct_hd)>>fs[])
  >>
    fs[EVERY_MEM]>>rw[]>>res_tac>>
    Cases_on`s`>>fs[]>>
    `n ≠ n'` by
      (fs[MEM_MAP]>>
      last_x_assum kall_tac>>
      last_x_assum (qspec_then`Section n' l'` assume_tac)>>rfs[])>>
    fs[loc_to_pc_skip_section]>>
    BasicProvers.EVERY_CASE_TAC>>fs[]>>
    pop_assum mp_tac>>
    pop_assum kall_tac>>
    pop_assum mp_tac>>
    pop_assum mp_tac>>
    pop_assum mp_tac>>
    ntac 2 (pop_assum kall_tac)>>
    pop_assum mp_tac>>
    pop_assum mp_tac>>
    rpt (pop_assum kall_tac)>>
    qid_spec_tac`x`>>
    Induct_on`l'`>>rw[labs_correct_def]>>fs[AND_IMP_INTRO]
    >-
      (first_assum match_mp_tac>>
      Cases_on`h`>>fs[ALL_DISTINCT,extract_labels_def])
    >-
      (Cases_on`h`>>fs[]>>
      `n'' ≠ n` by
        (fs[extract_labels_def]>>
        first_x_assum(qspec_then`n'',n0` mp_tac)>>fs[])>>
      pop_assum mp_tac>>
      pop_assum mp_tac>>
      ntac 5 (pop_assum kall_tac)>>
      ntac 2 (pop_assum mp_tac)>>
      rpt (pop_assum kall_tac)>>
      map_every qid_spec_tac [`n''`,`n0`,`l`]>>
      Induct>> once_rewrite_tac [labSemTheory.loc_to_pc_def]>>fs[]>>
      rw[]>>fs[is_Label_def,extract_labels_def,AND_IMP_INTRO]
      >-
        (fs[FORALL_PROD]>>metis_tac[])
      >-
        (fs[FORALL_PROD]>>metis_tac[])
      >-
        (first_assum match_mp_tac>>
        Cases_on`h`>>fs[extract_labels_def])
      >>
        rveq>>fs[loc_to_pc_skip_section]>>
        (first_x_assum(qspecl_then[`n0`,`n''`] mp_tac)>>
        impl_tac>- (Cases_on`h`>>fs[extract_labels_def])>>
        fs[]))
    >>
      first_x_assum (qspec_then`x+1` mp_tac)>>
      impl_tac
      >-
        (Cases_on`h`>>fs[ALL_DISTINCT,extract_labels_def])
      >>
       fs[]);

val labs_correct_append = Q.store_thm("labs_correct_append",`
  ∀ls pc.
  labs_correct pc (ls ++ rest) code ⇒
  labs_correct pc ls code`,
  Induct>>fs[labs_correct_def]>>rw[]);

val code_installed_prog_to_section = Q.store_thm("code_installed_prog_to_section",
  `!prog4 n prog3.
      labels_ok (MAP prog_to_section prog4) ∧
      ALOOKUP prog4 n = SOME prog3 ==>
      ?pc.
        code_installed pc (append (FST (flatten prog3 n (next_lab prog3 1))))
          (MAP prog_to_section prog4) /\
        loc_to_pc n 0 (MAP prog_to_section prog4) = SOME pc`,
  rpt strip_tac \\ fs [code_installed_eq]
  \\ drule code_installed_prog_to_section_lemma \\ strip_tac
  \\ asm_exists_tac \\ fs []
  \\ imp_res_tac labels_ok_labs_correct
  \\ fs[EVERY_MEM,MEM_MAP]
  \\ imp_res_tac ALOOKUP_MEM
  \\ first_x_assum (qspec_then`prog_to_section (n,prog3)` mp_tac)
  \\ impl_tac >- metis_tac[]
  \\ BasicProvers.TOP_CASE_TAC>>fs[stack_to_labTheory.prog_to_section_def]
  \\ pairarg_tac>>fs[]>>rveq>>fs[]
  \\ metis_tac[labs_correct_append]);

val upshift_downshift_syntax = Q.store_thm("upshift_downshift_syntax",`
  ∀n n0.
  good_syntax (upshift n n0) 1 2 0 ∧
  good_syntax (downshift n n0) 1 2 0`,
  completeInduct_on`n0`>>simp[Once stack_removeTheory.upshift_def,Once stack_removeTheory.downshift_def]>>strip_tac>>IF_CASES_TAC>>simp[sl_gs_def]>>
  first_assum match_mp_tac>>EVAL_TAC>>fs[])

val stack_remove_syntax_pres = Q.store_thm("stack_remove_syntax_pres",
  `Abbrev (prog3 = compile off n bitmaps k pos prog2) /\
    EVERY (λp. good_syntax p 1 2 0) (MAP SND prog2) ==>
    EVERY (λp. good_syntax p 1 2 0) (MAP SND prog3)`,
  rw[]>>
  unabbrev_all_tac>>fs[]>>
  EVAL_TAC>>
  IF_CASES_TAC>>EVAL_TAC>>
  pop_assum kall_tac>>
  fs[EVERY_MAP,EVERY_MEM,FORALL_PROD,stack_removeTheory.prog_comp_def]>>
  TRY(CONJ_TAC>-
    (Induct_on`bitmaps`>>fs[stack_removeTheory.store_list_code_def]>>
    EVAL_TAC>>fs[]))>>
  (rw[]>>res_tac>> pop_assum mp_tac>> rpt (pop_assum kall_tac)>>
  map_every qid_spec_tac[`p_2`,`k`,`off`]>>
  ho_match_mp_tac stack_removeTheory.comp_ind>>
  Cases_on`p_2`>>rw[]>>
  ONCE_REWRITE_TAC [stack_removeTheory.comp_def]>>
  fs convs>>
  TRY(IF_CASES_TAC>>fs convs)
  >-
    (BasicProvers.EVERY_CASE_TAC>>fs[])
  >>
  TRY (* stack_alloc and stack_free *)
    (completeInduct_on`n`>>simp[Once stack_removeTheory.stack_alloc_def,stack_removeTheory.single_stack_alloc_def,Once stack_removeTheory.stack_free_def,stack_removeTheory.single_stack_free_def]>>
    rpt (IF_CASES_TAC>>fs convs)>>
    first_assum match_mp_tac>>
    EVAL_TAC>>fs[]>>NO_TAC)
  >- simp[stack_removeTheory.stack_store_def,stack_removeTheory.stack_load_def,sl_gs_def,upshift_downshift_syntax]
  >- simp[stack_removeTheory.stack_store_def,stack_removeTheory.stack_load_def,sl_gs_def,upshift_downshift_syntax]
  >- EVAL_TAC));

val stack_names_syntax_pres = Q.store_thm("stack_names_syntax_pres",
  `Abbrev (prog4 = stack_names$compile f prog3) /\
    EVERY (λp. good_syntax p 1 2 0) (MAP SND prog3) ==>
    EVERY (λp. good_syntax p (find_name f 1)
                             (find_name f 2)
                             (find_name f 0)) (MAP SND prog4)`,
  rw[]>>
  unabbrev_all_tac>>fs[stack_namesTheory.compile_def]>>
  fs[EVERY_MAP,EVERY_MEM,FORALL_PROD,stack_namesTheory.prog_comp_def]>>
  rw[]>>res_tac>> pop_assum mp_tac>> rpt (pop_assum kall_tac)>>
  map_every qid_spec_tac[`p_2`,`f`]>>
  ho_match_mp_tac stack_namesTheory.comp_ind>>
  Cases_on`p_2`>>rw[]>>
  ONCE_REWRITE_TAC [stack_namesTheory.comp_def]>>
  fs convs>>
  BasicProvers.EVERY_CASE_TAC>>fs[]);

val MEM_pair_IMP = Q.store_thm("MEM_pair_IMP",
  `!xs. MEM (x,y) xs ==> MEM x (MAP FST xs) /\ MEM y (MAP SND xs)`,
  Induct \\ fs [FORALL_PROD] \\ metis_tac []);

val IS_SOME_EQ_CASE = Q.store_thm("IS_SOME_EQ_CASE",
  `IS_SOME x <=> case x of NONE => F | SOME _ => T`,
  Cases_on `x` \\ fs []);

val compile_eq_imp = Q.prove(
  `x = x' /\ y = y' ==>
    lab_to_target$compile x y = lab_to_target$compile x' y'`,
  fs []);

val BIJ_FLOOKUP_MAPKEYS = Q.store_thm("BIJ_FLOOKUP_MAPKEYS",
  `BIJ bij UNIV UNIV ==>
    FLOOKUP (MAP_KEYS (LINV bij UNIV) f) n = FLOOKUP f (bij n)`,
  fs [FLOOKUP_DEF,MAP_KEYS_def,BIJ_DEF] \\ strip_tac
  \\ match_mp_tac (METIS_PROVE []
      ``x=x'/\(x /\ x' ==> y=y') ==> (if x then y else z) = (if x' then y' else z)``)
  \\ fs [] \\ rw []
  THEN1 (eq_tac \\ rw [] \\ metis_tac [BIJ_LINV_INV,BIJ_DEF,IN_UNIV,LINV_DEF])
  \\ `BIJ (LINV bij UNIV) UNIV UNIV` by metis_tac [BIJ_LINV_BIJ,BIJ_DEF]
  \\ `INJ (LINV bij UNIV) (FDOM f) UNIV` by fs [INJ_DEF,IN_UNIV,BIJ_DEF]
  \\ fs [MAP_KEYS_def] \\ metis_tac [BIJ_LINV_INV,BIJ_DEF,IN_UNIV,LINV_DEF]);

val word_list_exists_imp = Q.store_thm("word_list_exists_imp",
  `dm = addresses a n /\
    dimindex (:'a) DIV 8 * n < dimword (:'a) ∧ good_dimindex (:'a) ⇒
    word_list_exists a n (fun2set (m1,dm:'a word set))`,
  metis_tac [stack_removeProofTheory.word_list_exists_addresses]);

val addresses_thm = Q.store_thm("addresses_thm",
  `!n a. addresses a n = { a + n2w i * bytes_in_word | i < n }`,
  Induct \\ fs [stack_removeProofTheory.addresses_def]
  \\ rw [EXTENSION] \\ eq_tac \\ rw []
  THEN1 (qexists_tac `0` \\ fs [])
  THEN1 (qexists_tac `SUC i` \\ fs [ADD1,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB])
  \\ Cases_on `i` \\ fs []
  \\ disj2_tac \\ fs []
  \\ once_rewrite_tac [CONJ_COMM]
  \\ asm_exists_tac \\ fs []
  \\ fs [ADD1,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]);

val IMP_MULT_DIV_LESS = Q.store_thm("IMP_MULT_DIV_LESS",
  `m <> 0 /\ d < k ==> m * (d DIV m) < k`,
  strip_tac \\ `0 < m` by decide_tac
  \\ drule DIVISION
  \\ disch_then (qspec_then `d` assume_tac)
  \\ decide_tac);

val WORD_LS_IMP = Q.store_thm("WORD_LS_IMP",
  `a <=+ b ==>
    ?k. Abbrev (b = a + n2w k) /\
        w2n (b - a) = k /\
        (!w. a <=+ w /\ w <+ b <=> ?i. w = a + n2w i /\ i < k)`,
  Cases_on `a` \\ Cases_on `b` \\ fs [WORD_LS]
  \\ fs [markerTheory.Abbrev_def]
  \\ full_simp_tac std_ss [GSYM word_sub_def,addressTheory.word_arith_lemma2]
  \\ fs [] \\ rw [] THEN1
   (rewrite_tac [GSYM word_sub_def]
    \\ once_rewrite_tac [WORD_ADD_COMM]
    \\ rewrite_tac [WORD_ADD_SUB])
  \\ Cases_on `w` \\ fs [WORD_LO,word_add_n2w]
  \\ eq_tac \\ rw [] \\ fs []
  \\ rename1 `k < m:num` \\ qexists_tac `k - n` \\ fs [])

val byte_aligned_mult = Q.store_thm("byte_aligned_mult",
  `good_dimindex (:'a) ==>
    byte_aligned (a + bytes_in_word * n2w i) = byte_aligned (a:'a word)`,
  fs [alignmentTheory.byte_aligned_def,labPropsTheory.good_dimindex_def]
  \\ rw [] \\ fs [bytes_in_word_def,word_mul_n2w]
  \\ once_rewrite_tac [MULT_COMM]
  \\ rewrite_tac [GSYM (EVAL ``2n**2``),GSYM (EVAL ``2n**3``),
        data_to_wordPropsTheory.aligned_add_pow]);

val DIV_LESS_DIV = Q.store_thm("DIV_LESS_DIV",
  `n MOD k = 0 /\ m MOD k = 0 /\ n < m /\ 0 < k ==> n DIV k < m DIV k`,
  strip_tac
  \\ drule DIVISION \\ disch_then (qspec_then `n` (strip_assume_tac o GSYM))
  \\ drule DIVISION \\ disch_then (qspec_then `m` (strip_assume_tac o GSYM))
  \\ rfs [] \\ metis_tac [LT_MULT_LCANCEL]);

val MOD_SUB_LEMMA = Q.store_thm("MOD_SUB_LEMMA",
  `n MOD k = 0 /\ m MOD k = 0 /\ 0 < k ==> (n - m) MOD k = 0`,
  Cases_on `m <= n` \\ fs []
  \\ imp_res_tac LESS_EQ_EXISTS \\ rw []
  \\ qpat_x_assum `(m + _) MOD k = 0` mp_tac
  \\ drule MOD_PLUS
  \\ disch_then (fn th => once_rewrite_tac [GSYM th]) \\ fs []);

val LESS_MULT_LEMMA = Q.store_thm("LESS_MULT_LEMMA",
  `n1 < n2 /\ d < k ==> k * n1 + d < k * n2:num`,
  Cases_on `n2` \\ fs [MULT_CLAUSES] \\ rw []
  \\ fs [DECIDE ``n1 < SUC k <=> n1 <= k``]
  \\ match_mp_tac (DECIDE ``n < n' /\ m <= m' ==> n + m < n' + m':num``)
  \\ fs []);

(* asm config's syntactic constraints needed for asm_ok to hold *)
val conf_constraint_def = Define`
  conf_constraint (conf:'a asm_config) ⇔
  addr_offset_ok 0w conf ∧
  (∀n.
     n ≤ max_stack_alloc ⇒
     conf.valid_imm (INL Sub)
       (n2w (n * (dimindex (:α) DIV 8))) ∧
     conf.valid_imm (INL Add)
       (n2w (n * (dimindex (:α) DIV 8)))) ∧
  conf.valid_imm (INL Add) 1w ∧
  conf.valid_imm (INL Sub) 1w ∧
  conf.valid_imm (INL Add) 4w ∧
  conf.valid_imm (INL Add) 8w ∧
  ∀s. addr_offset_ok (store_offset s) conf`;

local
val lemma = Q.store_thm("imples_data_to_word_precond",
  `(from_data c prog = SOME (bytes,ffis) /\
     EVERY (\n. data_num_stubs ≤ n) (MAP FST prog) /\ ALL_DISTINCT (MAP FST prog) /\
     byte_aligned (t.regs (find_name c.stack_conf.reg_names 2)) /\
     byte_aligned (t.regs (find_name c.stack_conf.reg_names 4)) /\
     t.regs (find_name c.stack_conf.reg_names 2) <=+
     t.regs (find_name c.stack_conf.reg_names 4) /\
     Abbrev (dm = { w | t.regs (find_name c.stack_conf.reg_names 2) <=+ w /\
                        w <+ t.regs (find_name c.stack_conf.reg_names 4) }) /\
     good_init_state mc_conf (t:'a asm_state)
       m ms ffi ffis bytes io_regs save_regs dm) /\
    (data_to_wordProof$conf_ok (:α) c.data_conf /\
    c.lab_conf.asm_conf = mc_conf.target.config /\
    backend_correct mc_conf.target /\ good_dimindex (:'a) /\
    find_name c.stack_conf.reg_names PERMUTES UNIV /\
    (case mc_conf.target.config.link_reg of NONE => 0 | SOME n => n) ∉
      ({mc_conf.len_reg; mc_conf.ptr_reg} UNION save_regs) /\
    find_name c.stack_conf.reg_names 2 = mc_conf.len_reg /\
    find_name c.stack_conf.reg_names 1 = mc_conf.ptr_reg /\
    (find_name c.stack_conf.reg_names 0 =
       case mc_conf.target.config.link_reg of NONE => 0 | SOME n => n) /\
    (* Syntactic constraints on asm_config*)
    conf_constraint mc_conf.target.config ∧
    (* Specific to register renamings*)
    names_ok c.stack_conf.reg_names mc_conf.target.config.reg_count mc_conf.target.config.avoid_regs ∧
    fixed_names c.stack_conf.reg_names mc_conf.target.config ∧
    Abbrev (ra_regs = (mc_conf.target.config.reg_count −
          (LENGTH mc_conf.target.config.avoid_regs + 5))) /\
    2 < ra_regs ∧
    save_regs = set mc_conf.callee_saved_regs /\
    MEM (find_name c.stack_conf.reg_names (ra_regs+2))
      mc_conf.callee_saved_regs /\
    MEM (find_name c.stack_conf.reg_names (ra_regs+3))
      mc_conf.callee_saved_regs /\
    MEM (find_name c.stack_conf.reg_names (ra_regs+4))
      mc_conf.callee_saved_regs /\
    10 ≤ ra_regs +2 /\
    (* At least 11 register available*)
    LENGTH mc_conf.target.config.avoid_regs + 11 ≤
      (mc_conf:('a,'b,'c) machine_config).target.config.reg_count) ==>
    data_to_word_precond (bytes,c,ffi:'ffi ffi_state,ffis,mc_conf,ms,prog)`,
  strip_tac \\ fs [data_to_word_precond_def]
  \\ `ffi.final_event = NONE /\ byte_aligned (t.regs mc_conf.ptr_reg)` by
        fs [good_init_state_def] \\ fs [EXISTS_PROD]
  \\ fs [EVAL ``lookup 0 (LS x)``,word_to_stackProofTheory.make_init_def]
  \\ fs [full_make_init_ffi,full_make_init_gc_fun]
  \\ ConseqConv.CONSEQ_CONV_TAC (ConseqConv.CONSEQ_REWRITE_CONV
                ([], [full_init_pre_IMP_init_store_ok,
                      full_init_pre_IMP_init_state_ok], []))
  \\ simp_tac (std_ss++CONJ_ss) [full_make_init_bitmaps] \\ fs [GSYM CONJ_ASSOC]
  \\ fs [from_data_def] \\ pairarg_tac \\ fs []
  \\ fs [from_word_def] \\ pairarg_tac \\ fs []
  \\ fs [from_stack_def]
  \\ fs [from_lab_def]
  \\ last_x_assum mp_tac
  \\ qpat_abbrev_tac `tp = compile _ _ _ _ _ p'`
  (*Parts of this proof can be re-used...*)
  \\ `labels_ok tp` by
    (fs[Abbr`tp`]>>match_mp_tac stack_to_lab_compile_lab_pres>>
    assume_tac (data_to_word_compile_lab_pres|>GEN_ALL |>Q.SPECL[`c.word_to_word_conf`,`prog`,`c.data_conf`,`mc_conf.target.config`])>>
    rfs[]>>
    assume_tac(word_to_stack_compile_lab_pres|>INST_TYPE[beta|->alpha]|>GEN_ALL|> Q.SPECL[`p`,`mc_conf.target.config`])>>
    rfs[]>>
    rewrite_tac [EVAL ``MAP FST (stubs (:α) c.data_conf)``,APPEND,EVERY_DEF,MEM,
                 EVAL ``raise_stub_location``,EVAL ``gc_stub_location``] >>
    CONV_TAC (DEPTH_CONV BETA_CONV) >>
    asm_simp_tac std_ss [ALL_DISTINCT,MEM] >>
    qpat_assum `EVERY (λn. data_num_stubs ≤ n) (MAP FST prog)` mp_tac >>
    rpt (pop_assum kall_tac) >>
    fs [EVERY_MEM,EVAL ``data_num_stubs``] \\
    rpt strip_tac \\ res_tac \\ fs [])
  \\ `all_enc_ok_pre mc_conf.target.config tp` by
    (fs[Abbr`tp`]>> match_mp_tac stack_to_lab_compile_all_enc_ok>>
    fs[stackPropsTheory.reg_name_def,conf_constraint_def]>>
    simp[GSYM EVERY_CONJ,LAMBDA_PROD]>>
    `p' = SND (compile mc_conf.target.config p)` by fs[]>>
    pop_assum SUBST1_TAC>>
    match_mp_tac word_to_stack_stack_asm_convs>>
    simp[]>>
    assume_tac(GEN_ALL data_to_wordProofTheory.data_to_word_compile_conventions)>>
    pop_assum (qspecl_then [`c.word_to_word_conf`,`prog`,`c.data_conf`,`mc_conf.target.config`] assume_tac)>>
    rfs[data_to_wordTheory.compile_def,EVERY_MEM,FORALL_PROD]>>
    metis_tac[])
  \\ imp_res_tac labels_ok_imp
  \\ strip_tac
  \\ fs[Abbr`tp`,stack_to_labTheory.compile_def]
  \\ asm_exists_tac \\ fs []
  \\ rename1 `_ = (c2,prog1)`
  \\ qabbrev_tac `prog2 = compile c.data_conf prog1`
  \\ qpat_x_assum `_ = SOME _` mp_tac
  \\ qpat_abbrev_tac `prog3 = compile _ _ c2.bitmaps _ _ prog2`
  \\ qabbrev_tac `prog4 = compile c.stack_conf.reg_names prog3`
  \\ disch_then (assume_tac o GSYM) \\ fs []
  \\ ConseqConv.CONSEQ_CONV_TAC (ConseqConv.CONSEQ_REWRITE_CONV
                ([], [compile_eq_imp], [])) \\ fs []
  \\ GEN_EXISTS_TAC "c1" `c.data_conf` \\ fs []
  \\ fs [data_to_wordTheory.compile_def]
  \\ GEN_EXISTS_TAC "asm_conf" `c.lab_conf.asm_conf` \\ fs []
  \\ GEN_EXISTS_TAC "max_heap" `2 * max_heap_limit (:α) c.data_conf - 1` \\ fs []
  \\ `LENGTH mc_conf.target.config.avoid_regs + 9 ≤ mc_conf.target.config.reg_count` by (fs[] \\ NO_TAC)
  \\ drule data_to_word_compile_imp \\ strip_tac
  \\ GEN_EXISTS_TAC "x1" `fromAList (stubs(:α)c.data_conf ++ MAP (compile_part c.data_conf) prog)` \\ fs []
  \\ GEN_EXISTS_TAC "code3" `p` \\ fs []
  \\ GEN_EXISTS_TAC "bitmaps" `c2.bitmaps` \\ fs []
  \\ GEN_EXISTS_TAC "codeN" `prog1` \\ fs []
  \\ drule word_to_stack_compile_imp \\ strip_tac \\ fs []
  \\ rfs[]
  \\ fs [full_init_pre_def |> SIMP_RULE (std_ss++CONJ_ss) [],full_init_pre_fail_def]
  \\ qabbrev_tac `sp = mc_conf.target.config.reg_count - (LENGTH mc_conf.target.config.avoid_regs +3)`
  \\ `sp = ra_regs+2` by
    (unabbrev_all_tac>>
    fs[] \\ NO_TAC)
  \\ GEN_EXISTS_TAC "k" `sp` \\ fs []
  \\ GEN_EXISTS_TAC "f" `c.stack_conf.reg_names` \\ fs []
  \\ `∀a. byte_align a ∈ dm ⇒ a ∈ dm` by
   (qunabbrev_tac `dm` \\ fs [] \\ rfs []
    \\ Cases_on `t.regs mc_conf.len_reg`
    \\ Cases_on `t.regs (find_name c.stack_conf.reg_names 4)` \\ Cases
    \\ fs [alignmentTheory.byte_align_def,alignmentTheory.byte_aligned_def]
    \\ fs [alignmentTheory.align_w2n,WORD_LO,WORD_LS]
    \\ `2 ** LOG2 (dimindex (:α) DIV 8) = dimindex (:α) DIV 8` by
         (fs [labPropsTheory.good_dimindex_def] \\ NO_TAC) \\ fs []
    \\ fs [stack_removeProofTheory.aligned_w2n]
    \\ rename1 `l:num < _`
    \\ `0 < dimindex (:α) DIV 8` by rfs [labPropsTheory.good_dimindex_def]
    \\ `(l DIV (dimindex (:α) DIV 8) * (dimindex (:α) DIV 8)) < dimword (:α)` by
     (drule DIVISION
      \\ disch_then (qspec_then `l` (strip_assume_tac o GSYM)) \\ rfs []) \\ fs []
    \\ strip_tac
    \\ drule DIVISION
    \\ disch_then (qspec_then `l` (strip_assume_tac o GSYM)) \\ rfs []
    \\ qpat_x_assum `_ = _` (fn th => once_rewrite_tac [GSYM th])
    \\ drule DIVISION
    \\ disch_then (qspec_then `n'` (strip_assume_tac o GSYM)) \\ rfs []
    \\ qpat_x_assum `_ < (nnn:num)` mp_tac
    \\ qpat_x_assum `_ = _` (fn th => once_rewrite_tac [GSYM th])
    \\ qabbrev_tac `k = dimindex (:'a) DIV 8`
    \\ qabbrev_tac `n1 = l DIV k`
    \\ qabbrev_tac `n2 = n' DIV k` \\ fs []
    \\ strip_tac \\ match_mp_tac LESS_MULT_LEMMA \\ fs [] \\ NO_TAC) \\ fs []
  \\ Cases_on`mc_conf.target.config.addr_offset`
  \\ qexists_tac`ffis` \\ qexists_tac`q` \\ qexists_tac `r` \\ fs[]
  \\ `?regs. init_pre (2 * max_heap_limit (:α) c.data_conf - 1) c2.bitmaps
        (ra_regs + 2) InitGlobals_location
        (make_init c.stack_conf.reg_names (fromAList prog3)
           (make_init (fromAList prog4) regs save_regs
              (make_init mc_conf ffi save_regs io_regs t m
                  (dm INTER byte_aligned) (ms:'b)
                   (MAP prog_to_section prog4))))` by
   (fs [stack_removeProofTheory.init_pre_def,
        stack_namesProofTheory.make_init_def,GSYM PULL_EXISTS]
    \\ conj_tac THEN1
     (unabbrev_all_tac
      \\ fs [stack_removeTheory.compile_def,lookup_fromAList,
             stack_removeTheory.init_stubs_def])
    \\ fs [stack_to_labProofTheory.make_init_def,
           lab_to_targetProofTheory.make_init_def,
           stack_removeProofTheory.init_code_pre_def]
    \\ qexists_tac `MAP (find_name c.stack_conf.reg_names) [2;3;4]`
    \\ fs [MAP,BIJ_FLOOKUP_MAPKEYS,FUPDATE_LIST] \\ fs [FLOOKUP_UPDATE]
    \\ conj_tac THEN1
      (fs[Abbr`prog3`,domain_fromAList,MEM_MAP]>>
      EVAL_TAC>>fs[EXISTS_PROD]>>
      metis_tac[])
    \\ conj_tac THEN1 metis_tac [LINV_DEF,IN_UNIV,BIJ_DEF]
    \\ conj_tac THEN1 metis_tac [LINV_DEF,IN_UNIV,BIJ_DEF]
    \\ conj_tac THEN1 metis_tac [LINV_DEF,IN_UNIV,BIJ_DEF]
    \\ qpat_x_assum `_ = mc_conf.len_reg` (fn th => fs [GSYM th])
    \\ qunabbrev_tac `dm`
    \\ rpt (qpat_x_assum `byte_aligned (t.regs _)` mp_tac)
    \\ rpt (qpat_x_assum `_ <=+ _` mp_tac)
    \\ qspec_tac (`t.regs (find_name c.stack_conf.reg_names 2)`,`a`)
    \\ qspec_tac (`t.regs (find_name c.stack_conf.reg_names 4)`,`b`)
    \\ `(w2n:'a word -> num) bytes_in_word = dimindex (:α) DIV 8` by
         rfs [labPropsTheory.good_dimindex_def,bytes_in_word_def,dimword_def]
    \\ fs [] \\ rpt strip_tac
    \\ match_mp_tac word_list_exists_imp \\ fs []
    \\ fs [addresses_thm]
    \\ `0 < dimindex (:α) DIV 8` by rfs [labPropsTheory.good_dimindex_def]
    \\ reverse conj_tac THEN1
     (fs [] \\ match_mp_tac IMP_MULT_DIV_LESS \\ fs [w2n_lt]
      \\ rfs [labPropsTheory.good_dimindex_def])
    \\ drule WORD_LS_IMP \\ strip_tac \\ fs [EXTENSION]
    \\ fs [IN_DEF,PULL_EXISTS,bytes_in_word_def,word_mul_n2w]
    \\ rw [] \\ reverse eq_tac THEN1
     (rw [] \\ fs [] \\ qexists_tac `i * (dimindex (:α) DIV 8)` \\ fs []
      \\ `0 < dimindex (:α) DIV 8` by rfs [labPropsTheory.good_dimindex_def]
      \\ drule X_LT_DIV \\ disch_then (fn th => fs [th])
      \\ fs [RIGHT_ADD_DISTRIB]
      \\ fs [GSYM word_mul_n2w,GSYM bytes_in_word_def]
      \\ fs [byte_aligned_mult])
    \\ rw [] \\ fs []
    \\ `i < dimword (:'a)` by metis_tac [LESS_TRANS,w2n_lt] \\ fs []
    \\ qexists_tac `i DIV (dimindex (:α) DIV 8)`
    \\ rfs [alignmentTheory.byte_aligned_def,
         ONCE_REWRITE_RULE [WORD_ADD_COMM] alignmentTheory.aligned_add_sub]
    \\ fs [stack_removeProofTheory.aligned_w2n]
    \\ drule DIVISION
    \\ disch_then (qspec_then `i` (strip_assume_tac o GSYM))
    \\ `2 ** LOG2 (dimindex (:α) DIV 8) = dimindex (:α) DIV 8` by
         (fs [labPropsTheory.good_dimindex_def] \\ NO_TAC)
    \\ fs [] \\ rfs [] \\ `-1w * a + b = b - a` by fs []
    \\ full_simp_tac std_ss []
    \\ Cases_on `a` \\ Cases_on `b`
    \\ full_simp_tac std_ss [WORD_LS,addressTheory.word_arith_lemma2]
    \\ fs [] \\ match_mp_tac DIV_LESS_DIV \\ fs []
    \\ rfs [] \\ fs [] \\ match_mp_tac MOD_SUB_LEMMA \\ fs [] \\ NO_TAC)
  \\ qexists_tac `regs` \\ fs [] \\ rfs []
  \\ pop_assum kall_tac
  \\ fs [IS_SOME_EQ_CASE] \\ CASE_TAC \\ fs []
  \\ SIMP_TAC (std_ss++CONJ_ss)
       [EVAL ``(make_init mc_conf ffi save_regs io_regs t m dm ms code).code``,
        EVAL ``(make_init mc_conf ffi save_regs io_regs t m dm ms code).pc``]
  \\ imp_res_tac make_init_opt_imp_bitmaps_limit \\ fs []
  \\ `loc_to_pc 0 0 (MAP prog_to_section prog4) = SOME 0` by
   (qunabbrev_tac `prog4`
    \\ qunabbrev_tac `prog3`
    \\ fs [stack_removeTheory.compile_def,
           stack_removeTheory.init_stubs_def,
           stack_namesTheory.compile_def,
           stack_namesTheory.prog_comp_def,
           stack_to_labTheory.prog_to_section_def]
    \\ pairarg_tac \\ fs [] \\ fs [Once labSemTheory.loc_to_pc_def] \\ NO_TAC)
  \\ fs []
  \\ imp_res_tac data_to_word_names
  \\ imp_res_tac word_to_stack_names \\ fs [ALOOKUP_NONE]
  \\ `MAP FST prog2 = gc_stub_location::MAP FST prog1` by metis_tac [stack_alloc_names] \\ fs []
  \\ simp[ALL_DISTINCT_APPEND]
  \\ fs [AC CONJ_ASSOC CONJ_COMM] \\ rfs []
  \\ rpt (pop_assum mp_tac)
  \\ cheat
  (*
  \\ rewrite_tac ([data_to_wordTheory.stubs_def]@code_and_locs)
  \\ rpt (disch_then assume_tac)
  \\ rpt (conj_tac THEN1 (EVAL_TAC))
  \\ rpt (conj_tac THEN1 (fs [EVERY_MEM,data_to_wordTheory.stubs_def] \\ strip_tac \\ res_tac \\ fs [] \\ EVAL_TAC))
  \\ rpt (conj_tac
    >- (
      EVAL_TAC \\ fs[EVERY_MEM] \\ strip_tac \\ res_tac \\ fs[]
      \\ pop_assum mp_tac \\ EVAL_TAC ))
  \\ TRY (conj_tac >-
    (fs[EVERY_MEM,FORALL_PROD]>>
    metis_tac[]))
  \\ TRY (conj_tac >- (
    ntac 3 strip_tac \\ rename1 `ALOOKUP prog1 k = SOME _`
    \\ imp_res_tac ALOOKUP_MEM
    \\ imp_res_tac MEM_pair_IMP
    \\ rfs [EVERY_MEM]
    \\ EVAL_TAC
    \\ res_tac \\ fs []
    \\ strip_tac \\ rw[]
    \\ pop_assum mp_tac \\ EVAL_TAC))
  \\ rpt (conj_tac THEN1
   (imp_res_tac (INST_TYPE[beta|->alpha]stack_alloc_syntax)
    \\ pop_assum(qspec_then`c`assume_tac) \\ rfs[]
    \\ fs [EVERY_MEM,FORALL_PROD]
    \\ ntac 3 strip_tac
    \\ `MEM p_1 (MAP FST prog2) /\ MEM p_2 (MAP SND prog2)` by
     (fs [MEM_MAP,PULL_EXISTS,FORALL_PROD,EXISTS_PROD]
      \\ rpt (asm_exists_tac \\ fs [])) \\ fs []
    \\ ntac 2 (pop_assum mp_tac)
    \\ simp[]
    \\ EVAL_TAC
    \\ rw[] \\ rw[]
    \\ res_tac
    \\ pop_assum mp_tac
    \\ EVAL_TAC \\ rw[]))
  \\ fs [state_rel_make_init,lab_to_targetProofTheory.make_init_def]
  \\ fs [PULL_EXISTS] \\ rpt strip_tac
  \\ TRY
   (fs [IN_DEF] \\ rename1 `byte_aligned w` \\ Cases_on `w`
    \\ fs [stack_removeProofTheory.aligned_w2n,
           alignmentTheory.byte_aligned_def]
    \\ rfs [labPropsTheory.good_dimindex_def] \\ rfs [] \\ NO_TAC)
  \\ fs [GSYM PULL_EXISTS] \\ fs [lookup_fromAList]
  \\ drule code_installed_prog_to_section \\ fs [] \\ strip_tac
  \\ imp_res_tac ALOOKUP_MEM
  \\ imp_res_tac MEM_pair_IMP
  \\ imp_res_tac (INST_TYPE[beta|->alpha]stack_alloc_syntax)
  \\ ntac 2 (first_x_assum (qspec_then`c` assume_tac))\\ rfs []
  \\ drule stack_remove_syntax_pres \\ fs [] \\ strip_tac
  \\ drule stack_names_syntax_pres \\ fs []
  \\ simp [EVERY_MEM] \\ disch_then drule \\ fs [] *))
  |> GEN_ALL |> SIMP_RULE std_ss [] |> SPEC_ALL
  |> Q.GEN `ra_regs` |> SIMP_RULE std_ss [GSYM PULL_EXISTS,
       METIS_PROVE [] ``(!x. P x ==> Q) <=> ((?x. P x) ==> Q)``];
val tm = lemma |> concl |> dest_imp |> fst |> dest_conj |> snd
in
(* TODO: this conf_ok should be defined in backendTheory, so that we
         can prove that each backend's config is correct without
         requiring to build all the proofs. *)
val conf_ok_def = Define `conf_ok c mc_conf = ^tm`
val imp_data_to_word_precond = lemma |> REWRITE_RULE [GSYM conf_ok_def]
end;

val clean_data_to_target_thm = let
  val th =
    IMP_TRANS imp_data_to_word_precond machine_sem_implements_data_sem
    |> SIMP_RULE std_ss [GSYM CONJ_ASSOC]
    |> Q.GENL [`t`,`m`,`dm`,`io_regs`]
    |> SIMP_RULE std_ss [GSYM CONJ_ASSOC,GSYM PULL_EXISTS]
    |> SIMP_RULE std_ss [CONJ_ASSOC,GSYM PULL_EXISTS]
    |> SIMP_RULE std_ss [GSYM CONJ_ASSOC,GSYM PULL_EXISTS]
    |> ONCE_REWRITE_RULE [METIS_PROVE[]``b1/\b2/\b3/\b4/\b5<=>b4/\b1/\b2/\b3/\b5``]
    |> SIMP_RULE std_ss [markerTheory.Abbrev_def]
  val tm = th |> concl |> dest_imp |> fst |> dest_conj |> fst
  val installed_def = define_abbrev "installed" tm
  val th = th |> REWRITE_RULE [GSYM installed_def]
  in th end;

(* --- composing source-to-target --- *)

val cnv = computeLib.compset_conv (wordsLib.words_compset())
  [computeLib.Extenders [compilerComputeLib.add_compiler_compset],
   computeLib.Defs
     [prim_config_def, primTypesTheory.prim_types_program_def]];

val prim_config_eq = save_thm("prim_config_eq", cnv ``prim_config``);

val id_CASE_eq_SOME = Q.prove(
  `id_CASE x f (λa b. NONE) = SOME z ⇔ ∃y. x = Short y ∧ f y = SOME z`,
  Cases_on`x`>>rw[])

val option_CASE_eq_SOME = Q.prove(
  `option_CASE x NONE z = SOME y ⇔ ∃a. x = SOME a ∧ z a = SOME y`,
  Cases_on`x`>>rw[]);

val else_NONE_eq_SOME = Q.store_thm("else_NONE_eq_SOME",
  `(((if t then y else NONE) = SOME z) ⇔ (t ∧ (y = SOME z)))`,
  rw[]);

val COND_eq_SOME = Q.store_thm("COND_eq_SOME",
  `((if t then SOME a else b) = SOME x) ⇔ ((t ∧ (a = x)) ∨ (¬t ∧ b = SOME x))`,
  rw[]);

val from_data_ignore = Q.store_thm("from_data_ignore",
  `from_data (c with <|source_conf := x; mod_conf := y; clos_conf := z|>) prog =
    from_data c prog`,
  fs [from_data_def,from_word_def,from_stack_def,from_lab_def]
  \\ rpt (pairarg_tac \\ fs []));

val clos_to_data_names = Q.store_thm("clos_to_data_names",
  `clos_to_bvl$compile c e4 = (c2,p2) /\
    bvl_to_bvi$compile n1 n limit p2 = (k,p3,n2) ==>
    EVERY (λn. data_num_stubs ≤ n) (MAP FST (bvi_to_data$compile_prog p3)) /\
    ALL_DISTINCT (MAP FST (bvi_to_data$compile_prog p3))`,
  fs[Once (GSYM bvi_to_dataProofTheory.MAP_FST_compile_prog)]>>
  fs[bvl_to_bviTheory.compile_def,bvl_to_bviTheory.compile_prog_def]>>
  strip_tac>>
  pairarg_tac>>fs[]>>rveq>>fs[]>>
  EVAL_TAC>>
  REWRITE_TAC[GSYM append_def] >>
  fs[EVERY_MEM]>>
  imp_res_tac compile_all_distinct_locs>>
  fs[]>>
  imp_res_tac compile_list_distinct_locs>>
  rfs[bvl_num_stubs_def,bvl_inlineProofTheory.MAP_FST_compile_prog]>>
  fs[EVERY_MEM]>>rw[]
  \\ TRY strip_tac
  \\ res_tac
  \\ pop_assum mp_tac
  \\ EVAL_TAC \\ rw[]);

val compile_correct = Q.store_thm("compile_correct",
  `let (s,env) = THE (prim_sem_env (ffi:'ffi ffi_state)) in
   (c:'a backend$config).source_conf = (prim_config:'a backend$config).source_conf ∧
   c.mod_conf = (prim_config:'a backend$config).mod_conf ∧
   0 < c.clos_conf.max_app ∧ conf_ok c mc ∧
   ¬semantics_prog s env prog Fail ∧
   compile c prog = SOME (bytes,ffis) ∧
   installed (bytes,c,ffi,ffis,mc,ms) ⇒
     machine_sem (mc:(α,β,γ) machine_config) ffi ms ⊆
       extend_with_resource_limit (semantics_prog s env prog)`,
  srw_tac[][compile_eq_from_source,from_source_def] >>
  drule(GEN_ALL(MATCH_MP SWAP_IMP source_to_modProofTheory.compile_correct)) >>
  fs[primSemEnvTheory.prim_sem_env_eq] >>
  qpat_x_assum`_ = s`(assume_tac o Abbrev_intro o SYM) >>
  qpat_x_assum`_ = env`(assume_tac o Abbrev_intro o SYM) >>
  `∃s2 env2 gtagenv.
     precondition s env c.source_conf s2 env2 ∧
     FST env2.c = [] ∧
     s2.globals = [] ∧
     s2.ffi = ffi ∧
     s2.refs = [] ∧
     s2.defined_types = s.defined_types ∧
     s2.defined_mods = s.defined_mods ∧
     envC_tagged env2.c prim_config.mod_conf.tag_env gtagenv ∧
     exhaustive_env_correct prim_config.mod_conf.exh_ctors_env gtagenv ∧
     gtagenv_wf gtagenv ∧
     next_inv (IMAGE (SND o SND) (FRANGE (SND(prim_config.mod_conf.tag_env))))
       prim_config.mod_conf.next_exception gtagenv` by (
    simp[source_to_modProofTheory.precondition_def] >>
    simp[Abbr`env`,Abbr`s`] >>
    srw_tac[QUANT_INST_ss[pair_default_qp,record_default_qp]][] >>
    rw[source_to_modProofTheory.invariant_def] >>
    rw[source_to_modProofTheory.s_rel_cases] >>
    rw[source_to_modProofTheory.v_rel_cases] >>
    rw[prim_config_eq] >>
    Cases_on`ffi`>>rw[ffiTheory.ffi_state_component_equality] >>
    fs[semanticPrimitivesTheory.merge_alist_mod_env_def] >>
    CONV_TAC(PATH_CONV"brrrllr"(REWRITE_CONV[DOMSUB_FUPDATE_THM] THENC EVAL)) >>
    rpt(CHANGED_TAC(CONV_TAC(PATH_CONV"brrrllr"(REWRITE_CONV[FRANGE_FUPDATE,DRESTRICT_FUPDATE] THENC EVAL)))) >>
    rw[DRESTRICT_DRESTRICT] >>
    rw[envC_tagged_def,
       semanticPrimitivesTheory.lookup_alist_mod_env_def,
       mod_to_conTheory.lookup_tag_env_def,
       mod_to_conTheory.lookup_tag_flat_def,
       FLOOKUP_DEF] >>
    simp[id_CASE_eq_SOME,PULL_EXISTS] >>
    simp[option_CASE_eq_SOME] >>
    simp[astTheory.id_to_n_def] >>
    simp[FAPPLY_FUPDATE_THM] >>
    simp[pair_CASE_eq,PULL_EXISTS] >>
    simp[COND_eq_SOME] >>
    srw_tac[DNF_ss][] >>
    (fn g =>
       let
         val tms = g |> #2 |> dest_exists |> #2
                     |> dest_conj |> #1
                     |> strip_conj |> filter is_eq
         val fm = tms |> hd |> lhs |> rator |> rand
         val ps = map ((rand ## I) o dest_eq) tms
         val tm = finite_mapSyntax.list_mk_fupdate
                  (finite_mapSyntax.mk_fempty (finite_mapSyntax.dest_fmap_ty(type_of fm)),
                   map pairSyntax.mk_pair ps)
       in exists_tac tm end g) >>
    simp[FAPPLY_FUPDATE_THM] >>
    conj_tac >- (
      simp[exhaustive_env_correct_def,IN_FRANGE,FLOOKUP_UPDATE,PULL_EXISTS] >>
      srw_tac[DNF_ss][] >>
      EVAL_TAC >>
      pop_assum mp_tac >> rw[] >>
      EVAL_TAC >>
      simp[PULL_EXISTS]) >>
    conj_tac >- (
      EVAL_TAC >> rw[] >> fs[semanticPrimitivesTheory.same_tid_def] ) >>
    simp[next_inv_def,PULL_EXISTS] >>
    simp[FLOOKUP_UPDATE] >>
    rw[] >> EVAL_TAC >>
    srw_tac[QUANT_INST_ss[std_qp]][]) >>
  disch_then drule >> strip_tac >>
  qhdtm_x_assum`from_mod`mp_tac >>
  srw_tac[][from_mod_def,Abbr`c''`,mod_to_conTheory.compile_def] >>
  pop_assum mp_tac >> BasicProvers.LET_ELIM_TAC >>
  qmatch_assum_abbrev_tac`semantics_prog s env prog sem2` >>
  `sem2 ≠ Fail` by metis_tac[] >>
  `semantics_prog s env prog = { sem2 }` by (
    simp[EXTENSION,IN_DEF] >>
    metis_tac[semantics_prog_deterministic] ) >>
  qunabbrev_tac`sem2` >>
  drule (GEN_ALL mod_to_conProofTheory.compile_prog_semantics) >>
  fs[] >> rveq >>
  simp[AND_IMP_INTRO] >> simp[Once CONJ_COMM] >>
  disch_then drule >>
  simp[mod_to_conProofTheory.invariant_def,
       mod_to_conTheory.get_exh_def,
       mod_to_conTheory.get_tagenv_def] >>
  simp[mod_to_conProofTheory.s_rel_cases] >>
  CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss()++QUANT_INST_ss[record_default_qp,pair_default_qp])[])) >>
  simp[mod_to_conProofTheory.cenv_inv_def] >>
  disch_then(qspec_then`gtagenv`mp_tac)>>
  impl_tac >- (
    rw[Abbr`s`,prim_config_eq] >>
    fs[prim_config_eq] >>
    qhdtm_x_assum`next_inv`mp_tac >>
    rpt(pop_assum kall_tac) >>
    REWRITE_TAC[FRANGE_FUPDATE,DRESTRICT_FUPDATE,DOMSUB_FUPDATE_THM] >>
    EVAL_TAC >> rw[SUBSET_DEF] >> fs[PULL_EXISTS] >>
    res_tac >> fs[] >>
    pop_assum mp_tac >>
    rpt(CHANGED_TAC(REWRITE_TAC[FRANGE_FUPDATE,DRESTRICT_FUPDATE,DOMSUB_FUPDATE_THM] >> EVAL_TAC)) >>
    rw[DRESTRICT_DRESTRICT] >> rw[]) >>
  strip_tac >>
  pop_assum(assume_tac o SYM) >> simp[] >>
  qunabbrev_tac`c'''`>>
  qhdtm_x_assum`from_con`mp_tac >>
  srw_tac[][from_con_def] >>
  pop_assum mp_tac >> BasicProvers.LET_ELIM_TAC >>
  rfs[] >> fs[] >>
  drule(GEN_ALL(MATCH_MP SWAP_IMP (REWRITE_RULE[GSYM AND_IMP_INTRO]con_to_decProofTheory.compile_semantics))) >>
  simp[] >>
  impl_tac >- (
    qhdtm_x_assum`mod_to_con$compile_prog`mp_tac >>
    simp[prim_config_eq] >> EVAL_TAC >>
    `semantics env2 s2 p ≠ Fail` by simp[] >>
    pop_assum mp_tac >>
    simp_tac(srw_ss())[modSemTheory.semantics_def] >>
    IF_CASES_TAC >> simp[] >> disch_then kall_tac >>
    pop_assum mp_tac >>
    simp[modSemTheory.evaluate_prog_def] >>
    BasicProvers.TOP_CASE_TAC >> simp[] >> strip_tac >> fs[] >>
    `¬MEM "option" (prog_to_top_types p)` by (
      fs[modSemTheory.no_dup_top_types_def,IN_DISJOINT,MEM_MAP] >>
      fs[Abbr`s`] >> metis_tac[] ) >>
    strip_tac >>
    match_mp_tac compile_prog_exh_unchanged >>
    asm_exists_tac >> simp[] >>
    qmatch_assum_abbrev_tac`compile_prog st p = _` >>
    qexists_tac`st`>>simp[Abbr`st`,mod_to_conTheory.get_exh_def] >>
    simp[FLOOKUP_UPDATE]) >>
  disch_then(strip_assume_tac o SYM) >> fs[] >>
  qhdtm_x_assum`from_dec`mp_tac >> srw_tac[][from_dec_def] >>
  pop_assum mp_tac >> BasicProvers.LET_ELIM_TAC >>
  qhdtm_x_assum`con_to_dec$compile`mp_tac >>
  `c'.next_global = 0` by (
    fs[source_to_modTheory.compile_def,LET_THM] >>
    pairarg_tac >> fs[] >>
    pairarg_tac >> fs[] >>
    rveq >> simp[prim_config_eq] ) >> fs[] >>
  strip_tac >> fs[] >>
  qunabbrev_tac`c''`>>fs[] >>
  qmatch_abbrev_tac`_ ⊆ _ { decSem$semantics env3 st3 [e3] }` >>
  (dec_to_exhProofTheory.compile_semantics
    |> Q.GENL[`sth`,`envh`,`e`,`st`,`env`]
    |> qispl_then[`env3`,`st3`,`e3`]mp_tac) >>
  simp[Abbr`env3`] >>
  simp[Once dec_to_exhProofTheory.v_rel_cases] >>
  simp[dec_to_exhProofTheory.state_rel_def] >>
  fs[Abbr`st3`,con_to_decProofTheory.compile_state_def] >>
  CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss()++QUANT_INST_ss[record_default_qp,pair_default_qp])[])) >>
  simp[Abbr`e3`] >>
  disch_then(strip_assume_tac o SYM) >> fs[] >>
  qhdtm_x_assum`from_exh`mp_tac >>
  srw_tac[][from_exh_def] >>
  pop_assum mp_tac >> BasicProvers.LET_ELIM_TAC >>
  fs[exh_to_patTheory.compile_def] >>
  qmatch_abbrev_tac`_ ⊆ _ { exhSem$semantics env3 st3 es3 }` >>
  (exh_to_patProofTheory.compile_exp_semantics
   |> Q.GENL[`es`,`st`,`env`]
   |> qispl_then[`env3`,`st3`,`es3`]mp_tac) >>
  simp[Abbr`es3`,Abbr`env3`] >>
  fs[exh_to_patProofTheory.compile_state_def,Abbr`st3`] >>
  disch_then(strip_assume_tac o SYM) >> fs[] >>
  qhdtm_x_assum`from_pat`mp_tac >>
  srw_tac[][from_pat_def] >>
  pop_assum mp_tac >> BasicProvers.LET_ELIM_TAC >>
  qmatch_abbrev_tac`_ ⊆ _ { patSem$semantics env3 st3 es3 }` >>
  (pat_to_closProofTheory.compile_semantics
   |> Q.GENL[`max_app`,`es`,`st`,`env`]
   |> qispl_then[`env3`,`st3`,`es3`]mp_tac) >>
  simp[Abbr`env3`,Abbr`es3`] >>
  first_assum(fn th => disch_then(mp_tac o C MATCH_MP th)) >>
  fs[pat_to_closProofTheory.compile_state_def,Abbr`st3`] >>
  disch_then(strip_assume_tac o SYM) >> fs[] >>
  qhdtm_x_assum`from_clos`mp_tac >>
  srw_tac[][from_clos_def] >>
  pop_assum mp_tac >> BasicProvers.LET_ELIM_TAC >>
  qmatch_abbrev_tac`_ ⊆ _ { closSem$semantics [] st3 [e3] }` >>
  (clos_to_bvlProofTheory.compile_semantics
   |> GEN_ALL
   |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["s","e","c"]))
   |> qispl_then[`st3`,`e3`,`c.clos_conf`]mp_tac) >>
  simp[] >>
  impl_tac >- (
    `esgc_free e3 ∧ BAG_ALL_DISTINCT (set_globals e3)` by
      (unabbrev_all_tac>>
      metis_tac[SND,
      mod_to_conProofTheory.compile_no_set_globals,con_to_decProofTheory.no_set_globals_imp_esgc_free,con_to_decTheory.compile_def,dec_to_exhProofTheory.compile_esgc_free,exh_to_patProofTheory.compile_esgc_free,pat_to_closProofTheory.compile_esgc_free,
      mod_to_conProofTheory.compile_no_set_globals,con_to_decProofTheory.no_set_globals_imp_bag_all_distinct,con_to_decTheory.compile_def,dec_to_exhProofTheory.compile_distinct_setglobals,exh_to_patProofTheory.compile_distinct_setglobals,pat_to_closProofTheory.compile_distinct_setglobals])>>
    EVAL_TAC>>simp[Abbr`st3`]>>
    unabbrev_all_tac >>
    simp[pat_to_closProofTheory.compile_contains_App_SOME] >>
    simp[pat_to_closProofTheory.compile_every_Fn_vs_NONE] >>
    simp[EVEN_ADD,EVEN_EXP_IFF])>>
  simp[Abbr`e3`] >>
  fs[Abbr`st3`] >>
  disch_then(strip_assume_tac o SYM) >> fs[] >>
  qhdtm_x_assum`from_bvl`mp_tac >>
  srw_tac[][from_bvl_def] >>
  pop_assum mp_tac >> BasicProvers.LET_ELIM_TAC >>
  Q.ISPEC_THEN`s2.ffi`drule(Q.GEN`ffi0` bvl_to_bviProofTheory.compile_semantics) >>
  qunabbrev_tac`c'''`>>fs[] >>
  impl_tac >- (
    match_mp_tac (GEN_ALL clos_to_bvlProofTheory.compile_all_distinct_locs)>>
    qexists_tac`e''''`>>
    qexists_tac`c''`>>
    qexists_tac`c.clos_conf`>>
    simp[]>>
    EVAL_TAC >>
    simp[EVEN_ADD,EVEN_EXP_IFF])>>
  disch_then(SUBST_ALL_TAC o SYM) >>
  qhdtm_x_assum`from_bvi`mp_tac >>
  srw_tac[][from_bvi_def] >>
  pop_assum mp_tac >> BasicProvers.LET_ELIM_TAC >>
  qmatch_abbrev_tac`_ ⊆ _ { bviSem$semantics ffi (fromAList p3) s3 }` >>
  (bvi_to_dataProofTheory.compile_prog_semantics
   |> GEN_ALL
   |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["prog","start"]))
   |> qispl_then[`p3`,`s3`,`ffi`]mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (SUBST_ALL_TAC o SYM)
  \\ `s3 = InitGlobals_location` by
   (fs [bvl_to_bviTheory.compile_def,bvl_to_bviTheory.compile_prog_def]
    \\ pairarg_tac \\ fs [])
  \\ rename1 `from_data c4 p4 = _`
  \\ `installed (bytes,c4,ffi,ffis,mc,ms)` by
       (fs [fetch "-" "installed_def",Abbr`c4`] \\ metis_tac [])
  \\ drule (GEN_ALL clean_data_to_target_thm)
  \\ disch_then drule
  \\ `conf_ok c4 mc` by (unabbrev_all_tac \\ fs [conf_ok_def] \\ metis_tac [])
  \\ simp[implements_def,AND_IMP_INTRO]
  \\ disch_then match_mp_tac \\ fs []
  \\ qunabbrev_tac `p4` \\ fs []
  \\ imp_res_tac clos_to_data_names
  \\ fs[AND_IMP_INTRO]);

val _ = export_theory();
