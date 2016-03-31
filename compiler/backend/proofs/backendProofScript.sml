open preamble initSemEnvTheory semanticsPropsTheory
     backendTheory
     source_to_modProofTheory
     mod_to_conProofTheory
     con_to_decProofTheory
     dec_to_exhProofTheory
     exh_to_patProofTheory
     pat_to_closProofTheory
     clos_to_bvlProofTheory
     bvl_to_bviProofTheory
     bvi_to_bvpProofTheory
     bvp_to_wordProofTheory
     word_to_stackProofTheory
     stack_to_labProofTheory
     lab_to_targetProofTheory
local open compilerComputeLib bvpPropsTheory in end
open word_to_stackTheory

val _ = new_theory"backendProof";

(* TODO: move *)

fun Abbrev_intro th =
  EQ_MP (SYM(SPEC(concl th)markerTheory.Abbrev_def)) th

val pair_CASE_eq = Q.store_thm("pair_CASE_eq",
  `pair_CASE p f = a ⇔ ∃x y. p = (x,y) ∧ f x y = a`,
  Cases_on`p`>>rw[]);

(* -- *)


(* --- composing bvp-to-target --- *)

val implements_intro_final = prove(
  ``(b /\ x <> Fail ==> y = {x}) ==> b ==> implements y {x}``,
  fs [implements_def] \\ rw [] \\ fs []
  \\ fs [semanticsPropsTheory.extend_with_resource_limit_def]);

val from_stack = let
  val lemma1 = lab_to_targetProofTheory.semantics_compile
    |> REWRITE_RULE [CONJ_ASSOC]
    |> MATCH_MP implements_intro_final
    |> REWRITE_RULE [GSYM CONJ_ASSOC] |> UNDISCH_ALL
    |> Q.INST [`code`|->`code2`]
  val lemma2 = stack_to_labProofTheory.full_make_init_semantics |> UNDISCH
    |> Q.INST [`code`|->`code1`]
  in simple_match_mp (MATCH_MP implements_trans lemma2) lemma1 end

val from_stack_fail = let
  val lemma1 = lab_to_targetProofTheory.semantics_compile
    |> REWRITE_RULE [CONJ_ASSOC]
    |> MATCH_MP implements_intro_final
    |> REWRITE_RULE [GSYM CONJ_ASSOC] |> UNDISCH_ALL
    |> Q.INST [`code`|->`code2`]
  val lemma2 = stack_to_labProofTheory.full_make_init_semantics_fail |> UNDISCH
    |> Q.INST [`code`|->`code1`]
  val th = EVAL ``(make_init mc_conf ffi save_regs io_regs t m ms code2).ffi``
  in simple_match_mp (MATCH_MP implements_trans lemma2) lemma1
     |> REWRITE_RULE [th] end

val from_word = let
  val lemma1 = word_to_stackProofTheory.compile_semantics
    |> REWRITE_RULE [CONJ_ASSOC]
    |> MATCH_MP implements_intro_ext
    |> REWRITE_RULE [GSYM CONJ_ASSOC] |> UNDISCH_ALL
    |> Q.INST [`code`|->`code3`]
  in simple_match_mp (MATCH_MP implements_trans lemma1) from_stack end

val full_make_init_ffi = prove(
  ``(full_make_init
         (bitmaps,c1,code,f,k,max_heap,regs,
          make_init mc_conf ffi save_regs io_regs t m ms code2,
          save_regs)).ffi = ffi``,
  fs [full_make_init_def,stack_allocProofTheory.make_init_def,
      stack_removeProofTheory.make_init_any_ffi] \\ EVAL_TAC);

val from_bvp = let
  val lemma1 = bvp_to_wordProofTheory.compile_semantics
    |> REWRITE_RULE [CONJ_ASSOC]
    |> MATCH_MP (GSYM implements_intro_ext)
    |> REWRITE_RULE [GSYM CONJ_ASSOC] |> UNDISCH_ALL
    |> Q.INST [`code`|->`code4`]
  in simple_match_mp (MATCH_MP implements_trans lemma1) from_word
     |> SIMP_RULE (srw_ss()) [full_make_init_ffi,
          word_to_stackProofTheory.make_init_def] end

val from_bvp_fail = let
  val th = bvpPropsTheory.Resource_limit_hit_implements_semantics
  val th = MATCH_MP implements_trans th
  val th = MATCH_MP th from_stack_fail
  val target = from_bvp |> concl
  val curr = concl th
  val i = fst (match_term curr target)
  in INST i th end

val full_make_init_code =
  ``(^(full_make_init_def |> SPEC_ALL |> concl |> dest_eq |> fst)).code``
  |> SIMP_CONV (srw_ss()) [full_make_init_def,stack_allocProofTheory.make_init_def]

fun define_abbrev name tm = let
  val vs = free_vars tm |> sort
    (fn v1 => fn v2 => fst (dest_var v1) <= fst (dest_var v2))
  val vars = foldr mk_pair (last vs) (butlast vs)
  val n = mk_var(name,mk_type("fun",[type_of vars, type_of tm]))
  in Define `^n ^vars = ^tm` end

val machine_sem_implements_bvp_sem = save_thm("machine_sem_implements_bvp_sem",let
  val th = from_bvp |> DISCH_ALL
           |> REWRITE_RULE [AND_IMP_INTRO,GSYM CONJ_ASSOC,full_make_init_code]
           |> Q.INST [`code1`|->`SND (compile asm_conf code3)`]
           |> REWRITE_RULE [GSYM AND_IMP_INTRO] |> UNDISCH_ALL
  val th_fail = from_bvp_fail |> DISCH_ALL
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
           |> DISCH ``from_bvp (c:'b backend$config) prog = SOME (bytes,ffi_limit)``
           |> DISCH_ALL
           |> INST_TYPE [``:'a``|->``:'ffi``,
                         ``:'b``|->``:'a``,
                         ``:'c``|->``:'b``,
                         ``:'d``|->``:'c``]
           |> MATCH_MP lemma2
  val (lhs,rhs) = dest_imp (concl th)
  fun diff xs ys = filter (fn x => not (mem x ys)) xs
  val vs = diff (free_vars lhs) (free_vars rhs) |> sort
    (fn v1 => fn v2 => fst (dest_var v1) <= fst (dest_var v2))
  val lemma = METIS_PROVE [] ``(!x. P x ==> Q) <=> ((?x. P x) ==> Q)``
  val th = GENL vs th |> SIMP_RULE std_ss [lemma]
  val def = define_abbrev "bvp_to_word_precond"
               (th |> concl |> dest_imp |> fst)
  val th = th |> REWRITE_RULE [GSYM def]
              |> SIMP_RULE std_ss [PULL_FORALL] |> SPEC_ALL
  in th end);

val bvp_to_word_precond_def = fetch "-" "bvp_to_word_precond_def" |> SPEC_ALL

val full_make_init_gc_fun = prove(
  ``(full_make_init
         (bitmaps,c1,code,f,k,max_heap,regs, xx,
          save_regs)).gc_fun = word_gc_fun c1``,
  fs [full_make_init_def,stack_allocProofTheory.make_init_def]);

val full_make_init_bitmaps = prove(
  ``full_init_pre
         (bitmaps,c1,SND (compile asm_conf code3),f,k,max_heap,regs,
          make_init mc_conf ffi save_regs io_regs t m ms code2,
          save_regs) ==>
    (full_make_init
         (bitmaps,c1,SND (compile asm_conf code3),f,k,max_heap,regs,
          make_init mc_conf ffi save_regs io_regs t m ms code2,
          save_regs)).bitmaps = bitmaps``,
  fs [full_make_init_def,stack_allocProofTheory.make_init_def,
      stack_removeProofTheory.make_init_any_bitmaps]
  \\ every_case_tac \\ fs [] \\ fs [full_init_pre_def]);

val full_init_pre_IMP_init_store_ok = prove(
  ``max_heap = 2 * max_heap_limit (:'a) c1 ==>
    init_store_ok c1
      ((full_make_init
          (bitmaps,c1,code3,f,k,max_heap,regs,(s:('a,'ffi)labSem$state),
             save_regs)).store \\ Handler)
       (full_make_init
          (bitmaps,c1,code3,f,k,max_heap,regs,s,save_regs)).memory
       (full_make_init
          (bitmaps,c1,code3,f,k,max_heap,regs,s,save_regs)).mdomain``,
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
  \\ asm_exists_tac \\ fs []
  \\ fs [FLOOKUP_DEF,DOMSUB_FAPPLY_THM,FAPPLY_FUPDATE_THM]);

val full_init_pre_IMP_init_state_ok = prove(
  ``2 < asm_conf.reg_count − (LENGTH asm_conf.avoid_regs + 5) /\
    (case bitmaps of [] => F | h::_ => 4w = h) /\
    good_dimindex (:α) ==>
    init_state_ok
      (asm_conf.reg_count − (LENGTH (asm_conf:'a asm_config).avoid_regs + 5))
      (full_make_init
        (bitmaps:'a word list,c1,code3,f,k,max_heap,regs,s,save_regs))``,
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
  \\ qpat_assum `LENGTH t2 = x.stack_space` (assume_tac o GSYM)
  \\ fs [DROP_LENGTH_APPEND] \\ fs [FLOOKUP_DEF]);

val sr_gs_def = stack_removeProofTheory.good_syntax_def
val sa_gs_def = stack_allocProofTheory.good_syntax_def
val sl_gs_def = stack_to_labProofTheory.good_syntax_def
val convs = [sr_gs_def,sa_gs_def,sl_gs_def,wordPropsTheory.post_alloc_conventions_def,wordPropsTheory.call_arg_convention_def,wordLangTheory.every_var_def,wordLangTheory.every_stack_var_def]

val stack_move_sa_gs = prove(``
  ∀n st off i p.
  good_syntax p ⇒
  good_syntax (stack_move n st off i p)``,
  Induct>>rw[stack_move_def,sa_gs_def])

val word_to_stack_sa_gs = prove(``
  ∀p n args.
  good_syntax (FST(word_to_stack$comp p n args))``,
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

val stack_move_sr_gs = prove(``
  ∀n st off i p k.
  i < k ∧
  good_syntax p k ⇒
  good_syntax (stack_move n st off i p) k``,
  Induct>>rw[stack_move_def,sr_gs_def])

val word_to_stack_sr_gs = prove(``
  ∀p n args.
  post_alloc_conventions (FST args) p ∧
  1 ≤ FST args ⇒
  good_syntax (FST(word_to_stack$comp p n args)) (FST args+2)``,
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
    fs[wStackLoad_def,sr_gs_def])
  >- (fs[wReg1_def,SeqStackFree_def]>>BasicProvers.EVERY_CASE_TAC>>fs[sr_gs_def,wStackLoad_def])
  >- rpt (pairarg_tac>>fs convs)
  >- (rpt (pairarg_tac>>fs convs)>>
  Cases_on`ri`>>fs[wReg1_def,wRegImm2_def,wReg2_def]>>BasicProvers.EVERY_CASE_TAC>>fs[]>>rveq>>fs[wStackLoad_def,sr_gs_def])
  >-
    (fs[wReg1_def]>>BasicProvers.EVERY_CASE_TAC>>
    fs[sr_gs_def,wStackLoad_def]>>
    (*TODO: Make the compiler check name ≠ BitmapBase more explicitly or
      delete this syntactic check using semantics?*)
    cheat)
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
  >- (rpt(pairarg_tac>>fs[sr_gs_def])>>rveq>>fs[sr_gs_def]))

val stack_move_sl_gs = prove(``
  ∀n st off i p.
  good_syntax p 2 1 0 ⇒
  good_syntax (stack_move n st off i p) 2 1 0``,
  Induct>>rw[stack_move_def,sl_gs_def])

val word_to_stack_sl_gs = prove(``
  ∀p n args.
  post_alloc_conventions (FST args) p ⇒
  good_syntax (FST(word_to_stack$comp p n args)) 2 1 0``,
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
    fs[wStackLoad_def,sl_gs_def])
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
  >- (rpt(pairarg_tac>>fs[sl_gs_def])>>rveq>>fs[sl_gs_def])
  (*TODO: the conventions for ptr and len in FFI are flipped...
    or should the check be 1 2 0 instead?*)
  >- cheat
  >- cheat);

val bvp_to_word_compile_imp = prove(
  ``
    (LENGTH mc_conf.target.config.avoid_regs + 5) < mc_conf.target.config.reg_count ∧
    compile (c:'a backend$config).word_to_word_conf mc_conf.target.config
        (MAP (compile_part c.bvp_conf) prog) = (col,p) ==>
    code_rel c.bvp_conf (fromAList prog)
      (fromAList (MAP ((compile_part c.bvp_conf) :
         num # num # bvp$prog -> num # num # 'a wordLang$prog) prog)) /\
    code_rel_ext
      (fromAList (MAP ((compile_part c.bvp_conf) :
         num # num # bvp$prog -> num # num # 'a wordLang$prog) prog),fromAList p) /\
    EVERY
    (λ(n,m,prog).
       flat_exp_conventions prog ∧
       post_alloc_conventions
         (mc_conf.target.config.reg_count −
          (LENGTH mc_conf.target.config.avoid_regs + 5)) prog) p /\
    (compile mc_conf.target.config p = (c2,prog1) ==>
     EVERY (\p. stack_to_labProof$good_syntax p 2 1 0) (MAP SND prog1) /\
     EVERY stack_allocProof$good_syntax (MAP SND prog1) /\
     EVERY (\p. stack_removeProof$good_syntax p (mc_conf.target.config.reg_count - (LENGTH mc_conf.target.config.avoid_regs +3)))
       (MAP SND prog1))``,
  fs[code_rel_def,code_rel_ext_def]>>strip_tac>>
  CONJ_TAC>-
    (fs[lookup_fromAList]>>
    last_x_assum kall_tac>>
    last_x_assum kall_tac>>
    Induct_on`prog`>>rw[]>>PairCases_on`h`>>
    fs[bvp_to_wordTheory.compile_part_def]>>
    IF_CASES_TAC>>fs[])>>
  CONJ_TAC>-
    (fs[lookup_fromAList,word_to_wordTheory.compile_def]>>
    pairarg_tac>>fs[]>>rveq>>
    (*existential shouldn't be there on p_2 because it's the oracle dependant on n*)
    cheat)>>
  CONJ_ASM1_TAC>-
    (assume_tac(GEN_ALL word_to_wordProofTheory.compile_to_word_conventions)>>
    pop_assum (qspecl_then [`c.word_to_word_conf`,`(MAP (compile_part c.bvp_conf) prog)`,`mc_conf.target.config`] assume_tac)>>rfs[])>>
  rw[]>>fs[word_to_stackTheory.compile_def]>>pairarg_tac>>fs[]>>rveq>>
  fs[word_to_stackTheory.raise_stub_def,sr_gs_def,sa_gs_def,sl_gs_def]>>
  fs[word_to_stackTheory.compile_word_to_stack_def]>>
  qabbrev_tac`b=[4w]`>>pop_assum kall_tac>>
  qpat_assum`A=(col,p)` kall_tac>>
  rpt (pop_assum mp_tac)>>
  map_every qid_spec_tac [`progs`,`bitmaps`,`p`,`b`]>>
  Induct_on`p`>>
  fs[compile_word_to_stack_def,FORALL_PROD]>>rw[]>>
  pairarg_tac>>fs[]>>
  pairarg_tac>>fs[]>>
  rveq>>fs[]>>
  (reverse CONJ_TAC>-metis_tac[])>>
  qpat_assum`A=(prog,bitmaps')` mp_tac>>
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

val stack_alloc_syntax = prove(
  ``10 ≤ sp ∧
    EVERY (λp. good_syntax p 2 1 0) (MAP SND prog1) /\
    EVERY (\p. stack_removeProof$good_syntax p sp)
       (MAP SND prog1) ==>
    EVERY (λp. good_syntax p 2 1 0) (MAP SND (compile c.bvp_conf prog1)) /\
    EVERY (\p. stack_removeProof$good_syntax p sp)
       (MAP SND (compile c.bvp_conf prog1))``,
  fs[stack_allocTheory.compile_def]>>
  EVAL_TAC>>fs[]>>
  cheat);

val word_to_stack_compile_imp = prove(
  ``word_to_stack$compile c p = (c2,prog1) ==>
    (case c2.bitmaps of [] => F | h::v1 => 4w = h)``,
  fs [word_to_stackTheory.compile_def] \\ pairarg_tac \\ fs [] \\ rw [] \\ fs []
  \\ imp_res_tac compile_word_to_stack_isPREFIX
  \\ Cases_on `bitmaps` \\ fs []);

val make_init_opt_imp_bitmaps_limit = prove(
  ``make_init_opt max_heap bitmaps k code s = SOME x ==>
    LENGTH (bitmaps:'a word list) < dimword (:'a) − 1``,
  fs [stack_removeProofTheory.make_init_opt_def]
  \\ every_case_tac \\ fs [] \\ rw []
  \\ fs [stack_removeProofTheory.init_prop_def,
         stack_removeProofTheory.init_reduce_def]);

val bvp_to_word_names = prove(
  ``word_to_word$compile c1 c2 (MAP (compile_part c3) prog) = (col,p) ==>
    MAP FST p = MAP FST prog``,
  rw[]>>assume_tac(GEN_ALL word_to_wordProofTheory.compile_to_word_conventions)>>
  pop_assum (qspecl_then [`c1`,`(MAP (compile_part c3) prog)`,`c2`] assume_tac)>>rfs[]>>
  fs[MAP_MAP_o,MAP_EQ_f,FORALL_PROD,bvp_to_wordTheory.compile_part_def]);

val word_to_stack_names = prove(
  ``word_to_stack$compile c1 p = (c2,prog1) ==>
    MAP FST prog1 = 5::MAP FST p``,
  fs [word_to_stackTheory.compile_def] \\ pairarg_tac \\ fs []
  \\ rw [] \\ fs []>>
  pop_assum mp_tac>>
  qabbrev_tac`b=[4w]`>>pop_assum kall_tac>>
  map_every qid_spec_tac [`progs`,`bitmaps`,`p`,`b`]>>
  Induct_on`p`>>fs[FORALL_PROD,word_to_stackTheory.compile_word_to_stack_def]>>
  rw[]>>rpt (pairarg_tac>>fs[])>>
  rveq>>fs[]>>
  metis_tac[]);

val stack_alloc_names = prove(
  ``stack_alloc$compile c1 p = prog1 ==>
    MAP FST prog1 = 10::MAP FST p``,
  fs [stack_allocTheory.compile_def,stack_allocTheory.stubs_def] \\ rw []
  \\ fs [MAP_MAP_o,MAP_EQ_f,FORALL_PROD,stack_allocTheory.prog_comp_def]);

val code_installed_prog_to_section = prove(
  ``ALOOKUP prog4 n = SOME prog3 ==>
    ?pc.
      code_installed pc (FST (flatten prog3 n (next_lab prog3)))
        (MAP prog_to_section prog4) /\
      loc_to_pc n 0 (MAP prog_to_section prog4) = SOME pc``,
  cheat);

val stack_remove_syntax_pres = prove(
  ``Abbrev (prog3 = compile n bitmaps k pos prog2) /\
    EVERY (λp. good_syntax p 2 1 0) (MAP SND prog2) ==>
    EVERY (λp. good_syntax p 2 1 0) (MAP SND prog3)``,
  cheat);

val stack_names_syntax_pres = prove(
  ``Abbrev (prog4 = stack_names$compile f prog3) /\
    EVERY (λp. good_syntax p 2 1 0) (MAP SND prog3) ==>
    EVERY (λp. good_syntax p (find_name f 2)
                             (find_name f 1)
                             (find_name f 0)) (MAP SND prog4)``,
  cheat);

val MEM_pair_IMP = prove(
  ``!xs. MEM (x,y) xs ==> MEM x (MAP FST xs) /\ MEM y (MAP SND xs)``,
  Induct \\ fs [FORALL_PROD] \\ metis_tac []);

val IS_SOME_EQ_CASE = prove(
  ``IS_SOME x <=> case x of NONE => F | SOME _ => T``,
  Cases_on `x` \\ fs []);

val compile_eq_imp = prove(
  ``x = x' /\ y = y' ==>
    lab_to_target$compile x y = lab_to_target$compile x' y'``,
  fs []);

val BIJ_FLOOKUP_MAPKEYS = prove(
  ``BIJ bij UNIV UNIV ==>
    FLOOKUP (MAP_KEYS (LINV bij UNIV) f) n = FLOOKUP f (bij n)``,
  fs [FLOOKUP_DEF,MAP_KEYS_def,BIJ_DEF] \\ strip_tac
  \\ match_mp_tac (METIS_PROVE []
      ``x=x'/\(x /\ x' ==> y=y') ==> (if x then y else z) = (if x' then y' else z)``)
  \\ fs [] \\ rw []
  THEN1 (eq_tac \\ rw [] \\ metis_tac [BIJ_LINV_INV,BIJ_DEF,IN_UNIV,LINV_DEF])
  \\ `BIJ (LINV bij UNIV) UNIV UNIV` by metis_tac [BIJ_LINV_BIJ,BIJ_DEF]
  \\ `INJ (LINV bij UNIV) (FDOM f) UNIV` by fs [INJ_DEF,IN_UNIV,BIJ_DEF]
  \\ fs [MAP_KEYS_def] \\ metis_tac [BIJ_LINV_INV,BIJ_DEF,IN_UNIV,LINV_DEF]);

(* Broken *)
local
val lemma = prove(
  ``(from_bvp c prog = SOME (bytes,ffi_limit) /\
     EVERY (\n. 30 <= n) (MAP FST prog) /\ ALL_DISTINCT (MAP FST prog) /\
     good_init_state mc_conf (t:'a asm_state)
       m ms ffi ffi_limit bytes io_regs save_regs) /\
    (bvp_to_wordProof$conf_ok (:α) c.bvp_conf /\
    c.lab_conf.encoder = mc_conf.target.encode /\
    c.lab_conf.asm_conf = mc_conf.target.config /\
    backend_correct mc_conf.target /\ good_dimindex (:'a) /\
    find_name c.stack_conf.reg_names PERMUTES UNIV /\
    (case mc_conf.target.config.link_reg of NONE => 0 | SOME n => n) ∉
      ({mc_conf.len_reg; mc_conf.ptr_reg} UNION save_regs) /\
    find_name c.stack_conf.reg_names 2 = mc_conf.len_reg /\
    find_name c.stack_conf.reg_names 1 = mc_conf.ptr_reg /\
    (find_name c.stack_conf.reg_names 0 =
       case mc_conf.target.config.link_reg of NONE => 0 | SOME n => n) /\
    2 < mc_conf.target.config.reg_count −
         (LENGTH mc_conf.target.config.avoid_regs + 5) /\
    save_regs = set mc_conf.caller_saved_regs /\
    MEM (find_name c.stack_conf.reg_names c.stack_conf.stack_ptr)
      mc_conf.caller_saved_regs /\
    MEM (find_name c.stack_conf.reg_names (c.stack_conf.stack_ptr+1))
      mc_conf.caller_saved_regs /\
    MEM (find_name c.stack_conf.reg_names (c.stack_conf.stack_ptr+2))
      mc_conf.caller_saved_regs /\
    8 <= c.stack_conf.stack_ptr) ==>
    bvp_to_word_precond (bytes,c,ffi:'ffi ffi_state,ffi_limit,mc_conf,ms,prog)``,
  strip_tac \\ fs [bvp_to_word_precond_def,lab_to_targetProofTheory.good_syntax_def]
  \\ `ffi.final_event = NONE /\ byte_aligned (t.regs mc_conf.ptr_reg)` by
        fs [good_init_state_def] \\ fs [EXISTS_PROD]
  \\ fs [EVAL ``lookup 0 (LS x)``,word_to_stackProofTheory.make_init_def]
  \\ fs [full_make_init_ffi,full_make_init_gc_fun]
  \\ ConseqConv.CONSEQ_CONV_TAC (ConseqConv.CONSEQ_REWRITE_CONV
                ([], [full_init_pre_IMP_init_store_ok,
                      full_init_pre_IMP_init_state_ok], []))
  \\ simp_tac (std_ss++CONJ_ss) [full_make_init_bitmaps] \\ fs [GSYM CONJ_ASSOC]
  \\ fs [from_bvp_def] \\ pairarg_tac \\ fs []
  \\ fs [from_word_def] \\ pairarg_tac \\ fs []
  \\ fs [from_stack_def,stack_to_labTheory.compile_def]
  \\ fs [from_lab_def]
  \\ asm_exists_tac \\ fs []
  \\ qcase_tac `_ = (c2,prog1)`
  \\ qabbrev_tac `prog2 = compile c.bvp_conf prog1`
  \\ qpat_assum `_ = SOME _` mp_tac
  \\ qpat_abbrev_tac `prog3 = compile _ _ _ _ _`
  \\ qabbrev_tac `prog4 = compile c.stack_conf.reg_names prog3`
  \\ disch_then (assume_tac o GSYM) \\ fs []
  \\ ConseqConv.CONSEQ_CONV_TAC (ConseqConv.CONSEQ_REWRITE_CONV
                ([], [compile_eq_imp], [])) \\ fs []
  \\ GEN_EXISTS_TAC "c1" `c.bvp_conf` \\ fs []
  \\ fs [bvp_to_wordTheory.compile_def]
  \\ GEN_EXISTS_TAC "asm_conf" `c.lab_conf.asm_conf` \\ fs []
  \\ GEN_EXISTS_TAC "max_heap" `2 * max_heap_limit (:α) c.bvp_conf` \\ fs []
  \\ drule bvp_to_word_compile_imp \\ strip_tac
  \\ GEN_EXISTS_TAC "x1" `fromAList (MAP (compile_part c.bvp_conf) prog)` \\ fs []
  \\ GEN_EXISTS_TAC "code3" `p` \\ fs []
  \\ GEN_EXISTS_TAC "bitmaps" `c2.bitmaps` \\ fs []
  \\ GEN_EXISTS_TAC "codeN" `prog1` \\ fs []
  \\ drule word_to_stack_compile_imp \\ strip_tac \\ fs []
  \\ fs [full_init_pre_def |> SIMP_RULE (std_ss++CONJ_ss) [],full_init_pre_fail_def]
  \\ GEN_EXISTS_TAC "k" `c.stack_conf.stack_ptr` \\ fs []
  \\ GEN_EXISTS_TAC "f" `c.stack_conf.reg_names` \\ fs []
  \\ `?regs. init_pre (2 * max_heap_limit (:α) c.bvp_conf) c2.bitmaps
        c.stack_conf.stack_ptr InitGlobals_location
        (make_init c.stack_conf.reg_names (fromAList prog3)
           (make_init (fromAList prog4) regs save_regs
              (make_init mc_conf ffi save_regs io_regs t m ms
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
    \\ conj_tac THEN1 metis_tac [LINV_DEF,IN_UNIV,BIJ_DEF]
    \\ conj_tac THEN1 metis_tac [LINV_DEF,IN_UNIV,BIJ_DEF]
    \\ conj_tac THEN1 metis_tac [LINV_DEF,IN_UNIV,BIJ_DEF]
    \\ cheat (* almost true *))
  \\ qexists_tac `regs` \\ fs []
  \\ fs [IS_SOME_EQ_CASE] \\ CASE_TAC \\ fs []
  \\ SIMP_TAC (std_ss++CONJ_ss)
       [EVAL ``(make_init mc_conf ffi save_regs io_regs t m ms code).code``,
        EVAL ``(make_init mc_conf ffi save_regs io_regs t m ms code).pc``]
  \\ imp_res_tac make_init_opt_imp_bitmaps_limit \\ fs []
  \\ `loc_to_pc 0 0 (MAP prog_to_section prog4) = SOME 0` by
   (qunabbrev_tac `prog4`
    \\ qunabbrev_tac `prog3`
    \\ fs [stack_removeTheory.compile_def,
           stack_removeTheory.init_stubs_def,
           stack_namesTheory.compile_def,
           stack_namesTheory.prog_comp_def,
           stack_to_labTheory.prog_to_section_def]
    \\ pairarg_tac \\ fs [] \\ fs [Once labSemTheory.loc_to_pc_def]) \\ fs []
  \\ imp_res_tac bvp_to_word_names
  \\ imp_res_tac word_to_stack_names \\ fs [ALOOKUP_NONE]
  \\ `MAP FST prog2 = 10::MAP FST prog1` by metis_tac [stack_alloc_names] \\ fs []
  \\ fs [AC CONJ_ASSOC CONJ_COMM] \\ rfs []
  \\ rpt (conj_tac THEN1 (fs [EVERY_MEM] \\ strip_tac \\ res_tac \\ fs []))
  \\ conj_tac \\ TRY
   (imp_res_tac stack_alloc_syntax \\ rfs []
    \\ fs [EVERY_MEM,FORALL_PROD] \\ rw []
    \\ `MEM p_1 (MAP FST prog2) /\ MEM p_2 (MAP SND prog2)` by
     (fs [MEM_MAP,PULL_EXISTS,FORALL_PROD,EXISTS_PROD]
      \\ rpt (asm_exists_tac \\ fs [])) \\ fs [] \\ rfs []
    \\ fs [MEM_MAP,EXISTS_PROD,PULL_EXISTS] \\ res_tac \\ fs [] \\ NO_TAC)
  \\ TRY conj_tac
  \\ TRY (rpt strip_tac \\ qcase_tac `ALOOKUP prog1 k = SOME _`
    \\ imp_res_tac ALOOKUP_MEM
    \\ imp_res_tac MEM_pair_IMP \\ rfs [EVERY_MEM]
    \\ res_tac \\ fs [])
  \\ fs [state_rel_make_init,lab_to_targetProofTheory.make_init_def]
  \\ fs [PULL_EXISTS] \\ rpt strip_tac
  \\ TRY (qcase_tac `byte_aligned w`
    \\ `byte_aligned (w + t.regs mc_conf.ptr_reg)` by
          fs [alignmentTheory.byte_aligned_def,alignmentTheory.aligned_add_sub]
    \\ pop_assum mp_tac
    \\ qspec_tac (`w + t.regs mc_conf.ptr_reg`,`v`)
    \\ Cases \\ fs [stack_removeProofTheory.aligned_w2n,
         alignmentTheory.byte_aligned_def]
    \\ fs [labPropsTheory.good_dimindex_def] \\ NO_TAC)
  \\ fs [GSYM PULL_EXISTS] \\ fs [lookup_fromAList]
  \\ drule code_installed_prog_to_section \\ fs [] \\ strip_tac
  \\ imp_res_tac ALOOKUP_MEM
  \\ imp_res_tac MEM_pair_IMP
  \\ imp_res_tac stack_alloc_syntax \\ rfs []
  \\ drule stack_remove_syntax_pres \\ fs [] \\ strip_tac
  \\ drule stack_names_syntax_pres \\ fs []
  \\ simp [EVERY_MEM] \\ disch_then drule \\ fs [])
  |> GEN_ALL |> SIMP_RULE std_ss [] |> SPEC_ALL;
val tm = lemma |> concl |> dest_imp |> fst |> dest_conj |> snd
in
(* TODO: this conf_ok should be defined in backendTheory, so that we
         can prove that each backend's config is correct without
         requiring to build all the proofs. *)
val conf_ok_def = Define `conf_ok c mc_conf = ^tm`
val imp_bvp_to_word_precond = lemma |> REWRITE_RULE [GSYM conf_ok_def]
end

val clean_bvp_to_target_thm = let
  val th =
    IMP_TRANS imp_bvp_to_word_precond machine_sem_implements_bvp_sem
    |> SIMP_RULE std_ss [GSYM CONJ_ASSOC]
    |> Q.GENL [`t`,`m`,`io_regs`]
    |> SIMP_RULE std_ss [GSYM CONJ_ASSOC,GSYM PULL_EXISTS]
    |> ONCE_REWRITE_RULE [METIS_PROVE[]``b1/\b2/\b3/\b4/\b5<=>b4/\b1/\b2/\b3/\b5``]
  val tm = th |> concl |> dest_imp |> fst |> dest_conj |> fst
  val installed_def = define_abbrev "installed" tm
  val th = th |> REWRITE_RULE [GSYM installed_def]
  in th end

(* --- composing source-to-target --- *)

val cnv = computeLib.compset_conv (wordsLib.words_compset())
  [computeLib.Extenders [compilerComputeLib.add_compiler_compset],
   computeLib.Defs
     [prim_config_def, initialProgramTheory.prim_types_program_def]]

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

val from_bvp_ignore = prove(
  ``from_bvp (c with <|source_conf := x; mod_conf := y; clos_conf := z|>) prog =
    from_bvp c prog``,
  fs [from_bvp_def,from_word_def,from_stack_def,from_lab_def]
  \\ rpt (pairarg_tac \\ fs []));

val clos_to_bvp_names = store_thm("clos_to_bvp_names",
  ``clos_to_bvl$compile c e4 = (c2,p2) /\
    bvl_to_bvi$compile n1 n p2 = (k,p3,n2) ==>
    EVERY (λn. 30 <= n) (MAP FST (bvi_to_bvp$compile_prog p3)) /\
    ALL_DISTINCT (MAP FST (bvi_to_bvp$compile_prog p3))``,
  cheat);

val compile_correct = Q.store_thm("compile_correct",
  `let (s,env) = THE (prim_sem_env (ffi:'ffi ffi_state)) in
   (c:'a backend$config).source_conf = (prim_config:'a backend$config).source_conf ∧
   c.mod_conf = (prim_config:'a backend$config).mod_conf ∧
   c.clos_conf = (prim_config:'a backend$config).clos_conf ∧
   ¬semantics_prog s env prog Fail ∧
   compile c prog = SOME (bytes,ffi_limit) ∧
   conf_ok c mc ∧
   installed (bytes,ffi,ffi_limit,mc,ms) ⇒
     machine_sem (mc:(α,β,γ) machine_config) ffi ms ⊆
       extend_with_resource_limit (semantics_prog s env prog)`,
  srw_tac[][compile_eq_from_source,from_source_def] >>
  drule(GEN_ALL(MATCH_MP SWAP_IMP source_to_modProofTheory.compile_correct)) >>
  fs[initSemEnvTheory.prim_sem_env_eq] >>
  qpat_assum`_ = s`(assume_tac o Abbrev_intro o SYM) >>
  qpat_assum`_ = env`(assume_tac o Abbrev_intro o SYM) >>
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
     next_inv (IMAGE (SND o SND) (FRANGE (SND( prim_config.mod_conf.tag_env))))
       prim_config.mod_conf.next_exception gtagenv` by (
    simp[source_to_modProofTheory.precondition_def] >>
    simp[Abbr`env`,Abbr`s`] >>
    srw_tac[QUANT_INST_ss[pair_default_qp,record_default_qp]][] >>
    rw[source_to_modProofTheory.invariant_def] >>
    rw[source_to_modProofTheory.s_rel_cases] >>
    rw[source_to_modProofTheory.v_rel_cases] >>
    rw[prim_config_eq] >>
    Cases_on`ffi`>>rw[ffiTheory.ffi_state_component_equality] >>
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
  rator_x_assum`from_mod`mp_tac >>
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
    rator_x_assum`next_inv`mp_tac >>
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
  rator_x_assum`from_con`mp_tac >>
  srw_tac[][from_con_def] >>
  pop_assum mp_tac >> BasicProvers.LET_ELIM_TAC >>
  rfs[] >> fs[] >>
  drule(GEN_ALL(MATCH_MP SWAP_IMP (REWRITE_RULE[GSYM AND_IMP_INTRO]con_to_decProofTheory.compile_semantics))) >>
  simp[] >>
  impl_tac >- (
    rator_x_assum`mod_to_con$compile_prog`mp_tac >>
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
  rator_x_assum`from_dec`mp_tac >> srw_tac[][from_dec_def] >>
  pop_assum mp_tac >> BasicProvers.LET_ELIM_TAC >>
  rator_x_assum`con_to_dec$compile`mp_tac >>
  `c'.next_global = 0` by (
    fs[source_to_modTheory.compile_def,LET_THM] >>
    pairarg_tac >> fs[] >>
    pairarg_tac >> fs[] >>
    rveq >> simp[prim_config_eq] ) >> fs[] >>
  strip_tac >> fs[] >>
  qunabbrev_tac`c''`>>fs[] >>
  qmatch_abbrev_tac`_ ⊆ _ { decSem$semantics env3 st3 es3 }` >>
  (dec_to_exhProofTheory.compile_exp_semantics
    |> Q.GENL[`sth`,`envh`,`es`,`st`,`env`]
    |> qispl_then[`env3`,`st3`,`es3`]mp_tac) >>
  simp[Abbr`env3`] >>
  simp[Once dec_to_exhProofTheory.v_rel_cases] >>
  simp[dec_to_exhProofTheory.state_rel_def] >>
  fs[Abbr`st3`,con_to_decProofTheory.compile_state_def] >>
  CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss()++QUANT_INST_ss[record_default_qp,pair_default_qp])[])) >>
  simp[Abbr`es3`,dec_to_exhTheory.compile_exp_def] >>
  disch_then(strip_assume_tac o SYM) >> fs[] >>
  rator_x_assum`from_exh`mp_tac >>
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
  rator_x_assum`from_pat`mp_tac >>
  srw_tac[][from_pat_def] >>
  pop_assum mp_tac >> BasicProvers.LET_ELIM_TAC >>
  qmatch_abbrev_tac`_ ⊆ _ { patSem$semantics env3 st3 es3 }` >>
  (pat_to_closProofTheory.compile_semantics
   |> Q.GENL[`es`,`st`,`env`]
   |> qispl_then[`env3`,`st3`,`es3`]mp_tac) >>
  simp[Abbr`env3`,Abbr`es3`] >>
  fs[pat_to_closProofTheory.compile_state_def,Abbr`st3`] >>
  disch_then(strip_assume_tac o SYM) >> fs[] >>
  rator_x_assum`from_clos`mp_tac >>
  srw_tac[][from_clos_def] >>
  pop_assum mp_tac >> BasicProvers.LET_ELIM_TAC >>
  qmatch_abbrev_tac`_ ⊆ _ { closSem$semantics [] st3 [e3] }` >>
  (clos_to_bvlProofTheory.compile_semantics
   |> GEN_ALL
   |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["s","e","c"]))
   |> qispl_then[`st3`,`e3`,`c.clos_conf`]mp_tac) >>
  simp[] >>
  impl_tac >- (
    simp[CONJ_ASSOC] >>
    conj_tac >- (
      unabbrev_all_tac >>
      simp[pat_to_closProofTheory.compile_contains_App_SOME] >>
      simp[pat_to_closProofTheory.compile_every_Fn_vs_NONE] >>
      simp[prim_config_eq] >> EVAL_TAC) >>
    simp[Abbr`st3`,clos_to_bvlProofTheory.full_state_rel_def] >>
    simp[Once clos_relationTheory.state_rel_rw] >>
    gen_tac >>
    qho_match_abbrev_tac`∃sa. P sa` >>
    srw_tac[QUANT_INST_ss[record_qp false (fn v => (K (type_of v = ``:'ffi closSem$state``))),pair_default_qp]][] >>
    simp[Abbr`P`] >>
    simp[clos_numberProofTheory.state_rel_def] >>
    qho_match_abbrev_tac`∃sa. P sa` >>
    srw_tac[QUANT_INST_ss[record_qp false (fn v => (K (type_of v = ``:'ffi closSem$state``))),pair_default_qp]][] >>
    simp[Abbr`P`] >>
    qho_match_abbrev_tac`∃sa. P sa` >>
    srw_tac[QUANT_INST_ss[record_qp false (fn v => (K (type_of v = ``:'ffi closSem$state``))),pair_default_qp]][] >>
    simp[Abbr`P`] >>
    simp[Once clos_relationTheory.state_rel_rw] >>
    simp[FEVERY_DEF] >>
    simp[clos_annotateProofTheory.state_rel_def] >>
    qho_match_abbrev_tac`∃sa. P sa` >>
    srw_tac[QUANT_INST_ss[record_qp false (fn v => (K (type_of v = ``:'ffi closSem$state``))),pair_default_qp]][] >>
    simp[Abbr`P`] >>
    qexists_tac`FEMPTY`>>simp[] >>
    simp[clos_to_bvlProofTheory.state_rel_def,FDOM_EQ_EMPTY] >>
    qexists_tac`FEMPTY`>>simp[] >>
    `∃c. p'' = toAList init_code ++ c` by (
      rator_x_assum`clos_to_bvl$compile`mp_tac >>
      rpt(pop_assum kall_tac) >>
      srw_tac[][clos_to_bvlTheory.compile_def] >>
      pop_assum mp_tac >> BasicProvers.LET_ELIM_TAC >>
      fs[] >> rveq >> rw[] ) >>
    rveq >>
    simp[lookup_fromAList,ALOOKUP_APPEND,ALOOKUP_toAList] >>
    strip_assume_tac init_code_ok >> simp[]) >>
  simp[Abbr`e3`] >>
  fs[Abbr`st3`] >>
  disch_then(strip_assume_tac o SYM) >> fs[] >>
  rator_x_assum`from_bvl`mp_tac >>
  srw_tac[][from_bvl_def] >>
  pop_assum mp_tac >> BasicProvers.LET_ELIM_TAC >>
  Q.ISPEC_THEN`s2.ffi`drule(Q.GEN`ffi0` bvl_to_bviProofTheory.compile_semantics) >>
  qunabbrev_tac`c'''`>>fs[] >>
  impl_tac >- (
    (clos_to_bvlProofTheory.compile_all_distinct_locs
     |> ONCE_REWRITE_RULE[CONJ_ASSOC,CONJ_COMM]
     |> ONCE_REWRITE_RULE[CONJ_COMM]
     |> drule) >>
    disch_then match_mp_tac >>
    simp[prim_config_eq] >>
    EVAL_TAC ) >>
  disch_then(SUBST_ALL_TAC o SYM) >>
  rator_x_assum`from_bvi`mp_tac >>
  srw_tac[][from_bvi_def] >>
  pop_assum mp_tac >> BasicProvers.LET_ELIM_TAC >>
  qmatch_abbrev_tac`_ ⊆ _ { bviSem$semantics ffi (fromAList p3) s3 }` >>
  (bvi_to_bvpProofTheory.compile_prog_semantics
   |> GEN_ALL
   |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["prog","start"]))
   |> qispl_then[`p3`,`s3`,`ffi`]mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (SUBST_ALL_TAC o SYM)
  \\ `s3 = InitGlobals_location` by
   (fs [bvl_to_bviTheory.compile_def,bvl_to_bviTheory.compile_prog_def]
    \\ pairarg_tac \\ fs [])
  \\ qcase_tac `from_bvp c4 p4 = _`
  \\ drule (GEN_ALL clean_bvp_to_target_thm)
  \\ disch_then drule
  \\ `conf_ok c4 mc` by (unabbrev_all_tac \\ fs [conf_ok_def] \\ NO_TAC)
  \\ simp[implements_def,AND_IMP_INTRO]
  \\ disch_then match_mp_tac \\ fs []
  \\ qunabbrev_tac `p4` \\ fs []
  \\ drule (GEN_ALL clos_to_bvp_names)
  \\ disch_then drule \\ fs []);

val _ = export_theory();
