(*
  Correctness proof for pan_globals
*)

open preamble
     panSemTheory panLangTheory pan_globalsTheory panPropsTheory
     stack_removeProofTheory (* TODO: just for addresses_def. should this be moved? *)

val _ = new_theory "pan_globalsProof";

val _ = set_grammar_ancestry  ["panSem", "pan_globals", "panProps", "panLang", "stack_removeProof"];

val s = ``s:('a,'ffi) panSem$state``

Definition disjoint_globals_def:
  disjoint_globals top_addr cglobals globals ⇔
  ∀v v' sh addr sh' addr'. v ≠ v' ∧ IS_SOME(FLOOKUP globals v) ∧ IS_SOME(FLOOKUP globals v') ∧
         FLOOKUP cglobals v =  SOME(sh, addr) ∧
         FLOOKUP cglobals v' = SOME(sh', addr') ⇒
         DISJOINT (addresses (top_addr - addr) (size_of_shape sh)) (addresses (top_addr - addr') (size_of_shape sh'))
End

Definition state_rel_def:
  state_rel ls ctxt ^s t ⇔
  s.top_addr = t.top_addr - ctxt.max_globals_size ∧
  (ls ⇒ s.locals = t.locals) ∧
  s.base_addr = t.base_addr ∧
  s.be = t.be ∧
  s.eshapes = t.eshapes ∧
  s.clock = t.clock ∧
  (∀v val.
     FLOOKUP s.globals v = SOME val ⇒
     ∃addr. FLOOKUP ctxt.globals v = SOME(shape_of val, addr) ∧
            mem_load (shape_of val) (t.top_addr - addr) t.memaddrs t.memory = SOME val ∧
            DISJOINT s.memaddrs (addresses (t.top_addr - addr) $ size_of_shape $ shape_of val) ∧
            byte_aligned addr
  ) ∧
  s.memaddrs ⊆ t.memaddrs ∧
  s.sh_memaddrs = t.sh_memaddrs ∧
  (∀addr. addr ∈ s.memaddrs ⇒ s.memory addr = t.memory addr) ∧
  s.ffi = t.ffi ∧
  (∀fname vshapes prog. FLOOKUP s.code fname = SOME (vshapes,prog) ⇒
           FLOOKUP t.code fname = SOME (vshapes, compile ctxt prog)) ∧
  disjoint_globals t.top_addr ctxt.globals s.globals ∧
  t.top_addr ∉ t.memaddrs ∧
  byte_aligned t.top_addr ∧
  good_dimindex(:'a)
End

Theorem state_rel_mem_load:
  state_rel ls ctxt ^s t ∧
  mem_load shape w s.memaddrs s.memory = SOME v ⇒
  mem_load shape w t.memaddrs t.memory = SOME v
Proof
  ‘(∀shape w sa sm ls ctxt ^s t v.
      state_rel ls ctxt s t ∧
      sa = s.memaddrs ∧
      sm = s.memory ∧
      mem_load shape w sa sm = SOME v ⇒
      mem_load shape w t.memaddrs t.memory = SOME v) ∧
   (∀shapes w sa sm ls ctxt ^s t v.
      state_rel ls ctxt s t ∧
      sa = s.memaddrs ∧
      sm = s.memory ∧
      mem_loads shapes w sa sm = SOME v ⇒
      mem_loads shapes w t.memaddrs t.memory = SOME v)
  ’ suffices_by metis_tac[] >>
  ho_match_mp_tac mem_load_ind >>
  rw[] >>
  gvs[mem_load_def,AllCaseEqs()]
  >- gvs[state_rel_def,SUBSET_DEF]
  >- metis_tac[]
  >- (conj_tac >- gvs[state_rel_def,SUBSET_DEF] >>
      reverse conj_tac >- gvs[state_rel_def,SUBSET_DEF] >>
      metis_tac[]) >>
  metis_tac[]
QED

Theorem compile_exp_correct:
  ∀s e v ctxt t.
  state_rel T ctxt s t ∧
  eval s e = SOME v
  ⇒
  eval t (compile_exp ctxt e) = SOME v
Proof
  recInduct eval_ind >> rpt strip_tac
  >~ [‘Var Global’]
  >- (gvs[eval_def,compile_exp_def,AllCaseEqs(),state_rel_def] >>
      first_x_assum drule >>
      rw[] >> rw[eval_def,wordLangTheory.word_op_def])
  >~ [‘Struct’]
  >- (gvs[eval_def,compile_exp_def,AllCaseEqs()] >>
      simp[OPT_MMAP_MAP_o] >>
      irule EQ_TRANS >>
      first_assum $ irule_at $ Pos last >>
      irule OPT_MMAP_CONG >>
      rw[] >>
      first_x_assum $ drule_then drule >>
      drule_all pan_commonPropsTheory.opt_mmap_mem_func >>
      strip_tac >> gvs[])
  >~ [‘Load’]
  >- (gvs[eval_def,compile_exp_def,AllCaseEqs()] >>
      metis_tac[state_rel_mem_load])
  >~ [‘LoadByte’]
  >- gvs[eval_def,compile_exp_def,AllCaseEqs(),mem_load_byte_def,
         state_rel_def,SUBSET_DEF]
  >~ [‘Op’]
  >- (gvs[eval_def,compile_exp_def,AllCaseEqs()] >>
      first_assum $ irule_at $ Pos last >>
      simp[OPT_MMAP_MAP_o] >>
      irule EQ_TRANS >>
      first_assum $ irule_at $ Pos last >>
      irule OPT_MMAP_CONG >>
      rw[] >>
      first_x_assum $ drule_then drule >>
      drule_all pan_commonPropsTheory.opt_mmap_mem_func >>
      strip_tac >> gvs[])
  >~ [‘Panop’]
  >- (gvs[eval_def,compile_exp_def,AllCaseEqs()] >>
      first_assum $ irule_at $ Pos last >>
      simp[OPT_MMAP_MAP_o] >>
      irule EQ_TRANS >>
      first_assum $ irule_at $ Pos last >>
      irule OPT_MMAP_CONG >>
      rw[] >>
      first_x_assum $ drule_then drule >>
      drule_all pan_commonPropsTheory.opt_mmap_mem_func >>
      strip_tac >> gvs[]) >>
  gvs[wordLangTheory.word_op_def,state_rel_def,eval_def,compile_exp_def,AllCaseEqs()]
QED

Definition good_res_def:
  good_res(SOME TimeOut) = F ∧
  good_res(SOME(Return v)) = F ∧
  good_res(SOME(Exception l v)) = F ∧
  good_res(SOME(FinalFFI ev)) = F ∧
  good_res _ = T
End

val gen_goal =
  “λcomp (p,s). ∀res ctxt t s'.
  state_rel T ctxt s t ∧
  evaluate(p,s) = (res,s') ∧
  res ≠ SOME Error
  ⇒
  ∃t'.
    evaluate(comp ctxt p,t) = (res,t') ∧
    state_rel (good_res res) ctxt s' t'”

local
  val goal = beta_conv ``^gen_goal pan_globals$compile``
  val ind_thm = panSemTheory.evaluate_ind
    |> ISPEC goal
    |> CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV) |> REWRITE_RULE [];
  fun list_dest_conj tm = if not (is_conj tm) then [tm] else let
    val (c1,c2) = dest_conj tm in list_dest_conj c1 @ list_dest_conj c2 end
  val ind_goals = ind_thm |> concl |> dest_imp |> fst |> list_dest_conj
in
  fun get_goal s = first (can (find_term (can (match_term (Term [QUOTE s]))))) ind_goals
  fun compile_tm () = ind_thm |> concl |> rand
  fun the_ind_thm () = ind_thm
  val fgoal = beta_conv ``^gen_goal pan_globals$compile``
end

Theorem compile_Skip_Break_Continue_Annot_Tick:
  ^(get_goal "compile _ Skip") /\
  ^(get_goal "compile _ Break") /\
  ^(get_goal "compile _ Continue") /\
  ^(get_goal "compile _ (Annot _ _)") /\
  ^(get_goal "compile _ Tick")
Proof
  rpt strip_tac >>
  gvs[evaluate_def,compile_def,AllCaseEqs(),dec_clock_def,
      state_rel_def,empty_locals_def]
QED

Theorem compile_Assign_Local:
  ^(get_goal "compile _ (Assign Local _ _)")
Proof
  rpt strip_tac >>
  gvs[evaluate_def,compile_def,AllCaseEqs()] >>
  drule_all_then strip_assume_tac compile_exp_correct >>
  simp[] >>
  gvs[state_rel_def]
QED

(* TODO: move? *)
Theorem mem_stores_append:
  ∀addr vs addrs memory vs'.
    mem_stores addr (vs ++ vs') addrs memory =
    case mem_stores addr vs addrs memory of
    NONE => NONE
    | SOME memory' => mem_stores (addr + bytes_in_word * n2w(LENGTH vs)) vs' addrs memory'
Proof
  Induct_on ‘vs’ >>
  rw[mem_stores_def] >>
  rpt (TOP_CASE_TAC >> gvs[n2w_SUC,WORD_LEFT_ADD_DISTRIB])
QED

Theorem mem_stores_memory_swap:
  ∀addr vs addrs memory memory' m.
    mem_stores addr vs addrs memory = SOME m ⇒
    ∃m'. mem_stores addr vs addrs memory' = SOME m'
Proof
  Induct_on ‘vs’ >> rw[mem_stores_def,AllCaseEqs(), mem_store_def] >>
  metis_tac[]
QED

Theorem mem_load_mem_store:
  (∀s (addr:'a word) addrs memory v w.
     mem_load s addr addrs memory = SOME v ∧
     shape_of w = s ⇒
     ∃m. mem_stores addr (flatten w) addrs memory = SOME m) ∧
  (∀ss (addr:'a word) addrs memory vs ws.
     mem_loads ss addr addrs memory = SOME vs ∧
     ss = MAP shape_of ws ⇒
     ∃m. mem_stores addr (FLAT (MAP (λa. flatten a) ws)) addrs memory = SOME m)
Proof
  ho_match_mp_tac mem_load_ind >>
  rw[mem_load_def,AllCaseEqs()]
  >- (gvs[Once $ oneline shape_of_def] >>
      gvs[AllCaseEqs(),mem_stores_def,flatten_def,mem_store_def])
  >- (first_x_assum $ drule_then drule >>
      strip_tac >>
      gvs[Once $ oneline shape_of_def,AllCaseEqs(),ETA_THM,flatten_def])
  >- simp[mem_stores_def]
  >- (gvs[MAP_EQ_CONS |> CONV_RULE $ LHS_CONV SYM_CONV] >>
      first_x_assum drule >> simp[] >>
      strip_tac >>
      simp[mem_stores_append] >>
      gvs[Once $ oneline shape_of_def, AllCaseEqs(), flatten_def, size_of_shape_def, ETA_THM] >>
      gvs[mem_stores_def,mem_store_def,AllCaseEqs()] >>
      metis_tac[mem_stores_memory_swap])
  >- (gvs[MAP_EQ_CONS |> CONV_RULE $ LHS_CONV SYM_CONV] >>
      first_x_assum $ resolve_then Any mp_tac EQ_REFL >>
      strip_tac >>
      simp[mem_stores_append] >>
      qpat_x_assum ‘_ = shape_of _’ $ assume_tac o GSYM >>
      gvs[Once $ oneline shape_of_def, AllCaseEqs(), flatten_def, size_of_shape_def, ETA_THM, LENGTH_FLAT] >>
      gvs[MAP_MAP_o,o_DEF,length_flatten_eq_size_of_shape] >>
      metis_tac[mem_stores_memory_swap])
QED

(* TODO: move *)
Theorem mem_stores_lookup:
  ∀addr vs addrs memory m addr'.
    mem_stores addr vs addrs memory = SOME m ∧
    addr' ∉ addresses addr (LENGTH vs) ⇒
    m addr' = memory addr'
Proof
  Induct_on ‘vs’ >>
  rw[mem_stores_def,AllCaseEqs(),addresses_def] >>
  res_tac >>
  simp[] >>
  gvs[mem_store_def,APPLY_UPDATE_THM]
QED

Theorem mem_stores_load_disjoint:
  (∀sh (addr:'a word) vs addrs memory m addr'.
    mem_stores addr vs addrs memory = SOME m ∧
    DISJOINT (addresses addr' (size_of_shape sh)) (addresses addr (LENGTH vs)) ⇒
    mem_load sh addr' addrs m = mem_load sh addr' addrs memory) ∧
  (∀shs (addr:'a word) vs addrs memory m addr'.
    mem_stores addr vs addrs memory = SOME m ∧
    DISJOINT (addresses addr' (SUM(MAP size_of_shape shs))) (addresses addr (LENGTH vs)) ⇒
    mem_loads shs addr' addrs m = mem_loads shs addr' addrs memory)
Proof
  Induct >>
  PURE_ONCE_REWRITE_TAC[mem_load_def] >>
  rw[addresses_def,size_of_shape_def,
     CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV addresses_def,
     ETA_THM]
  >- metis_tac[mem_stores_lookup]
  >- metis_tac[] >>
  ntac 2 $ first_x_assum drule >>
  disch_then $ qspec_then ‘addr'’ mp_tac >>
  impl_tac
  >- (gvs[addresses_thm,DISJOINT_ALT,PULL_EXISTS] >>
      rpt strip_tac >>
      first_x_assum $ qspec_then ‘i’ mp_tac >>
      simp[] >>
      metis_tac[]) >>
  strip_tac >>
  simp[] >>
  qmatch_goalsub_abbrev_tac ‘mem_loads _ a1’ >>
  disch_then $ qspec_then ‘a1’ mp_tac >>
  impl_tac
  >- (gvs[addresses_thm,DISJOINT_ALT,PULL_EXISTS, Abbr ‘a1’] >>
      rpt strip_tac >>
      first_x_assum $ qspec_then ‘i + size_of_shape sh’ mp_tac >>
      simp[GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB] >>
      metis_tac[]) >>
  strip_tac >>
  simp[]
QED

Theorem mem_stores_mem_load_back:
  (∀val (addr:'a word) addrs memory m.
    mem_stores addr (flatten val) addrs memory = SOME m ∧
    LENGTH(flatten val)*w2n(bytes_in_word:'a word) < dimword(:'a) ∧
    good_dimindex(:'a)
    ⇒
    mem_load (shape_of val) addr addrs m =
    SOME val) ∧
  (∀vals (addr:'a word) addrs memory m.
    mem_stores addr (FLAT (MAP (λa. flatten a) vals)) addrs memory = SOME m ∧
    LENGTH(FLAT (MAP (λa. flatten a) vals))*w2n(bytes_in_word:'a word) < dimword(:'a) ∧
    good_dimindex(:'a) ⇒
    mem_loads (MAP shape_of vals) addr addrs m =
    SOME vals)
Proof
  ho_match_mp_tac v_induction >>
  rw[flatten_def,shape_of_def,mem_stores_def,AllCaseEqs(),
     mem_store_def,mem_load_def] >>
  rw[UPDATE_APPLY]
  >- (rw[Once $ oneline shape_of_def] >> PURE_CASE_TAC >> simp[])
  >- (first_x_assum drule >> gvs[ETA_THM])
  >- (gvs[mem_stores_append,AllCaseEqs()] >>
      res_tac >>
      fs[] >>
      gvs[]
      >- (gvs[] >>
          irule mem_stores_lookup >>
          first_assum $ irule_at (Pos last) >>
          simp[addresses_thm] >>
          gvs[oneline shape_of_def,AllCaseEqs(),flatten_def] >>
          SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC, addressTheory.WORD_EQ_ADD_CANCEL] >>
          rpt strip_tac >>
          gvs[bytes_in_word_def,word_mul_n2w,word_add_n2w,good_dimindex_def,dimword_def]) >>
      simp[mem_load_def] >>
      drule $ cj 2 mem_stores_load_disjoint >>
      disch_then $ qspecl_then [‘shapes’,‘addr’] mp_tac >>
      reverse impl_tac >- pop_assum $ simp o single >>
      gvs[shape_of_def,ETA_THM,LENGTH_FLAT,
          MAP_MAP_o,o_DEF,length_flatten_eq_size_of_shape,
          size_of_shape_def
         ] >>
      gvs[DISJOINT_ALT,addresses_thm,PULL_EXISTS] >>
      rw[] >>
      gvs[ETA_THM] >>
      FULL_SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC, addressTheory.WORD_EQ_ADD_CANCEL] >>
      spose_not_then strip_assume_tac >>
      gvs[bytes_in_word_def,word_mul_n2w,word_add_n2w,good_dimindex_def,dimword_def,
          LEFT_ADD_DISTRIB,shape_of_def]) >>
  gvs[mem_stores_append,AllCaseEqs()] >>
  first_x_assum drule >> simp[] >>
  strip_tac >>
  gvs[length_flatten_eq_size_of_shape]
QED

Theorem LESS_MULT_MONO'[local]:
  0:num < a ⇒ (a * m < a * n ⇔ m < n)
Proof
  rw[]
QED

Theorem byte_aligned_mul_bytes_in_word:
  good_dimindex(:'a) ∧
  byte_aligned(a:'a word) ⇒
  ∃b. a = b*bytes_in_word ∧ w2n b * w2n(bytes_in_word:'a word) < dimword(:'a)
Proof
  rpt strip_tac >>
  gvs[byte_aligned_def,aligned_def,align_w2n] >>
  qexists_tac ‘n2w(w2n a DIV w2n(bytes_in_word:'a word))’ >>
  irule_at Any EQ_TRANS >>
  first_x_assum $ irule_at Any o GSYM >>
  gvs[good_dimindex_def,bytes_in_word_def,word_mul_n2w,word_add_n2w,dimword_def] >>
  Cases_on ‘a’ >>
  simp[DIV_MOD_MOD_DIV] >>
  gvs[dimword_def] >>
  intLib.COOPER_TAC
QED

Theorem w2n_add_alt:
  ∀a b.
    w2n(a:'a word) + w2n(b:'a word) < dimword(:'a) ⇒
    w2n a + w2n b = w2n(a+b)
Proof
  Cases >> Cases >>
  gvs[word_add_n2w, word_ls_n2w, w2n_n2w, word_L_def, dimword_def,
       INT_MIN_def, WORD_MSB_INT_MIN_LS, DIMINDEX_GT_0]
QED

Theorem good_dimindex_w2n_add:
  good_dimindex(:'a) ∧
  byte_aligned(a:'a word) ∧
  a ≠ -1w * bytes_in_word
  ⇒
  w2n a + w2n(bytes_in_word:'a word) = w2n(a+bytes_in_word)
Proof
  rpt strip_tac >>
  irule w2n_add_alt >>
  drule_all byte_aligned_mul_bytes_in_word >>
  strip_tac >>
  gvs[] >>
  Cases_on ‘b’ >>
  gvs[word_add_n2w, word_ls_n2w, w2n_n2w, word_L_def, dimword_def, word_mul_n2w,
       INT_MIN_def, WORD_MSB_INT_MIN_LS, DIMINDEX_GT_0,good_dimindex_def,bytes_in_word_def] >>
  simp[GSYM SUB_LEFT_LESS]
  >- (gvs[LT_EXISTS] >>
      ntac 4 (rename [‘SUC dd’] >>
              Cases_on ‘dd’ >> gvs[ADD_EQ_SUB] >>
              gvs[Once ADD1])
      >- (ntac 2 $ pop_assum mp_tac >>
          EVAL_TAC >> simp[dimword_def]) >>
      intLib.COOPER_TAC)
  >- (gvs[LT_EXISTS] >>
      ntac 8 (rename [‘SUC dd’] >>
              Cases_on ‘dd’ >> gvs[ADD_EQ_SUB] >>
              gvs[Once ADD1])
      >- (ntac 2 $ pop_assum mp_tac >>
          EVAL_TAC >> simp[dimword_def]) >>
      intLib.COOPER_TAC)
QED

Theorem mem_stores_bounded_length:
  ∀addr ws addrs memory m addr'.
    mem_stores addr ws addrs memory = SOME m ∧
    addr' ∉ addrs ∧
    byte_aligned addr ∧
    byte_aligned(addr':'a word) ∧
    good_dimindex(:'a)
    ⇒
    w2n(bytes_in_word:'a word)*LENGTH ws ≤ w2n(addr' - addr)
Proof
  Induct_on ‘ws’ >>
  rw[mem_stores_def,mem_store_def,AllCaseEqs()] >>
  first_x_assum drule >>
  simp[] >>
  disch_then $ qspec_then ‘addr'’ mp_tac >>
  simp[] >>
  impl_keep_tac
  >- (irule byte_aligned_add >>
      simp[] >>
      gvs[good_dimindex_def,bytes_in_word_def,byte_aligned_def,aligned_def,align_def] >>
      EVAL_TAC >> simp[dimword_def] >> EVAL_TAC >> simp[dimword_def] >> EVAL_TAC) >>
  Cases_on ‘addr = addr'’ >> gvs[] >>
  simp[ADD1,LEFT_ADD_DISTRIB,WORD_LEFT_ADD_DISTRIB] >>
  strip_tac >>
  Cases_on ‘-1w * addr + addr' + -1w * bytes_in_word = -1w * bytes_in_word’
  >- gvs[WORD_SUM_ZERO] >>
  dxrule $ iffRL ADD_MONO_LESS_EQ >>
  disch_then $ qspec_then ‘w2n(bytes_in_word:'a word)’ mp_tac >>
  strip_tac >>
  irule LESS_EQ_TRANS >>
  first_x_assum $ irule_at $ Pos hd >>
  PURE_ONCE_REWRITE_TAC[ADD_COMM] >>
  dep_rewrite.DEP_ONCE_REWRITE_TAC[good_dimindex_w2n_add] >>
  simp[] >>
  irule byte_aligned_add >>
  reverse conj_tac
  >- (EVAL_TAC >> gvs[good_dimindex_def,dimword_def] >> EVAL_TAC >> simp[dimword_def] >> EVAL_TAC) >>
  irule byte_aligned_add >>
  simp[] >>
  rw[byte_aligned_def] >>
  irule $ SIMP_RULE (srw_ss()) [] $ Q.SPECL [‘p’,‘0w’] aligned_add_sub_cor >>
  simp[aligned_0] >>
  gvs[byte_aligned_def]
QED

Theorem compile_Assign_Global:
  ^(get_goal "compile _ (Assign Global _ _)")
Proof
  rw[evaluate_def,compile_def,AllCaseEqs(),
     is_valid_value_def,good_res_def
    ] >>
  drule_all_then strip_assume_tac compile_exp_correct >>
  gvs[state_rel_def] >>
  res_tac >>
  fs[evaluate_def,eval_def,wordLangTheory.word_op_def] >>
  drule $ cj 1 mem_load_mem_store >>
  disch_then drule >>
  strip_tac >>
  simp[] >>
  conj_tac
  >- (rw[FLOOKUP_UPDATE]
      >- (res_tac >> fs[] >>
          qpat_x_assum ‘shape_of _ = shape_of _’ $ assume_tac o GSYM >>
          simp[] >>
          irule $ cj 1 mem_stores_mem_load_back >>
          first_assum $ irule_at $ Pos last >>
          gvs[] >>
          drule mem_stores_bounded_length >>
          disch_then drule >>
          impl_tac
          >- (gvs[state_rel_def] >>
              irule byte_aligned_add >>
              simp[] >>
              rw[byte_aligned_def] >>
              irule $ SIMP_RULE (srw_ss()) [] $ Q.SPECL [‘p’,‘0w’] aligned_add_sub_cor >>
              simp[aligned_0] >>
              gvs[byte_aligned_def]) >>
          simp[] >>
          strip_tac >>
          irule LESS_EQ_LESS_TRANS >>
          first_x_assum $ irule_at (Pos last) >>
          simp[w2n_lt]) >>
      res_tac >> fs[] >>
      drule $ cj 1 mem_stores_load_disjoint >>
      simp[length_flatten_eq_size_of_shape] >>
      strip_tac >>
      irule EQ_TRANS >>
      first_x_assum $ irule_at $ Pos last >>
      first_x_assum irule >>
      gvs[disjoint_globals_def,IS_SOME_EXISTS,PULL_EXISTS] >>
      res_tac >> fs[]) >>
  conj_tac
  >- (rw[] >>
      gvs[DISJOINT_ALT] >>
      drule mem_stores_lookup >>
      simp[length_flatten_eq_size_of_shape]) >>
  gvs[disjoint_globals_def,FLOOKUP_UPDATE,IS_SOME_EXISTS,PULL_EXISTS] >>
  rw[] >>
  res_tac >>
  fs[]
QED

Theorem state_rel_res_var[local]:
  state_rel l ctxt s t ∧ state_rel T ctxt s' t' ⇒
  state_rel l ctxt
            (s with locals := res_var s.locals (v,FLOOKUP s'.locals v'))
            (t with locals := res_var t.locals (v,FLOOKUP t'.locals v'))
Proof
  rw[state_rel_def]
QED

Theorem compile_Dec:
  ^(get_goal "compile _ (Dec _ _ _)")
Proof
  rpt strip_tac >>
  gvs[evaluate_def,compile_def,AllCaseEqs(),UNCURRY_eq_pair] >>
  drule_all_then strip_assume_tac compile_exp_correct >>
  simp[PULL_EXISTS] >>
  irule_at Any state_rel_res_var >>
  simp[] >>
  simp[Once CONJ_SYM] >>
  first_x_assum irule >>
  gvs[state_rel_def]
QED

Theorem mem_load_disjoint:
  (∀val addr' memory v addr addrs.
     (addr':'a word) ∉ addresses addr (size_of_shape(shape_of val)) ∧
     mem_load (shape_of val) addr addrs memory = SOME val ⇒
     mem_load (shape_of val) addr addrs memory⦇addr' ↦ v⦈ = SOME val) ∧
  (∀vals addr' memory v addr addrs.
     (addr':'a word) ∉ addresses addr (SUM(MAP (size_of_shape o shape_of) vals)) ∧
     mem_loads (MAP shape_of vals) addr addrs memory = SOME vals ⇒
     mem_loads (MAP shape_of vals) addr addrs memory⦇addr' ↦ v⦈ = SOME vals)
Proof
  Induct
  >- (Cases >>
      rw[mem_load_def,AllCaseEqs(),shape_of_def,size_of_shape_def,
         CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV addresses_def,
         APPLY_UPDATE_THM
        ])
  >- (rw[mem_load_def,AllCaseEqs(),shape_of_def,size_of_shape_def,
         CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV addresses_def,
         APPLY_UPDATE_THM,MAP_MAP_o,o_DEF,ETA_AX
        ])
  >- (rw[mem_load_def,shape_of_def]) >>
  rw[cj 3 mem_load_def,AllCaseEqs()]
  >- (first_x_assum irule >>
      gvs[addresses_thm] >>
      rw[] >>
      first_x_assum $ resolve_then Any mp_tac EQ_REFL >>
      simp[]) >>
  first_x_assum irule >>
  simp[] >>
  gvs[addresses_thm] >>
  rw[] >>
  first_x_assum $ qspec_then ‘i + size_of_shape (shape_of val)’ mp_tac >>
  impl_tac
  >- simp[GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB] >>
  simp[]
QED

Theorem state_rel_memory_update:
  state_rel T ctxt s t ∧ addr ∈ s.memaddrs ⇒
  state_rel T ctxt (s with memory := s.memory⦇addr ↦ h⦈) (t with memory := t.memory⦇addr ↦ h⦈)
Proof
  rw[] >>
  gvs[state_rel_def] >>
  reverse conj_tac >- rw[APPLY_UPDATE_THM] >>
  rw[] >>
  res_tac >>
  first_assum $ irule_at $ Pos hd >>
  simp[] >>
  irule $ cj 1 mem_load_disjoint >>
  simp[] >>
  gvs[DISJOINT_ALT]
QED

Theorem compile_Store:
  ^(get_goal "compile _ (Store _ _)")
Proof
  rw[evaluate_def,compile_def,AllCaseEqs(),UNCURRY_eq_pair,SF DNF_ss] >>
  imp_res_tac compile_exp_correct >>
  simp[] >>
  gvs[good_res_def] >>
  rpt $ qpat_x_assum ‘eval _ _ = _’ kall_tac >>
  rename1 ‘mem_stores _ v’ >>
  rpt $ pop_assum mp_tac >>
  MAP_EVERY qid_spec_tac [‘v’,‘s’,‘t’,‘addr’,‘m’] >>
  Induct_on ‘v’
  >- (rw[mem_stores_def] >>
      ‘s with memory := s.memory = s’ by simp[state_component_equality] >>
      ‘t with memory := t.memory = t’ by simp[state_component_equality] >>
      simp[]) >>
  rw[mem_stores_def,AllCaseEqs(),mem_store_def] >>
  ‘addr ∈ t.memaddrs’ by(gvs[state_rel_def,SUBSET_DEF]) >>
  simp[] >>
  drule_all state_rel_memory_update >>
  strip_tac >>
  first_x_assum (fn thm => first_x_assum $ resolve_then Any mp_tac thm) >>
  simp[]
QED

Theorem compile_StoreByte:
  ^(get_goal "compile _ (StoreByte _ _)")
Proof
  rw[evaluate_def,compile_def,AllCaseEqs(),UNCURRY_eq_pair,SF DNF_ss, mem_store_byte_def,
     good_res_def] >>
  imp_res_tac compile_exp_correct >>
  ‘s.be = t.be’ by gvs[state_rel_def] >>
  simp[] >>
  irule_at (Pos last) state_rel_memory_update >>
  simp[] >>
  gvs[state_rel_def,SUBSET_DEF]
QED

Triviality v_neq_v':
  v ≠ v ^ «'»
Proof
  Cases_on ‘v’ >>
  rw[mlstringTheory.strcat_def,mlstringTheory.concat_def]
QED

Theorem compile_ShMemLoad:
  ^(get_goal "compile _ (ShMemLoad _ _ _ _)")
Proof
  strip_tac >> Cases
  >~ [‘Local’]
  >- (rw[evaluate_def,AllCaseEqs(),compile_def,PULL_EXISTS,lookup_kvar_def] >>
      drule_all_then strip_assume_tac compile_exp_correct >>
      gvs[state_rel_def,sh_mem_load_def,AllCaseEqs(),PULL_EXISTS,set_kvar_def,
          SUBSET_DEF,set_var_def,empty_locals_def])
  >~ [‘Global’]
  >- (rw[evaluate_def,AllCaseEqs(),compile_def,PULL_EXISTS,lookup_kvar_def] >>
      drule_all_then strip_assume_tac compile_exp_correct >>
      rename1 ‘FLOOKUP _ _ = SOME(Val vv)’ >>
      ‘∃addr. FLOOKUP ctxt.globals v = SOME(shape_of(Val vv), addr) ∧
              mem_load (shape_of(Val vv)) (t.top_addr - addr) t.memaddrs t.memory = SOME(Val vv) ∧
              DISJOINT s.memaddrs (addresses (t.top_addr - addr) (size_of_shape(shape_of(Val vv)))) ∧
              byte_aligned addr’
        by gvs[state_rel_def] >>
      ‘s.locals = t.locals’ by gvs[state_rel_def] >>
      ‘s.sh_memaddrs = t.sh_memaddrs’ by gvs[state_rel_def] >>
      ‘s.ffi = t.ffi’ by gvs[state_rel_def] >>
      gvs[] >>
      simp[oneline shape_of_def] >>
      PURE_CASE_TAC >>
      gvs[] >>
      gvs[evaluate_def,eval_def,FLOOKUP_UPDATE,v_neq_v',
          lookup_kvar_def,sh_mem_load_def,AllCaseEqs(),
          wordLangTheory.word_op_def,set_kvar_def,set_var_def,set_global_def,
          mem_stores_def,mem_store_def,mem_load_def,flatten_def]
      >- (gvs[state_rel_def,good_res_def] >>
          conj_tac
          >- (rw[fmap_eq_flookup,FLOOKUP_pan_res_var_thm,FLOOKUP_UPDATE] >> rw[]) >>
          conj_tac
          >- (rw[FLOOKUP_UPDATE]
              >- (res_tac >> fs[shape_of_def,mem_load_def]) >>
              res_tac >>
              simp[] >>
              irule $ cj 1 mem_load_disjoint >>
              simp[] >>
              gvs[disjoint_globals_def] >>
              res_tac >>
              fs[DISJOINT_ALT,size_of_shape_def,IS_SOME_EXISTS,PULL_EXISTS] >>
              gvs[size_of_shape_def,
                  CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV addresses_def]) >>
          conj_tac
          >- (rw[] >>
              gvs[SUBSET_DEF] >>
              res_tac >>
              gvs[size_of_shape_def,shape_of_def] >>
              qhdtm_x_assum ‘DISJOINT’ mp_tac >>
              rw[Once $ oneline addresses_def, addresses_def] >>
              rw[APPLY_UPDATE_THM] >>
              gvs[])
          >- (gvs[disjoint_globals_def,FLOOKUP_UPDATE,IS_SOME_EXISTS, SF DNF_ss] >>
              rw[] >>
              res_tac >>
              fs[])
         )
      >- (gvs[state_rel_def,empty_locals_def,good_res_def] >>
          rw[fmap_eq_flookup,FLOOKUP_pan_res_var_thm,FLOOKUP_UPDATE])
      >- (gvs[state_rel_def,good_res_def] >>
          conj_tac
          >- (rw[fmap_eq_flookup,FLOOKUP_pan_res_var_thm,FLOOKUP_UPDATE] >> rw[]) >>
          conj_tac
          >- (rw[FLOOKUP_UPDATE]
              >- (res_tac >> fs[shape_of_def,mem_load_def]) >>
              res_tac >>
              simp[] >>
              irule $ cj 1 mem_load_disjoint >>
              simp[] >>
              gvs[disjoint_globals_def] >>
              res_tac >>
              fs[DISJOINT_ALT,size_of_shape_def,IS_SOME_EXISTS,PULL_EXISTS] >>
              gvs[size_of_shape_def,
                  CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV addresses_def]) >>
          conj_tac
          >- (rw[] >>
              gvs[SUBSET_DEF] >>
              res_tac >>
              gvs[size_of_shape_def,shape_of_def] >>
              qhdtm_x_assum ‘DISJOINT’ mp_tac >>
              rw[Once $ oneline addresses_def, addresses_def] >>
              rw[APPLY_UPDATE_THM] >>
              gvs[])
          >- (gvs[disjoint_globals_def,FLOOKUP_UPDATE,IS_SOME_EXISTS, SF DNF_ss] >>
              rw[] >>
              res_tac >>
              fs[]))
      >- (gvs[state_rel_def,empty_locals_def,good_res_def] >>
          rw[fmap_eq_flookup,FLOOKUP_pan_res_var_thm,FLOOKUP_UPDATE]))
QED

Theorem compile_ShMemStore:
  ^(get_goal "compile _ (ShMemStore _ _ _)")
Proof
  Cases >> rw[] >>
  gvs[AllCaseEqs(),panSemTheory.evaluate_def,compile_def,
      oneline nb_op_def,
      panSemTheory.nb_op_def,panSemTheory.sh_mem_load_def,
      panSemTheory.sh_mem_store_def,panLangTheory.size_of_shape_def,
      asmTheory.is_load_def,panLangTheory.store_op_def,
      localised_prog_def,SF DNF_ss, good_res_def
      ] >>
  imp_res_tac compile_exp_correct >>
  gvs[state_rel_def]
QED

Theorem compile_Return:
  ^(get_goal "compile _ (Return _)")
Proof
  rw[evaluate_def,compile_def,AllCaseEqs()] >>
  imp_res_tac compile_exp_correct >>
  gvs[state_rel_def,empty_locals_def]
QED

Theorem compile_Raise:
  ^(get_goal "compile _ (Raise _ _)")
Proof
  rw[evaluate_def,compile_def,AllCaseEqs()] >>
  imp_res_tac compile_exp_correct >>
  gvs[state_rel_def,empty_locals_def]
QED

Theorem compile_Seq:
  ^(get_goal "compile _ (Seq _ _)")
Proof
  rw[evaluate_def,compile_def] >>
  gvs[UNCURRY_eq_pair,AllCaseEqs()] >>
  first_x_assum drule >>
  strip_tac >>
  gvs[good_res_def]
QED

Theorem compile_If:
  ^(get_goal "compile _ (If _ _ _)")
Proof
  rw[evaluate_def,compile_def] >>
  gvs[UNCURRY_eq_pair,AllCaseEqs()] >>
  imp_res_tac compile_exp_correct >>
  first_x_assum drule >>
  strip_tac >>
  gvs[good_res_def] >>
  rw[] >>
  fs[]
QED

Theorem state_rel_dec_clock[local]:
  state_rel ls ctxt s t ⇒ state_rel ls ctxt (dec_clock s) (dec_clock t)
Proof
  rw[state_rel_def,dec_clock_def]
QED

Theorem compile_While:
  ^(get_goal "compile _ (While _ _)")
Proof
  rpt strip_tac >>
  qpat_x_assum ‘evaluate (While e c,s) = (res,s1)’ mp_tac >>
  rw [Once evaluate_def] >>
  gvs[AllCaseEqs(),compile_def] >>
  imp_res_tac compile_exp_correct >>
  simp[] >>
  gvs[good_res_def]
  >- gvs[state_rel_def,empty_locals_def, Once evaluate_def]
  >- gvs[state_rel_def,empty_locals_def, Once evaluate_def] >>
  ‘s.clock = t.clock’ by gvs[state_rel_def] >>
  PURE_ONCE_REWRITE_TAC[evaluate_def] >>
  simp[] >>
  imp_res_tac state_rel_dec_clock >>
  gvs[UNCURRY_eq_pair] >>
  first_x_assum $ drule_at $ Pat ‘state_rel _ _ (dec_clock _) _’ >>
  impl_tac >- spose_not_then $ gvs o single >>
  strip_tac >> gvs[] >>
  gvs[AllCaseEqs(),good_res_def]
QED

Theorem OPT_MMAP_eval_correct:
  state_rel T ctxt s t ∧
  OPT_MMAP (eval s) argexps = SOME args ⇒
  OPT_MMAP (eval t) (MAP (compile_exp ctxt) argexps) = SOME args
Proof
  rw[OPT_MMAP_MAP_o] >>
  irule EQ_TRANS >>
  first_assum $ irule_at $ Pos last >>
  irule OPT_MMAP_CONG >>
  rw[] >>
  imp_res_tac pan_commonPropsTheory.opt_mmap_mem_func >>
  imp_res_tac compile_exp_correct >>
  gvs[]
QED

Theorem state_rel_lookup_code:
  state_rel ls ctxt s t ∧
  lookup_code s.code fname args = SOME (prog,newlocals) ⇒
  lookup_code t.code fname args = SOME (compile ctxt prog,newlocals)
Proof
  rw[] >>
  gvs[state_rel_def,lookup_code_def,AllCaseEqs()] >>
  res_tac >> fs[]
QED

(* Simplifier doesn't trigger if flag is left symbolic *)
Theorem state_rel_empty_locals:
  (state_rel T ctxt s t ⇒ state_rel ls' ctxt (empty_locals s) (empty_locals t)) ∧
  (state_rel F ctxt s t ⇒ state_rel ls' ctxt (empty_locals s) (empty_locals t))
Proof
  rw[] >>
  gvs[state_rel_def,empty_locals_def]
QED

Theorem state_rel_change_locals:
  (state_rel T ctxt s t ⇒ state_rel ls' ctxt (s with locals := x) (t with locals := x)) ∧
  (state_rel F ctxt s t ⇒ state_rel ls' ctxt (s with locals := x) (t with locals := x))
Proof
  rw[] >>
  gvs[state_rel_def,empty_locals_def]
QED

Theorem state_rel_set_var:
  (state_rel T ctxt s t ⇒ state_rel ls' ctxt (set_var rt retv s) (set_var rt retv t))
Proof
  rw[] >>
  gvs[state_rel_def,empty_locals_def,set_var_def]
QED

Theorem compile_Call:
  ^(get_goal "compile _ (Call _ _ _)")
Proof
  rpt strip_tac >>
  ‘s.clock = t.clock ∧ s.locals = t.locals’ by gvs[state_rel_def] >>
  gvs[evaluate_def,compile_def,SF DNF_ss, good_res_def] >>
  qpat_x_assum ‘_ = (_,_)’ mp_tac >>
  PURE_TOP_CASE_TAC >> gvs[] >>
  PURE_TOP_CASE_TAC >> gvs[] >>
  imp_res_tac OPT_MMAP_eval_correct >>
  PURE_TOP_CASE_TAC >> gvs[] >>
  drule_all_then strip_assume_tac state_rel_lookup_code >>
  gvs[] >>
  IF_CASES_TAC
  >- (rw[] >> gvs[state_rel_def,good_res_def,empty_locals_def]) >>
  gvs[] >>
  PURE_TOP_CASE_TAC >> gvs[] >>
  rename1 ‘option_CASE opt’ >>
  Cases_on ‘opt = SOME Error’ >- rw[] >>
  first_x_assum $ drule_at $ Pos last >>
  disch_then $ qspecl_then [‘ctxt’,‘dec_clock t with locals := r’] mp_tac >>
  impl_keep_tac
  >- gvs[state_rel_def,dec_clock_def] >>
  strip_tac >>
  rw[] >>
  gvs[AllCaseEqs(),good_res_def,state_rel_empty_locals,PULL_EXISTS,
      state_rel_change_locals,state_rel_set_var]
  >- metis_tac[option_nchotomy,PAIR]
  >- metis_tac[option_nchotomy,PAIR] >>
  first_x_assum $ qspecl_then [‘ctxt’,‘set_var evar exn (t' with locals := t.locals)’] mp_tac >>
  impl_keep_tac
  >- gvs[state_rel_change_locals,state_rel_set_var] >>
  strip_tac >>
  simp[] >>
  gvs[state_rel_def]
QED

Theorem compile_DecCall:
  ^(get_goal "compile _ (DecCall _ _ _ _ _)")
Proof
  rw[evaluate_def,compile_def] >>
  gvs[CaseEq "option"] >>
  gvs[CaseEq "prod"] >>
  drule_all OPT_MMAP_eval_correct >>
  drule_all state_rel_lookup_code >>
  rpt strip_tac >> gvs[] >>
  ‘s.clock = t.clock’ by fs[state_rel_def] >>
  gvs[CaseEq "bool", good_res_def,state_rel_empty_locals] >>
  drule state_rel_dec_clock >>
  strip_tac >>
  dxrule $ cj 1 state_rel_change_locals >>
  disch_then $ qspecl_then [‘newlocals’,‘T’] strip_assume_tac >>
  first_x_assum $ drule_at $ Pos hd >>
  strip_tac >>
  gvs[AllCaseEqs(), SF DNF_ss,UNCURRY_eq_pair,good_res_def,state_rel_empty_locals] >>
  irule_at Any state_rel_res_var >>
  simp[Once CONJ_SYM] >>
  first_x_assum irule >>
  irule state_rel_set_var >>
  gvs[state_rel_def]
QED

Theorem state_rel_read_bytearray:
  ∀ls ctxt s t bytes sz ad.
    state_rel ls ctxt s t ∧
    read_bytearray sz ad (mem_load_byte s.memory s.memaddrs s.be) = SOME bytes ⇒
    read_bytearray sz ad (mem_load_byte t.memory t.memaddrs t.be) = SOME bytes
Proof
  Induct_on ‘ad’ >>
  rw[read_bytearray_def,AllCaseEqs(),mem_load_byte_def,PULL_EXISTS] >>
  first_x_assum $ irule_at $ Any >>
  first_assum $ irule_at $ Pos hd >>
  first_assum $ irule_at $ Any >>
  gvs[state_rel_def,SUBSET_DEF]
QED

Theorem state_rel_mem_store_byte:
  state_rel ls ctxt s t ∧
  mem_store_byte s.memory s.memaddrs s.be addr b = SOME m' ⇒
  ∃m''. mem_store_byte t.memory t.memaddrs t.be addr b = SOME m'' ∧
       state_rel ls ctxt (s with memory := m') (t with memory := m'')
Proof
  rw[mem_store_byte_def,AllCaseEqs(),PULL_EXISTS,state_rel_def,SUBSET_DEF] >>
  res_tac >>
  gvs[] >>
  rw[APPLY_UPDATE_THM] >>
  res_tac >>
  fs[] >>
  drule_at_then Any irule $ cj 1 mem_load_disjoint >>
  gvs[DISJOINT_ALT]
QED

Theorem state_rel_change_ffi:
  (state_rel ls' ctxt s t ⇒ state_rel ls' ctxt (s with ffi := x) (t with ffi := x))
Proof
  rw[] >>
  gvs[state_rel_def]
QED

Theorem state_rel_write_bytearray:
  ∀a ls ctxt s t sz nbw bs.
    state_rel ls ctxt s t ∧
    read_bytearray sz (LENGTH nbw) (mem_load_byte s.memory s.memaddrs s.be) = SOME bs
    ⇒
    state_rel ls ctxt (s with memory := write_bytearray sz nbw s.memory s.memaddrs s.be)
              (t with memory := write_bytearray sz nbw t.memory t.memaddrs t.be)
Proof
  Induct_on ‘nbw’ >>
  rw[write_bytearray_def,read_bytearray_def,mem_load_byte_def,AllCaseEqs()]
  >- gvs[state_rel_def] >>
  TOP_CASE_TAC
  >- gvs[mem_store_byte_def,AllCaseEqs()] >>
  first_x_assum drule >>
  disch_then $ qspec_then ‘sz + 1w’ mp_tac >>
  disch_then drule >>
  strip_tac >>
  drule state_rel_mem_store_byte >>
  simp[] >>
  disch_then drule >>
  strip_tac >>
  simp[]
QED

Theorem compile_ExtCall:
  ^(get_goal "compile _ (ExtCall _ _ _ _ _)")
Proof
  rw[compile_def,evaluate_def,AllCaseEqs(), PULL_EXISTS] >>
  imp_res_tac compile_exp_correct >>
  simp[] >>
  imp_res_tac state_rel_read_bytearray >>
  simp[] >>
  ‘s.ffi = t.ffi’ by fs[state_rel_def] >>
  gvs[state_rel_empty_locals] >>
  imp_res_tac read_bytearray_LENGTH >>
  imp_res_tac call_FFI_LENGTH >>
  ntac 3 $ pop_assum $ mp_tac o GSYM >>
  ntac 3 strip_tac >>
  gvs[] >>
  drule_then (qspec_then ‘new_ffi’ strip_assume_tac) state_rel_change_ffi >>
  drule state_rel_write_bytearray >>
  simp[] >>
  disch_then drule >>
  simp[good_res_def]
QED

Theorem compile_correct:
   ^(compile_tm ())
Proof
  match_mp_tac $ the_ind_thm() >>
  EVERY (map strip_assume_tac
         [compile_Skip_Break_Continue_Annot_Tick,
          compile_Dec, compile_ShMemLoad, compile_ShMemStore,
          compile_Assign_Local, compile_Store, compile_StoreByte, compile_Seq,
          compile_Assign_Global,
          compile_If, compile_While, compile_Call, compile_ExtCall,
          compile_Raise, compile_Return, compile_DecCall]) >>
  asm_rewrite_tac [] >> rw [] >> rpt (pop_assum kall_tac)
QED

Definition fperm_code_def:
  fperm_code f g code =
  FUN_FMAP ((I ## fperm f g) o THE o FLOOKUP code o fperm_name f g) (PREIMAGE (fperm_name f g) (FDOM code))
End

Theorem fperm_name_cancel[simp]:
  fperm_name f g (fperm_name f g name) = name
Proof
  rw[fperm_name_def] >>
  rpt(pop_assum mp_tac) >> rw[]
QED

Theorem fperm_name_cong[simp]:
  fperm_name f g x = fperm_name f g y ⇔ x = y
Proof
  rw[fperm_name_def] >> rw[]
QED

Theorem FLOOKUP_fperm_code:
  FLOOKUP (fperm_code f g code) (fperm_name f g name) =
  OPTION_MAP (I ## fperm f g) $ FLOOKUP code name
Proof
  rw[fperm_code_def] >>
  simp[FLOOKUP_FUN_FMAP,FINITE_PREIMAGE,IMAGE_FINITE,FDOM_FINITE] >>
  rw[] >>
  gvs[GSYM flookup_thm] >>
  gvs[FDOM_FLOOKUP]
QED

Theorem lookup_code_fperm_code:
  lookup_code (fperm_code f g code) (fperm_name f g name) args =
  OPTION_MAP (fperm f g ## I) (lookup_code code name args)
Proof
  rw[lookup_code_def,FLOOKUP_fperm_code] >>
  Cases_on ‘FLOOKUP code name’ >> gvs[AllCaseEqs(),PULL_EXISTS] >>
  metis_tac[FST,SND,PAIR]
QED

(* TODO: move *)
Theorem eval_upd_code_eta =
  CONV_RULE (QUANT_CONV SWAP_FORALL_CONV) eval_upd_code_eq
    |> REWRITE_RULE[GSYM FUN_EQ_THM,ETA_THM]

Theorem evaluate_fperm:
  ∀f g p s res s'.
    evaluate(p,s) = (res,s') ⇒
    evaluate(fperm f g p,s with code := fperm_code f g s.code) =
    (res,s' with code := fperm_code f g s'.code)
Proof
  ntac 2 strip_tac >>
  recInduct evaluate_ind >>
  rpt conj_tac
  >~ [‘While’]
  >- (rpt gen_tac >> strip_tac >>
      simp[fperm_def] >>
      PURE_ONCE_REWRITE_TAC[evaluate_def] >>
      simp[eval_upd_code_eq] >>
      ntac 3 (PURE_TOP_CASE_TAC >> simp[]) >>
      IF_CASES_TAC >> simp[] >>
      IF_CASES_TAC >> simp[empty_locals_def] >>
      gvs[] >>
      pairarg_tac >>
      simp[] >>
      first_x_assum drule >>
      rpt strip_tac >>
      gvs[dec_clock_def] >>
      gvs[AllCaseEqs(),fperm_def])
  >~ [‘Call’]
  >- (rpt gen_tac >> strip_tac >>
      simp[fperm_def] >>
      PURE_ONCE_REWRITE_TAC[evaluate_def] >>
      simp[eval_upd_code_eq,eval_upd_code_eta] >>
      rpt gen_tac >>
      PURE_TOP_CASE_TAC >> simp[] >>
      simp[lookup_code_fperm_code] >>
      PURE_TOP_CASE_TAC >> simp[] >>
      PURE_TOP_CASE_TAC >> simp[] >>
      PURE_TOP_CASE_TAC
      >- (rw[] >> gvs[empty_locals_def]) >>
      simp[] >>
      gvs[] >>
      PURE_TOP_CASE_TAC >>
      gvs[dec_clock_def] >>
      PURE_TOP_CASE_TAC >> simp[] >>
      PURE_TOP_CASE_TAC >>
      rw[] >> gvs[empty_locals_def] >>
      PURE_CASE_TAC >> gvs[] >>
      PURE_CASE_TAC >> gvs[] >>
      PURE_CASE_TAC >> gvs[] >>
      PURE_CASE_TAC >> gvs[] >>
      gvs[set_var_def] >>
      PURE_CASE_TAC >> gvs[] >>
      PURE_TOP_CASE_TAC >> gvs[] >>
      PURE_TOP_CASE_TAC >> gvs[] >>
      PURE_TOP_CASE_TAC >> gvs[set_var_def] >>
      IF_CASES_TAC >> gvs[set_var_def])
  >~ [‘DecCall’]
  >- (rpt gen_tac >> strip_tac >>
      simp[fperm_def] >>
      PURE_ONCE_REWRITE_TAC[evaluate_def] >>
      simp[eval_upd_code_eq,eval_upd_code_eta] >>
      rpt gen_tac >>
      PURE_TOP_CASE_TAC >> simp[] >>
      simp[lookup_code_fperm_code] >>
      PURE_TOP_CASE_TAC >> simp[] >>
      PURE_TOP_CASE_TAC >> simp[] >>
      PURE_TOP_CASE_TAC
      >- (rw[] >> gvs[empty_locals_def]) >>
      simp[] >>
      gvs[] >>
      PURE_TOP_CASE_TAC >>
      gvs[dec_clock_def] >>
      PURE_TOP_CASE_TAC >> simp[] >>
      PURE_TOP_CASE_TAC >>
      rw[] >> gvs[empty_locals_def,UNCURRY_eq_pair] >>
      gvs[set_var_def]) >>
  rw[evaluate_def,fperm_def,AllCaseEqs(),UNCURRY_eq_pair,
     eval_upd_code_eq] >>
  res_tac >>
  rw[] >>
  gvs[lookup_kvar_def,AllCaseEqs(),sh_mem_load_def,set_kvar_def,
      set_var_def,empty_locals_def,set_global_def,sh_mem_store_def,dec_clock_def]
QED

Theorem resort_decls_evaluate:
  ∀s decs. evaluate_decls s (resort_decls decs) = evaluate_decls s decs
Proof
  Induct_on ‘decs’ >> gvs[resort_decls_def] >>
  Cases >>
  gvs[is_function_def,evaluate_decls_def] >>
  strip_tac >>
  irule EQ_TRANS >>
  first_x_assum $ irule_at $ Pos last >>
  qmatch_goalsub_abbrev_tac ‘a1 ++ _’ >>
  ‘EVERY ($¬ ∘ is_function) a1’
    by(gvs[Abbr ‘a1’] >> rw[EVERY_MEM,MEM_FILTER]) >>
  rename1 ‘_::a2’ >>
  last_x_assum kall_tac >>
  qid_spec_tac ‘a2’ >>
  qid_spec_tac ‘s’ >>
  Induct_on ‘a1’ using SNOC_INDUCT
  >- simp[evaluate_decls_def] >>
  Cases >>
  rw[SNOC_APPEND,is_function_def] >>
  SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND] >>
  gvs[] >>
  irule EQ_TRANS >>
  first_x_assum $ irule_at $ Pos last >>
  simp[evaluate_decls_append,evaluate_decl_commute]
QED

Theorem compile_decs_functions_thm:
  ∀ctxt fdecs decls funs ctxt'.
    compile_decs ctxt fdecs = (decls,funs,ctxt') ∧
    EVERY (is_function) fdecs ⇒
    (decls = [] ∧ ctxt' = ctxt ∧
     funs =
     MAP (λx. case x of Function f xp args body =>
                          Function f xp args (compile ctxt' body) | _ => ARB)
         fdecs)
Proof
  ho_match_mp_tac compile_decs_ind >> rpt conj_tac
  >- rw[compile_decs_def] >>
  PURE_REWRITE_TAC[compile_decs_def] >>
  rpt strip_tac >>
  FULL_SIMP_TAC std_ss [LET_THM,UNCURRY_eq_pair] >>
  rveq >>
  fs[is_function_def]
QED

Theorem compile_decs_decls_thm:
  ∀ctxt fdecs decls funs ctxt'.
    compile_decs ctxt fdecs = (decls,funs,ctxt') ∧
    EVERY ($¬ o is_function) fdecs ⇒
    funs = []
Proof
  ho_match_mp_tac compile_decs_ind >> rpt conj_tac >>
  rw[compile_decs_def,is_function_def,UNCURRY_eq_pair] >> gvs[]
QED

Theorem compile_decs_EVERY_is_function:
  ∀ctxt decs decls funs ctxt'.
    compile_decs ctxt decs = (decls,funs,ctxt') ⇒
    EVERY is_function funs
Proof
  ho_match_mp_tac compile_decs_ind >> rpt conj_tac >>
  rw[compile_decs_def,is_function_def,UNCURRY_eq_pair] >> gvs[is_function_def]
QED

Theorem compile_decls_append:
  ∀decs' ctxt decs .
    compile_decs ctxt (decs ++ decs') =
    let (decls,funs,ctxt') = compile_decs ctxt decs;
        (decls',funs',ctxt'') = compile_decs ctxt' decs'
    in
      (decls++decls',funs++funs',ctxt'')
Proof
  strip_tac >>
  recInduct compile_decs_ind >>
  rw[UNCURRY_eq_pair,compile_decs_def,PULL_EXISTS] >>
  metis_tac[FST,SND,PAIR]
QED

Theorem fperm_decs_append:
  ∀f g xs ys.
    fperm_decs f g (xs ++ ys) =
    fperm_decs f g xs ++ fperm_decs f g ys
Proof
  recInduct fperm_decs_ind >>
  rw[fperm_decs_def]
QED

Theorem fperm_decs_decls:
  ∀f g xs ys.
    EVERY ($¬ o is_function) xs ⇒
    fperm_decs f g xs = xs
Proof
  recInduct fperm_decs_ind >>
  rw[fperm_decs_def,is_function_def]
QED

Theorem fperm_decs_FILTER_is_function:
  ∀f g decs.
    fperm_decs f g (FILTER is_function decs) =
    FILTER is_function (fperm_decs f g decs)
Proof
  recInduct fperm_decs_ind >>
  rw[fperm_decs_def,is_function_def]
QED

Theorem mem_stores_addrs_IS_SOME:
  ∀addr ws memaddrs memory.
    addresses addr (LENGTH ws) ⊆ memaddrs ⇒
    ∃m. mem_stores addr ws memaddrs memory = SOME m
Proof
  Induct_on ‘ws’ >>
  rw[addresses_def,mem_stores_def,mem_store_def]
QED

Theorem byte_aligned_bytes_in_word_mul:
  good_dimindex(:'a) ⇒ byte_aligned (bytes_in_word:'a word * x)
Proof
  Cases_on ‘x’ >>
  rw[byte_aligned_def,good_dimindex_def,bytes_in_word_def,word_mul_n2w] >>
  gvs[] >>
  irule MOD_0_aligned >>
  simp[]
QED

Theorem DISJOINT_addresses_lemma:
  (addr1:'a word)+bytes_in_word*n2w offs = addr2 ∧ good_dimindex(:'a) ∧
  w2n(bytes_in_word:'a word)*(offs + offs') < dimword(:'a) ⇒
  DISJOINT (addresses addr1 offs) (addresses addr2 offs')
Proof
  rw[addresses_thm,DISJOINT_ALT] >>
  FULL_SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC, addressTheory.WORD_EQ_ADD_CANCEL] >>
  spose_not_then strip_assume_tac >>
  gvs[good_dimindex_def,bytes_in_word_def,word_add_n2w,word_mul_n2w,LEFT_ADD_DISTRIB] >>
  gvs[dimword_def]
QED

Theorem evaluate_decls_init_globals_lemma:
  ∀s decls s' decls' funs ctxt' ctxt t free_addrs.
    evaluate_decls ^s decls = SOME s' ∧
    EVERY ($¬ o is_function) decls ∧
    compile_decs ctxt decls = (decls',funs,ctxt') ∧
    state_rel F ctxt s t ∧
    free_addrs = addresses (t.top_addr - bytes_in_word*n2w(SUM(MAP size_of_shape(dec_shapes decls))) - ctxt.globals_size) (SUM(MAP size_of_shape(dec_shapes decls))) ∧
    DISJOINT s.memaddrs free_addrs ∧
    free_addrs ⊆ t.memaddrs ∧
    byte_aligned ctxt.globals_size ∧
    s.code = FEMPTY ∧
    (∀v sh addr. IS_SOME(FLOOKUP s.globals v) ∧ FLOOKUP ctxt.globals v = SOME(sh, addr) ⇒ DISJOINT (addresses (t.top_addr-addr) (size_of_shape sh)) free_addrs) ∧
    w2n(bytes_in_word:'a word) * (SUM (MAP size_of_shape (dec_shapes decls))) < dimword (:α)
    ⇒
    ∃t'. panSem$evaluate (nested_seq decls',t) = (NONE,t') ∧
         state_rel F ctxt' s' t' ∧
         byte_aligned ctxt'.globals_size
Proof
  ho_match_mp_tac evaluate_decls_ind >>
  rw[evaluate_decls_def,compile_decs_def,AllCaseEqs(),UNCURRY_eq_pair,
     nested_seq_def,evaluate_def] >>
  gvs[nested_seq_def,evaluate_def,UNCURRY_eq_pair,
      eval_def,wordLangTheory.word_op_def,is_function_def,dec_shapes_def] >>
  drule $ cj 2 state_rel_empty_locals >>
  disch_then $ qspec_then ‘T’ mp_tac >>
  strip_tac >>
  gvs[empty_locals_def] >>
  gvs[] >>
  drule_all compile_exp_correct >>
  strip_tac >>
  simp[PULL_EXISTS] >>
  drule eval_empty_locals_IMP >>
  strip_tac >>
  simp[] >>
  qmatch_goalsub_abbrev_tac ‘mem_stores a1 a2 a3 a4’ >>
  qspecl_then [‘a1’,‘a2’,‘a3’,‘a4’] mp_tac mem_stores_addrs_IS_SOME >>
  unabbrev_all_tac >>
  impl_tac >-
   (irule SUBSET_TRANS >>
    first_x_assum $ irule_at Any >>
    qpat_x_assum ‘state_rel _ _ _ _’ mp_tac >>
    rpt $ pop_assum kall_tac (* premature?*) >>
    strip_tac >>
    rw[addresses_thm,length_flatten_eq_size_of_shape,SUBSET_DEF] >>
    qexists_tac ‘SUM(MAP size_of_shape (dec_shapes decls)) + i’ >>
    simp[] >>
    SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC, addressTheory.WORD_EQ_ADD_CANCEL] >>
    gvs[bytes_in_word_def,word_mul_n2w,word_add_n2w,good_dimindex_def,dimword_def,state_rel_def,LEFT_ADD_DISTRIB,WORD_LEFT_ADD_DISTRIB] >>
    gvs[GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]) >>
  strip_tac >>
  simp[] >>
  first_x_assum irule >>
  first_assum $ irule_at $ Pat ‘compile_decs _ _ = _’ >>
  simp[] >>
  conj_tac
  >- (gvs[state_rel_def,IS_SOME_EXISTS,FLOOKUP_UPDATE] >>
      rw[]
      >- (irule $ iffLR DISJOINT_SYM >>
          irule DISJOINT_addresses_lemma >>
          simp[]) >>
      gvs[PULL_EXISTS] >>
      res_tac >>
      irule DISJOINT_SUBSET >>
      first_assum $ irule_at $ Pos hd >>
      simp[SUBSET_DEF,addresses_thm,SF DNF_ss] >>
      rpt strip_tac >>
      qexists_tac ‘i’ >>
      simp[] >>
      SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC, addressTheory.WORD_EQ_ADD_CANCEL] >>
      gvs[bytes_in_word_def,word_mul_n2w,word_add_n2w,good_dimindex_def,dimword_def,state_rel_def,LEFT_ADD_DISTRIB,WORD_LEFT_ADD_DISTRIB] >>
      gvs[GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]) >>
  conj_asm1_tac
  >- (irule byte_aligned_add >>
      simp[] >>
      irule byte_aligned_bytes_in_word_mul >>
      gvs[state_rel_def]) >>
  conj_tac
  >- (drule_then irule DISJOINT_SUBSET >>
      qpat_x_assum ‘state_rel _ _ _ _’ mp_tac >>
      rpt $ pop_assum kall_tac >>
      strip_tac >>
      rw[addresses_thm,length_flatten_eq_size_of_shape,SUBSET_DEF] >>
      qexists_tac ‘i’ >>
      simp[] >>
      SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC, addressTheory.WORD_EQ_ADD_CANCEL] >>
      gvs[bytes_in_word_def,word_mul_n2w,word_add_n2w,good_dimindex_def,dimword_def,state_rel_def,LEFT_ADD_DISTRIB,WORD_LEFT_ADD_DISTRIB] >>
      gvs[GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]) >>
  conj_tac
  >- (irule SUBSET_TRANS >>
      first_x_assum $ irule_at Any >>
      qpat_x_assum ‘state_rel _ _ _ _’ mp_tac >>
      rpt $ pop_assum kall_tac >>
      strip_tac >>
      rw[addresses_thm,length_flatten_eq_size_of_shape,SUBSET_DEF] >>
      qexists_tac ‘i’ >>
      simp[] >>
      SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC, addressTheory.WORD_EQ_ADD_CANCEL] >>
      gvs[bytes_in_word_def,word_mul_n2w,word_add_n2w,good_dimindex_def,dimword_def,state_rel_def,LEFT_ADD_DISTRIB,WORD_LEFT_ADD_DISTRIB] >>
      gvs[GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]) >>
  gvs[state_rel_def] >>
  conj_tac
  >- (rw[FLOOKUP_UPDATE] >> res_tac >> fs[]
      >- (drule $ cj 1 mem_stores_mem_load_back >>
          simp[] >>
          reverse impl_tac >- simp[] >>
          drule mem_stores_bounded_length >>
          disch_then drule >>
          impl_tac
          >- (simp[] >>
              irule byte_aligned_add >>
              simp[] >>
              rw[byte_aligned_def] >>
              irule $ SIMP_RULE (srw_ss()) [] $ Q.SPECL [‘p’,‘0w’] aligned_add_sub_cor >>
              simp[aligned_0] >>
              gvs[byte_aligned_def]) >>
          simp[Once MULT_SYM] >>
          strip_tac >> drule LESS_EQ_LESS_TRANS >>
          disch_then irule >>
          simp[w2n_lt])
      >- (drule_then irule DISJOINT_SUBSET >>
          rw[addresses_thm,length_flatten_eq_size_of_shape,SUBSET_DEF] >>
          qexists_tac ‘i + SUM (MAP size_of_shape (dec_shapes decls))’ >>
          simp[] >>
          SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC, addressTheory.WORD_EQ_ADD_CANCEL] >>
          gvs[bytes_in_word_def,word_mul_n2w,word_add_n2w,good_dimindex_def,dimword_def,state_rel_def,LEFT_ADD_DISTRIB,WORD_LEFT_ADD_DISTRIB] >>
          gvs[GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB])
      >- (irule EQ_TRANS >>
          irule_at (Pos hd) $ cj 1 mem_stores_load_disjoint >>
          first_assum $ irule_at $ Pos hd >>
          simp[] >>
          gvs[IS_SOME_EXISTS] >> res_tac >>
          drule_then irule DISJOINT_SUBSET >>
          simp[addresses_thm,SUBSET_DEF,SF DNF_ss] >>
          rpt strip_tac >>
          qexists_tac ‘i+SUM (MAP size_of_shape (dec_shapes decls))’ >>
          simp[] >>
          SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC, addressTheory.WORD_EQ_ADD_CANCEL] >>
          gvs[bytes_in_word_def,word_mul_n2w,word_add_n2w,good_dimindex_def,dimword_def,state_rel_def,LEFT_ADD_DISTRIB,WORD_LEFT_ADD_DISTRIB,length_flatten_eq_size_of_shape] >>
          gvs[GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB])) >>
  conj_tac
  >- (rpt strip_tac >>
      irule EQ_SYM >>
      irule mem_stores_lookup >>
      first_assum $ irule_at $ Pos last >>
      rw[addresses_thm] >>
      spose_not_then strip_assume_tac >>
      qpat_x_assum ‘DISJOINT s.memaddrs _’ mp_tac >>
      simp[DISJOINT_ALT] >>
      first_x_assum $ irule_at $ Pos hd >>
      simp[addresses_thm] >>
      gvs[length_flatten_eq_size_of_shape] >>
      qexists_tac ‘i + SUM(MAP size_of_shape(dec_shapes decls))’ >>
      simp[] >>
      SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC, addressTheory.WORD_EQ_ADD_CANCEL] >>
      gvs[bytes_in_word_def,word_mul_n2w,word_add_n2w,good_dimindex_def,dimword_def,state_rel_def,LEFT_ADD_DISTRIB,WORD_LEFT_ADD_DISTRIB] >>
      gvs[GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]) >>
  gvs[disjoint_globals_def] >>
  rw[IS_SOME_EXISTS,FLOOKUP_UPDATE]
  >- (gvs[IS_SOME_EXISTS] >>
      res_tac >>
      gvs[] >>
      irule $ iffLR DISJOINT_SYM >>
      drule_then irule DISJOINT_SUBSET >>
      simp[addresses_thm,SUBSET_DEF,SF DNF_ss] >>
      rpt strip_tac >>
      qexists_tac ‘i+SUM (MAP size_of_shape (dec_shapes decls))’ >>
      simp[] >>
      SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC, addressTheory.WORD_EQ_ADD_CANCEL] >>
      gvs[bytes_in_word_def,word_mul_n2w,word_add_n2w,good_dimindex_def,dimword_def,state_rel_def,LEFT_ADD_DISTRIB,WORD_LEFT_ADD_DISTRIB,length_flatten_eq_size_of_shape] >>
      gvs[GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB])
  >- (gvs[IS_SOME_EXISTS] >>
      res_tac >>
      gvs[] >>
      drule_then irule DISJOINT_SUBSET >>
      simp[addresses_thm,SUBSET_DEF,SF DNF_ss] >>
      rpt strip_tac >>
      qexists_tac ‘i+SUM (MAP size_of_shape (dec_shapes decls))’ >>
      simp[] >>
      SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC, addressTheory.WORD_EQ_ADD_CANCEL] >>
      gvs[bytes_in_word_def,word_mul_n2w,word_add_n2w,good_dimindex_def,dimword_def,state_rel_def,LEFT_ADD_DISTRIB,WORD_LEFT_ADD_DISTRIB,length_flatten_eq_size_of_shape] >>
      gvs[GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]) >>
  gvs[IS_SOME_EXISTS] >>
  res_tac
QED

Theorem evaluate_decls_init_globals_thm:
    evaluate_decls ^s decls = SOME s' ∧
    t = s with <| top_addr := s.top_addr + mgs;
                  memaddrs := (s.memaddrs ∪ free_addrs);
                  memory   := tmem;
                  locals := tlocals
                |> ∧
    s.code = FEMPTY ∧
    s.globals = FEMPTY ∧
    byte_aligned(s.top_addr) ∧
    good_dimindex(:'a) ∧
    mgs = bytes_in_word*n2w(SUM(MAP size_of_shape(dec_shapes decls))) ∧
    ctxt = <| globals := FEMPTY; globals_size := 0w;
              max_globals_size := mgs |> ∧
    EVERY ($¬ o is_function) decls ∧
    compile_decs ctxt decls = (decls',funs,ctxt') ∧
    free_addrs = addresses (s.top_addr) (SUM(MAP size_of_shape(dec_shapes decls))) ∧
    DISJOINT s.memaddrs free_addrs ∧
    (∀addr. addr ∈ s.memaddrs ⇒ s.memory addr = tmem addr) ∧
    s.top_addr + mgs ∉ s.memaddrs ∧
    w2n(bytes_in_word:'a word)*SUM(MAP size_of_shape(dec_shapes decls)) < dimword(:'a) ∧
    byte_aligned s.top_addr
    ⇒
    ∃t'. panSem$evaluate (nested_seq decls',t) = (NONE,t') ∧
         state_rel F ctxt' s' t'
Proof
  rpt strip_tac >>
  drule evaluate_decls_init_globals_lemma >>
  disch_then drule >>
  disch_then drule >>
  disch_then $ resolve_then (Pat ‘_ = _’) mp_tac EQ_REFL >>
  disch_then $ qspec_then ‘t’ mp_tac >>
  reverse impl_tac
  >- (rw[] >> simp[]) >>
  gvs[] >>
  conj_tac
  >- (gvs[state_rel_def,disjoint_globals_def] >>
      conj_tac
      >- (simp[addresses_thm] >>
          FULL_SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC, addressTheory.WORD_EQ_ADD_CANCEL] >>
          gvs[bytes_in_word_def,word_mul_n2w,word_add_n2w,good_dimindex_def,dimword_def,state_rel_def,LEFT_ADD_DISTRIB,WORD_LEFT_ADD_DISTRIB,length_flatten_eq_size_of_shape] >>
          intLib.COOPER_TAC) >>
      irule byte_aligned_add >>
      simp[] >>
      irule byte_aligned_bytes_in_word_mul >>
      simp[]) >>
  EVAL_TAC
QED

(* Not true as written yet *)
Theorem evaluate_decls_compile_top:
  evaluate_decls s decs = SOME s' ∧
  ALOOKUP (functions decs) start = SOME (args,body) ⇒
  evaluate_decls s (compile_top decs start) =
  SOME
  (s with
     code :=
   s.code |+
    (start,args,
     Seq (nested_seq decls')
         (TailCall (new_main_name decs) (MAP (Var Local ∘ FST) args))) |++
    MAP (λ(x,y,z). (x,y,compile ctxttt z))
    (functions (fperm_decs start (new_main_name decs) decs)))
Proof
  rw[compile_top_def, UNCURRY_eq_pair] >>
  qpat_x_assum ‘evaluate_decls _ _ = _’ $ assume_tac o PURE_ONCE_REWRITE_RULE[GSYM resort_decls_evaluate] >>
  pairarg_tac >>
  simp[] >>
  simp[evaluate_decls_def] >>
  gvs[resort_decls_def] >>
  gvs[compile_decls_append,fperm_decs_append,UNCURRY_eq_pair] >>
  gvs[fperm_decs_decls,EVERY_FILTER] >>
  qpat_x_assum ‘compile_decs <|globals := _; globals_size := _; max_globals_size := _|> _ = _’ assume_tac >>
  drule compile_decs_decls_thm >>
  simp[EVERY_FILTER] >>
  disch_then $ gvs o single >>
  imp_res_tac compile_decs_EVERY_is_function >>
  gvs[] >>
  simp[evaluate_decls_only_functions'] >>
  gvs[evaluate_decls_append,AllCaseEqs()] >>
  drule_at (Pos last) evaluate_decls_only_functions >>
  simp[EVERY_FILTER] >>
  disch_then $ gvs o single >>
  gvs[fperm_decs_FILTER_is_function] >>
  qpat_x_assum ‘compile_decs _ (FILTER is_function _) = _’ assume_tac >>
  drule compile_decs_functions_thm >>
  simp[EVERY_FILTER] >>
  strip_tac >>
  gvs[] >>

  qmatch_goalsub_abbrev_tac ‘functions (MAP f1 (FILTER is_function a1))’ >>
  ‘functions (MAP f1 (FILTER is_function a1)) =
   MAP (λ(x,y,z). (x,y,compile ctxt z)) (functions a1)’
    by(qunabbrev_tac ‘f1’ >>
       rpt $ pop_assum kall_tac >>
       Induct_on ‘a1’ using functions_ind >> gvs[functions_def,is_function_def]) >>
  pop_assum SUBST_ALL_TAC >>
  unabbrev_all_tac >>

  cheat
QED

val _ = export_theory();
