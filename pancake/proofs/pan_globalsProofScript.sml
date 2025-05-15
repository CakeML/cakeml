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
  state_rel ls ctxt s t ⇔
  s.top_addr = t.top_addr - ctxt.globals_size ∧
  (ls ⇒ s.locals = t.locals) ∧
  s.base_addr = t.base_addr ∧
  s.be = t.be ∧
  s.eshapes = t.eshapes ∧
  s.clock = t.clock ∧
  (∀v val.
     FLOOKUP s.globals v = SOME val ⇒
     ∃addr. FLOOKUP ctxt.globals v = SOME(shape_of val, addr) ∧
            mem_load (shape_of val) (t.top_addr - addr) t.memaddrs t.memory = SOME val ∧
            DISJOINT s.memaddrs (addresses (t.top_addr - addr) $ size_of_shape $ shape_of val)
  ) ∧
  s.memaddrs ⊆ t.memaddrs ∧
  s.sh_memaddrs = t.sh_memaddrs ∧
  (∀addr. addr ∈ s.memaddrs ⇒ s.memory addr = t.memory addr) ∧
  s.ffi = t.ffi ∧
  (∀fname vshapes prog. FLOOKUP s.code fname = SOME (vshapes,prog) ⇒
           FLOOKUP t.code fname = SOME (vshapes, compile ctxt prog)) ∧
  disjoint_globals t.top_addr ctxt.globals s.globals
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

(* unprovable *)
(*
Theorem mem_stores_mem_load_back:
  (∀val (addr:'a word) addrs memory m.
    mem_stores addr (flatten val) addrs memory = SOME m ⇒
    mem_load (shape_of val) addr addrs m =
    SOME val) ∧
  (∀vals (addr:'a word) addrs memory m.
    mem_stores addr (FLAT (MAP (λa. flatten a) vals)) addrs memory = SOME m ⇒
    mem_loads (MAP shape_of vals) addr addrs m =
    SOME vals)
Proof
  ho_match_mp_tac v_induction >>
  rw[flatten_def,shape_of_def,mem_stores_def,AllCaseEqs(),
     mem_store_def,mem_load_def
    ] >>
  rw[UPDATE_APPLY]
  >- (rw[Once $ oneline shape_of_def] >> PURE_CASE_TAC >> simp[])
  >- metis_tac[]
  >- (gvs[mem_stores_append,AllCaseEqs()] >>
      res_tac >>
      fs[] >>
      gvs[] >>


     )
     )
  >- ()
QED
*)

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
  cheat (* unprovable *)
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
              DISJOINT s.memaddrs (addresses (t.top_addr - addr) (size_of_shape(shape_of(Val vv))))’
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

val _ = export_theory();
