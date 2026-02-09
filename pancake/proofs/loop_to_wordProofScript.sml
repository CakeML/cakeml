(*
  Correctness proof for loop_to_word
*)
Theory loop_to_wordProof
Libs
  preamble
Ancestors
  loopSem loopProps wordLang wordSem wordProps pan_common
  pan_commonProps loop_to_word loop_removeProof wordConvs


val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"];

val _ = temp_delsimps ["fromAList_def", "domain_union",
                       "domain_inter", "domain_difference",
                       "domain_map", "sptree.map_def", "sptree.lookup_rwts",
                       "sptree.insert_notEmpty", "sptree.isEmpty_union"];

Definition locals_rel_def:
  locals_rel ctxt l1 l2 ⇔
    INJ (find_var ctxt) (domain ctxt) UNIV ∧
    (∀n m. lookup n ctxt = SOME m ==> m ≠ 0) ∧
    ∀n v. lookup n l1 = SOME v ⇒
          ∃m. lookup n ctxt = SOME m ∧ lookup m l2 = SOME v
End

Definition globals_rel_def:
  globals_rel g1 g2 =
    ∀n v. FLOOKUP g1 n = SOME v ⇒ FLOOKUP g2 (Temp n) = SOME v
End

Definition code_rel_def:
  code_rel s_code t_code =
    ∀name params body.
      lookup name s_code = SOME (params,body) ⇒
      lookup name t_code = SOME (LENGTH params+1, comp_func name params body) ∧
      no_Loops body ∧ ALL_DISTINCT params
End

Definition state_rel_def:
  state_rel s t <=>
  ∃len.
    t.memory = s.memory ∧
    t.mdomain = s.mdomain ∧
    t.sh_mdomain = s.sh_mdomain ∧
    t.clock = s.clock ∧
    t.be = s.be ∧
    t.ffi = s.ffi ∧
    ALOOKUP (fmap_to_alist t.store) CurrHeap = SOME (Word s.base_addr) ∧
    ALOOKUP (fmap_to_alist t.store) HeapLength = SOME (Word len) ∧
    s.top_addr = s.base_addr + 2w*len ∧
    globals_rel s.globals t.store ∧
    code_rel s.code t.code
End

val goal =
  ``λ(prog:α loopLang$prog, s). ∀res s1 t ctxt retv l.
      evaluate (prog,s) = (res,s1) ∧ res ≠ SOME Error ∧
      state_rel s t ∧ locals_rel ctxt s.locals t.locals ∧
(*      ALOOKUP (fmap_to_alist t.store) CurrHeap = SOME (Word s.base_addr) ∧
      ALOOKUP (fmap_to_alist t.store) EndOfHeap = SOME (Word s.top_addr) ∧*)
      lookup 0 t.locals = SOME retv ∧ no_Loops prog ∧
      good_dimindex(:'a) ∧
      ~(isWord retv) ∧
      domain (acc_vars prog LN) ⊆ domain ctxt ⇒
      ∃t1 res1.
         evaluate (FST (comp ctxt prog l),t) = (res1,t1) ∧
         t1.ffi = s1.ffi ∧
         case res of
         | NONE => state_rel s1 t1 ∧ res1 = NONE ∧ lookup 0 t1.locals = SOME retv ∧
                   (* always return to the label stored in Var 0 for wordLang's prog *)
                   locals_rel ctxt s1.locals t1.locals ∧
                   t1.stack = t.stack ∧ t1.handler = t.handler
         | SOME (Result v) => state_rel s1 t1 ∧ res1 = SOME (Result retv [v]) ∧
                                     t1.stack = t.stack ∧ t1.handler = t.handler
         | SOME TimeOut => res1 = SOME TimeOut
         | SOME (FinalFFI f) => res1 = SOME (FinalFFI f)
         | SOME (Exception v) =>
            state_rel s1 t1 ∧
            (res1 ≠ SOME Error ⇒ ∃u1 u2. res1 = SOME (Exception u1 u2)) ∧
            ∀r l1 l2. jump_exc (t1 with <| stack := t.stack;
                                           handler := t.handler |>) = SOME (r,l1,l2) ⇒
                      res1 = SOME (Exception (Loc l1 l2) v) ∧ r = t1
         | _ => F``

local
  val ind_thm = loopSemTheory.evaluate_ind
    |> ISPEC goal
    |> CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV) |> REWRITE_RULE [];
  fun list_dest_conj tm = if not (is_conj tm) then [tm] else let
    val (c1,c2) = dest_conj tm in list_dest_conj c1 @ list_dest_conj c2 end
  val ind_goals = ind_thm |> concl |> dest_imp |> fst |> list_dest_conj
in
  fun get_goal s = first (can (find_term (can (match_term (Term [QUOTE s]))))) ind_goals
  fun compile_correct_tm () = ind_thm |> concl |> rand
  fun the_ind_thm () = ind_thm
end

Theorem locals_rel_intro:
  locals_rel ctxt l1 l2 ==>
    INJ (find_var ctxt) (domain ctxt) UNIV ∧
    (∀n m. lookup n ctxt = SOME m ==> m ≠ 0) ∧
    ∀n v. lookup n l1 = SOME v ⇒
          ∃m. lookup n ctxt = SOME m ∧ lookup m l2 = SOME v
Proof
  rw [locals_rel_def]
QED

Theorem globals_rel_intro:
  globals_rel g1 g2 ==>
    ∀n v. FLOOKUP g1 n = SOME v ⇒ FLOOKUP g2 (Temp n) = SOME v
Proof
  rw [globals_rel_def]
QED

Theorem code_rel_intro:
  code_rel s_code t_code ==>
    ∀name params body.
      lookup name s_code = SOME (params,body) ⇒
      lookup name t_code = SOME (LENGTH params+1, comp_func name params body) ∧
      no_Loops body ∧ ALL_DISTINCT params
Proof
  rw [code_rel_def] >> metis_tac []
QED

Theorem state_rel_intro:
  state_rel s t ==>
    t.memory = s.memory ∧
    t.mdomain = s.mdomain ∧
    t.clock = s.clock ∧
    t.be = s.be ∧
    t.ffi = s.ffi ∧
    ALOOKUP (fmap_to_alist t.store) CurrHeap = SOME (Word s.base_addr) ∧
    globals_rel s.globals t.store ∧
    code_rel s.code t.code
Proof
  rw [state_rel_def] >> simp[]
QED

Theorem find_var_neq_0:
  v ∈ domain ctxt ∧ locals_rel ctxt lcl lcl' ⇒
  find_var ctxt v ≠ 0
Proof
  fs [locals_rel_def, find_var_def] >> rw [] >>
  Cases_on ‘lookup var_name ctxt’ >> fs [] >>
  fs [domain_lookup] >> res_tac >> metis_tac []
QED

Theorem locals_rel_insert:
  locals_rel ctxt lcl lcl' ∧ v IN domain ctxt ⇒
  locals_rel ctxt (insert v w lcl)
     (insert (find_var ctxt v) w lcl')
Proof
  fs [locals_rel_def,lookup_insert] >> rw [] >>
  fs [CaseEq"bool"] >> rveq >> fs [] >>
  fs [domain_lookup,find_var_def] >>
  res_tac >> fs [] >>
  disj2_tac >> CCONTR_TAC >> fs [] >> rveq >> fs [] >>
  fs [INJ_DEF,domain_lookup] >>
  first_x_assum (qspecl_then [‘v’,‘n’] mp_tac) >>
  fs [] >> fs [find_var_def]
QED

Theorem locals_rel_get_var:
  locals_rel ctxt l t.locals ∧ lookup n l = SOME w ⇒
  wordSem$get_var (find_var ctxt n) t = SOME w
Proof
  fs [locals_rel_def] >> rw[] >> res_tac >>
  fs [find_var_def, get_var_def]
QED

Theorem locals_rel_get_vars:
  ∀argvars argvals.
    locals_rel ctxt s.locals t.locals ∧
    loopSem$get_vars argvars s = SOME argvals ⇒
    wordSem$get_vars (MAP (find_var ctxt) argvars) t = SOME argvals ∧
    LENGTH argvals = LENGTH argvars
Proof
  Induct >> fs [loopSemTheory.get_vars_def,get_vars_def,CaseEq"option"]
  >> rw [] >> imp_res_tac locals_rel_get_var >> fs []
QED


Theorem state_rel_IMP[local]:
  state_rel s t ⇒ t.clock = s.clock
Proof
  fs [state_rel_def] >> metis_tac[]
QED

Theorem set_fromNumSet:
  set (fromNumSet t) = domain t
Proof
  fs [fromNumSet_def,EXTENSION,MEM_MAP,EXISTS_PROD,MEM_toAList,domain_lookup]
QED

Theorem domain_toNumSet:
  domain (toNumSet ps) = set ps
Proof
  Induct_on ‘ps’ >> fs [toNumSet_def]
QED

Theorem domain_make_ctxt:
  ∀n ps l. domain (make_ctxt n ps l) = domain l UNION set ps
Proof
  Induct_on ‘ps’ >> fs [make_ctxt_def] >> fs [EXTENSION] >> metis_tac []
QED

Theorem make_ctxt_inj:
  ∀xs l n. (∀x y v. lookup x l = SOME v ∧ lookup y l = SOME v ⇒ x = y ∧ v < n) ⇒
           (∀x y v. lookup x (make_ctxt n xs l) = SOME v ∧
                    lookup y (make_ctxt n xs l) = SOME v ⇒ x = y)
Proof
  Induct_on ‘xs’ >> fs [make_ctxt_def] >> rw []
  >> first_x_assum (qspecl_then [‘insert h n l’,‘n+2’] mp_tac)
  >> impl_tac >-
   (fs [lookup_insert] >> rw []
    >> CCONTR_TAC >> fs [] >> res_tac >> fs [])
  >> metis_tac []
QED

Theorem make_ctxt_APPEND[local]:
  ∀xs ys n l.
    make_ctxt n (xs ++ ys) l =
    make_ctxt (n + 2 * LENGTH xs) ys (make_ctxt n xs l)
Proof
  Induct >> fs [make_ctxt_def,MULT_CLAUSES]
QED

Theorem make_ctxt_NOT_MEM[local]:
  ∀xs n l x. ~MEM x xs ⇒ lookup x (make_ctxt n xs l) = lookup x l
Proof
  Induct >> fs [make_ctxt_def,lookup_insert]
QED

Theorem lookup_EL_make_ctxt:
  ∀params k n l.
    k < LENGTH params ∧ ALL_DISTINCT params ⇒
    lookup (EL k params) (make_ctxt n params l) = SOME (2 * k + n)
Proof
  Induct >> Cases_on ‘k’ >> fs [] >> fs [make_ctxt_def,make_ctxt_NOT_MEM]
QED

Theorem lookup_make_ctxt_range:
  ∀xs m l n y.
    lookup n (make_ctxt m xs l) = SOME y ⇒
    lookup n l = SOME y ∨ m ≤ y
Proof
  Induct >> fs [make_ctxt_def] >> rw []
  >> first_x_assum drule
  >> fs [lookup_insert] >> rw [] >> fs []
QED

Theorem locals_rel_make_ctxt:
  ALL_DISTINCT params ∧ DISJOINT (set params) (set xs) ∧
  LENGTH params = LENGTH l ⇒
  locals_rel (make_ctxt 2 (params ++ xs) LN)
    (fromAList (ZIP (params,l))) (fromList2 (retv::l))
Proof
  fs [locals_rel_def] >> rw []
  >-
   (fs [INJ_DEF,find_var_def,domain_lookup] >> rw [] >> rfs []
    >> rveq >> fs []
    >> imp_res_tac (MP_CANON make_ctxt_inj) >> fs [lookup_def])
  >-
   (Cases_on ‘lookup n (make_ctxt 2 (params ++ xs) LN)’ >> simp []
    >> drule lookup_make_ctxt_range >> fs [lookup_def])
  >> fs [lookup_fromAList]
  >> imp_res_tac ALOOKUP_MEM
  >> rfs [MEM_ZIP]  >> rveq >> fs [make_ctxt_APPEND]
  >> rename [‘k < LENGTH _’]
  >> ‘k < LENGTH params’ by fs []
  >> drule EL_MEM >> strip_tac
  >> ‘~MEM (EL k params) xs’ by (fs [IN_DISJOINT] >> metis_tac [])
  >> fs [make_ctxt_NOT_MEM]
  >> fs [lookup_EL_make_ctxt]
  >> fs [lookup_fromList2,EVEN_ADD,EVEN_DOUBLE]
  >> ‘2 * k + 2 = (SUC k) * 2’ by fs []
  >> asm_rewrite_tac [MATCH_MP MULT_DIV (DECIDE “0 < 2:num”)]
  >> fs [lookup_fromList]
  >> rewrite_tac [GSYM ADD1,EL,TL]
QED

Theorem domain_mk_new_cutset_not_empty:
  domain (mk_new_cutset ctxt x1) ≠ ∅
Proof
  fs [mk_new_cutset_def]
QED

Theorem cut_env_mk_new_cutset:
  locals_rel ctxt l1 l2 ∧ domain x1 ⊆ domain l1 ∧ lookup 0 l2 = SOME y ⇒
  ∃env1. cut_env (mk_new_cutset ctxt x1,LN) l2 = SOME env1 ∧
         locals_rel ctxt (inter l1 x1) env1
Proof
  fs [locals_rel_def,SUBSET_DEF,cut_env_def,cut_envs_def,cut_names_def,AllCaseEqs()]
  >> fs [lookup_inter_alt]
  >> fs [mk_new_cutset_def,domain_toNumSet,MEM_MAP,set_fromNumSet,PULL_EXISTS]
  >> fs [DISJ_IMP_THM,PULL_EXISTS]
  >> strip_tac >> fs [domain_lookup]
  >> rw [] >> res_tac >> fs [] >> rveq >> fs [find_var_def]
  >> rw [] >> res_tac >> fs [] >> rveq >> fs [find_var_def]
  >> disj2_tac >> qexists_tac ‘n’ >> fs []
QED

Theorem env_to_list_IMP:
  env_to_list env1 t.permute = (l,permute) ⇒
  domain (fromAList l) = domain env1 ∧
  ∀x. lookup x (fromAList l) = lookup x env1
Proof
  strip_tac >> drule env_to_list_lookup_equiv
  >> fs [EXTENSION,domain_lookup,lookup_fromAList]
QED

Theorem cut_env_LN_IMP:
  cut_env (s,LN) l = SOME env ⇒
  cut_envs (s,LN) l = SOME (env,LN)
Proof
  gvs [cut_env_def,cut_envs_def,cut_names_def]
  \\ IF_CASES_TAC \\ gvs []
QED

Theorem env_to_list_LN_IMP:
  env_to_list LN l = (x,p) ⇒ x = []
Proof
  strip_tac
  \\ drule_all env_to_list_lookup_equiv
  \\ gvs [lookup_def,ALOOKUP_NONE]
  \\ Cases_on ‘x’ \\ gvs []
  \\ Cases_on ‘h’ \\ gvs []
  \\ metis_tac []
QED

Theorem cut_env_mk_new_cutset_IMP:
  cut_env (mk_new_cutset ctxt x1,LN) l1 = SOME l2 ⇒
  lookup 0 l2 = lookup 0 l1
Proof
  fs [cut_env_def,cut_envs_def,cut_names_def] >> rw []
  >> fs [SUBSET_DEF,mk_new_cutset_def]
  >> fs [lookup_inter_alt]
QED

Theorem LASTN_ADD_CONS[local]:
  ~(LENGTH xs <= n) ⇒ LASTN (n + 1) (x::xs) = LASTN (n + 1) xs
Proof
  fs [LASTN_CONS]
QED

Theorem comp_exp_preserves_eval:
  ∀s (e:'a loopLang$exp) v t ctxt.
    eval s e = SOME v ∧ good_dimindex(:'a) ∧
    state_rel s t /\ locals_rel ctxt s.locals t.locals ==>
    word_exp t (comp_exp ctxt e) = SOME v
Proof
  ho_match_mp_tac eval_ind >>
  rw [] >>
  fs [eval_def, comp_exp_def, word_exp_def, get_var_def]
  >-
   (fs [find_var_def, locals_rel_def] >>
    TOP_CASE_TAC >> fs [] >>
    first_x_assum drule >>
    strip_tac >> fs [] >> rveq >> fs [])
  >- fs [state_rel_def, globals_rel_def, get_store_def]
  >-
   (cases_on ‘eval s e’ >> fs [] >>
    cases_on ‘x’ >> fs [] >>
    first_x_assum drule_all >> fs [] >>
    strip_tac >>
    fs [state_rel_def, mem_load_def,
        loopSemTheory.mem_load_def])
  >-
   (fs [CaseEq "option"] >>
    qsuff_tac
    ‘the_words (MAP (λa. word_exp t a)
                    (MAP (λa. comp_exp ctxt a) wexps)) = SOME ws’
    >- fs [] >>
    ntac 2 (pop_assum mp_tac) >>
    ntac 3 (pop_assum kall_tac) >>
    rpt (pop_assum mp_tac) >>
    qid_spec_tac ‘ws’ >>
    qid_spec_tac ‘wexps’ >>
    Induct >> rw [] >>
    last_assum mp_tac >>
    impl_tac >- metis_tac [] >>
    fs [the_words_def, CaseEq"option", CaseEq"word_loc"] >>
    rveq >> fs [])
  >-
   (fs [CaseEq"option", CaseEq"word_loc"] >> rveq >> fs []) >>
  fs[state_rel_def,get_store_def] >>
  Cases_on ‘FLOOKUP t.store CurrHeap’ >> fs[] >>
  rename1 ‘x’ >>
  Cases_on ‘x’ >> fs[theWord_def, isWord_def,word_sh_def, the_words_def, good_dimindex_def,word_op_def] >>
  gvs[] >>
  simp[WORD_MUL_LSL]
QED

Theorem compile_Skip:
  ^(get_goal "comp _ loopLang$Skip") ∧
  ^(get_goal "comp _ loopLang$Fail") ∧
  ^(get_goal "comp _ loopLang$Tick")
Proof
  rpt strip_tac >>
  fs [loopSemTheory.evaluate_def, comp_def,
      evaluate_def] >>
  rveq >> fs []
  >- fs [state_rel_def]
  >- (TOP_CASE_TAC >>
      fs [flush_state_def, state_rel_def,
          loopSemTheory.dec_clock_def, dec_clock_def] >> rveq >>
      fs [] >>
      rw[])
QED

Theorem compile_Loop:
  ^(get_goal "comp _ loopLang$Continue") ∧
  ^(get_goal "comp _ loopLang$Break") ∧
  ^(get_goal "comp _ (loopLang$Loop _ _ _)")
Proof
  rpt strip_tac >>
  fs [no_Loops_def, every_prog_def] >>
  fs [no_Loop_def, every_prog_def]
QED

Theorem compile_Mark:
  ^(get_goal "comp _ (Mark _)")
Proof
  rpt strip_tac >>
  fs [loopSemTheory.evaluate_def, comp_def,
      evaluate_def, no_Loops_def,
      loopLangTheory.acc_vars_def, no_Loop_def, every_prog_def]
QED

Theorem compile_Return:
  ^(get_goal "loopLang$Return")
Proof
  rpt strip_tac >>
  fs [loopSemTheory.evaluate_def, comp_def, evaluate_def] >>
  cases_on ‘lookup n s.locals’ >>
  fs []  >> rveq >>
  TOP_CASE_TAC >>
  fs [find_var_def, locals_rel_def, get_var_def, get_vars_def] >>
  res_tac >> rveq >>
  fs [] >>
  TOP_CASE_TAC >> fs [isWord_def] >>
  fs [flush_state_def, state_rel_def,
      loopSemTheory.call_env_def]
QED

Theorem compile_Raise:
  ^(get_goal "loopLang$Raise")
Proof
  fs [comp_def,loopSemTheory.evaluate_def,CaseEq"option"] >>
  rw [] >> fs [evaluate_def] >>
  imp_res_tac locals_rel_get_var >> fs [] >>
  Cases_on ‘jump_exc t’ >> fs []
  >- fs [jump_exc_def, state_rel_def, loopSemTheory.call_env_def] >>
  fs [CaseEq"prod",PULL_EXISTS] >>
  PairCases_on ‘x’ >> fs [loopSemTheory.call_env_def] >>
  pop_assum mp_tac >>
  fs [CaseEq"option",CaseEq"prod", jump_exc_def,
      CaseEq"stack_frame", CaseEq"list"] >>
  strip_tac >> fs [] >> rveq >> fs [] >>
  fs [state_rel_def]
QED

Theorem compile_Seq:
  ^(get_goal "comp _ (loopLang$Seq _ _)")
Proof
  rpt strip_tac >>
  fs [loopSemTheory.evaluate_def] >>
  pairarg_tac >> fs [comp_def] >>
  rpt (pairarg_tac >> fs []) >>
  fs [evaluate_def] >>
  rpt (pairarg_tac >> fs []) >>
  first_x_assum (qspecl_then [‘t’,‘ctxt’,‘retv’,‘l’] mp_tac) >>
  impl_tac
  >- (
   fs [] >>
   conj_tac >- (CCONTR_TAC >> fs []) >>
   fs [no_Loops_def, no_Loop_def, every_prog_def] >>
   qpat_x_assum ‘_ ⊆ domain ctxt’ mp_tac >>
   fs [loopLangTheory.acc_vars_def] >>
   once_rewrite_tac [acc_vars_acc] >> fs []) >>
  fs [] >> strip_tac >>
  reverse (Cases_on ‘res'’) >> fs [] >> rveq >> fs []
  >- (
   Cases_on ‘x’ >> fs [] >>
   IF_CASES_TAC >> fs []) >>
  rename [‘state_rel s2 t2’] >>
  first_x_assum drule >>
  fs[state_rel_def]>>
  rpt (disch_then drule) >>
  disch_then (qspec_then ‘l'’ mp_tac) >>
  impl_tac
  >- (
   qpat_x_assum ‘_ ⊆ domain ctxt’ mp_tac >>
   fs [no_Loops_def, no_Loop_def, every_prog_def] >>
   fs [loopLangTheory.acc_vars_def] >>
   once_rewrite_tac [acc_vars_acc] >> fs []
   ) >>
  fs [] >> strip_tac >> fs [] >>
  Cases_on ‘res’ >> fs [] >>
  Cases_on ‘x’ >> fs []
QED

Theorem compile_Assign:
  ^(get_goal "loopLang$Assign") ∧
  ^(get_goal "loopLang$LocValue")
Proof
  rpt strip_tac >>
  fs [loopSemTheory.evaluate_def,
      comp_def, evaluate_def]
  >- (
   cases_on ‘eval s exp’ >> fs [] >>
   rveq >> fs [] >>
   imp_res_tac comp_exp_preserves_eval >>
   fs [loopSemTheory.set_var_def, set_var_def] >>
   conj_tac >- fs [state_rel_def] >>
   conj_tac >- fs [state_rel_def] >>
   conj_tac
   >- (
    fs [lookup_insert, CaseEq "bool", loopLangTheory.acc_vars_def] >>
    imp_res_tac find_var_neq_0 >> fs []) >>
   match_mp_tac locals_rel_insert >>
   fs [loopLangTheory.acc_vars_def]) >>
  fs [CaseEq "bool"] >> rveq >> fs [] >>
  fs [loopSemTheory.set_var_def, set_var_def] >>
  conj_tac
  >- (
   fs [state_rel_def,
       code_rel_def,domain_lookup,EXISTS_PROD] >>
   metis_tac []) >>
  conj_tac >- fs [state_rel_def] >>
  conj_tac >- fs [state_rel_def] >>
  conj_tac
  >- (
   fs [lookup_insert, CaseEq "bool", loopLangTheory.acc_vars_def] >>
   imp_res_tac find_var_neq_0 >> fs []) >>
  match_mp_tac locals_rel_insert >>
  fs [loopLangTheory.acc_vars_def]
QED

Theorem compile_Store:
  ^(get_goal "loopLang$Store") ∧
  ^(get_goal "loopLang$Store32") ∧
  ^(get_goal "loopLang$StoreByte")
Proof
  rpt strip_tac >>
  fs [loopSemTheory.evaluate_def,
      comp_def, evaluate_def]
  >- (
   fs [CaseEq "option", CaseEq "word_loc"] >> rveq >>
   imp_res_tac comp_exp_preserves_eval >>
   fs [] >>
   drule_all locals_rel_get_var >>
   strip_tac >> fs [] >>
   fs [loopSemTheory.mem_store_def, mem_store_def] >>
   rveq >> fs [state_rel_def]) >>
  fs [CaseEq "option", CaseEq "word_loc"] >> rveq >>
  fs [inst_def, word_exp_def] >>
  drule locals_rel_intro >>
  strip_tac >>
  res_tac >> fs [] >>
  fs [find_var_def, the_words_def, word_op_def] >>
  fs [get_var_def] >>
  fs [state_rel_def]
QED

Theorem compile_Load32:
  ^(get_goal "loopLang$Load32")
Proof
  rpt strip_tac >>
  fs [loopSemTheory.evaluate_def,
      comp_def, evaluate_def] >>
  fs [CaseEq "option", CaseEq "word_loc"] >> rveq >>
  fs [inst_def, word_exp_def] >>
  drule locals_rel_intro >>
  strip_tac >>
  res_tac >> fs [] >>
  fs [find_var_def, the_words_def, word_op_def, get_var_def] >>
  drule state_rel_intro >>
  strip_tac >> fs [] >>
  fs [loopSemTheory.set_var_def, set_var_def] >>
  conj_tac >- fs [state_rel_def] >>
  fs [loopLangTheory.acc_vars_def] >>
  imp_res_tac find_var_neq_0 >>
  fs [domain_lookup, lookup_insert, CaseEq "bool"] >>
  conj_tac
  >- (CCONTR_TAC >> res_tac >> fs []) >>
  drule locals_rel_insert >>
  disch_then (qspecl_then [‘Word (w2w b)’, ‘v’] mp_tac) >>
  fs [domain_lookup, find_var_def]
QED

Theorem compile_LoadByte:
  ^(get_goal "loopLang$LoadByte")
Proof
  rpt strip_tac >>
  fs [loopSemTheory.evaluate_def,
      comp_def, evaluate_def] >>
  fs [CaseEq "option", CaseEq "word_loc"] >> rveq >>
  fs [inst_def, word_exp_def] >>
  drule locals_rel_intro >>
  strip_tac >>
  res_tac >> fs [] >>
  fs [find_var_def, the_words_def, word_op_def, get_var_def] >>
  drule state_rel_intro >>
  strip_tac >> fs [] >>
  fs [loopSemTheory.set_var_def, set_var_def] >>
  conj_tac >- fs [state_rel_def] >>
  fs [loopLangTheory.acc_vars_def] >>
  imp_res_tac find_var_neq_0 >>
  fs [domain_lookup, lookup_insert, CaseEq "bool"] >>
  conj_tac
  >- (CCONTR_TAC >> res_tac >> fs []) >>
  drule locals_rel_insert >>
  disch_then (qspecl_then [‘Word (w2w b)’, ‘v’] mp_tac) >>
  fs [domain_lookup, find_var_def]
QED

Theorem compile_SetGlobal:
  ^(get_goal "loopLang$SetGlobal")
Proof
  rpt strip_tac >>
  fs [loopSemTheory.evaluate_def,
      comp_def, evaluate_def] >>
  fs [CaseEq "option"] >>
  rveq >> fs [] >>
  imp_res_tac comp_exp_preserves_eval >>
  fs [] >>
  fs [state_rel_def, set_store_def,
      loopSemTheory.set_globals_def, globals_rel_def] >>
  rw [FLOOKUP_UPDATE] >>
  rw[] >> gvs[]
QED

Theorem acc_vars_acc'[local] =
        acc_vars_acc |> CONV_RULE SWAP_FORALL_CONV |> SPEC “acc_vars (q:'a loopLang$prog) LN”;

Theorem compile_If:
  ^(get_goal "loopLang$If")
Proof
  rpt strip_tac >>
  ‘no_Loops c1 ∧ no_Loops c2’ by (gvs[no_Loops_def,no_Loop_def,every_prog_def]) >>
  fs [loopSemTheory.evaluate_def, comp_def] >>
  rpt(pairarg_tac >> simp[]) >>
  fs [find_var_def, get_var_def] >>
  imp_res_tac locals_rel_intro >> fs [] >>
  gvs[AllCaseEqs(),
      DefnBase.one_line_ify NONE loopSemTheory.cut_res_def,
      DefnBase.one_line_ify NONE cut_state_def,
      loopLangTheory.acc_vars_def,
      acc_vars_acc'
      ] >>
  first_assum $ drule_then strip_assume_tac >>
  gvs[AllCaseEqs(),
      DefnBase.one_line_ify NONE loopSemTheory.get_var_imm_def] >>
  first_assum $ drule_then strip_assume_tac >>
  simp[evaluate_def,get_var_def,find_reg_imm_def,get_var_imm_def,find_var_def] >>
  rw[] >> fs[] >>
  last_x_assum drule >> rpt(disch_then drule) >>
  rename1 ‘comp ctxt cv’ >>
  rename1 ‘comp ctxt cv the_l’ >>
  disch_then $ qspec_then ‘the_l’ strip_assume_tac >>
  gvs[] >>
  (* the every_case_tac replaces a deeply nested TRY block, so hopefully it's
     a forgivable sin *)
  every_case_tac >> gvs[] >>
  gvs[state_rel_def,flush_state_def,
      AllCaseEqs(),
      DefnBase.one_line_ify NONE loopSemTheory.cut_state_def,
      loopSemTheory.dec_clock_def,wordSemTheory.dec_clock_def
     ] >>
  gvs[locals_rel_def,lookup_inter_alt]
QED

Theorem compile_Call:
  ^(get_goal "comp _ (loopLang$Call _ _ _ _)")
Proof
  rw [] >> qpat_x_assum ‘evaluate _ = (res,_)’ mp_tac
  >> simp [loopSemTheory.evaluate_def]
  >> simp [CaseEq"option"]
  >> strip_tac >> fs []
  >> rename [‘find_code _ _ _ = SOME x’]
  >> PairCases_on ‘x’ >> fs []
  >> rename [‘find_code _ _ _ = SOME (new_env,new_code)’]
  >> ‘~bad_dest_args dest (MAP (find_var ctxt) argvars)’ by
       (pop_assum kall_tac >> Cases_on ‘dest’ >> fs [bad_dest_args_def]
        >> fs [loopSemTheory.find_code_def]
        >> imp_res_tac locals_rel_get_vars >> CCONTR_TAC >> fs [])
  >> Cases_on ‘ret’ >> fs []
  >-
   (fs [comp_def,evaluate_def]
    >> imp_res_tac locals_rel_get_vars >> fs [add_ret_loc_def]
    >> fs [get_vars_def,get_var_def]
    >> simp [bad_dest_args_def,call_env_def,dec_clock_def]
    >> ‘∃args1 prog1 ss1 name1 ctxt1 l1.
         find_code dest (retv::argvals) t.code t.stack_size = SOME (args1,prog1,ss1) ∧
         FST (comp ctxt1 new_code l1) = prog1 ∧
         lookup 0 (fromList2 args1) = SOME retv ∧
         locals_rel ctxt1 new_env (fromList2 args1) ∧ no_Loops new_code ∧
         domain (acc_vars new_code LN) ⊆ domain ctxt1’ by
      (qpat_x_assum ‘_ = (res,_)’ kall_tac
       >> Cases_on ‘dest’ >> fs [loopSemTheory.find_code_def]
       >-
        (fs [CaseEq"word_loc",CaseEq"num",CaseEq"option",CaseEq"prod",CaseEq"bool"]
         >> rveq >> fs [code_rel_def,state_rel_def]
         >> first_x_assum drule >> strip_tac >> fs []
         >> fs [find_code_def]
         >> ‘∃x l. argvals = SNOC x l’ by metis_tac [SNOC_CASES]
         >> qpat_x_assum ‘_ = Loc loc 0’ mp_tac
         >> rveq >> rewrite_tac [GSYM SNOC,LAST_SNOC,FRONT_SNOC] >> fs []
         >> strip_tac >> rveq >> fs []
         >> simp [comp_func_def]
         >> qmatch_goalsub_abbrev_tac ‘comp ctxt2 _ ll2’
         >> qexists_tac ‘ctxt2’ >> qexists_tac ‘ll2’ >> fs []
         >> conj_tac >- fs [lookup_fromList2,lookup_fromList]
         >> simp [Abbr‘ctxt2’,domain_make_ctxt,set_fromNumSet,
                  domain_difference,domain_toNumSet, SUBSET_DEF]
         >> match_mp_tac locals_rel_make_ctxt
         >> fs [IN_DISJOINT,set_fromNumSet,domain_difference,
                domain_toNumSet,GSYM IMP_DISJ_THM])
       >> fs [CaseEq"word_loc",CaseEq"num",CaseEq"option",CaseEq"prod",CaseEq"bool"]
       >> rveq >> fs [code_rel_def,state_rel_def]
       >> first_x_assum drule >> strip_tac >> fs []
       >> fs [find_code_def]
       >> simp [comp_func_def]
       >> qmatch_goalsub_abbrev_tac ‘comp ctxt2 _ ll2’
       >> qexists_tac ‘ctxt2’ >> qexists_tac ‘ll2’ >> fs []
       >> conj_tac >- fs [lookup_fromList2,lookup_fromList]
       >> simp [Abbr‘ctxt2’,domain_make_ctxt,set_fromNumSet,
                domain_difference,domain_toNumSet, SUBSET_DEF]
       >> match_mp_tac locals_rel_make_ctxt
       >> fs [IN_DISJOINT,set_fromNumSet,domain_difference,
              domain_toNumSet,GSYM IMP_DISJ_THM])
    >> fs [] >> imp_res_tac state_rel_IMP
    >> fs [] >> IF_CASES_TAC >> fs []
    >-
     (fs [CaseEq"bool"] >> rveq >> fs []
      >> fs [state_rel_def,flush_state_def])
    >> Cases_on ‘handler = NONE’ >> fs [] >> rveq
    >> Cases_on ‘evaluate (new_code,dec_clock s with locals := new_env)’ >> fs []
    >> Cases_on ‘q’ >> fs []
    >> Cases_on ‘x = Error’ >> rveq >> fs []
    >> qmatch_goalsub_abbrev_tac ‘wordSem$evaluate (_,tt)’
    >> first_x_assum (qspecl_then [‘tt’,‘ctxt1’,‘retv’,‘l1’] mp_tac)
    >> impl_tac
    >- (fs [Abbr‘tt’] >>
        fs [state_rel_def,loopSemTheory.dec_clock_def])
    >> strip_tac >> fs []
    >> Cases_on ‘x’ >> fs [] >> rveq >> fs []
    >- fs [Abbr‘tt’]
    >> qexists_tac ‘t1’ >> fs []
    >> qexists_tac ‘res1’ >> fs []
    >> conj_tac >- (Cases_on ‘res1’ >> simp [CaseEq"option"] >> fs [])
    >> rpt gen_tac >> strip_tac >> pop_assum mp_tac
    >> qunabbrev_tac ‘tt’ >> fs [])
  >> fs [comp_def,evaluate_def]
  >> imp_res_tac locals_rel_get_vars >> fs [add_ret_loc_def]
  >> fs [get_vars_def,get_var_def]
  >> simp [bad_dest_args_def,call_env_def,dec_clock_def]
  >> PairCases_on ‘x’ >> PairCases_on ‘l’
  >> fs [] >> imp_res_tac state_rel_IMP
  >> ‘∃args1 prog1 ss1 name1 ctxt1 l2.
         find_code dest (Loc l0 l1::argvals) t.code t.stack_size = SOME (args1,prog1,ss1) ∧
         FST (comp ctxt1 new_code l2) = prog1 ∧
         lookup 0 (fromList2 args1) = SOME (Loc l0 l1) ∧
         locals_rel ctxt1 new_env (fromList2 args1) ∧ no_Loops new_code ∧
         domain (acc_vars new_code LN) ⊆ domain ctxt1’ by
    (qpat_x_assum ‘_ = (res,_)’ kall_tac
     >> rpt (qpat_x_assum ‘∀x. _’ kall_tac)
     >> Cases_on ‘dest’ >> fs [loopSemTheory.find_code_def]
     >-
      (fs [CaseEq"word_loc",CaseEq"num",CaseEq"option",CaseEq"prod",CaseEq"bool"]
       >> rveq >> fs [code_rel_def,state_rel_def]
       >> first_x_assum drule >> strip_tac >> fs []
       >> fs [find_code_def]
       >> ‘∃x l. argvals = SNOC x l’ by metis_tac [SNOC_CASES]
       >> qpat_x_assum ‘_ = Loc loc 0’ mp_tac
       >> rveq >> rewrite_tac [GSYM SNOC,LAST_SNOC,FRONT_SNOC] >> fs []
       >> strip_tac >> rveq >> fs []
       >> simp [comp_func_def]
       >> qmatch_goalsub_abbrev_tac ‘comp ctxt2 _ ll2’
       >> qexists_tac ‘ctxt2’ >> qexists_tac ‘ll2’ >> fs []
       >> conj_tac >- fs [lookup_fromList2,lookup_fromList]
       >> simp [Abbr‘ctxt2’,domain_make_ctxt,set_fromNumSet,
                domain_difference,domain_toNumSet, SUBSET_DEF]
       >> match_mp_tac locals_rel_make_ctxt
       >> fs [IN_DISJOINT,set_fromNumSet,domain_difference,
              domain_toNumSet,GSYM IMP_DISJ_THM])
     >> fs [CaseEq"word_loc",CaseEq"num",CaseEq"option",CaseEq"prod",CaseEq"bool"]
     >> rveq >> fs [code_rel_def,state_rel_def]
     >> first_x_assum drule >> strip_tac >> fs []
     >> fs [find_code_def]
     >> simp [comp_func_def]
     >> qmatch_goalsub_abbrev_tac ‘comp ctxt2 _ ll2’
     >> qexists_tac ‘ctxt2’ >> qexists_tac ‘ll2’ >> fs []
     >> conj_tac >- fs [lookup_fromList2,lookup_fromList]
     >> simp [Abbr‘ctxt2’,domain_make_ctxt,set_fromNumSet,
              domain_difference,domain_toNumSet, SUBSET_DEF]
     >> match_mp_tac locals_rel_make_ctxt
     >> fs [IN_DISJOINT,set_fromNumSet,domain_difference,
            domain_toNumSet,GSYM IMP_DISJ_THM])
  >> Cases_on ‘handler’ >> fs []
  >-
   (fs [evaluate_def,add_ret_loc_def,domain_mk_new_cutset_not_empty,cut_res_def]
    >> fs [loopSemTheory.cut_state_def]
    >> Cases_on ‘domain x1 ⊆ domain s.locals’ >> fs []
    >> qpat_x_assum ‘locals_rel _ s.locals _’ assume_tac
    >> drule cut_env_mk_new_cutset
    >> rpt (disch_then drule) >> strip_tac >> fs []
    >> drule cut_env_LN_IMP >> strip_tac >> fs []
    >> (IF_CASES_TAC >> fs [] >- (rveq >> fs [flush_state_def,state_rel_def]))
    >> fs [CaseEq"prod",CaseEq"option"] >> fs [] >> rveq >> fs []
    >> rename [‘_ = (SOME res2,st)’]
    >> qmatch_goalsub_abbrev_tac ‘wordSem$evaluate (_,tt)’
    >> fs [PULL_EXISTS]
    >> Cases_on ‘res2 = Error’ >> fs []
    >> first_x_assum (qspecl_then [‘tt’,‘ctxt1’,‘Loc l0 l1’,‘l2’] mp_tac)
    >> (impl_tac >-
         (fs [Abbr‘tt’,call_env_def,push_env_def,isWord_def]
          >> pairarg_tac >> fs [dec_clock_def,loopSemTheory.dec_clock_def,state_rel_def]))
    >> strip_tac >> fs []
    >> Cases_on ‘res2’ >> fs [] >> rveq >> fs []
    >-
     (fs [Abbr‘tt’,call_env_def,push_env_def,dec_clock_def]
      >> pairarg_tac >> fs [pop_env_def,set_var_def,set_vars_def,alist_insert_def]
      >> imp_res_tac env_to_list_LN_IMP
      >> fs [domain_union,fromAList_def,domain_fromAList_toAList]
      >> fs [loopSemTheory.set_var_def,loopSemTheory.dec_clock_def]
      >> fs [state_rel_def,lookup_insert,lookup_fromAList_toAList]
      >> rename [‘find_var ctxt var_name’]
      >> ‘var_name IN domain ctxt’ by fs [loopLangTheory.acc_vars_def]
      >> simp [lookup_insert]
      >> imp_res_tac find_var_neq_0 >> fs []
      >> imp_res_tac cut_env_mk_new_cutset_IMP >> fs []
      >> match_mp_tac locals_rel_insert >> fs []
      >> fs [locals_rel_def,lookup_fromAList_toAList])
    >> qunabbrev_tac ‘tt’
    >> pop_assum mp_tac
    >> Cases_on ‘res1’ >- fs []
    >> disch_then (fn th => assume_tac (REWRITE_RULE [IMP_DISJ_THM] th))
    >> fs [] >> Cases_on ‘x’ >> fs []
    >> fs [state_rel_def]
    >> fs [call_env_def,push_env_def] >> pairarg_tac >> fs [dec_clock_def]
    >> fs [jump_exc_def,NOT_LESS]
    >> Cases_on ‘LENGTH t.stack <= t.handler’ >> fs [LASTN_ADD_CONS]
    >> simp [CaseEq"option",CaseEq"prod",CaseEq"bool",set_var_def,CaseEq"list",
             CaseEq"stack_frame"] >> rw [] >> fs [])
  >> PairCases_on ‘x’ >> fs []
  >> rpt (pairarg_tac >> fs [])
  >> fs [evaluate_def,add_ret_loc_def,domain_mk_new_cutset_not_empty,cut_res_def]
  >> fs [loopSemTheory.cut_state_def]
  >> Cases_on ‘domain x1 ⊆ domain s.locals’ >> fs []
  >> qpat_x_assum ‘locals_rel _ s.locals _’ assume_tac
  >> drule cut_env_mk_new_cutset
  >> rpt (disch_then drule) >> strip_tac >> fs []
  >> drule cut_env_LN_IMP >> strip_tac >> fs []
  >> (IF_CASES_TAC >> fs [] >- (rveq >> fs [flush_state_def,state_rel_def]))
  >> fs [CaseEq"prod",CaseEq"option"] >> fs [] >> rveq >> fs []
  >> rename [‘_ = (SOME res2,st)’]
  >> qmatch_goalsub_abbrev_tac ‘wordSem$evaluate (_,tt)’
  >> fs [PULL_EXISTS]
  >> Cases_on ‘res2 = Error’ >> fs []
  >> first_x_assum (qspecl_then [‘tt’,‘ctxt1’,‘Loc l0 l1’,‘l2’] mp_tac)
  >> (impl_tac >-
       (fs [Abbr‘tt’] >> rename [‘SOME (find_var _ _,p1,l8)’]
        >> PairCases_on ‘l8’ >> fs [call_env_def,push_env_def,isWord_def]
        >> pairarg_tac >> fs [dec_clock_def,loopSemTheory.dec_clock_def,state_rel_def]))
  >> strip_tac >> fs []
  >> Cases_on ‘res2’ >> fs [] >> rveq >> fs []
  >> fs [loopSemTheory.dec_clock_def]
  >-
   (rename [‘loopSem$set_var hvar w _’]
    >> Cases_on ‘evaluate (x2,set_var hvar w (st with locals := inter s.locals x1))’
    >> fs []
    >> Cases_on ‘q = SOME Error’ >- fs [cut_res_def] >> fs []
    >> fs [pop_env_def,Abbr‘tt’] >> fs [call_env_def,push_env_def]
    >> rename [‘SOME (find_var _ _,p1,l8)’]
    >> PairCases_on ‘l8’ >> fs [call_env_def,push_env_def]
    >> pairarg_tac >> fs [dec_clock_def,loopSemTheory.dec_clock_def]
    >> pop_assum mp_tac
    >> pairarg_tac >> fs [dec_clock_def,loopSemTheory.dec_clock_def]
    >> imp_res_tac env_to_list_LN_IMP
    >> fs [domain_union,fromAList_def,domain_fromAList_toAList]
    >> fs [set_vars_def,alist_insert_def]
    >> fs [cut_res_def]
    >> qmatch_goalsub_abbrev_tac ‘wordSem$evaluate (_,tt)’ >> strip_tac
    >> first_x_assum (qspecl_then [‘tt’,‘ctxt’,‘retv’,‘l1'’] mp_tac)
    >> impl_tac >-
     (fs [loopSemTheory.set_var_def,state_rel_def,Abbr‘tt’]
      >> qpat_x_assum ‘_ SUBSET domain ctxt’ mp_tac
      >> simp [loopLangTheory.acc_vars_def]
      >> once_rewrite_tac [acc_vars_acc]
      >> once_rewrite_tac [acc_vars_acc] >> fs [] >> strip_tac
      >> qpat_x_assum ‘no_Loops (Call _ _ _ _)’ mp_tac
      >> simp [no_Loops_def,every_prog_def,no_Loop_def] >> strip_tac
      >> imp_res_tac env_to_list_LN_IMP
      >> fs [domain_union,fromAList_def,domain_fromAList_toAList]
      >> fs [lookup_insert,lookup_fromAList,ALOOKUP_toAList]
      >> imp_res_tac find_var_neq_0 >> fs []
      >> imp_res_tac cut_env_mk_new_cutset_IMP >> fs []
      >> match_mp_tac locals_rel_insert >> fs [locals_rel_def]
      >> fs [lookup_fromAList,ALOOKUP_toAList])
    >> fs [lookup_fromAList,ALOOKUP_toAList] >> strip_tac
    >> Cases_on ‘q’ >> fs [] >> rveq >> fs []
    >-
     (rename [‘cut_state names s9’]
      >> fs [loopSemTheory.cut_state_def]
      >> Cases_on ‘domain names ⊆ domain s9.locals’ >> fs []
      >> imp_res_tac state_rel_IMP >> fs []
      >> IF_CASES_TAC
      >> fs [flush_state_def] >> rveq >> fs [] >> fs [state_rel_def,dec_clock_def]
      >> fs [loopSemTheory.dec_clock_def,Abbr‘tt’]
      >> fs [locals_rel_def,lookup_inter_alt])
    >> Cases_on ‘x’ >> fs []
    >- fs [Abbr‘tt’]
    >> pop_assum mp_tac >> rewrite_tac [IMP_DISJ_THM]
    >> IF_CASES_TAC >> fs []
    >> fs [Abbr‘tt’] >> metis_tac [])
  >> qpat_x_assum ‘∀x. _’ (assume_tac o REWRITE_RULE [IMP_DISJ_THM])
  >> rename [‘loopSem$set_var hvar w _’]
  >> Cases_on ‘evaluate (x1',set_var hvar w (st with locals := inter s.locals x1))’
  >> fs []
  >> Cases_on ‘q = SOME Error’ >- fs [cut_res_def] >> fs []
  >> fs [pop_env_def,Abbr‘tt’] >> fs [call_env_def,push_env_def]
  >> rename [‘SOME (find_var _ _,p1,l8)’]
  >> PairCases_on ‘l8’ >> fs [call_env_def,push_env_def]
  >> pairarg_tac >> fs [dec_clock_def,loopSemTheory.dec_clock_def]
  >> pop_assum mp_tac
  >> pairarg_tac >> fs [dec_clock_def,loopSemTheory.dec_clock_def]
  >> Cases_on ‘res1’ >> fs [] >> rveq >> fs []
  >> qpat_x_assum ‘∀x. _’ mp_tac
  >> simp [jump_exc_def]
  >> qmatch_goalsub_abbrev_tac ‘LASTN n1 xs1’
  >> ‘LASTN n1 xs1 = xs1’  by
    (qsuff_tac ‘n1 = LENGTH xs1’ >> fs [LASTN_LENGTH_ID]
     >> unabbrev_all_tac >> fs [])
  >> fs [] >> fs [Abbr‘n1’,Abbr‘xs1’] >> strip_tac >> rveq >> fs []
  >> imp_res_tac env_to_list_LN_IMP >> fs [fromAList_def]
  >> ‘t1.locals = fromAList (toAList env1) ∧
      t1.stack = t.stack ∧ t1.handler = t.handler’ by fs [state_component_equality]
  >> simp [domain_fromAList_toAList]
  >> strip_tac >> fs []
  >> pop_assum mp_tac >> fs [set_var_def]
  >> fs [cut_res_def]
  >> qmatch_goalsub_abbrev_tac ‘wordSem$evaluate (_,tt)’ >> strip_tac
  >> first_x_assum (qspecl_then [‘tt’,‘ctxt’,‘retv’,‘(l0,l1 + 1)’] mp_tac)
  >> impl_tac >-
   (fs [loopSemTheory.set_var_def,state_rel_def,Abbr‘tt’]
    >> qpat_x_assum ‘_ SUBSET domain ctxt’ mp_tac
    >> simp [loopLangTheory.acc_vars_def]
    >> once_rewrite_tac [acc_vars_acc]
    >> once_rewrite_tac [acc_vars_acc] >> fs [] >> strip_tac
    >> qpat_x_assum ‘no_Loops (Call _ _ _ _)’ mp_tac
    >> simp [no_Loops_def,every_prog_def,no_Loop_def] >> strip_tac
    >> fs [lookup_insert,lookup_fromAList,ALOOKUP_toAList]
    >> imp_res_tac find_var_neq_0 >> fs []
    >> imp_res_tac cut_env_mk_new_cutset_IMP >> fs []
    >> match_mp_tac locals_rel_insert >> fs [locals_rel_def]
    >> fs [lookup_insert,lookup_fromAList,ALOOKUP_toAList])
  >> fs [] >> strip_tac
  >> Cases_on ‘q’ >> fs [] >> rveq >> fs []
  >-
   (rename [‘cut_state names s9’]
    >> fs [loopSemTheory.cut_state_def]
    >> Cases_on ‘domain names ⊆ domain s9.locals’ >> fs []
    >> imp_res_tac state_rel_IMP >> fs []
    >> IF_CASES_TAC
    >> fs [flush_state_def] >> rveq >> fs [] >> fs [state_rel_def,dec_clock_def]
    >> fs [loopSemTheory.dec_clock_def,Abbr‘tt’]
    >> fs [locals_rel_def,lookup_inter_alt])
  >> pop_assum (assume_tac o REWRITE_RULE [IMP_DISJ_THM])
  >> Cases_on ‘x’ >> fs []
  >- fs [Abbr‘tt’]
  >> rveq >> fs []
  >> pop_assum mp_tac
  >> fs [Abbr‘tt’,jump_exc_def]
  >> metis_tac []
QED

Theorem compile_FFI:
  ^(get_goal "loopLang$FFI")
Proof
  rpt strip_tac >>
  fs [loopSemTheory.evaluate_def,
      comp_def, evaluate_def] >>
  fs [CaseEq "option", CaseEq "word_loc"] >>
  rveq >> fs [] >>
  fs [find_var_def, get_var_def] >>
  imp_res_tac state_rel_intro >>
  imp_res_tac locals_rel_intro >>
  res_tac >> fs [] >>
  fs [loopSemTheory.cut_state_def] >> rveq >>
  drule_all cut_env_mk_new_cutset >>
  strip_tac >> fs [] >>
  TOP_CASE_TAC >> fs [] >> rveq >> fs [] >>
  fs [state_rel_def, flush_state_def,
      loopSemTheory.call_env_def] >>
  fs [cut_env_def,cut_envs_def,cut_names_def,AllCaseEqs()] >>
  rveq >> fs [] >>
  fs [lookup_inter] >>
  TOP_CASE_TAC >>
  fs [mk_new_cutset_def]
QED

Theorem compile_Arith:
  ^(get_goal "loopLang$Arith")
Proof
  rpt strip_tac >>
  gvs [loopSemTheory.evaluate_def,
       comp_def, evaluate_def,DefnBase.one_line_ify NONE loop_arith_def,
       AllCaseEqs(),inst_def,PULL_EXISTS,get_vars_def,find_var_def,get_var_def,
       loopSemTheory.set_var_def,wordSemTheory.set_var_def,
       state_rel_def,SUBSET_DEF,loopLangTheory.acc_vars_def,
       SF DNF_ss
      ] >>
  imp_res_tac locals_rel_intro >>
  gvs[lookup_insert,lookup_insert,domain_lookup] >>
  rw[] >>
  gvs[locals_rel_def,lookup_insert] >>
  rw[] >>
  res_tac >> gvs[] >> rw[] >>
  gvs[INJ_DEF,domain_lookup,PULL_EXISTS,find_var_def]
QED

Theorem TAKE_1_word_to_bytes:
  good_dimindex(:'a) ⇒ TAKE 1 (word_to_bytes (w:'a word) F) = [get_byte 0w w F]
Proof
  rw[word_to_bytes_def,good_dimindex_def] >> rw[word_to_bytes_aux_compute]
QED

Theorem compile_ShMem:
  ^(get_goal "loopLang$ShMem")
Proof
  rpt strip_tac >>
  gvs [loopSemTheory.evaluate_def,comp_def,evaluate_def,
       DefnBase.one_line_ify NONE loopSemTheory.sh_mem_op_def,
       AllCaseEqs(),PULL_EXISTS,
       loopSemTheory.sh_mem_load_def,
       loopSemTheory.sh_mem_store_def,
       loopLangTheory.acc_vars_def,
       domain_lookup
      ] >>
  imp_res_tac comp_exp_preserves_eval >>
  gvs[DefnBase.one_line_ify NONE wordSemTheory.share_inst_def,
      PULL_EXISTS,
      sh_mem_load_def,
      sh_mem_load_byte_def,
      sh_mem_load16_def,
      sh_mem_load32_def,
      sh_mem_store_def,
      sh_mem_store_byte_def,
      sh_mem_store16_def,
      sh_mem_store32_def,
      sh_mem_set_var_def,
      find_var_def,
      state_rel_def,
      set_var_def,
      loopSemTheory.set_var_def,
      locals_rel_def,
      lookup_insert,
      get_var_def
     ] >>
  rw[] >>
  gvs[flush_state_def,loopSemTheory.call_env_def] >>
  res_tac >>
  rw[] >>
  gvs[INJ_DEF,domain_lookup, SF DNF_ss, PULL_EXISTS,find_var_def,
      TAKE_1_word_to_bytes
     ]
QED

Theorem compile_correct:
  ^(compile_correct_tm())
Proof
  match_mp_tac (the_ind_thm())
  >> EVERY (map strip_assume_tac [compile_Skip, compile_Raise,
       compile_Mark, compile_Return, compile_Assign, compile_Store,
       compile_SetGlobal, compile_Call, compile_Seq, compile_If,
       compile_FFI, compile_Loop, compile_LoadByte, compile_Arith,
       compile_Load32,
       compile_ShMem])
  >> asm_rewrite_tac [] >> rw [] >> rpt (pop_assum kall_tac)
QED

Theorem state_rel_with_clock:
  state_rel s t ==>
  state_rel (s with clock := k) (t with clock := k)
Proof
  rw [] >>
  fs [state_rel_def]
QED

Theorem locals_rel_mk_ctxt_ln:
  0 < n ==>
  locals_rel (make_ctxt n xs LN) LN lc
Proof
  rw [locals_rel_def]
  >- (
   rw [INJ_DEF] >>
   fs [find_var_def, domain_lookup] >>
   rfs [] >> rveq >>
   imp_res_tac (MP_CANON make_ctxt_inj) >>
   rfs [lookup_def])
  >- (
   CCONTR_TAC >> fs [] >>
   drule lookup_make_ctxt_range >>
   fs [lookup_def]) >>
  fs [lookup_def]
QED

(*
  initialising the compiler correctness theorem for a labeled call with
  zero arguments and no exception handler
*)
val comp_Call =
   compile_correct |> Q.SPEC ‘Call NONE (SOME start) [] NONE’

(* druling th by first rewriting it into AND_IMP_INTRO *)
fun drule0 th =
  first_assum (mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))

Theorem state_rel_imp_semantics:
  !s t start. state_rel s t ∧
  isEmpty s.locals /\ good_dimindex(:'a) ∧
  lookup 0 t.locals = SOME (Loc 1 0) (* for the returning code *) /\
  (∃(prog:'a loopLang$prog). lookup start s.code = SOME ([], prog)) /\
  semantics s start <> Fail ==>
  semantics t start = semantics s start
Proof
  rw [] >>
  ‘code_rel s.code t.code’ by
    fs [state_rel_def] >>
  drule code_rel_intro >>
  disch_then (qspecl_then [‘start’, ‘[]’, ‘prog’] mp_tac) >>
  fs [] >>
  strip_tac >>
  fs [comp_func_def] >>
  qmatch_asmsub_abbrev_tac ‘comp ctxt _ _’ >>
  reverse (Cases_on ‘semantics s start’) >> fs []
  >- (
   (* Termination case of loop semantics *)
   fs [loopSemTheory.semantics_def] >>
   pop_assum mp_tac >>
   IF_CASES_TAC >> fs [] >>
   DEEP_INTRO_TAC some_intro >> simp[] >>
   rw [] >>
   rw [wordSemTheory.semantics_def]
   >- (
    (* the fail case of word semantics *)
    qhdtm_x_assum ‘loopSem$evaluate’ kall_tac >>
    last_x_assum(qspec_then ‘k'’ mp_tac) >> simp[] >>
    (fn g => subterm (fn tm => Cases_on ‘^(assert(has_pair_type)tm)’) (#2 g) g) >>
    CCONTR_TAC >>
    drule0 comp_Call >> fs[] >>
    drule0(GEN_ALL state_rel_with_clock) >>
    disch_then(qspec_then ‘k'’ strip_assume_tac) >>
    map_every qexists_tac [‘t with clock := k'’] >>
    qexists_tac ‘ctxt’ >>
    fs [] >>
    (* what is l in comp, what is new_l in the comp for Call,
       understand how comp for Call works, its only updated for the
       return call, in the tail call the same l is passed along  *)
    Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_EXISTS] >>
    conj_tac
    >- (
     cases_on ‘q’ >> fs [] >>
     cases_on ‘x’ >> fs []) >>
    conj_tac
    >- (
     fs [Abbr ‘ctxt’] >>
     match_mp_tac locals_rel_mk_ctxt_ln >>
     fs [])
    >> (
     fs [no_Loops_def, no_Loop_def] >>
     fs [every_prog_def]) >>
    conj_tac >- fs [wordSemTheory.isWord_def] >>
    conj_tac >- fs [loopLangTheory.acc_vars_def] >>
    fs [comp_def] >>
    (* casing on the evaluation results of loopLang *)
    cases_on ‘r’ >> fs [] >>
    cases_on ‘x’ >> fs [] >> rveq >> fs [] >> (
    cases_on ‘evaluate (Call NONE (SOME start) [0] NONE,t with clock := k')’ >>
    fs [] >>
    cases_on ‘q’ >> fs [] >>
    cases_on ‘x’ >> fs [] >>
    rveq >> fs [] >>
    cases_on ‘q'’ >> fs [] >>
    cases_on ‘x’ >> fs [])) >>
   (* the termination/diverging case of word semantics *)
   DEEP_INTRO_TAC some_intro >> simp[] >>
   conj_tac
   (* the termination case of word semantics *)
   >- (
    rw [] >> fs [] >>
    drule0 comp_Call >>
    ‘r <> SOME Error’ by(CCONTR_TAC >> fs[]) >>
    simp[] >>
    drule0 (GEN_ALL state_rel_with_clock) >> simp[] >>
    disch_then (qspec_then ‘k’ mp_tac) >> simp[] >>
    strip_tac >>
    disch_then drule >>
    disch_then (qspec_then ‘ctxt’ mp_tac) >>
    fs [] >>
    Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_FORALL] >>
    impl_tac
    >- (
     conj_tac
     >- (
      fs [Abbr ‘ctxt’] >>
      match_mp_tac locals_rel_mk_ctxt_ln >>
      fs [])
     >> (
      fs [no_Loops_def, no_Loop_def] >>
      fs [every_prog_def]) >>
     fs [wordSemTheory.isWord_def, loopLangTheory.acc_vars_def]) >>
    fs [comp_def] >>
    strip_tac >>
    drule0 (GEN_ALL wordPropsTheory.evaluate_add_clock) >>
    disch_then (qspec_then ‘k'’ mp_tac) >>
    impl_tac
    >- (
     CCONTR_TAC >> fs[] >> rveq >> fs[] >> every_case_tac >> fs[]) >>
    qpat_x_assum ‘evaluate _ = (r', _)’ assume_tac >>
    drule0 (GEN_ALL wordPropsTheory.evaluate_add_clock) >>
    disch_then (qspec_then ‘k’ mp_tac) >>
    impl_tac >- (CCONTR_TAC >> fs[]) >>
    ntac 2 strip_tac >> fs[] >> rveq >> fs[] >>
    Cases_on ‘r’ >> fs[] >>
    Cases_on ‘r'’ >> fs [] >>
    Cases_on ‘x’ >> fs [] >> rveq >> fs [] >>
    fs [state_rel_def] >>
    ‘t1.ffi = t''.ffi’ by
      fs [wordSemTheory.state_accfupds, wordSemTheory.state_component_equality] >>
    qpat_x_assum ‘t1.ffi = t'.ffi’ (assume_tac o GSYM) >>
    fs []) >>
   (* the diverging case of word semantics *)
   rw[] >> fs[] >> CCONTR_TAC >> fs [] >>
   drule0 comp_Call >>
   ‘r ≠ SOME Error’ by (
     last_x_assum (qspec_then ‘k'’ mp_tac) >> simp[] >>
     rw[] >> strip_tac >> fs[]) >>
   simp [] >>
   map_every qexists_tac [‘t with clock := k’] >>
   drule0 (GEN_ALL state_rel_with_clock) >>
   disch_then(qspec_then ‘k’ strip_assume_tac) >>
   simp [] >>
   qexists_tac ‘ctxt’ >>
   Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_EXISTS] >>
   conj_tac
   >- (
    fs [Abbr ‘ctxt’] >>
    match_mp_tac locals_rel_mk_ctxt_ln >>
    fs [])
     >> (
    fs [no_Loops_def, no_Loop_def] >>
    fs [every_prog_def]) >>
   conj_tac >- fs [wordSemTheory.isWord_def] >>
   conj_tac >- fs [loopLangTheory.acc_vars_def] >>
   fs [comp_def] >>
   CCONTR_TAC >> fs [] >>
   first_x_assum (qspec_then ‘k’ mp_tac) >> simp[] >>
   first_x_assum(qspec_then ‘k’ mp_tac) >> simp[] >>
   every_case_tac >> fs[] >> rw[] >> rfs[]) >>
  (* the diverging case of loop semantics *)
  fs [loopSemTheory.semantics_def] >>
  pop_assum mp_tac >>
  IF_CASES_TAC >> fs [] >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  rw [] >>
  rw [wordSemTheory.semantics_def]
  >- (
   (* the fail case of word semantics *)
   fs[] >> rveq >> fs[] >>
   last_x_assum (qspec_then ‘k’ mp_tac) >> simp[] >>
   (fn g => subterm (fn tm => Cases_on ‘^(assert(has_pair_type)tm)’) (#2 g) g) >>
   CCONTR_TAC >>
   drule0 comp_Call >> fs[] >>
   drule0(GEN_ALL state_rel_with_clock) >>
   disch_then (qspec_then ‘k’ strip_assume_tac) >>
   map_every qexists_tac [‘t with clock := k’] >>
   fs [] >>
   qexists_tac ‘ctxt’ >>
   Ho_Rewrite.PURE_REWRITE_TAC [GSYM PULL_EXISTS] >>
   fs [] >>
   conj_tac
   >- (
    cases_on ‘q’ >> fs [] >>
    cases_on ‘x’ >> fs []) >>
   conj_tac
   >- (
    fs [Abbr ‘ctxt’] >>
    match_mp_tac locals_rel_mk_ctxt_ln >>
    fs [])
     >> (
    fs [no_Loops_def, no_Loop_def] >>
    fs [every_prog_def]) >>
   conj_tac >- fs [wordSemTheory.isWord_def] >>
   conj_tac >- fs [loopLangTheory.acc_vars_def] >>
   fs [comp_def] >>
   CCONTR_TAC >> fs [] >>
   cases_on ‘q’ >> fs [] >>
   cases_on ‘x’ >> fs []) >>
  (* the termination/diverging case of word semantics *)
  DEEP_INTRO_TAC some_intro >> simp[] >>
  conj_tac
  (* the termination case of word semantics *)
  >- (
   rw [] >>  fs[] >>
   qpat_x_assum ‘∀x y. _’ (qspec_then ‘k’ mp_tac)>>
   (fn g => subterm (fn tm => Cases_on ‘^(assert(has_pair_type)tm)’) (#2 g) g) >>
   strip_tac >>
   drule0 comp_Call >> fs [] >>
   drule0(GEN_ALL state_rel_with_clock) >>
   disch_then(qspec_then ‘k’ strip_assume_tac) >>
   map_every qexists_tac [‘t with clock := k’] >>
   fs [] >>
   qexists_tac ‘ctxt’ >>
   Ho_Rewrite.PURE_REWRITE_TAC [GSYM PULL_EXISTS] >>
   fs [] >>
   conj_tac
   >- (
    cases_on ‘q’ >> fs [] >>
    cases_on ‘x’ >> fs [] >>
    last_x_assum (qspec_then ‘k’ mp_tac) >>
    fs []) >>
   conj_tac
   >- (
    fs [Abbr ‘ctxt’] >>
    match_mp_tac locals_rel_mk_ctxt_ln >>
    fs [])
     >> (
    fs [no_Loops_def, no_Loop_def] >>
    fs [every_prog_def]) >>
   conj_tac >- fs [wordSemTheory.isWord_def] >>
   conj_tac >- fs [loopLangTheory.acc_vars_def] >>
   fs [comp_def] >>
   CCONTR_TAC >> fs [] >>
   first_x_assum(qspec_then ‘k’ mp_tac) >>
   fsrw_tac[ARITH_ss][] >>
   first_x_assum(qspec_then ‘k’ mp_tac) >>
   fsrw_tac[ARITH_ss][] >>
   every_case_tac >> fs[] >> rfs[] >> rw[]>> fs[]) >>
  (* the diverging case of word semantics *)
  rw [] >>
  qmatch_abbrev_tac ‘build_lprefix_lub l1 = build_lprefix_lub l2’ >>
  ‘(lprefix_chain l1 ∧ lprefix_chain l2) ∧ equiv_lprefix_chain l1 l2’
    suffices_by metis_tac[build_lprefix_lub_thm,lprefix_lub_new_chain,unique_lprefix_lub] >>
  conj_asm1_tac
  >- (
   UNABBREV_ALL_TAC >>
   conj_tac >>
   Ho_Rewrite.ONCE_REWRITE_TAC[GSYM o_DEF] >>
   REWRITE_TAC[IMAGE_COMPOSE] >>
   match_mp_tac prefix_chain_lprefix_chain >>
   simp[prefix_chain_def,PULL_EXISTS] >>
   qx_genl_tac [‘k1’, ‘k2’] >>
   qspecl_then [‘k1’, ‘k2’] mp_tac LESS_EQ_CASES >>
   simp[LESS_EQ_EXISTS] >>
   rw [] >>
   assume_tac (INST_TYPE [``:'a``|->``:'a``,
                          ``:'b``|->``:'b``]
               loopPropsTheory.evaluate_add_clock_io_events_mono) >>
   assume_tac (INST_TYPE [``:'a``|->``:'a``,
                          ``:'b``|->``:'c``,
                          ``:'c``|->``:'b``]
               wordPropsTheory.evaluate_add_clock_io_events_mono) >>
   first_assum (qspecl_then
                [‘Call NONE (SOME start) [0] NONE’, ‘t with clock := k1’, ‘p’] mp_tac) >>
   first_assum (qspecl_then
                [‘Call NONE (SOME start) [0] NONE’, ‘t with clock := k2’, ‘p’] mp_tac) >>
   first_assum (qspecl_then
                [‘Call NONE (SOME start) [] NONE’, ‘s with clock := k1’, ‘p’] mp_tac) >>
   first_assum (qspecl_then
                [‘Call NONE (SOME start) [] NONE’, ‘s with clock := k2’, ‘p’] mp_tac) >>
   fs []) >>
  simp [equiv_lprefix_chain_thm] >>
  fs [Abbr ‘l1’, Abbr ‘l2’]  >> simp[PULL_EXISTS] >>
  pop_assum kall_tac >>
  simp[LNTH_fromList,PULL_EXISTS] >>
  simp[GSYM FORALL_AND_THM] >>
  rpt gen_tac >>
  reverse conj_tac >> strip_tac
  >- (
   qmatch_assum_abbrev_tac`n < LENGTH (_ (_ (SND p)))` >>
   Cases_on`p` >> pop_assum(assume_tac o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
   drule0 comp_Call >>
   simp[GSYM AND_IMP_INTRO,RIGHT_FORALL_IMP_THM] >>
   impl_tac
   >- (
    cases_on ‘q’ >> fs [] >>
    cases_on ‘x’ >> fs [] >>
    last_x_assum (qspec_then ‘k’ mp_tac) >>
    fs []) >>
   drule0(GEN_ALL state_rel_with_clock) >>
   disch_then(qspec_then`k`strip_assume_tac) >>
   disch_then drule0 >>
   simp[] >>
   disch_then (qspec_then ‘ctxt’ mp_tac) >>
   impl_tac
   >- (
    fs [Abbr ‘ctxt’] >>
    match_mp_tac locals_rel_mk_ctxt_ln >>
    fs []) >>
   impl_tac >- (
    fs [no_Loops_def, no_Loop_def] >>
    fs [every_prog_def]) >>
   impl_tac >- fs [wordSemTheory.isWord_def] >>
   impl_tac >- fs [loopLangTheory.acc_vars_def] >>
   fs [comp_def] >>
   strip_tac >>
   qexists_tac`k`>>simp[]>>
   first_x_assum(qspec_then`k`mp_tac)>>simp[]>>
   BasicProvers.TOP_CASE_TAC >> simp[] >>
   fs [state_rel_def]) >>
  (fn g => subterm (fn tm => Cases_on`^(Term.subst[{redex = #1(dest_exists(#2 g)), residue = ``k:num``}]
                                        (assert(has_pair_type)tm))`) (#2 g) g) >>
  drule0 comp_Call >>
  simp[GSYM AND_IMP_INTRO,RIGHT_FORALL_IMP_THM] >>
  impl_tac
  >- (
   cases_on ‘q’ >> fs [] >>
   cases_on ‘x’ >> fs [] >>
   last_x_assum (qspec_then ‘k’ mp_tac) >>
   fs []) >>
  drule0(GEN_ALL state_rel_with_clock) >>
  disch_then(qspec_then`k`strip_assume_tac) >>
  disch_then drule0 >>
  simp[] >>
  disch_then (qspec_then ‘ctxt’ mp_tac) >>
  impl_tac
  >- (
   fs [Abbr ‘ctxt’] >>
   match_mp_tac locals_rel_mk_ctxt_ln >>
   fs []) >>
  impl_tac
  >- (
   fs [no_Loops_def, no_Loop_def] >>
   fs [every_prog_def]) >>
  impl_tac >- fs [wordSemTheory.isWord_def] >>
  impl_tac >- fs [loopLangTheory.acc_vars_def] >>
  fs [comp_def] >>
  strip_tac >>
  assume_tac (INST_TYPE [``:'a``|->``:'a``,
                         ``:'b``|->``:'c``,
                         ``:'c``|->``:'b``]
              wordPropsTheory.evaluate_io_events_mono) >>
  first_x_assum (qspecl_then
               [‘Call NONE (SOME start) [0] NONE’, ‘t with clock := k’] mp_tac) >>
  strip_tac >> fs [] >>
  qexists_tac ‘k’ >> fs [] >>
  fs [state_rel_def] >>
  first_x_assum drule >>
  gvs[]
QED

Definition st_rel_def:
  st_rel s t prog <=>
  let c = fromAList (loop_remove$comp_prog prog);
      s' = s with code := c in
    loop_removeProof$state_rel s s' ∧
    state_rel s' t /\
    code_rel c t.code
End

Theorem st_rel_intro:
  st_rel s t prog ==>
  let c = fromAList (loop_remove$comp_prog prog);
      s' = s with code := c in
    loop_removeProof$state_rel s s' ∧
    state_rel s' t /\
    code_rel c t.code
Proof
  rw [] >>
  fs [st_rel_def] >>
  metis_tac []
QED

Theorem first_compile_prog_all_distinct:
  !prog. ALL_DISTINCT (MAP FST prog) ==>
    ALL_DISTINCT (MAP FST (compile_prog prog))
Proof
  rw [] >>
  fs [loop_to_wordTheory.compile_prog_def] >>
  fs [MAP_MAP_o] >>
  qmatch_goalsub_abbrev_tac ‘MAP ls _’ >>
  ‘MAP ls prog = MAP FST prog’ by (
    fs [Abbr ‘ls’] >>
    fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
    rw [] >>
    cases_on ‘EL n prog’ >> fs [] >>
    cases_on ‘r’ >> fs []) >>
  fs []
QED

Theorem first_compile_all_distinct:
  !prog. ALL_DISTINCT (MAP FST prog) ==>
    ALL_DISTINCT (MAP FST (compile prog))
Proof
  rw [] >>
  fs [compile_def] >>
  match_mp_tac first_compile_prog_all_distinct >>
  match_mp_tac first_comp_prog_all_distinct >>
  fs []
QED

Theorem mem_prog_mem_compile_prog:
  !prog name params body.
     MEM (name,params,body) prog ==>
     MEM (name,LENGTH params + 1,comp_func name params body)
         (compile_prog prog)
Proof
  rw [] >>
  fs [MEM_EL] >>
  qexists_tac ‘n’ >>
  fs [compile_prog_def] >>
  qmatch_goalsub_abbrev_tac ‘MAP ls _’ >>
  ‘EL n (MAP ls prog) = ls (EL n prog)’ by (
    match_mp_tac EL_MAP >>
    fs []) >>
  fs [Abbr ‘ls’] >>
  cases_on ‘EL n prog’ >> fs [] >>
  cases_on ‘r’ >> fs []
QED

Theorem lookup_prog_some_lookup_compile_prog:
  !prog name params body. lookup name (fromAList prog) = SOME (params,body) ==>
  lookup name (fromAList (compile_prog prog)) =
  SOME (LENGTH params + 1,comp_func name params body)
Proof
  Induct >> rw []
  >- fs [compile_prog_def, fromAList_def, lookup_def] >>
  fs [compile_prog_def] >>
  cases_on ‘h’ >> fs [] >>
  cases_on ‘r’ >> fs [] >>
  fs [fromAList_def] >>
  fs [lookup_insert] >>
  TOP_CASE_TAC >> fs []
QED

Theorem fstate_rel_imp_semantics:
  !s t loop_code start prog.
  st_rel s t loop_code ∧
  isEmpty s.locals ∧
  s.code = fromAList loop_code ∧
  t.code = fromAList (loop_to_word$compile loop_code) ∧
  lookup 0 t.locals = SOME (Loc 1 0) (* for the returning code *) ∧
  lookup start s.code = SOME ([], (prog:'a loopLang$prog)) ∧
  good_dimindex(:'a) ∧
  semantics s start <> Fail ==>
  semantics t start = semantics s start
Proof
  rw [] >>
  drule st_rel_intro >>
  strip_tac >> fs [] >>
  drule loop_removeProofTheory.state_rel_imp_semantics >>
  disch_then (qspecl_then [‘start’, ‘loop_code’] mp_tac) >>
  fs [] >>
  strip_tac >>
  pop_assum (assume_tac o GSYM) >>
  fs [] >>
  pop_assum kall_tac >>
  drule state_rel_imp_semantics >>
  disch_then (qspecl_then [‘start’] mp_tac) >>
  (* might need to replace prog with something else *)
  fs [] >>
  fs [loop_removeProofTheory.state_rel_def] >> rveq >>
  res_tac >> fs [] >>
  cases_on ‘(comp (start,[],prog) init)’ >>
  fs [has_code_def] >>
  fs [loop_removeTheory.comp_def] >>
  cases_on ‘(comp_with_loop (Fail,Fail) prog Fail init)’ >>
  fs [] >>
  cases_on ‘r'’ >> fs [] >>
  rveq >> fs [EVERY_DEF]
QED

(*** no_install/no_alloc/no_mt lemmas ***)

Theorem loop_to_word_comp_not_created:
  (!x. (case x of ShareInst _ _ _ => T | Call _ _ _ _ => T
        | LocValue _ _ => T | _ => F) ==>
    P x) ==>
  !ctxt prog l wprog l2.
  comp ctxt prog l = (wprog, l2) ==>
  not_created_subprogs P wprog
Proof
  disch_tac
  \\ recInduct comp_ind
  \\ rw [comp_def]
  \\ gs [not_created_subprogs_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ gs [AllCaseEqs (), UNCURRY_eq_pair]
  \\ gvs [not_created_subprogs_def]
  \\ every_case_tac \\ fs []
QED

Theorem loop_to_word_comp_func_not_created:
  (!x. (case x of ShareInst _ _ _ => T | Call _ _ _ _ => T
        | LocValue _ _ => T | _ => F) ==>
    P x) ==>
  !body name params. not_created_subprogs P (comp_func name params body)
Proof
  rw[comp_func_def]
  \\ simp [Q.prove (`!x. FST x = (\(y, z). y) x`, simp [FORALL_PROD])]
  \\ pairarg_tac \\ fs []
  \\ metis_tac [loop_to_word_comp_not_created]
QED

Theorem loop_to_word_compile_not_created:
  !pan_prog.
  (!x. (case x of ShareInst _ _ _ => T | Call _ _ _ _ => T
        | LocValue _ _ => T | _ => F) ==>
    P x) ==>
  EVERY (not_created_subprogs P) (MAP (SND o SND) (compile_prog pan_prog))
Proof
  Induct>>
  gs[compile_def, compile_prog_def]>>
  strip_tac>>pairarg_tac>>gs[loop_to_word_comp_func_not_created]
QED

Theorem loop_to_word_compile_not_created_MEM[local]:
  MEM (a, b, p) (compile_prog pan_prog) ==>
  (!x. (case x of ShareInst _ _ _ => T | Call _ _ _ _ => T
        | LocValue _ _ => T | _ => F) ==>
    P x) ==>
  not_created_subprogs P p
Proof
  qspec_then `pan_prog` mp_tac loop_to_word_compile_not_created
  \\ rw [] \\ fs [EVERY_MAP]
  \\ fs [EVERY_MEM, FORALL_PROD]
  \\ metis_tac []
QED

Theorem loop_compile_no_install_code:
  no_install_code (fromAList (compile prog))
Proof
  gs[compile_def]>>
  rw[no_install_code_def, no_install_subprogs_def]>>
  gs[lookup_fromAList, EVERY_MEM, MEM_MAP]>>
  drule ALOOKUP_MEM>>strip_tac>>
  drule_then irule loop_to_word_compile_not_created_MEM>>
  simp []
QED

Theorem loop_compile_no_alloc_code:
  no_alloc_code (fromAList (compile prog))
Proof
  gs[compile_def]>>
  rw[no_alloc_code_def, no_alloc_subprogs_def]>>
  gs[lookup_fromAList, EVERY_MEM, MEM_MAP]>>
  drule ALOOKUP_MEM>>strip_tac>>
  drule_then irule loop_to_word_compile_not_created_MEM>>
  simp []
QED

Theorem loop_compile_no_mt_code:
  no_mt_code (fromAList (compile prog))
Proof
  gs[compile_def]>>
  rw[no_mt_code_def, no_mt_subprogs_def]>>
  gs[lookup_fromAList, EVERY_MEM, MEM_MAP]>>
  drule ALOOKUP_MEM>>strip_tac>>
  drule_then irule loop_to_word_compile_not_created_MEM>>
  simp []
QED

(*** loop_to_word good_handlers ***)

Theorem comp_l_invariant:
  ∀ctxt prog l prog' l'. comp ctxt prog l = (prog',l') ⇒ FST l' = FST l
Proof
  ho_match_mp_tac comp_ind >>
  rw[comp_def] >>
  gvs[ELIM_UNCURRY,PULL_FORALL,AllCaseEqs()] >> metis_tac[PAIR]
QED

Theorem good_handlers_comp:
  ∀ctxt prog l. good_handlers (FST l) (FST (comp ctxt prog l))
Proof
  ho_match_mp_tac comp_ind >>
  rw[good_handlers_def,
     comp_def] >>
  gvs[ELIM_UNCURRY] >>
  rpt(PURE_TOP_CASE_TAC >> gvs[]) >>
  metis_tac[PAIR,FST,SND,comp_l_invariant]
QED

Theorem loop_to_word_good_handlers:
  (compile_prog prog) = prog' ⇒
  EVERY (λ(n,m,pp). good_handlers n pp) prog'
Proof
  fs[compile_def,
     compile_prog_def,
     comp_func_def]>>
  rw[]>>
  fs[EVERY_MEM,MEM_MAP,PULL_EXISTS]>>
  PairCases >>
  rw[] >>
  pop_assum kall_tac >>
  rename1 ‘comp ctxt prog’ >>
  rename1 ‘(n,m)’ >>
  metis_tac[PAIR,FST,SND,good_handlers_comp]
QED

(**** lab_pres for loop_to_word ****)

Theorem loop_to_word_comp_SND_LE:
  ∀ctxt prog l p r.
    comp ctxt prog l = (p,r) ⇒
    SND l ≤ SND r
Proof
  ho_match_mp_tac loop_to_wordTheory.comp_ind>>
  rw[loop_to_wordTheory.comp_def]>>
  rpt (FULL_CASE_TAC>>gs[])>>gvs[]>>
  pairarg_tac>>gs[]>>pairarg_tac>>gs[]>>
  rveq>>gs[]
QED

Theorem loop_to_word_comp_extract_labels_len:
  ∀ctxt prog l p r.
    comp ctxt prog l = (p,r) ⇒
    LENGTH (extract_labels p) = SND r - SND l
Proof
  ho_match_mp_tac loop_to_wordTheory.comp_ind>>
  rw[loop_to_wordTheory.comp_def]>>
  gs[extract_labels_def]
  >- gvs[AllCaseEqs(),extract_labels_def]
  >- (pairarg_tac>>gs[]>>
      pairarg_tac>>gs[]>>
      rveq>>gs[extract_labels_def]>>
      drule loop_to_word_comp_SND_LE>>strip_tac>>
      qpat_x_assum ‘_= (_, l')’ assume_tac>>
      drule loop_to_word_comp_SND_LE>>strip_tac>>
      gs[])
  >- (pairarg_tac>>gs[]>>
      pairarg_tac>>gs[]>>
      rveq>>gs[extract_labels_def]>>
      drule loop_to_word_comp_SND_LE>>strip_tac>>
      qpat_x_assum ‘_= (_, l')’ assume_tac>>
      drule loop_to_word_comp_SND_LE>>strip_tac>>
      gs[])>>
  rpt (FULL_CASE_TAC>>gs[])>>
  rveq>>gs[extract_labels_def]
  >~[‘LENGTH _ = 1’]>- (Cases_on ‘l’>>gs[])>>
  pairarg_tac>>gs[]>>pairarg_tac>>gs[]>>
  rveq>>gs[extract_labels_def]>>
  Cases_on ‘l’>>gs[]>>
  rename1 ‘comp _ _ l1 = (_, l1')’>>
  Cases_on ‘l1'’>>gs[]>>
  drule loop_to_word_comp_SND_LE>>strip_tac>>gs[]>>
  qpat_x_assum ‘_= (_, l1)’ assume_tac>>
  drule loop_to_word_comp_SND_LE>>strip_tac>>gs[]
QED

Theorem loop_to_word_comp_extract_labels:
  ∀ctxt prog l p l'.
    loop_to_word$comp ctxt prog l = (p,l') ⇒
    EVERY (λ(q, r). q = FST l ∧ SND l ≤ r ∧ r < SND l') (extract_labels p)
Proof
  ho_match_mp_tac loop_to_wordTheory.comp_ind>>
  rw[loop_to_wordTheory.comp_def]>>
  gs[extract_labels_def]
  >- gvs[AllCaseEqs(),extract_labels_def]
  >- (pairarg_tac>>gs[]>>
      pairarg_tac>>gs[]>>
      rveq>>gs[extract_labels_def]>>
      ‘FST l'' = FST l’ by metis_tac[comp_l_invariant]>>gs[]>>
      drule loop_to_word_comp_SND_LE>>strip_tac>>
      qpat_x_assum ‘_= (_, l'')’ assume_tac>>
      drule loop_to_word_comp_SND_LE>>strip_tac>>
      conj_tac>>gs[EVERY_EL]>>strip_tac>>strip_tac>>pairarg_tac>>gs[]
      >- (first_x_assum $ qspec_then ‘n’ assume_tac>>gs[])>>
      last_x_assum $ qspec_then ‘n’ assume_tac>>gs[])
  >- (pairarg_tac>>gs[]>>
      pairarg_tac>>gs[]>>
      rveq>>gs[extract_labels_def]>>
      ‘FST l'' = FST l’ by metis_tac[comp_l_invariant]>>gs[]>>
      drule loop_to_word_comp_SND_LE>>strip_tac>>
      qpat_x_assum ‘_= (_, l'')’ assume_tac>>
      drule loop_to_word_comp_SND_LE>>strip_tac>>
      conj_tac>>gs[EVERY_EL]>>strip_tac>>strip_tac>>pairarg_tac>>gs[]
      >- (first_x_assum $ qspec_then ‘n’ assume_tac>>gs[])>>
      last_x_assum $ qspec_then ‘n’ assume_tac>>gs[])>>
  gs[CaseEq"option",CaseEq"prod"]>>rpt (pairarg_tac>>gs[])>>
  gvs[extract_labels_def]>>
  Cases_on ‘l’>>gs[]>>
  rename1 ‘comp _ _ l1 = (_, l1')’>>
  Cases_on ‘l1'’>>gs[]>>
  drule loop_to_word_comp_SND_LE>>strip_tac>>gs[]>>
  qpat_x_assum ‘_= (_, l1)’ assume_tac>>
  drule loop_to_word_comp_SND_LE>>strip_tac>>gs[]>>
  Cases_on ‘l1’>>gs[]>>
  drule comp_l_invariant>>gs[]>>
  strip_tac>>gs[]>>
  qpat_x_assum ‘_= (_, _, r')’ assume_tac>>
  drule comp_l_invariant>>gs[]>>strip_tac>>
  conj_tac>>gs[EVERY_EL]>>strip_tac>>strip_tac>>pairarg_tac>>gs[]
  >- (last_x_assum $ qspec_then ‘n’ assume_tac>>gs[])>>
  first_x_assum $ qspec_then ‘n’ assume_tac>>gs[]
QED

Theorem loop_to_word_comp_ALL_DISTINCT:
  ∀ctxt prog l p r.
    comp ctxt prog l = (p,r) ⇒
    ALL_DISTINCT (extract_labels p)
Proof
  ho_match_mp_tac loop_to_wordTheory.comp_ind>>
  rw[loop_to_wordTheory.comp_def]>>
  gs[extract_labels_def]
  >- gvs[AllCaseEqs(),extract_labels_def]
  >- (pairarg_tac>>gs[]>>
      pairarg_tac>>gs[]>>
      rveq>>
      gs[extract_labels_def,
         ALL_DISTINCT_APPEND]>>rpt strip_tac>>
      drule loop_to_word_comp_extract_labels>>strip_tac>>
      drule loop_to_word_comp_SND_LE>>strip_tac>>
      qpat_x_assum ‘_= (_, l')’ assume_tac>>
      drule loop_to_word_comp_extract_labels>>strip_tac>>
      drule loop_to_word_comp_SND_LE>>strip_tac>>
      gs[EVERY_MEM]>>
      rpt (first_x_assum $ qspec_then ‘e’ assume_tac)>>gs[]>>
      Cases_on ‘e’>>gs[])
  >- (pairarg_tac>>gs[]>>
      pairarg_tac>>gs[]>>
      rveq>>
      gs[extract_labels_def,
         ALL_DISTINCT_APPEND]>>rpt strip_tac>>
      drule loop_to_word_comp_extract_labels>>strip_tac>>
      drule loop_to_word_comp_SND_LE>>strip_tac>>
      qpat_x_assum ‘_= (_, l')’ assume_tac>>
      drule loop_to_word_comp_extract_labels>>strip_tac>>
      drule loop_to_word_comp_SND_LE>>strip_tac>>
      gs[EVERY_MEM]>>
      rpt (first_x_assum $ qspec_then ‘e’ assume_tac)>>gs[]>>
      Cases_on ‘e’>>gs[])>>
  rename1 ‘_ = (q, r)’>>
  gs[CaseEq"option", CaseEq"prod"]>>
  rpt (pairarg_tac>>gs[])>>
  gvs[extract_labels_def]>>
  Cases_on ‘l’>>gs[]>>
  rename1 ‘comp _ _ l1 = (_, l1')’>>
  Cases_on ‘l1'’>>gs[]>>
  rename1 ‘comp _ _ l1 = (_, q', r')’>>
  drule loop_to_word_comp_extract_labels>>strip_tac>>
  drule loop_to_word_comp_SND_LE>>strip_tac>>
  rename1 ‘_= (p1', l1)’>>
  qpat_x_assum ‘_= (p1', l1)’ assume_tac>>
  drule loop_to_word_comp_extract_labels>>strip_tac>>
  drule loop_to_word_comp_SND_LE>>strip_tac>>
  gs[]>>
  Cases_on ‘l1’>>gs[]>>
  gs[ALL_DISTINCT_APPEND, EVERY_MEM]>>rw[]
  >- (last_x_assum $ qspec_then ‘(q, r)’ assume_tac>>gs[])
  >- (first_x_assum $ qspec_then ‘(q, r)’ assume_tac>>gs[])
  >- (last_x_assum $ qspec_then ‘(q', r')’ assume_tac>>gs[])
  >- (first_x_assum $ qspec_then ‘(q', r')’ assume_tac>>gs[])>>
  first_x_assum $ qspec_then ‘e’ assume_tac>>gs[]>>
  first_x_assum $ qspec_then ‘e’ assume_tac>>gs[]>>
  Cases_on ‘e’>>gs[]
QED

Theorem loop_to_word_comp_func_lab_pres:
    comp_func n' params body = p ⇒
    (∀n. n < LENGTH (extract_labels p) ⇒
         (λ(l1,l2). l1 = n' ∧ l2 ≠ 0 ∧ l2 ≠ 1)
         (EL n (extract_labels p))) ∧
    ALL_DISTINCT (extract_labels p)
Proof
  strip_tac>>
  gs[loop_to_wordTheory.comp_func_def]>>
  qmatch_asmsub_abbrev_tac ‘FST cmp = _’>>
  Cases_on ‘cmp’>>gs[]>>
  drule loop_to_word_comp_extract_labels>>strip_tac>>
  drule loop_to_word_comp_ALL_DISTINCT>>strip_tac>>
  gs[]>>rpt strip_tac>>
  gs[EVERY_EL]>>
  first_x_assum $ qspec_then ‘n’ assume_tac>>gs[]>>
  pairarg_tac>>gs[]
QED

Theorem loop_to_word_compile_prog_lab_pres:
  loop_to_word$compile_prog prog = prog' ⇒
  EVERY
  (λ(n,m,p).
     (let
        labs = extract_labels p
      in
        EVERY (λ(l1,l2). l1 = n ∧ l2 ≠ 0 ∧ l2 ≠ 1) labs ∧
        ALL_DISTINCT labs)) prog'
Proof
  strip_tac>>
  gs[loop_to_wordTheory.compile_prog_def]>>
  gs[EVERY_EL]>>ntac 2 strip_tac>>
  pairarg_tac>>gs[]>>rveq>>gs[EL_MAP]>>
  pairarg_tac>>gs[]>>
  drule loop_to_word_comp_func_lab_pres>>rw[]
QED

(* first_name offset *)

Theorem loop_to_word_compile_prog_FST_eq:
  compile_prog prog = prog' ⇒
  MAP FST prog' = MAP FST prog
Proof
  strip_tac>>gs[loop_to_wordTheory.compile_prog_def]>>
  ‘LENGTH prog = LENGTH prog'’ by (rveq>>gs[LENGTH_MAP])>>
  gs[MAP_EQ_EVERY2]>>gs[LIST_REL_EL_EQN]>>
  strip_tac>>strip_tac>>gs[]>>rveq>>gs[EL_MAP]>>
  pairarg_tac>>gs[]
QED

Theorem loop_to_word_compile_prog_lab_min:
  compile_prog prog = prog' ∧
  EVERY (λp. x ≤ FST p) prog ⇒
  EVERY (λp. x ≤ FST p) prog'
Proof
  strip_tac>>
  drule loop_to_word_compile_prog_FST_eq>>gs[GSYM EVERY_MAP]
QED

Theorem loop_to_word_compile_lab_min:
  compile prog = prog' ∧
  EVERY (λp. x ≤ FST p) prog ⇒
  EVERY (λp. x ≤ FST p) prog'
Proof
  strip_tac>>
  gs[loop_to_wordTheory.compile_def]>>
  drule_then irule loop_to_word_compile_prog_lab_min>>
  gs[]>>irule loop_removeProofTheory.loop_remove_comp_prog_lab_min>>
  metis_tac[]
QED

(* inst_ok_less *)

Theorem full_imp_inst_ok_less:
  ∀c prog.
    full_inst_ok_less c prog ⇒
    every_inst (inst_ok_less c) prog
Proof
  recInduct full_inst_ok_less_ind>>
  rw[full_inst_ok_less_def,
     inst_ok_less_def,
     every_inst_def]>>
  Cases_on ‘ret’>-gs[]>>
  rename1 ‘SOME x’>>PairCases_on ‘x’>>gs[]>>
  Cases_on ‘handler’>-gs[]>>
  rename1 ‘SOME x’>>PairCases_on ‘x’>>gs[]
QED

(* TODO: move to loopProps *)
Definition loop_inst_ok_def:
  (loop_inst_ok c (Arith (LDiv r1 r2 r3)) ⇔ c.ISA ∈ {ARMv8; MIPS; RISC_V}) ∧
  (loop_inst_ok c (Arith (LLongMul r1 r2 r3 r4)) ⇔
     (c.ISA = ARMv7 ⇒ r1 ≠ r2) ∧
     (c.ISA = ARMv8 ∨ c.ISA = RISC_V ∨ c.ISA = Ag32 ⇒ r1 ≠ r3 ∧ r1 ≠ r4)) ∧
  (loop_inst_ok c (Arith (LLongDiv r1 r2 r3 r4 r5)) ⇔ c.ISA = x86_64) ∧
  (loop_inst_ok c _ ⇔ T)
End

Theorem loop_to_word_comp_every_inst_ok_less:
  ∀ctxt prog l.
    byte_offset_ok c 0w ∧ addr_offset_ok c 0w ∧
    every_prog (loop_inst_ok c) prog ∧
    domain(acc_vars prog LN) ⊆ domain ctxt ∧
    INJ (find_var ctxt) (domain ctxt) 𝕌(:num) ∧
    (∀n m. lookup n ctxt = SOME m ⇒ m ≠ 0)
    ⇒
    every_inst (inst_ok_less c) (FST (comp ctxt prog l))
Proof
  ho_match_mp_tac loop_to_wordTheory.comp_ind >>
  rw[loop_to_wordTheory.comp_def,
     every_inst_def,
     inst_ok_less_def,
     every_prog_def,DefnBase.one_line_ify NONE loop_inst_ok_def,
     loopLangTheory.acc_vars_def
     ]
  >~ [‘loop_arith_CASE arith’] >-
   (Cases_on ‘arith’ >>
    gvs[every_inst_def,inst_ok_less_def] >>
    rw[] >>
    res_tac >>
    fs[INJ_DEF]
    >- (spose_not_then strip_assume_tac \\ res_tac \\ simp[]) >>
    rename1 ‘_ ≠ find_var _ nm’ >>
    Cases_on ‘nm ∈ domain ctxt’ >- metis_tac[] >>
    fs[GSYM lookup_NONE_domain] >>
    fs[find_var_def,domain_lookup] >>
    metis_tac[SOME_11]) >>
  TRY (Cases_on ‘ret’>-gs[every_inst_def]>>
       rename1 ‘SOME x’>>PairCases_on ‘x’>>gs[]>>
       Cases_on ‘handler’>-gs[every_inst_def]>>
       rename1 ‘SOME x’>>PairCases_on ‘x’)>>
  gs[]>>rpt (pairarg_tac>>gs[])>>
  gs[every_inst_def,
     PURE_ONCE_REWRITE_CONV [acc_vars_acc] “domain(acc_vars (x:'a loopLang$prog) (acc_vars (y:'a loopLang$prog) z))”,
     PURE_ONCE_REWRITE_CONV [acc_vars_acc] “domain(acc_vars (x:'a loopLang$prog) (insert y () z))”
     ]
QED

Theorem loop_to_word_comp_func_every_inst_ok_less:
  comp_func n params body = p ∧
  every_prog (loop_inst_ok c) body ∧
  addr_offset_ok c 0w ∧ byte_offset_ok c 0w ⇒
  every_inst (inst_ok_less c) p
Proof
  strip_tac>>gs[loop_to_wordTheory.comp_func_def]>>
  rveq>>
  drule_then irule loop_to_word_comp_every_inst_ok_less >>
  assume_tac $ DECIDE “0 < 2:num” >>
  dxrule locals_rel_mk_ctxt_ln >>
  qmatch_goalsub_abbrev_tac ‘make_ctxt _ lista’ >>
  disch_then $ qspecl_then [‘lista’] mp_tac >>
  rw[locals_rel_def,Abbr ‘lista’,domain_make_ctxt] >>
  rw[SUBSET_DEF,set_fromNumSet,domain_difference,domain_toNumSet]
QED

Theorem loop_to_word_compile_prog_every_inst_ok_less:
  compile_prog lprog = wprog0 ∧
  byte_offset_ok c 0w ∧ addr_offset_ok c 0w ∧
  EVERY (λ(n,params,body). every_prog (loop_inst_ok c) body) lprog
  ⇒
  EVERY (λ(n,m,p). every_inst (inst_ok_less c) p) wprog0
Proof
  strip_tac>>gs[loop_to_wordTheory.compile_prog_def]>>
  rveq>>gs[EVERY_MAP, EVERY_EL]>>rpt strip_tac>>
  pairarg_tac>>gs[]>>
  pairarg_tac>>gs[]>>
  drule_then irule loop_to_word_comp_func_every_inst_ok_less>>
  gs[] >>
  first_x_assum drule >>
  simp[]
QED

Theorem comp_with_loop_alt_ind[local] =
  loop_removeTheory.comp_with_loop_ind
    |> PURE_REWRITE_RULE [METIS_PROVE [] “(a,b) = comp_with_loop x y z w ⇔ comp_with_loop x y z w = (a,b)”,
                          METIS_PROVE [] “(a,b) = store_cont x y z ⇔ store_cont x y z = (a,b)”];


Theorem eq_forall_elim[local]:
  (∀x. y = x ⇒ P x) = P y
Proof
  metis_tac[]
QED

Theorem every_loop_inst_ok_comp_no_loop:
  ∀p prog.
    every_prog (loop_inst_ok c) prog ∧
    every_prog (loop_inst_ok c) (FST p) ∧
    every_prog (loop_inst_ok c) (SND p)
    ⇒
    every_prog (loop_inst_ok c) (comp_no_loop p prog)
Proof
  ho_match_mp_tac loop_removeTheory.comp_no_loop_ind \\
  rw[every_prog_def,loop_inst_ok_def, loop_removeTheory.comp_no_loop_def] \\
  Cases_on ‘handler’ \\ gvs[] \\
  PairCases_on ‘x’ \\ gvs[]
QED

fun separate_simp_tac ss = POP_ASSUM_LIST (fn assms =>
  simp ss
  \\ MAP_EVERY (fn t => assume_tac (SIMP_RULE (srw_ss ()) ss t)) assms
  );

Theorem every_loop_inst_ok_comp_lemma:
  ∀p prog cont s body n funs.
    comp_with_loop p prog cont s = (body,n,funs) ∧
    every_prog (loop_inst_ok c) prog ∧
    every_prog (loop_inst_ok c) cont ∧
    EVERY (λ(n,params,body). every_prog (loop_inst_ok c) body) (SND s) ∧
    every_prog (loop_inst_ok c) (FST p) ∧
    every_prog (loop_inst_ok c) (SND p) ⇒
    (every_prog (loop_inst_ok c) body ∧
     EVERY (λ(n,params,body). every_prog (loop_inst_ok c) body) funs)
Proof
  ho_match_mp_tac (name_ind_cases [] comp_with_loop_alt_ind) \\
  rpt strip_tac \\
  separate_simp_tac [LET_THM, loop_removeTheory.comp_with_loop_def] \\
  rpt (pairarg_tac \\ POP_ASSUM (fn t => separate_simp_tac [t] \\ assume_tac t)) \\
  separate_simp_tac [Q.SPECL [`p`, `(x, y)`] PAIR_FST_SND_EQ] \\
  POP_ASSUM_LIST (MAP_EVERY strip_assume_tac) \\
  rveq \\
  separate_simp_tac [] \\
  gs [every_prog_def,loop_inst_ok_def] \\
  gs [DefnBase.one_line_ify NONE loop_removeTheory.store_cont_def] \\
  every_case_tac \\ fs [] \\
  gs [every_prog_def,loop_inst_ok_def] \\
  rpt (pairarg_tac \\ fs []) \\
  gs [every_prog_def,loop_inst_ok_def,every_loop_inst_ok_comp_no_loop]
QED

Theorem every_loop_inst_ok_comp:
  every_prog (loop_inst_ok c) prog ∧
  EVERY (λ(n,params,body). every_prog (loop_inst_ok c) body) (SND s) ∧
  comp (name,params,prog) s = (n,funs) ⇒
  EVERY (λ(n,params,body). every_prog (loop_inst_ok c) body) funs
Proof
  rw[loop_removeTheory.comp_def] \\
  pairarg_tac \\ gvs[] \\
  drule_then match_mp_tac every_loop_inst_ok_comp_lemma \\
  rw[every_prog_def,loop_inst_ok_def]
QED

Theorem every_loop_inst_ok_comp_prog:
  EVERY (λ(n,params,body). every_prog (loop_inst_ok c) body) lprog ⇒
  EVERY (λ(n,params,body). every_prog (loop_inst_ok c) body) (comp_prog lprog)
Proof
  rw[loop_removeTheory.comp_prog_def,EVERY_MEM] \\
  qmatch_asmsub_abbrev_tac ‘FOLDR comp acc’ \\
  ‘EVERY (λ(n,params,body). every_prog (loop_inst_ok c) body) (SND acc)’
    by(rw[Abbr ‘acc’]) \\
  qhdtm_x_assum ‘Abbrev’ kall_tac \\
  rpt $ pop_assum mp_tac \\
  qid_spec_tac ‘acc’ \\
  Induct_on ‘lprog’ using SNOC_INDUCT
  THEN1 rw[EVERY_MEM] \\
  rw[SF DNF_ss,FOLDR_SNOC] \\
  rpt(pairarg_tac \\ gvs[]) \\
  first_x_assum $ match_mp_tac o MP_CANON \\
  first_x_assum $ irule_at $ Pos hd \\
  match_mp_tac $ GEN_ALL every_loop_inst_ok_comp \\
  metis_tac[PAIR,FST,SND]
QED

Theorem loop_to_word_every_inst_ok_less:
  compile lprog = wprog0 ∧
  byte_offset_ok c 0w ∧ addr_offset_ok c 0w ∧
  EVERY (λ(n,params,body). every_prog (loop_inst_ok c) body) lprog ⇒
  EVERY (λ(n,m,p). every_inst (inst_ok_less c) p) wprog0
Proof
  strip_tac>>gs[loop_to_wordTheory.compile_def]>>
  drule_then irule loop_to_word_compile_prog_every_inst_ok_less>>
  gs[every_loop_inst_ok_comp_prog]
QED
