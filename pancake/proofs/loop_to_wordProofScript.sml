(*
  Correctness proof for loop_to_word
*)

open preamble
     loopSemTheory loopPropsTheory
     wordLangTheory wordSemTheory wordPropsTheory
     pan_commonTheory pan_commonPropsTheory
     loop_to_wordTheory

val _ = new_theory "loop_to_wordProof";

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
      lookup name t_code = SOME (LENGTH params+1, compile name params body) ∧
      no_Loops body ∧ ALL_DISTINCT params
End

Definition state_rel_def:
  state_rel s t <=>
    t.memory = s.memory ∧
    t.mdomain = s.mdomain ∧
    t.clock = s.clock ∧
    t.be = s.be ∧
    t.ffi = s.ffi ∧
    globals_rel s.globals t.store ∧
    code_rel s.code t.code
End

(* TOASK: l is only being used in comp? *)
val goal =
  ``λ(prog, s). ∀res s1 t ctxt retv l.
      evaluate (prog,s) = (res,s1) ∧ res ≠ SOME Error ∧
      state_rel s t ∧ locals_rel ctxt s.locals t.locals ∧
      lookup 0 t.locals = SOME retv ∧ no_Loops prog ∧
      ~(isWord retv) ∧
      domain (acc_vars prog LN) ⊆ domain ctxt ⇒
      ∃t1 res1.
         evaluate (FST (comp ctxt prog l),t) = (res1,t1) ∧
         state_rel s1 t1 ∧
         case res of
         | NONE => res1 = NONE ∧ lookup 0 t1.locals = SOME retv ∧
                   locals_rel ctxt s1.locals t1.locals ∧
                   t1.stack = t.stack ∧ t1.handler = t.handler
         | SOME (Result v) => res1 = SOME (Result retv v) ∧
                                     t1.stack = t.stack ∧ t1.handler = t.handler
         | SOME TimeOut => res1 = SOME TimeOut
         | SOME (FinalFFI f) => res1 = SOME (FinalFFI f)
         | SOME (Exception v) =>
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
      lookup name t_code = SOME (LENGTH params+1, compile name params body) ∧
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
    globals_rel s.globals t.store ∧
    code_rel s.code t.code
Proof
  rw [state_rel_def]
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


Triviality state_rel_IMP:
  state_rel s t ⇒ t.clock = s.clock
Proof
  fs [state_rel_def]
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

Triviality make_ctxt_APPEND:
  ∀xs ys n l.
    make_ctxt n (xs ++ ys) l =
    make_ctxt (n + 2 * LENGTH xs) ys (make_ctxt n xs l)
Proof
  Induct >> fs [make_ctxt_def,MULT_CLAUSES]
QED

Triviality make_ctxt_NOT_MEM:
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
QED

Theorem domain_mk_new_cutset_not_empty:
  domain (mk_new_cutset ctxt x1) ≠ ∅
Proof
  fs [mk_new_cutset_def]
QED

Theorem cut_env_mk_new_cutset:
  locals_rel ctxt l1 l2 ∧ domain x1 ⊆ domain l1 ∧ lookup 0 l2 = SOME y ⇒
  ∃env1. cut_env (mk_new_cutset ctxt x1) l2 = SOME env1 ∧
         locals_rel ctxt (inter l1 x1) env1
Proof
  fs [locals_rel_def,SUBSET_DEF,cut_env_def] >> fs [lookup_inter_alt]
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

Theorem cut_env_mk_new_cutset_IMP:
  cut_env (mk_new_cutset ctxt x1) l1 = SOME l2 ⇒
  lookup 0 l2 = lookup 0 l1
Proof
  fs [cut_env_def] >> rw []
  >> fs [SUBSET_DEF,mk_new_cutset_def]
  >> fs [lookup_inter_alt]
QED

Triviality LASTN_ADD_CONS:
  ~(LENGTH xs <= n) ⇒ LASTN (n + 1) (x::xs) = LASTN (n + 1) xs
Proof
  fs [LASTN_CONS]
QED


Theorem comp_exp_preserves_eval:
  !s e v t ctxt.
   eval s e = SOME v ∧
   state_rel s t /\ locals_rel ctxt s.locals t.locals ==>
    word_exp t (comp_exp ctxt e) = SOME v
Proof
  ho_match_mp_tac eval_ind >>
  rw [] >>
  fs [eval_def, comp_exp_def, word_exp_def]
  >- (
   fs [find_var_def, locals_rel_def] >>
   TOP_CASE_TAC >> fs [] >>
   first_x_assum drule >>
   strip_tac >> fs [] >> rveq >> fs [])
  >- fs [state_rel_def, globals_rel_def]
  >- (
   cases_on ‘eval s e’ >> fs [] >>
   cases_on ‘x’ >> fs [] >>
   first_x_assum drule_all >> fs [] >>
   strip_tac >>
   fs [state_rel_def, mem_load_def,
       loopSemTheory.mem_load_def])
  >- (
   fs [CaseEq "option"] >>
   qsuff_tac
   ‘the_words (MAP (λa. word_exp t a)
               (MAP (λa. comp_exp ctxt a) wexps)) = SOME ws’
   >- fs [] >>
   ntac 2 (pop_assum mp_tac) >>
   ntac 2 (pop_assum kall_tac) >>
   rpt (pop_assum mp_tac) >>
   qid_spec_tac ‘ws’ >>
   qid_spec_tac ‘wexps’ >>
   Induct >> rw [] >>
   last_assum mp_tac >>
   impl_tac >- metis_tac [] >>
   fs [the_words_def, CaseEq"option", CaseEq"word_loc"] >>
   rveq >> fs []) >>
  fs [CaseEq"option", CaseEq"word_loc"] >> rveq >> fs []
QED


Theorem compile_Skip:
  ^(get_goal "comp _ loopLang$Skip") ∧
  ^(get_goal "comp _ loopLang$Fail") ∧
  ^(get_goal "comp _ loopLang$Tick")
Proof
  rpt strip_tac >>
  fs [loopSemTheory.evaluate_def, comp_def,
      evaluate_def] >>
  rveq >> fs [] >>
  TOP_CASE_TAC >>
  fs [flush_state_def, state_rel_def,
      loopSemTheory.dec_clock_def, dec_clock_def] >> rveq >>
  fs []
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
  fs [find_var_def, locals_rel_def, get_var_def] >>
  res_tac >> rveq >>
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
  rpt (disch_then drule) >>
  disch_then (qspec_then ‘l'’ mp_tac) >>
  impl_tac
  >- (
   qpat_x_assum ‘_ ⊆ domain ctxt’ mp_tac >>
   fs [no_Loops_def, no_Loop_def, every_prog_def] >>
   fs [loopLangTheory.acc_vars_def] >>
   once_rewrite_tac [acc_vars_acc] >> fs []) >>
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
  conj_tac
  >- (
   fs [lookup_insert, CaseEq "bool", loopLangTheory.acc_vars_def] >>
   imp_res_tac find_var_neq_0 >> fs []) >>
  match_mp_tac locals_rel_insert >>
  fs [loopLangTheory.acc_vars_def]
QED

Theorem compile_Store:
  ^(get_goal "loopLang$Store") ∧
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
  fs [find_var_def, the_words_def, word_op_def] >>
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
  rw [FLOOKUP_UPDATE]
QED

Theorem compile_If:
  ^(get_goal "loopLang$If")
Proof
  rpt strip_tac >>
  fs [loopSemTheory.evaluate_def, comp_def] >>
  fs [CaseEq "option", CaseEq "word_loc"] >>
  rveq >> fs [] >>
  pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >>
  fs [evaluate_def] >>
  fs [find_var_def, get_var_def] >>
  imp_res_tac locals_rel_intro >> fs [] >>
  cases_on ‘ri’ >>
  fs [loopSemTheory.get_var_imm_def] >>
  fs [find_reg_imm_def, get_var_imm_def] >>
  fs [find_var_def, get_var_def] >>
  imp_res_tac locals_rel_intro >> fs [] >> rveq >>
  pairarg_tac >> fs [] >>
  rename [‘word_cmp cmp x cy’] >> (
  cases_on ‘word_cmp cmp x cy’ >> fs [] >>
  rename [‘cut_res live_out (evaluate (cc,s)) = _’] >>
  qpat_x_assum ‘comp _ cc _ = _’ mp_tac >>
  qmatch_goalsub_rename_tac ‘comp _ cc cl = _’ >>
  strip_tac >> (
  cases_on ‘evaluate (cc,s)’ >>
  cases_on ‘q’ >> TRY (cases_on ‘x'’) >>
  fs [loopSemTheory.cut_res_def,
      loopSemTheory.cut_state_def] >> rveq >> fs [] >>
  TRY (
  last_x_assum drule >>
  disch_then (qspecl_then [‘ctxt’, ‘retv’, ‘cl’] mp_tac) >>
  fs [] >>
  impl_tac
  >- (
   fs [loopLangTheory.acc_vars_def, no_Loops_def, no_Loop_def,
       every_prog_def] >>
   qpat_x_assum ‘_ ⊆ domain ctxt’ mp_tac >>
   once_rewrite_tac [acc_vars_acc] >>
   fs []) >>
  fs [] >> strip_tac >>
  fs [state_rel_def, flush_state_def, loopSemTheory.dec_clock_def,
      dec_clock_def] >> NO_TAC)
  >- (
   cases_on ‘domain live_out ⊆ domain r.locals’ >> fs [] >>
   cases_on ‘r.clock = 0’ >> fs [] >> rveq >> fs [] >> (
   last_x_assum drule >>
   disch_then (qspecl_then [‘ctxt’, ‘retv’, ‘cl’] mp_tac) >>
   fs [] >>
   impl_tac
   >- (
    fs [loopLangTheory.acc_vars_def, no_Loops_def, no_Loop_def,
        every_prog_def] >>
    qpat_x_assum ‘_ ⊆ domain ctxt’ mp_tac >>
    once_rewrite_tac [acc_vars_acc] >>
    fs []) >>
   fs [] >> strip_tac >>
   fs [state_rel_def, flush_state_def, loopSemTheory.dec_clock_def,
       dec_clock_def] >>
   TRY (
   fs [locals_rel_def] >> rw [] >>
   fs [lookup_inter, CaseEq "option"])))
  >- (
   last_x_assum drule >>
   disch_then (qspecl_then [‘ctxt’, ‘retv’, ‘cl’] mp_tac) >>
   fs [] >>
   impl_tac
   >- (
    fs [loopLangTheory.acc_vars_def, no_Loops_def, no_Loop_def,
        every_prog_def] >>
    qpat_x_assum ‘_ ⊆ domain ctxt’ mp_tac >>
    once_rewrite_tac [acc_vars_acc] >>
    fs []) >>
   fs [] >> strip_tac >>
   cases_on ‘res' = SOME Error’ >>
   fs [] >> rw [] >> fs []) >>
  last_x_assum (qspecl_then [‘t’, ‘ctxt’, ‘retv’] mp_tac) >>
  fs [] >> CCONTR_TAC >> fs [] >>
  fs [no_Loops_def, no_Loop_def, loopLangTheory.acc_vars_def, every_prog_def] >>
  TRY (metis_tac []) >>
  qpat_x_assum ‘_ ⊆ domain ctxt’ mp_tac >>
  simp [Once acc_vars_acc]))
QED

Theorem compile_Call:
  ^(get_goal "comp _ (loopLang$Call _ _ _ _)")
Proof
  rw [] >> qpat_x_assum ‘evaluate _ = (res,_)’ mp_tac >> simp [loopSemTheory.evaluate_def]
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
         >> simp [compile_def]
         >> qmatch_goalsub_abbrev_tac ‘comp ctxt2 _ ll2’
         >> qexists_tac ‘ctxt2’ >> qexists_tac ‘ll2’ >> fs []
         >> conj_tac >- fs [lookup_fromList2,lookup_fromList]
         >> simp [Abbr‘ctxt2’,domain_make_ctxt,set_fromNumSet,
                  domain_difference,domain_toNumSet]
         >> reverse conj_tac >- fs [SUBSET_DEF]
         >> match_mp_tac locals_rel_make_ctxt
         >> fs [IN_DISJOINT,set_fromNumSet,domain_difference,
                domain_toNumSet,GSYM IMP_DISJ_THM])
       >> fs [CaseEq"word_loc",CaseEq"num",CaseEq"option",CaseEq"prod",CaseEq"bool"]
       >> rveq >> fs [code_rel_def,state_rel_def]
       >> first_x_assum drule >> strip_tac >> fs []
       >> fs [find_code_def]
       >> simp [compile_def]
       >> qmatch_goalsub_abbrev_tac ‘comp ctxt2 _ ll2’
       >> qexists_tac ‘ctxt2’ >> qexists_tac ‘ll2’ >> fs []
       >> conj_tac >- fs [lookup_fromList2,lookup_fromList]
       >> simp [Abbr‘ctxt2’,domain_make_ctxt,set_fromNumSet,
                domain_difference,domain_toNumSet]
       >> reverse conj_tac >- fs [SUBSET_DEF]
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
    >- (fs [Abbr‘tt’] >> fs [state_rel_def,loopSemTheory.dec_clock_def])
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
       >> simp [compile_def]
       >> qmatch_goalsub_abbrev_tac ‘comp ctxt2 _ ll2’
       >> qexists_tac ‘ctxt2’ >> qexists_tac ‘ll2’ >> fs []
       >> conj_tac >- fs [lookup_fromList2,lookup_fromList]
       >> simp [Abbr‘ctxt2’,domain_make_ctxt,set_fromNumSet,
                domain_difference,domain_toNumSet]
       >> reverse conj_tac >- fs [SUBSET_DEF]
       >> match_mp_tac locals_rel_make_ctxt
       >> fs [IN_DISJOINT,set_fromNumSet,domain_difference,
              domain_toNumSet,GSYM IMP_DISJ_THM])
     >> fs [CaseEq"word_loc",CaseEq"num",CaseEq"option",CaseEq"prod",CaseEq"bool"]
     >> rveq >> fs [code_rel_def,state_rel_def]
     >> first_x_assum drule >> strip_tac >> fs []
     >> fs [find_code_def]
     >> simp [compile_def]
     >> qmatch_goalsub_abbrev_tac ‘comp ctxt2 _ ll2’
     >> qexists_tac ‘ctxt2’ >> qexists_tac ‘ll2’ >> fs []
     >> conj_tac >- fs [lookup_fromList2,lookup_fromList]
     >> simp [Abbr‘ctxt2’,domain_make_ctxt,set_fromNumSet,
              domain_difference,domain_toNumSet]
     >> reverse conj_tac >- fs [SUBSET_DEF]
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
      >> pairarg_tac >> fs [pop_env_def,set_var_def]
      >> imp_res_tac env_to_list_IMP
      >> fs [loopSemTheory.set_var_def,loopSemTheory.dec_clock_def]
      >> fs [state_rel_def]
      >> rename [‘find_var ctxt var_name’]
      >> ‘var_name IN domain ctxt’ by fs [loopLangTheory.acc_vars_def]
      >> simp [lookup_insert]
      >> imp_res_tac find_var_neq_0 >> fs []
      >> imp_res_tac cut_env_mk_new_cutset_IMP >> fs []
      >> match_mp_tac locals_rel_insert >> fs []
      >> fs [locals_rel_def])
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
    >> reverse IF_CASES_TAC >- (imp_res_tac env_to_list_IMP >> fs [])
    >> strip_tac >> fs [] >> pop_assum mp_tac >> fs [set_var_def]
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
      >> imp_res_tac env_to_list_IMP >> fs []
      >> fs [lookup_insert]
      >> imp_res_tac find_var_neq_0 >> fs []
      >> imp_res_tac cut_env_mk_new_cutset_IMP >> fs []
      >> match_mp_tac locals_rel_insert >> fs [locals_rel_def])
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
    >> Cases_on ‘x’ >> fs []
    >- fs [Abbr‘tt’]
    >> pop_assum mp_tac >> rewrite_tac [IMP_DISJ_THM]
    >> IF_CASES_TAC >> fs []
    >> fs [Abbr‘tt’] >> metis_tac [])
  >-
   (qpat_x_assum ‘∀x. _’ (assume_tac o REWRITE_RULE [IMP_DISJ_THM])
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
    >> ‘t1.locals = fromAList l ∧
        t1.stack = t.stack ∧ t1.handler = t.handler’ by fs [state_component_equality]
    >> reverse IF_CASES_TAC >- (imp_res_tac env_to_list_IMP >> fs [] >> rfs [])
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
      >> imp_res_tac env_to_list_IMP >> fs []
      >> fs [lookup_insert]
      >> imp_res_tac find_var_neq_0 >> fs []
      >> imp_res_tac cut_env_mk_new_cutset_IMP >> fs []
      >> match_mp_tac locals_rel_insert >> fs [locals_rel_def])
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
    >> metis_tac [])
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
  fs [cut_env_def] >>
  rveq >> fs [] >>
  fs [lookup_inter] >>
  TOP_CASE_TAC >>
  fs [mk_new_cutset_def]
QED


Theorem compile_correct:
  ^(compile_correct_tm())
Proof
  match_mp_tac (the_ind_thm())
  >> EVERY (map strip_assume_tac [compile_Skip, compile_Raise,
       compile_Mark, compile_Return, compile_Assign, compile_Store,
       compile_SetGlobal, compile_Call, compile_Seq, compile_If,
       compile_FFI, compile_Loop, compile_LoadByte])
  >> asm_rewrite_tac [] >> rw [] >> rpt (pop_assum kall_tac)
QED

val _ = export_theory();
