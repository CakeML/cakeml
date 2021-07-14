(*
  Correctness proof for pan_simp
*)

open preamble
     panSemTheory pan_simpTheory panPropsTheory

val _ = new_theory "pan_simpProof";

val _ = set_grammar_ancestry  ["panSem", "pan_simp", "panProps"];

val s = ``s:('a,'ffi) panSem$state``

Theorem exp_ids_ret_to_tail_eq:
  !p. exp_ids (ret_to_tail p) = exp_ids p
Proof
  ho_match_mp_tac ret_to_tail_ind >> rw [] >>
  fs [ret_to_tail_def, panLangTheory.exp_ids_def]
  >- (
   fs [seq_call_ret_def] >>
   every_case_tac >> fs [panLangTheory.exp_ids_def]) >>
  every_case_tac >> fs [panLangTheory.exp_ids_def]
QED


Theorem exp_ids_seq_assoc_eq:
  !p q. exp_ids (seq_assoc p q) = exp_ids p ++ exp_ids q
Proof
  ho_match_mp_tac seq_assoc_ind >> rw [] >>
  fs [seq_assoc_def, panLangTheory.exp_ids_def] >>
  every_case_tac >> fs [seq_assoc_def, panLangTheory.exp_ids_def]
QED


Theorem exp_ids_compile_eq:
  !p. exp_ids (compile p) = exp_ids p
Proof
  rw [] >>
  fs [compile_def] >>
  fs [exp_ids_ret_to_tail_eq, exp_ids_seq_assoc_eq,
      panLangTheory.exp_ids_def]
QED

Theorem map_snd_f_eq:
  !p f g. MAP (g ∘ SND ∘ SND ∘ (λ(name,params,body). (name,params,f body))) p =
        MAP (g ∘ f) (MAP (SND ∘ SND) p)
Proof
  Induct >> rw [] >>
  cases_on ‘h’ >> fs [] >>
  cases_on ‘r’ >> fs []
QED

Theorem size_of_eids_compile_eq:
  !pan_code.
   size_of_eids (compile_prog pan_code) =
   size_of_eids pan_code
Proof
  rw [] >>
  fs [panLangTheory.size_of_eids_def] >>
  fs [pan_simpTheory.compile_prog_def] >>
  qmatch_goalsub_abbrev_tac ‘remove_dup (FLAT es)’ >>
  qmatch_goalsub_abbrev_tac ‘_ = LENGTH
    (remove_dup (FLAT ces))’ >>
  qsuff_tac ‘es = ces’
  >- fs [] >>
  fs [Abbr ‘es’, Abbr ‘ces’, pan_simpTheory.compile_prog_def] >>
  fs [MAP_MAP_o] >>
  fs [map_snd_f_eq] >>
  fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
  rw [] >>
  ‘EL n (MAP (SND ∘ SND) pan_code) =
   (SND ∘ SND) (EL n pan_code)’ by (
    match_mp_tac EL_MAP >>
    fs []) >>
  fs [] >>
  fs [exp_ids_compile_eq]
QED


Theorem evaluate_SmartSeq:
  evaluate (SmartSeq p q,s) = evaluate (Seq p q,^s)
Proof
  rw [SmartSeq_def, evaluate_def]
QED

Theorem evaluate_seq_skip:
   !p s. evaluate (Seq p Skip,s) = evaluate (p,^s)
Proof
  Induct >> fs [Once evaluate_def] >> rw [] >>
  rpt (pairarg_tac >> fs [] >> rw [evaluate_def] >> fs [])
QED

Theorem evaluate_skip_seq:
  evaluate (Seq Skip p,s) = evaluate (p,^s)
Proof
  fs [evaluate_def]
QED

Theorem evaluate_while_body_same:
  (!(s:('a,'b)state). evaluate (body,s) = evaluate (body',s)) ==>
  !(s:('a,'b)state). evaluate (While e body,s) = evaluate (While e body',s)
Proof
  rw [] >> completeInduct_on ‘s.clock’ >>
  rw [] >> fs [PULL_EXISTS,PULL_FORALL] >>
  once_rewrite_tac [evaluate_def] >>
  TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs [] >>
  rpt (pairarg_tac >> fs [] >> rveq) >>
  last_x_assum (qspec_then ‘s’ mp_tac) >>
  fs [] >> rw [] >>
  every_case_tac >>
  imp_res_tac evaluate_clock >>
  fs [dec_clock_def]
QED


Theorem evaluate_while_no_error_imp:
  eval s e = SOME (ValWord w) /\
  w <> 0w /\ s.clock <> 0 /\
  FST (evaluate (While e c,s)) <> SOME Error ==>
  FST (evaluate (c,dec_clock s)) <> SOME Error
Proof
  rw [] >>
  pop_assum mp_tac >>
  once_rewrite_tac [evaluate_def] >>
  TOP_CASE_TAC >> fs [] >>
  pairarg_tac >> fs [] >> rveq >>
  every_case_tac >> fs []
QED

Theorem evaluate_seq_assoc:
  !p q s. evaluate (seq_assoc p q,s) = evaluate (Seq p q,^s)
Proof
  ho_match_mp_tac seq_assoc_ind >> rw [] >>
  fs [evaluate_seq_skip, seq_assoc_def] >>
  TRY (
  rename1 ‘While’ >>
  TOP_CASE_TAC >> fs [] >> rveq >>
  fs [evaluate_skip_seq]
  >- metis_tac [evaluate_while_body_same] >>
  once_rewrite_tac [evaluate_def] >> fs [] >>
  rpt (pairarg_tac >> fs [] >> rveq) >>
  TOP_CASE_TAC >> fs [] >>
  metis_tac [evaluate_while_body_same]) >>
  gvs [evaluate_def] >> rpt (pairarg_tac >> fs [] >> rw [] >> gvs[]) >>
  every_case_tac >> gvs [evaluate_skip_seq, evaluate_def] >>
  every_case_tac >> gvs [evaluate_skip_seq, evaluate_def]
QED


Theorem evaluate_seq_call_ret_eq:
  !p s.
   FST (evaluate (p,s)) <> SOME Error ==>
   evaluate (seq_call_ret p,s) = evaluate (p,s)
Proof
  rw [seq_call_ret_def] >>
  every_case_tac >> fs [] >> rveq >>
  fs [evaluate_def] >>
  pairarg_tac >> fs [] >>
  every_case_tac >> fs [] >> rveq >>
  TRY (metis_tac [] >> NO_TAC) >>
  fs [empty_locals_def, set_var_def] >>
  fs [eval_def, FLOOKUP_UPDATE]
QED


Theorem evaluate_seq_no_error_fst:
  FST (evaluate (Seq p p',s)) ≠ SOME Error ==>
  FST (evaluate (p,s)) ≠ SOME Error
Proof
  rw [evaluate_def] >>
  rpt (pairarg_tac >> fs []) >>
  every_case_tac >> fs[]
QED


Theorem eval_seq_assoc_eq_evaluate:
  evaluate ((seq_assoc Skip p),s) = (res, t) ==>
  evaluate (p,s) = (res, t)
Proof
  rw [] >>
  fs [evaluate_seq_assoc] >>
  fs [evaluate_def]
QED

Theorem eval_seq_assoc_not_error:
  FST (evaluate (p,s)) ≠ SOME Error ==>
      FST (evaluate ((seq_assoc Skip p),s)) ≠ SOME Error
Proof
  rw [evaluate_seq_assoc] >>
  rw [evaluate_def]
QED


val goal =
  ``λ(prog, s).
    FST (evaluate (prog,s)) <> SOME Error ==>
    evaluate (ret_to_tail prog, s) = evaluate (prog,s)``

local
  val ind_thm = panSemTheory.evaluate_ind
    |> ISPEC goal
    |> CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV) |> REWRITE_RULE [];
  fun list_dest_conj tm = if not (is_conj tm) then [tm] else let
    val (c1,c2) = dest_conj tm in list_dest_conj c1 @ list_dest_conj c2 end
  val ind_goals = ind_thm |> concl |> dest_imp |> fst |> list_dest_conj
in
  fun get_goal s = first (can (find_term (can (match_term (Term [QUOTE s]))))) ind_goals
  fun ret_to_tail_tm () = ind_thm |> concl |> rand
  fun the_ind_thm () = ind_thm
end


Theorem ret_to_tail_Dec:
  ^(get_goal "panLang$Dec")
Proof
  rw [ret_to_tail_def] >>
  fs [evaluate_def] >>
  TOP_CASE_TAC >> fs [] >>
  rpt (pairarg_tac >> fs [] >> rveq)
QED


Theorem ret_to_tail_Seq:
  ^(get_goal "panLang$Seq")
Proof
  rw [ret_to_tail_def] >>
  qmatch_goalsub_abbrev_tac ‘seq_call_ret sprog’ >>
  ‘evaluate (seq_call_ret sprog,s) = evaluate (sprog,s)’ by (
    ho_match_mp_tac evaluate_seq_call_ret_eq >>
    unabbrev_all_tac >>
    imp_res_tac evaluate_seq_no_error_fst >> fs [] >>
    fs [evaluate_def] >>
    pairarg_tac >> fs [] >>
    TOP_CASE_TAC >> fs []) >>
  fs [] >> pop_assum kall_tac >>
  unabbrev_all_tac >>
  rw [evaluate_def] >>
  rpt (pairarg_tac >> fs []) >>
  every_case_tac >> fs [] >> rveq >>
  fs [evaluate_def]
QED

Theorem ret_to_tail_If:
  ^(get_goal "panLang$If")
Proof
  rw [ret_to_tail_def] >>
  fs [evaluate_def] >>
  every_case_tac >> fs [] >>
  rpt (pairarg_tac >> fs [] >> rveq)
QED

Theorem ret_to_tail_While:
  ^(get_goal "panLang$While")
Proof
  rw [] >>
  fs [ret_to_tail_def] >>
  once_rewrite_tac [evaluate_def] >>
  TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs [] >>
  drule evaluate_while_no_error_imp >>
  disch_then (qspec_then ‘c’ mp_tac) >>
  rw [] >> fs [] >>
  rpt (pairarg_tac >> fs [] >> rveq) >>
  every_case_tac >> fs [] >>
  ‘FST (evaluate (While e c,s1)) ≠ SOME Error’ by
    fs [Once evaluate_def]  >>
  fs []
QED

Theorem ret_to_tail_Call:
  ^(get_goal "panLang$Call")
Proof
  rw [] >>
  fs [ret_to_tail_def, evaluate_def] >>
  every_case_tac >>
  fs [evaluate_def, ret_to_tail_def]
QED

Theorem ret_to_tail_Others:
  ^(get_goal "panLang$Skip") /\
  ^(get_goal "panLang$Assign") /\
  ^(get_goal "panLang$Store") /\
  ^(get_goal "panLang$StoreByte") /\
  ^(get_goal "panLang$Break") /\
  ^(get_goal "panLang$Continue") /\
  ^(get_goal "panLang$ExtCall") /\
  ^(get_goal "panLang$Raise") /\
  ^(get_goal "panLang$Return") /\
  ^(get_goal "panLang$Tick")
Proof
  rw [ret_to_tail_def]
QED

Theorem ret_to_tail_correct:
  ^(ret_to_tail_tm())
Proof
  match_mp_tac (the_ind_thm()) >>
  EVERY (map strip_assume_tac
         [ret_to_tail_Dec, ret_to_tail_Seq,
          ret_to_tail_If, ret_to_tail_While, ret_to_tail_Call,
          ret_to_tail_Others]) >>
  asm_rewrite_tac [] >> rw [] >> rpt (pop_assum kall_tac)
QED

Theorem compile_correct_same_state:
  FST (evaluate (p,s)) <> SOME Error ==>
    evaluate (compile p, s) = evaluate (p,s)
Proof
  rw [compile_def] >>
  dxrule eval_seq_assoc_not_error >> strip_tac >>
  imp_res_tac ret_to_tail_correct >> fs [] >>
  rw [evaluate_seq_assoc, evaluate_def]
QED

Theorem evaluate_seq_simp:
  evaluate (p,s) = (res, t) /\ res <> SOME Error ==>
   evaluate (compile p, s) = (res,t)
Proof
  fs [compile_correct_same_state]
QED


Definition state_rel_def:
  state_rel s t c <=>
     (t = s with code := c) /\
     (∀f.
        FLOOKUP s.code f = NONE ==>
         FLOOKUP c f = NONE) /\
     (∀f vshs prog.
        FLOOKUP s.code f = SOME (vshs, prog) ==>
         FLOOKUP c f = SOME (vshs, pan_simp$compile prog))
End


Theorem state_rel_intro:
  !s t c. state_rel s t c ==>
     (t = s with code := c) /\
     (∀f vshs prog.
        FLOOKUP s.code f = SOME (vshs, prog) ==>
         FLOOKUP c f = SOME (vshs, pan_simp$compile prog))
Proof
  rw [state_rel_def]
QED


Theorem compile_eval_correct:
  ∀s e v t.
    eval s e = SOME v /\
    state_rel s t t.code ==>
     eval t e = SOME v
Proof
  ho_match_mp_tac panSemTheory.eval_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (
   rename [‘Const w’] >>
   fs [panSemTheory.eval_def])
  >- (
   rename [‘eval s (Var vname)’] >>
   fs [panSemTheory.eval_def] >> rveq >>
   fs [state_rel_def, state_component_equality])
  >- (
   rename [‘eval s (Label fname)’] >>
   fs [panSemTheory.eval_def, option_case_eq] >> rveq >>
   cases_on ‘v1’ >>
   fs [state_rel_def, state_component_equality] >>
   res_tac >> fs [])
  >- (
   rename [‘eval s (Struct es)’] >>
   rpt gen_tac >> strip_tac >> fs [] >>
   fs [panSemTheory.eval_def, option_case_eq] >> rveq >>
   rpt (pop_assum mp_tac) >>
   MAP_EVERY qid_spec_tac [‘vs’, ‘es’] >>
   Induct >> fs []
   >-  fs [OPT_MMAP_def] >>
   rpt gen_tac >> strip_tac >> fs [OPT_MMAP_def] >>
   rewrite_tac [AND_IMP_INTRO] >> strip_tac >> rveq >>
   rename [‘_ = SOME vs’] >>
   fs [])
  >- (
   rename [‘eval s (Field index e)’] >>
   rpt gen_tac >> strip_tac >> fs [] >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq] >> rveq >>
   fs [])
  >- (
   rename [‘eval s (Load sh e)’] >>
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq,
       CaseEq "word_lab"] >> rveq >> fs [] >>
   fs [state_rel_def, state_component_equality])
  >- (
   rename [‘eval s (LoadByte e)’] >>
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq,
       CaseEq "word_lab", option_case_eq] >> rveq >> fs [] >>
   fs [state_rel_def, state_component_equality])
  >- (
   rename [‘eval s (Op op es)’] >>
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq,
       CaseEq "word_lab", option_case_eq] >> rveq >> fs [] >>
   qsuff_tac ‘OPT_MMAP (λa. eval t a) es = SOME ws’
   >- fs [] >>
   pop_assum mp_tac >>
   pop_assum kall_tac >>
   pop_assum kall_tac >>
   pop_assum mp_tac >>
   pop_assum mp_tac >>
   MAP_EVERY qid_spec_tac [‘ws’, ‘es’] >>
   Induct >> fs []
   >- fs [OPT_MMAP_def] >>
   rpt gen_tac >> strip_tac >> fs [OPT_MMAP_def] >>
   rewrite_tac [AND_IMP_INTRO] >> strip_tac >> rveq >>
   fs [])
  >- (
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def] >>
   fs [option_case_eq, v_case_eq, word_lab_case_eq] >> rveq >>
   fs []) >>
  rpt gen_tac >> strip_tac >>
  fs [panSemTheory.eval_def] >>
  fs [option_case_eq, v_case_eq, word_lab_case_eq] >> rveq >>
  fs []
QED


Theorem compile_eval_correct_none:
  ∀s e t.
      eval s e = NONE /\
      state_rel s t t.code ==>
      eval t e = NONE
Proof
  ho_match_mp_tac panSemTheory.eval_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (
   rename [‘Const w’] >>
   fs [panSemTheory.eval_def])
  >- (
   rename [‘eval s (Var vname)’] >>
   fs [panSemTheory.eval_def] >> rveq >>
   fs [state_rel_def, state_component_equality])
  >- (
   rename [‘eval s (Label fname)’] >>
   fs [panSemTheory.eval_def, option_case_eq] >> rveq >>
   fs [state_rel_def, state_component_equality] >>
   res_tac >> fs [])
  >- (
   rename [‘eval s (Struct es)’] >>
   rpt gen_tac >> strip_tac >> fs [] >>
   fs [panSemTheory.eval_def, option_case_eq] >> rveq >>
   rpt (pop_assum mp_tac) >>
   MAP_EVERY qid_spec_tac [‘es’] >>
   Induct >> fs []
   >-  fs [OPT_MMAP_def] >>
   rpt gen_tac >> strip_tac >> fs [OPT_MMAP_def] >>
   rewrite_tac [AND_IMP_INTRO] >> strip_tac >> rveq  >>
   fs [] >>
   drule compile_eval_correct >>
   fs [])
  >- (
   rename [‘eval s (Field index e)’] >>
   rpt gen_tac >> strip_tac >> fs [] >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq] >> rveq >>
   imp_res_tac compile_eval_correct >>
   fs [])
  >- (
   rename [‘eval s (Load sh e)’] >>
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq,
       CaseEq "word_lab"] >> rveq >> fs [] >>
   imp_res_tac compile_eval_correct >>
   fs [] >>
   fs [state_rel_def, state_component_equality])
  >- (
   rename [‘eval s (LoadByte e)’] >>
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq,
       CaseEq "word_lab", option_case_eq] >> rveq >> fs [] >>
   imp_res_tac compile_eval_correct >>
   fs [] >>
   fs [state_rel_def, state_component_equality])
  >- (
   rename [‘eval s (Op op es)’] >>
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq,
       CaseEq "word_lab", option_case_eq] >> rveq >> fs []
   >- (
    qsuff_tac ‘OPT_MMAP (λa. eval t a) es = NONE’
    >- fs [] >>
    pop_assum mp_tac >>
    pop_assum mp_tac >>
    pop_assum mp_tac >>
    MAP_EVERY qid_spec_tac [‘es’] >>
    Induct >> fs []
    >- fs [OPT_MMAP_def] >>
    rpt gen_tac >> strip_tac >> fs [OPT_MMAP_def] >>
    rewrite_tac [AND_IMP_INTRO] >> strip_tac >> rveq >>
    fs [] >>
    imp_res_tac compile_eval_correct >>
    fs []) >>
   qsuff_tac ‘OPT_MMAP (λa. eval t a) es = SOME ws’
   >- fs [] >>
   pop_assum mp_tac >>
   pop_assum kall_tac >>
   pop_assum mp_tac >>
   pop_assum mp_tac >>
   MAP_EVERY qid_spec_tac [‘ws’, ‘es’] >>
   Induct >> fs []
   >- fs [OPT_MMAP_def] >>
   rpt gen_tac >> strip_tac >> fs [OPT_MMAP_def] >>
   rewrite_tac [AND_IMP_INTRO] >> strip_tac >> rveq >>
   fs [] >>
   imp_res_tac compile_eval_correct >>
   fs [])
  >- (
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def] >>
   fs [option_case_eq, v_case_eq, word_lab_case_eq] >> rveq >>
   fs [] >>
   imp_res_tac compile_eval_correct >>
   fs []) >>
  rpt gen_tac >> strip_tac >>
  fs [panSemTheory.eval_def] >>
  fs [option_case_eq, v_case_eq, word_lab_case_eq] >> rveq >>
  fs [] >>
  imp_res_tac compile_eval_correct >>
  fs []
QED

val goal =
  ``λ comp (prog, s). ∀res s1 t ctxt.
      evaluate (prog,s) = (res,s1) ∧ res ≠ SOME Error ∧
      state_rel s t t.code ==>
      ∃t1. evaluate (comp prog,t) = (res,t1) /\
      state_rel s1 t1 t1.code``

local
  val goal = beta_conv ``^goal (pan_simp$seq_assoc Skip)``
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
end


Theorem compile_Seq:
  ^(get_goal "panLang$Seq")
Proof
  rw [] >>
  fs [evaluate_seq_assoc, evaluate_skip_seq] >>
  fs [evaluate_def] >>
  pairarg_tac >> fs [] >> rveq >> fs [] >>
  pairarg_tac >> fs [] >> rveq >> fs [] >>
  cases_on ‘res''’ >> fs [] >> rveq >> fs []
  >- (
   ‘res' = NONE’ by (
     res_tac >> fs []) >>
   fs [] >>
   first_x_assum drule >>
   strip_tac >>
   fs [] >> rveq >> fs []) >>
  ‘res' <> NONE’ by (
    res_tac >> fs [] >> rveq >> fs []) >>
  fs [] >>
  res_tac >> fs [] >>
  rveq >> fs []
QED

Theorem compile_Dec:
  ^(get_goal "panLang$Dec")
Proof
  rw [] >>
  fs [evaluate_seq_assoc, evaluate_skip_seq] >>
  fs [evaluate_def] >>
  cases_on ‘eval s e’ >> fs [] >> rveq >>
  drule compile_eval_correct >>
  disch_then drule >>
  strip_tac >>
  fs [] >>
  pairarg_tac >> fs [] >> rveq >> fs [] >>
  pairarg_tac >> fs [] >> rveq >> fs [] >>
  first_x_assum (qspec_then ‘t with locals := t.locals |+ (v,x)’ mp_tac) >>
  impl_tac
  >- fs [state_rel_def, state_component_equality] >>
  strip_tac >> fs [] >> rveq >>
  rfs [state_rel_def] >>
  fs [state_component_equality]
QED

Theorem compile_If:
  ^(get_goal "panLang$If")
Proof
  rw [] >>
  fs [evaluate_seq_assoc, evaluate_skip_seq] >>
  fs [evaluate_def] >>
  cases_on ‘eval s e’ >> fs [] >> rveq >>
  drule compile_eval_correct >>
  disch_then drule >>
  strip_tac >>
  fs [] >>
  TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs []
QED


Theorem compile_Call:
  ^(get_goal "panLang$Call")
Proof
  rw [] >>
  fs [evaluate_seq_assoc, evaluate_skip_seq] >>
  fs [evaluate_def] >>
  cases_on ‘eval s trgt’ >> fs [] >> rveq >> fs [] >>
  imp_res_tac compile_eval_correct >>
  fs [] >>
  TOP_CASE_TAC >> fs [] >> rveq >> fs [] >>
  TOP_CASE_TAC >> fs [] >> rveq >> fs [] >>
  cases_on ‘OPT_MMAP (eval s) argexps’ >>
  fs [] >>
  ‘OPT_MMAP (eval t) argexps = OPT_MMAP (eval s) argexps’ by (
    match_mp_tac IMP_OPT_MMAP_EQ >>
    fs [pan_commonPropsTheory.opt_mmap_eq_some] >>
    fs [MAP_EQ_EVERY2] >>
    fs [LIST_REL_EL_EQN] >>
    rw [] >>
    metis_tac [compile_eval_correct]) >>
  fs [] >>
  cases_on ‘lookup_code s.code m x’ >> fs [] >>
  fs [lookup_code_def] >>
  cases_on ‘FLOOKUP s.code m’ >> fs [] >>
  cases_on ‘ x''’ >> fs [] >> rveq >>
  qpat_x_assum ‘state_rel s t t.code’ assume_tac >>
  drule state_rel_intro >>
  strip_tac >> rveq >> fs [] >>
  pop_assum drule >>
  strip_tac >> fs [] >>
  ‘t.clock = s.clock’ by
    fs [state_rel_def, state_component_equality] >>
  fs [] >>
  cases_on ‘s.clock = 0’ >> fs []
  >- (
   fs [empty_locals_def] >> rveq >>
   fs [state_rel_def, state_component_equality]) >>
  cases_on ‘evaluate
             (r,dec_clock s with locals := FEMPTY |++ ZIP (MAP FST q,x))’ >>
  fs [] >>
  cases_on ‘q'’ >> fs [] >>
  cases_on ‘x'’ >> fs [] >> rveq >> fs []
  >- (
   last_x_assum (qspec_then ‘dec_clock t with
                             locals := FEMPTY |++ ZIP (MAP FST q,x)’ mp_tac) >>
   impl_tac
   >- fs [dec_clock_def, state_rel_def, state_component_equality] >>
   strip_tac >> fs [] >>
   drule evaluate_seq_simp >>
   fs [] >>
   strip_tac >>
   fs [empty_locals_def] >> rveq >>
   fs [state_rel_def, state_component_equality])
  >- (
   last_x_assum (qspec_then ‘dec_clock t with
                             locals := FEMPTY |++ ZIP (MAP FST q,x)’ mp_tac) >>
   impl_tac
   >- fs [dec_clock_def, state_rel_def, state_component_equality] >>
   strip_tac >> fs [] >>
   drule evaluate_seq_simp >>
   fs [] >>
   strip_tac >>
   fs [] >> rveq >>
   cases_on ‘caltyp’ >> rfs [] >>
   fs [empty_locals_def] >> rveq >>
   fs [state_rel_def, state_component_equality] >>
   every_case_tac >> fs [set_var_def] >> rveq >> rfs [])
  >- (
   last_x_assum (qspec_then ‘dec_clock t with
                             locals := FEMPTY |++ ZIP (MAP FST q,x)’ mp_tac) >>
   impl_tac
   >- fs [dec_clock_def, state_rel_def, state_component_equality] >>
   strip_tac >> fs [] >>
   drule evaluate_seq_simp >>
   fs [] >>
   strip_tac >>
   fs [] >> rveq >>
   cases_on ‘caltyp’ >> rfs [] >>
   fs [empty_locals_def] >> rveq >>
   fs [state_rel_def, state_component_equality] >>
   every_case_tac >> fs [set_var_def] >> rveq >> rfs []) >>
  last_x_assum (qspec_then ‘dec_clock t with
                            locals := FEMPTY |++ ZIP (MAP FST q,x)’ mp_tac) >>
  impl_tac
  >- fs [dec_clock_def, state_rel_def, state_component_equality] >>
  strip_tac >> fs [] >>
  drule evaluate_seq_simp >>
  fs [] >>
  strip_tac >>
  fs [empty_locals_def] >> rveq >>
  fs [state_rel_def, state_component_equality]
QED


Theorem compile_While:
  ^(get_goal "panLang$While")
Proof
  rw [] >>
  fs [evaluate_seq_assoc, evaluate_skip_seq] >>
  qpat_x_assum ‘ evaluate (While e c,s) = (res,s1)’ mp_tac >>
  once_rewrite_tac [evaluate_def] >>
  TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs []
  >- (
   TOP_CASE_TAC >> fs [] >>
   strip_tac >> rveq >> fs [] >>
   imp_res_tac compile_eval_correct >>
   fs []
   >- (
    ‘t.clock = 0’ by
      fs [state_rel_def, state_component_equality] >>
    fs [] >>
    fs [empty_locals_def, state_rel_def, state_component_equality]) >>
   ‘t.clock <> 0’ by
     fs [state_rel_def, state_component_equality] >>
   fs [] >>
   cases_on ‘evaluate (c,dec_clock s)’ >>
   fs [] >>
   cases_on ‘q’ >> fs [] >> rveq >> fs [] >>
   TRY (cases_on ‘x’ >> fs [] >> rveq >> fs []) >> (
   last_x_assum (qspec_then ‘dec_clock t’ mp_tac) >>
   impl_tac
   >- fs [dec_clock_def, state_rel_def, state_component_equality] >>
   strip_tac >> fs [])) >>
  strip_tac >> rveq >> fs [] >>
  imp_res_tac compile_eval_correct >>
  fs []
QED

Theorem compile_ExtCall:
  ^(get_goal "panLang$ExtCall")
Proof
  rw [] >>
  fs [evaluate_seq_assoc, evaluate_skip_seq] >>
  fs [evaluate_def] >> rveq >> fs [] >>
  last_x_assum mp_tac >>
  rpt (TOP_CASE_TAC >> fs []) >>
  TRY (
  rfs [state_rel_def, state_component_equality,
       empty_locals_def, dec_clock_def] >> rveq >> fs [] >> NO_TAC) >>
  rfs [state_rel_def, state_component_equality,
       empty_locals_def, dec_clock_def] >> rveq >> fs [] >>
  rveq >> fs [] >> rveq >> rfs [] >>
  strip_tac >> fs []
QED

Theorem compile_Others:
  ^(get_goal "panLang$Skip") /\
  ^(get_goal "panLang$Assign") /\
  ^(get_goal "panLang$Store") /\
  ^(get_goal "panLang$StoreByte") /\
  ^(get_goal "panLang$Break") /\
  ^(get_goal "panLang$Continue") /\
  ^(get_goal "panLang$Raise") /\
  ^(get_goal "panLang$Return") /\
  ^(get_goal "panLang$Tick")
Proof
  rw [] >>
  fs [evaluate_seq_assoc, evaluate_skip_seq] >>
  fs [evaluate_def] >> rveq >> fs [] >>
  (
  every_case_tac >> gvs [] >>
  imp_res_tac compile_eval_correct >>
  gvs [state_rel_def, state_component_equality,
       empty_locals_def, dec_clock_def])
QED

Theorem compile_correct:
  ^(compile_tm())
Proof
  match_mp_tac (the_ind_thm()) >>
  EVERY (map strip_assume_tac
         [compile_Dec, compile_Seq,
          compile_If, compile_While, compile_Call,
          compile_ExtCall, compile_Call,compile_Others]) >>
  asm_rewrite_tac [] >> rw [] >> rpt (pop_assum kall_tac)
QED


Theorem first_compile_prog_all_distinct:
  ALL_DISTINCT (MAP FST prog) ==>
  ALL_DISTINCT (MAP FST (pan_simp$compile_prog prog))
Proof
  rw [] >>
  fs [pan_simpTheory.compile_prog_def] >>
  fs [MAP_MAP_o] >>
  qmatch_goalsub_abbrev_tac ‘MAP ls _’ >>
  ‘MAP ls prog = MAP FST prog’ suffices_by fs [] >>
  fs [Abbr ‘ls’] >>
  fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
  rw [] >>
  cases_on ‘EL n prog’ >>
  fs [] >>
  cases_on ‘r’ >>
  fs []
QED


Theorem el_compile_prog_el_prog_eq:
  !prog n start pprog p.
   EL n (compile_prog prog) = (start,[],pprog) /\
   ALL_DISTINCT (MAP FST prog) /\ n < LENGTH prog /\
   ALOOKUP prog start = SOME ([],p) ==>
     EL n prog = (start,[],p)
Proof
  Induct >> rw [] >>
  fs [compile_prog_def] >>
  cases_on ‘n’ >> fs [] >> rveq >> fs []
  >- (
   cases_on ‘h’ >> rfs [] >>
   cases_on ‘r’ >> rfs [] >> rveq >> fs []) >>
  last_x_assum match_mp_tac >>
  qexists_tac ‘pprog’ >> fs [] >>
  cases_on ‘h’ >> fs [] >>
  cases_on ‘q = start’ >> fs [] >> rveq >> fs [] >>
  fs [MEM_EL] >>
  first_x_assum (qspec_then ‘n'’ mp_tac) >>
  fs [] >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac ‘EL _ (MAP ff _) = _’ >>
  ‘EL n' (MAP ff prog) = ff (EL n' prog)’ by (
    match_mp_tac EL_MAP >> fs []) >>
  fs [] >>
  fs [Abbr ‘ff’] >>
  cases_on ‘EL n' prog’ >> fs [] >>
  cases_on ‘r’ >> fs [] >> rveq >> rfs [] >>
  metis_tac [pan_commonPropsTheory.el_pair_map_fst_el]
QED


Theorem compile_prog_distinct_params:
  ∀prog.
    EVERY (λ(name,params,body). ALL_DISTINCT params) prog ⇒
    EVERY (λ(name,params,body). ALL_DISTINCT params) (compile_prog prog)
Proof
  rw [] >>
  fs [EVERY_MEM] >>
  rw [] >>
  PairCases_on ‘e’ >> fs [] >>
  fs [compile_prog_def] >>
  fs [MEM_EL] >>
  qmatch_asmsub_abbrev_tac ‘MAP ff _’ >>
  ‘EL n (MAP ff prog) = ff (EL n prog)’ by (
    match_mp_tac EL_MAP >>
    fs []) >>
  fs [] >> rveq >> fs [] >>
  pop_assum kall_tac >>
  fs [Abbr ‘ff’] >>
  cases_on ‘EL n prog’ >>
  cases_on ‘r’ >> fs [] >> rveq >>
  last_x_assum (qspec_then ‘(e0,e1,r')’ mp_tac) >>
  fs [] >>
  impl_tac
  >- metis_tac [] >>
  fs []
QED


Theorem state_rel_imp_semantics:
  !s t pan_code start prog. state_rel s t t.code ∧
  ALL_DISTINCT (MAP FST pan_code) ∧
  s.code = alist_to_fmap pan_code ∧
  t.code = alist_to_fmap (pan_simp$compile_prog pan_code) ∧
  ALOOKUP pan_code start = SOME ([],prog) ∧
  semantics s start <> Fail ==>
  semantics t start = semantics s start
Proof
  rw [] >>
  fs [] >>
  reverse (Cases_on ‘semantics s start’) >> fs []
  >- (
   (* Termination case of pan semantics *)
   fs [panSemTheory.semantics_def] >>
   pop_assum mp_tac >>
   IF_CASES_TAC >> fs [] >>
   DEEP_INTRO_TAC some_intro >> simp[] >>
   rw []
   >- (
    (* the fail case of pan_simp semantics *)
    CCONTR_TAC >> fs [] >> rveq >> fs [] >>
    last_x_assum (qspec_then ‘k'’ mp_tac) >>
    (fn g => subterm (fn tm => Cases_on ‘^(assert(has_pair_type)tm)’) (#2 g) g) >>
    strip_tac >>
    fs [] >>
    drule compile_correct >> fs [] >>
    qexists_tac ‘t with clock := k'’ >>
    fs [] >>
    Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_EXISTS] >>
    conj_tac
    >- (
     fs [state_rel_def] >>
     cases_on ‘q’ >> fs [] >>
     cases_on ‘x’ >> fs []) >>
    CCONTR_TAC >>
    fs [] >>
    dxrule eval_seq_assoc_eq_evaluate >>
    strip_tac >> fs []) >>
   DEEP_INTRO_TAC some_intro >> simp[] >>
   conj_tac
   (* the termination case of pan-simp semantics *)
   >- (
    rw [] >> fs [] >>
    last_x_assum (qspec_then ‘k'’ mp_tac) >>
    (fn g => subterm (fn tm => Cases_on ‘^(assert(has_pair_type)tm)’) (#2 g) g) >>
    strip_tac >>
    fs [] >>
    drule compile_correct >> fs [] >>
    last_x_assum (qspec_then ‘k'’ mp_tac) >>
    fs [] >>
    strip_tac >> fs [] >>
    disch_then (qspecl_then [‘t with clock := k'’] mp_tac) >>
    impl_tac
    >- (
     fs [state_rel_def] >>
     cases_on ‘q’ >> fs [] >>
     cases_on ‘x’ >> fs []) >>
    strip_tac >> fs [] >>
    dxrule eval_seq_assoc_eq_evaluate >>
    strip_tac >> fs [] >> rveq >> fs [] >>
    pop_assum mp_tac >>
    dxrule panPropsTheory.evaluate_add_clock_eq >>
    dxrule panPropsTheory.evaluate_add_clock_eq >>
    disch_then (qspec_then ‘k'’ assume_tac) >>
    disch_then (qspec_then ‘k’ assume_tac) >>
    fs [] >>
    strip_tac >>
    cases_on ‘r’ >> fs [] >>
    cases_on ‘x’ >> fs [] >>(
    cases_on ‘q’ >> fs [] >>
    cases_on ‘x’ >> fs [] >> rveq >> fs [] >>
    fs [state_rel_def, state_component_equality])) >>
   (* the diverging case of pan-simp semantics *)
   rw[] >> fs[] >> CCONTR_TAC >> fs [] >>
   drule compile_correct >> fs [] >>
   ‘r ≠ SOME Error ∧
    r ≠ SOME Break ∧ r ≠ SOME Continue ∧ r ≠ NONE’ by (
     cases_on ‘r’ >> fs [] >>
     cases_on ‘x’ >> fs []) >>
   fs [] >>
   qexists_tac ‘t with clock := k’ >>
   fs [] >>
   Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_EXISTS] >>
   conj_tac
   >- (
    fs [state_rel_def] >>
    cases_on ‘q’ >> fs [] >>
    cases_on ‘x’ >> fs []) >>
   CCONTR_TAC >> fs [] >>
   fs [] >>
   dxrule eval_seq_assoc_eq_evaluate >>
   strip_tac >> fs [] >> rveq >> fs [] >>
   first_x_assum (qspec_then ‘k’ mp_tac) >> simp[] >>
   first_x_assum(qspec_then ‘k’ mp_tac) >> simp[] >>
   every_case_tac >> fs[] >> rw[] >> rfs[]) >>
  fs [panSemTheory.semantics_def] >>
  pop_assum mp_tac >>
  IF_CASES_TAC >> fs [] >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  rw []
  >- (
   (* the fail case of pan-simp semantics *)
   fs[] >> rveq >> fs[] >>
   last_x_assum (qspec_then ‘k’ mp_tac) >> simp[] >>
   (fn g => subterm (fn tm => Cases_on ‘^(assert(has_pair_type)tm)’) (#2 g) g) >>
   CCONTR_TAC >> fs [] >>
   drule compile_correct >> fs [] >>
   qexists_tac ‘t with clock := k’ >>
   fs [] >>
   Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_EXISTS] >>
   conj_tac
   >- (
    fs [state_rel_def] >>
    cases_on ‘q’ >> fs [] >>
    cases_on ‘x’ >> fs []) >>
   CCONTR_TAC >>
   fs [] >>
   dxrule eval_seq_assoc_eq_evaluate >>
   strip_tac >> fs [] >> rveq >> fs []) >>
  (* the termination/diverging case of pan-simp semantics *)
  DEEP_INTRO_TAC some_intro >> simp[] >>
  conj_tac
  (* the termination case of pan-simp semantics *)
  >- (
   rw [] >>  fs[] >>
   qpat_x_assum ‘∀x y. _’ (qspec_then ‘k’ mp_tac)>>
   (fn g => subterm (fn tm => Cases_on ‘^(assert(has_pair_type)tm)’) (#2 g) g) >>
   strip_tac >>
   drule compile_correct >> fs [] >>
   qexists_tac ‘t with clock := k’ >>
   fs [] >>
   Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_EXISTS] >>
   conj_tac
   >- (
    fs [state_rel_def] >>
    last_x_assum (qspec_then ‘k’ assume_tac) >>
    rfs [] >>
    cases_on ‘q’ >> fs [] >>
    cases_on ‘x’ >> fs []) >>
   CCONTR_TAC >>
   fs [] >>
   dxrule eval_seq_assoc_eq_evaluate >>
   strip_tac >> fs [] >> rveq >> fs []) >>
  (* the diverging case of pan-simp semantics *)
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
               panPropsTheory.evaluate_add_clock_io_events_mono) >>
   first_assum (qspecl_then
                [‘Call Tail (Label start) []’, ‘t with clock := k1’, ‘p’] mp_tac) >>
   first_assum (qspecl_then
                [‘Call Tail (Label start) []’, ‘t with clock := k2’, ‘p’] mp_tac) >>
   first_assum (qspecl_then
                [‘TailCall (Label start) []’, ‘s with clock := k1’, ‘p’] mp_tac) >>
   first_assum (qspecl_then
                [‘TailCall (Label start) []’, ‘s with clock := k2’, ‘p’] mp_tac) >>
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
   drule compile_correct >> fs [] >>
   ‘q ≠ SOME Error ∧
    q ≠ SOME Break ∧ q ≠ SOME Continue ∧ q ≠ NONE’ by (
     last_x_assum (qspec_then ‘k’ assume_tac) >> rfs [] >>
     cases_on ‘q’ >> fs [] >>
     cases_on ‘x’ >> fs []) >>
   fs [] >>
   disch_then (qspec_then ‘t with clock := k’ mp_tac) >>
   impl_tac
   >- fs [state_rel_def] >>
   strip_tac >> fs [] >>
   qexists_tac ‘ck+k’ >> simp[] >>
   dxrule eval_seq_assoc_eq_evaluate >>
   strip_tac >> fs [] >> rveq >> fs [] >>
   first_x_assum (qspec_then ‘k’ kall_tac) >>
   first_x_assum (qspec_then ‘k’ mp_tac) >>
   fs [] >>
   strip_tac >>
   cases_on ‘q’ >> fs [] >> rveq >> fs [] >>
   cases_on ‘x’ >> fs [] >> rveq >> fs [] >>
   assume_tac (INST_TYPE [``:'a``|->``:'a``,
                          ``:'b``|->``:'b``]
               panPropsTheory.evaluate_add_clock_io_events_mono) >>
   first_x_assum (qspecl_then
                  [‘TailCall (Label start) []’,
                   ‘t with clock := k’, ‘ck’] mp_tac) >>
   strip_tac >> rfs [] >>
   rfs [state_rel_def, state_component_equality, IS_PREFIX_THM]) >>
  (fn g => subterm (fn tm => Cases_on`^(Term.subst[{redex = #1(dest_exists(#2 g)), residue = ``k:num``}]
                                        (assert(has_pair_type)tm))`) (#2 g) g) >>
  drule compile_correct >> fs [] >>
  ‘q ≠ SOME Error ∧
   q ≠ SOME Break ∧ q ≠ SOME Continue ∧ q ≠ NONE’ by (
    last_x_assum (qspec_then ‘k’ assume_tac) >> rfs [] >>
    cases_on ‘q’ >> fs [] >>
    cases_on ‘x’ >> fs []) >>
  fs [] >>
  disch_then (qspec_then ‘t with clock := k’ mp_tac) >>
  impl_tac
  >- fs [state_rel_def] >>
  strip_tac >> fs [] >>
  dxrule eval_seq_assoc_eq_evaluate >>
  strip_tac >> fs [] >> rveq >> fs [] >>
  qexists_tac ‘k’ >>
  fs [] >>
  fs [state_rel_def, state_component_equality, IS_PREFIX_THM]
QED

val _ = export_theory();
