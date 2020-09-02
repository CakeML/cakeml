(*
  Correctness proof for pan_simp
*)

open preamble
     panSemTheory pan_simpTheory

val _ = new_theory "pan_simpProof";

val _ = set_grammar_ancestry  ["panSem", "pan_simp"];

val s = ``s:('a,'ffi) panSem$state``


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
  fs [evaluate_def] >> rpt (pairarg_tac >> fs [] >> rw [] >> fs []) >>
  every_case_tac >> fs [] >> rveq  >> fs [evaluate_skip_seq, evaluate_def]
QED


Theorem eval_seq_assoc_not_error:
  FST (evaluate (p,s)) ≠ SOME Error ==>
      FST (evaluate ((seq_assoc Skip p),s)) ≠ SOME Error
Proof
  rw [evaluate_seq_assoc] >>
  rw [evaluate_def]
QED

Definition state_rel_def:
  state_rel s t c <=>
     (t = s with code := c) /\
     (∀f vshs prog.
        FLOOKUP s.code f = SOME (vshs, prog) ==>
         FLOOKUP c f = SOME (vshs, pan_simp$seq_assoc Skip prog))
End


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


Theorem compile_eval_correct:
  ∀s e v t.
      eval s e = SOME v /\
      state_rel s t t.code ==>
      eval t e = SOME v
Proof
  cheat
QED


Theorem compile_eval_correct_none:
  ∀s e t.
      eval s e = NONE /\
      state_rel s t t.code ==>
      eval t e = NONE
Proof
  cheat
QED


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


Theorem compile_While:
  ^(get_goal "panLang$While")
Proof
  rw [] >>
  fs [evaluate_seq_assoc, evaluate_skip_seq] >>
  once_rewrite_tac [evaluate_def] >>
  cases_on ‘eval s e’ >> fs [] >> rveq
  >- (
   drule compile_eval_correct_none >>
   disch_then drule >>
   strip_tac >>
   fs [] >>
   fs [Once evaluate_def]) >>
  drule compile_eval_correct >>
  disch_then drule >>
  strip_tac >>
  fs [] >>
  reverse TOP_CASE_TAC >> fs []
  >- fs [Once evaluate_def] >>
  reverse TOP_CASE_TAC >> fs []
  >- fs [Once evaluate_def] >>
  reverse TOP_CASE_TAC >> fs []
  >- (
   fs [Once evaluate_def] >>
   rveq >> fs []) >>
  TOP_CASE_TAC >> fs []
  >- (
   ‘s.clock ≠ 0’ by cheat >>
   fs [] >>
   cheat) >>
  cheat
QED


Theorem compile_Call:
  ^(get_goal "panLang$Call")
Proof
  rw [] >>
  fs [evaluate_seq_assoc, evaluate_skip_seq] >>
  fs [evaluate_def] >>
  cheat
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
  every_case_tac >> fs [] >> rveq >>
  imp_res_tac compile_eval_correct >>
  fs [] >> rveq >> fs [] >>
  rfs [state_rel_def, state_component_equality,
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


(* unitl here *)



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
  rw [ret_to_tail_def] >>
  fs [evaluate_def] >>
  every_case_tac >> fs []
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

Theorem compile_correct:
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
   evaluate (compile p, s) = evaluate (p,s)
Proof
  fs [compile_correct]
QED







val _ = export_theory();
