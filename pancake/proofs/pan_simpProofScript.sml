(*
  Correctness proof for pan_simp
*)

open preamble panLangTheory pan_simpTheory panSemTheory

val _ = new_theory "pan_simpProof";

val _ = set_grammar_ancestry ["panLang", "pan_simp", "panSem"];

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


Theorem eval_set_var_lookup_eq:
  eval (s with locals := lcs |+ (v,value)) (Var v) =
  SOME value
Proof
  rw [eval_def, FLOOKUP_UPDATE]
QED

Theorem evaluate_retcall_ret_to_tail_eq:
  !p s.
   FST (evaluate (p,s)) <> SOME Error ==>
   evaluate (retcall_ret_to_tail p,s) = evaluate (p,s)
Proof
  rw [retcall_ret_to_tail_def] >>
  every_case_tac >> fs [] >> rveq >>
  fs [evaluate_def] >>
  pairarg_tac >> fs [] >>
  every_case_tac >> fs [] >> rveq >>
  TRY (metis_tac [] >> NO_TAC) >>
  fs [empty_locals_def, set_var_def] >>
  fs [eval_set_var_lookup_eq]
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
    evaluate (retcall_elim prog, s) = evaluate (prog,s)``

local
  val ind_thm = panSemTheory.evaluate_ind
    |> ISPEC goal
    |> CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV) |> REWRITE_RULE [];
  fun list_dest_conj tm = if not (is_conj tm) then [tm] else let
    val (c1,c2) = dest_conj tm in list_dest_conj c1 @ list_dest_conj c2 end
  val ind_goals = ind_thm |> concl |> dest_imp |> fst |> list_dest_conj
in
  fun get_goal s = first (can (find_term (can (match_term (Term [QUOTE s]))))) ind_goals
  fun retcall_elim_tm () = ind_thm |> concl |> rand
  fun the_ind_thm () = ind_thm
end


Theorem retcall_elim_dec:
  ^(get_goal "panLang$Dec")
Proof
  rw [retcall_elim_def] >>
  fs [evaluate_def] >>
  TOP_CASE_TAC >> fs [] >>
  rpt (pairarg_tac >> fs [] >> rveq)
QED


Theorem retcall_elim_seq:
  ^(get_goal "panLang$Seq")
Proof
  rw [retcall_elim_def] >>
  qmatch_goalsub_abbrev_tac ‘retcall_ret_to_tail sprog’ >>
  ‘evaluate (retcall_ret_to_tail sprog,s) = evaluate (sprog,s)’ by (
    ho_match_mp_tac evaluate_retcall_ret_to_tail_eq >>
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


Theorem retcall_elim_if:
  ^(get_goal "panLang$If")
Proof
  rw [retcall_elim_def] >>
  fs [evaluate_def] >>
  every_case_tac >> fs [] >>
  rpt (pairarg_tac >> fs [] >> rveq)
QED

Theorem evaluate_while_no_error_imp:
  eval s e = SOME (ValWord w) /\
  w <> 0w /\
  FST (evaluate (While e c,s)) <> SOME Error ==>
  FST (evaluate (c,s)) <> SOME Error
Proof
  rw [] >>
  pop_assum mp_tac >>
  once_rewrite_tac [evaluate_def] >>
  TOP_CASE_TAC >> fs [] >>
  pairarg_tac >> fs [] >> rveq >>
  every_case_tac >> fs []
QED

Theorem retcall_elim_while:
  ^(get_goal "panLang$While")
Proof
  rw [] >>
  fs [retcall_elim_def] >>
  once_rewrite_tac [evaluate_def] >>
  TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs [] >>
  drule evaluate_while_no_error_imp >>
  disch_then (qspec_then ‘c’ mp_tac) >>
  rw [] >> fs [] >>
  rpt (pairarg_tac >> fs [] >> rveq) >>
  TOP_CASE_TAC >> fs [] >> rveq >>
  every_case_tac >> fs [] >>
  ‘FST (evaluate (While e c,dec_clock s1)) ≠ SOME Error’ by
    fs [Once evaluate_def]  >>
  fs []
QED


Theorem retcall_elim_call:
  ^(get_goal "panLang$Call")
Proof
  rw [retcall_elim_def] >>
  fs [evaluate_def] >>
  every_case_tac >> fs []
QED


Theorem retcall_elim_others:
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
  rw [retcall_elim_def]
QED

Theorem retcall_elim_correct:
  ^(retcall_elim_tm())
Proof
  match_mp_tac (the_ind_thm()) >>
  EVERY (map strip_assume_tac [retcall_elim_dec, retcall_elim_seq,
         retcall_elim_if, retcall_elim_while, retcall_elim_call,
         retcall_elim_others]) >>
  asm_rewrite_tac [] >> rw [] >> rpt (pop_assum kall_tac)
QED

Theorem eval_seq_assoc_not_error:
  FST (evaluate (p,s)) ≠ SOME Error ==>
      FST (evaluate ((seq_assoc Skip p),s)) ≠ SOME Error
Proof
  rw [evaluate_seq_assoc] >>
  rw [evaluate_def]
QED

Theorem compile_correct:
  FST (evaluate (p,s)) <> SOME Error ==>
    evaluate (compile_prog p, s) = evaluate (p,s)
Proof
  rw [compile_prog_def] >>
  dxrule eval_seq_assoc_not_error >> strip_tac >>
  imp_res_tac retcall_elim_correct >> fs [] >>
  rw [evaluate_seq_assoc, evaluate_def]
QED

val _ = export_theory();
