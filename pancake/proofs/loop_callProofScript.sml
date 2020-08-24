(*
   loop_call proof
*)

open preamble
     loopSemTheory loopPropsTheory
     loop_callTheory

val _ = new_theory "loop_callProof";

Definition labels_in_def:
  labels_in l locals =
    !n x. lookup n l = SOME x ==> lookup n locals = SOME (Loc x 0)
End

val goal =
  “λ(prog, s). ∀res s1 l p nl.
    evaluate (prog,s) = (res,s1) ∧ res ≠ SOME Error ∧
    comp l prog = (p, nl) /\ labels_in l s.locals ==>
    evaluate (p,s) = (res,s1) /\ labels_in nl s1.locals”

local
  val ind_thm = loopSemTheory.evaluate_ind |> ISPEC goal
    |> CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV) |> REWRITE_RULE [];
  fun list_dest_conj tm = if not (is_conj tm) then [tm] else let
    val (c1,c2) = dest_conj tm in list_dest_conj c1 @ list_dest_conj c2 end
  val ind_goals = ind_thm |> concl |> dest_imp |> fst |> list_dest_conj
in
  fun get_goal s = first (can (find_term (can (match_term (Term [QUOTE s]))))) ind_goals
  fun compile_correct_tm () = ind_thm |> concl |> rand
  fun the_ind_thm () = ind_thm
end


Theorem compile_Seq:
  ^(get_goal "comp _ (loopLang$Seq _ _)")
Proof
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  fs [loopSemTheory.evaluate_def, labels_in_def] >>
  pairarg_tac >> fs [comp_def] >>
  rpt (pairarg_tac >> fs []) >>
  fs [evaluate_def] >>
  rpt (pairarg_tac >> fs []) >>
  rveq >> fs [] >>
  cases_on ‘res' = NONE’ >>
  fs [] >> rveq >> fs []
  >- (
  first_x_assum (qspecl_then [‘l’, ‘np’, ‘nl'’] mp_tac) >>
  impl_tac
  >- (
   fs [] >>
   rveq >> fs [] >>
   CCONTR_TAC >> fs []) >>
  strip_tac >> rveq >>
  fs [evaluate_def] >> rveq >> fs [] >>
  last_x_assum (qspecl_then [‘nl'’, ‘nq’, ‘nl''’] mp_tac) >>
  fs [lookup_def]) >>
  first_x_assum (qspecl_then [‘l’, ‘np’, ‘nl'’] mp_tac) >>
  fs [] >>
  strip_tac >>
  fs [evaluate_def, lookup_def]
QED


Theorem compile_LocValue:
  ^(get_goal "comp _ (loopLang$LocValue _ _)")
Proof
  rpt gen_tac >>
  strip_tac >>
  fs [evaluate_def, labels_in_def, comp_def] >>
  rveq >> fs [] >>
  fs [evaluate_def] >>
  cases_on ‘res’ >> fs []  >>
  every_case_tac >> fs [] >>
  last_x_assum (assume_tac o GSYM) >>
  rveq >> fs [set_var_def] >>
  rw [] >>
  fs [lookup_insert] >>
  every_case_tac >> fs []
QED


Theorem compile_Assign:
  ^(get_goal "comp _ (loopLang$Assign _ _)")
Proof
  rpt gen_tac >>
  strip_tac >>
  cases_on ‘exp’ >>
  TRY (
  rename [‘Assign n (Var m)’] >>
  fs [evaluate_def, comp_def] >>
  rveq >> fs [] >>
  fs [evaluate_def] >>
  fs [CaseEq "option"] >> rveq >> fs [] >>
  reverse TOP_CASE_TAC >> fs []
  >- (
   fs [labels_in_def, eval_def] >>
   rw [] >> fs [] >>
   fs [set_var_def] >>
   cases_on ‘n = n'’ >>
   fs [lookup_insert] >>
   rveq >> res_tac >> fs []) >>
  TOP_CASE_TAC >> fs [] >>
  fs [labels_in_def, eval_def] >>
  rw [] >> fs [] >>
  fs [set_var_def] >>
  fs [lookup_insert, lookup_delete] >>
  every_case_tac >> fs [] >> rveq >> fs []) >>
  fs [evaluate_def, labels_in_def, comp_def] >>
  rveq >> fs [] >>
  fs [evaluate_def] >>
  every_case_tac >> fs [] >>
  last_x_assum (assume_tac o GSYM) >>
  rveq >> fs [set_var_def] >>
  rw [] >>
  fs [lookup_insert] >>
  every_case_tac >> fs [] >>
  rveq >> fs [lookup_delete]
QED

Theorem compile_LoadByte:
  ^(get_goal "comp _ (loopLang$LoadByte _ _)")
Proof
  rpt gen_tac >>
  strip_tac >>
  fs [evaluate_def,labels_in_def, comp_def] >>
  rveq >> fs [] >>
  fs [evaluate_def] >>
  cases_on ‘res’ >> fs []  >>
  every_case_tac >> fs [] >>
  last_x_assum (assume_tac o GSYM) >>
  rveq >> fs [set_var_def] >>
  rw [] >>
  fs [lookup_insert] >>
  every_case_tac >> fs [] >>
  rveq >> fs [lookup_delete]
QED


Theorem compile_Mark:
  ^(get_goal "comp _ (loopLang$Mark _)")
Proof
  rpt gen_tac >>
  strip_tac >>
  rpt gen_tac >>
  fs [comp_def] >>
  pairarg_tac >> fs [] >> rveq >>
  fs [] >>
  strip_tac >> fs [] >>
  rveq >> fs [] >>
  fs [evaluate_def] >>
  res_tac >> fs []
QED


Theorem compile_FFI:
  ^(get_goal "comp _ (loopLang$FFI _ _ _ _ _ _)")
Proof
  rpt gen_tac >>
  strip_tac >>
  rpt gen_tac >>
  fs [labels_in_def, comp_def] >>
  every_case_tac >> fs [] >>
  rveq >> fs [] >>
  fs [evaluate_def] >>
  every_case_tac >> fs [] >> rveq >>
  fs [] >>
  fs [cut_state_def] >> rveq >> fs [lookup_def]
QED


Theorem compile_If:
  ^(get_goal "comp _ (loopLang$If _ _ _ _ _ _)")
Proof
  rpt gen_tac >>
  strip_tac >>
  rpt gen_tac >>
  strip_tac >>
  fs [evaluate_def, labels_in_def, comp_def] >>
  rveq >> fs [] >>
  fs [evaluate_def, CaseEq "option", CaseEq "word_loc"] >>
  rveq >> fs [] >>
  cases_on ‘word_cmp cmp x y’ >> fs [] >> rveq >>
  pairarg_tac >> fs [] >>
  pairarg_tac >> fs [] >> rveq >> fs []
  >- (
   cases_on ‘evaluate (c1,s)’ >> fs [] >>
   fs [cut_res_def] >>
   cases_on ‘q ≠ NONE’ >> fs [] >> rveq >> fs []
   >- (
    last_x_assum drule >>
    fs [] >>
    strip_tac >> fs [] >>
    fs [evaluate_def] >>
    cases_on ‘q’ >> fs [cut_res_def, lookup_def]) >>
   last_x_assum drule >>
   fs [] >>
   strip_tac >> fs [CaseEq "option"] >>
   rveq >> fs []  >>
   fs [evaluate_def, lookup_def] >>
   fs [cut_res_def]) >>
  cases_on ‘evaluate (c2,s)’ >> fs [] >>
  fs [cut_res_def, lookup_def] >>
  cases_on ‘q ≠ NONE’ >> fs [] >> rveq >> fs []
  >- (
   last_x_assum drule >>
   fs [] >>
   strip_tac >> fs [] >>
   fs [evaluate_def] >>
   cases_on ‘q’ >> fs [cut_res_def]) >>
  last_x_assum drule >>
  fs [] >>
  strip_tac >> fs [CaseEq "option"] >>
  rveq >> fs []  >>
  fs [evaluate_def] >>
  fs [cut_res_def]
QED

Theorem compile_StoreByte:
  ^(get_goal "comp _ (loopLang$StoreByte _ _)")
Proof
  rpt gen_tac >>
  strip_tac >>
  fs [evaluate_def, labels_in_def, comp_def] >>
  rveq >> fs [] >>
  fs [evaluate_def] >>
  cases_on ‘res’ >> fs []  >>
  every_case_tac >> fs [] >>
  last_x_assum (assume_tac o GSYM) >>
  rveq >> fs []
QED


Theorem compile_Store:
  ^(get_goal "comp _ (loopLang$Store _ _)")
Proof
  rpt gen_tac >>
  strip_tac >>
  fs [evaluate_def, labels_in_def, comp_def] >>
  rveq >> fs [] >>
  fs [evaluate_def] >>
  cases_on ‘res’ >> fs []  >>
  every_case_tac >> fs [mem_store_def] >>
  last_x_assum (assume_tac o GSYM) >>
  rveq >> fs []
QED

Theorem get_vars_front:
  !xs ys s. get_vars xs s = SOME ys /\ xs <> []==>
   get_vars (FRONT xs) s = SOME (FRONT ys)
Proof
  Induct >>
  rw [] >>
  fs [FRONT_DEF] >>
  every_case_tac >> fs []
  >- (
   fs [get_vars_def] >>
   every_case_tac >> fs [] >>
   pop_assum (assume_tac o GSYM) >>
   fs []) >>
  fs [get_vars_def] >>
  every_case_tac >> fs [] >>
  pop_assum (assume_tac o GSYM) >>
  fs [] >>
  res_tac >> fs [] >>
  fs [FRONT_DEF] >>
  TOP_CASE_TAC >> fs [] >>
  rveq >> fs [] >>
  cases_on ‘xs’ >>
  fs [get_vars_def] >>
  every_case_tac >> fs []
QED


Theorem get_vars_last:
  !xs ys s. get_vars xs s = SOME ys /\ xs <> []==>
   lookup (LAST xs) s.locals = SOME (LAST ys)
Proof
  Induct >>
  rw [] >>
  fs [LAST_DEF] >>
  every_case_tac >> fs []
  >- (
   fs [get_vars_def] >>
   every_case_tac >> fs [] >>
   pop_assum (assume_tac o GSYM) >>
   fs []) >>
  fs [get_vars_def] >>
  every_case_tac >> fs [] >>
  pop_assum (assume_tac o GSYM) >>
  fs [] >>
  res_tac >> fs [] >>
  fs [LAST_DEF] >>
  TOP_CASE_TAC >> fs [] >>
  rveq >> fs [] >>
  cases_on ‘xs’ >>
  fs [get_vars_def] >>
  every_case_tac >> fs []
QED

Theorem compile_Call:
  ^(get_goal "comp _ (loopLang$Call _ _ _ _)")
Proof
  rpt gen_tac >>
  strip_tac >>
  rpt gen_tac >>
  rpt (pop_assum kall_tac) >>
  strip_tac >>
  reverse (cases_on ‘dest’)
  >- (
   fs [loop_callTheory.comp_def] >>
   rveq >> fs [] >>
   fs [labels_in_def, lookup_def]) >>
  cases_on ‘argvars’
  >- (
   fs [loop_callTheory.comp_def, evaluate_def, get_vars_def] >>
   fs [find_code_def]) >>
  fs [loop_callTheory.comp_def] >> rveq >>
  TOP_CASE_TAC >> fs []
  >- fs [labels_in_def, lookup_def] >>
  fs [labels_in_def, lookup_def] >>
  fs [evaluate_def] >>
  cases_on ‘get_vars (h::t) s’ >> fs [] >>
  qmatch_asmsub_rename_tac ‘get_vars (h::t) _ = SOME argsval’ >>
  cases_on ‘find_code NONE argsval s.code’ >>
  fs [] >>
  ‘get_vars (FRONT (h::t)) s = SOME (FRONT argsval)’ by (
    fs [] >>
    drule get_vars_front >>
    fs []) >>
  fs [] >>
  ‘find_code (SOME x) (FRONT argsval) s.code = SOME x'’ suffices_by fs [] >>
  ‘LAST argsval = (Loc x 0)’ by (
    ‘LAST argsval = THE(lookup (LAST (h::t)) s.locals)’ by (
      fs [] >>
      pop_assum mp_tac >>
      drule get_vars_last >>
      fs []) >>
    fs []  >>
    res_tac >> fs []) >>
  fs [find_code_def] >>
  TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs [] >>
  fs [LENGTH_FRONT]
QED


Theorem compile_Loop:
  ^(get_goal "comp _ (loopLang$Loop _ _ _)")
Proof
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  fs [comp_def] >>
  pairarg_tac >> fs [] >>
  rveq >> fs [] >>
  qpat_x_assum ‘evaluate (Loop _ _ _,_) = (_,_)’ mp_tac >>
  once_rewrite_tac [evaluate_def] >>
  TOP_CASE_TAC >> fs [] >> rveq >>
  reverse TOP_CASE_TAC >> fs [] >> rveq >> fs []
  >- (
   strip_tac >> rveq >>
   fs [labels_in_def, lookup_def]) >>
  TOP_CASE_TAC >> fs [] >> rveq >> fs [] >>
  TOP_CASE_TAC >> fs [] >> rveq >> fs [] >>
  TOP_CASE_TAC >> fs [] >> rveq >> fs [] >> (
  strip_tac >> rveq >> fs [] >>
  res_tac >> fs [labels_in_def, lookup_def]) >>
  first_x_assum (qspec_then ‘LN’ mp_tac) >>
  fs [labels_in_def, lookup_def]
QED


Theorem compile_others:
  ^(get_goal "comp _ loopLang$Skip") ∧
  ^(get_goal "comp _ loopLang$Fail") ∧
  ^(get_goal "comp _ (loopLang$SetGlobal _ _)") ∧
  ^(get_goal "comp _ loopLang$Tick") ∧
  ^(get_goal "comp _ loopLang$Break") ∧
  ^(get_goal "comp _ loopLang$Continue") ∧
  ^(get_goal "comp _ (loopLang$Return _)") ∧
  ^(get_goal "comp _ (loopLang$Raise _)")
Proof
  rpt conj_tac >>
  rpt gen_tac >> strip_tac >>
  fs [evaluate_def, labels_in_def, comp_def] >>
  rveq >> fs [] >>
  fs [evaluate_def] >>
  every_case_tac >> fs [dec_clock_def] >>
  last_x_assum (assume_tac o GSYM) >>
  rveq >> fs [set_globals_def, lookup_def]
QED


Theorem compile_correct:
  ^(compile_correct_tm())
Proof
  match_mp_tac (the_ind_thm()) >>
  EVERY (map strip_assume_tac
         [compile_others,compile_LocValue,compile_LoadByte,compile_StoreByte,
          compile_Mark, compile_Assign, compile_Store,
          compile_Call, compile_Seq, compile_If, compile_FFI, compile_Loop]) >>
  asm_rewrite_tac [] >> rw [] >> rpt (pop_assum kall_tac)
QED


val _ = export_theory();
