(*
   loop_call proof
*)

open preamble
     loopSemTheory loopPropsTheory
     loop_callTheory

val _ = new_theory "loop_callProof";

val goal =
  “λ(prog, s). ∀res s1 l p nl.
    evaluate (prog,s) = (res,s1) ∧ res ≠ SOME Error ∧
    comp l prog = (p, nl) /\
    (∀n x. lookup n l = SOME x ==> lookup n s.locals = SOME (Loc x 0)) ==>
    evaluate (p,s) = (res,s1) /\
    case res of
     | NONE => (∀n x. lookup n nl = SOME x ==> lookup n s1.locals = SOME (Loc x 0))
     | _ => T ”

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
  rpt gen_tac >>
  strip_tac >>
  rpt gen_tac >>
  strip_tac >>
  fs [loopSemTheory.evaluate_def] >>
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
  last_x_assum (qspecl_then [‘nl'’, ‘nq’, ‘nl’] mp_tac) >>
  fs []) >>
  first_x_assum (qspecl_then [‘l’, ‘np’, ‘nl'’] mp_tac) >>
  fs [] >>
  strip_tac >>
  fs [evaluate_def] >> rveq >> fs [] >>
  cases_on ‘res’ >> fs []
QED


Theorem compile_LocValue:
  ^(get_goal "comp _ (loopLang$LocValue _ _)")
Proof
  rpt gen_tac >>
  strip_tac >>
  fs [evaluate_def, comp_def] >>
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
  fs [evaluate_def, comp_def] >>
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

Theorem compile_LoadByte:
  ^(get_goal "comp _ (loopLang$LoadByte _ _)")
Proof
  rpt gen_tac >>
  strip_tac >>
  fs [evaluate_def, comp_def] >>
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
  fs [comp_def] >>
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
  fs [evaluate_def, comp_def] >>
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
    cases_on ‘q’ >> fs [cut_res_def]) >>
   last_x_assum drule >>
   fs [] >>
   strip_tac >> fs [CaseEq "option"] >>
   rveq >> fs []  >>
   fs [evaluate_def] >>
   fs [cut_res_def] >>
   cases_on ‘v.clock = 0’ >> fs [] >> rveq >> fs [] >>
   fs [dec_clock_def, lookup_inter, cut_state_def] >>
   qpat_x_assum ‘r with locals := _ = _’ (assume_tac o GSYM) >>
   rveq >> fs [] >>
   rw [] >>
   fs [CaseEq "option"] >> rveq >> fs [lookup_inter] >>
   res_tac >>
   TOP_CASE_TAC >> fs [] >> rveq >>
   fs [lookup_def] >>
   TOP_CASE_TAC >> fs []) >>
  cases_on ‘evaluate (c2,s)’ >> fs [] >>
  fs [cut_res_def] >>
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
  fs [cut_res_def] >>
  cases_on ‘v.clock = 0’ >> fs [] >> rveq >> fs [] >>
  fs [dec_clock_def, lookup_inter, cut_state_def] >>
  qpat_x_assum ‘r with locals := _ = _’ (assume_tac o GSYM) >>
  rveq >> fs [] >>
  rw [] >>
  fs [CaseEq "option"] >> rveq >> fs [lookup_inter] >>
  res_tac >>
  TOP_CASE_TAC >> fs [] >> rveq >>
  fs [lookup_def] >>
  TOP_CASE_TAC >> fs []
QED

Theorem compile_StoreByte:
  ^(get_goal "comp _ (loopLang$StoreByte _ _)")
Proof
  rpt gen_tac >>
  strip_tac >>
  fs [evaluate_def, comp_def] >>
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
  fs [evaluate_def, comp_def] >>
  rveq >> fs [] >>
  fs [evaluate_def] >>
  cases_on ‘res’ >> fs []  >>
  every_case_tac >> fs [mem_store_def] >>
  last_x_assum (assume_tac o GSYM) >>
  rveq >> fs []
QED


Theorem compile_Call:
  ^(get_goal "comp _ (loopLang$Call _ _ _ _)")
Proof
  cheat
QED

Theorem compile_Loop:
  ^(get_goal "comp _ (loopLang$Loop _ _ _)")
Proof
  rpt gen_tac >>
  strip_tac >>
  rpt gen_tac >>
  strip_tac >>
  fs [Once evaluate_def, comp_def] >>
  cases_on ‘cut_res live_in (NONE:'a result option,s)’ >> fs [] >>
  rveq >> fs [] >>
  pairarg_tac >>
  fs [] >>
  reverse (cases_on ‘q’) >> fs [] >> rveq >> fs []
  >- fs [Once evaluate_def] >>
  cases_on ‘evaluate (body,r)’ >> fs [] >>
  cases_on ‘q’ >> fs [] >>
  cases_on ‘x’ >> fs [] >>
  rveq >> fs [] >>
  fs [Once evaluate_def] >>
  res_tac >> fs [] >>
  cheat
QED


Theorem compile_others:
  ^(get_goal "comp _ loopLang$Skip") ∧
  ^(get_goal "comp _ loopLang$Fail") ∧
  ^(get_goal "comp _ loopLang$Tick") ∧
  ^(get_goal "comp _ loopLang$Break") ∧
  ^(get_goal "comp _ loopLang$Continue") ∧
  ^(get_goal "comp _ (loopLang$Raise _)") ∧
  ^(get_goal "comp _ (loopLang$Return _)") ∧
  ^(get_goal "comp _ (loopLang$SetGlobal _ _)")
Proof
  rw [] >>
  fs [evaluate_def, comp_def] >>
  rveq >> fs [] >>
  fs [evaluate_def] >>
  cases_on ‘res’ >>
  fs [] >>
  every_case_tac >> fs [dec_clock_def] >>
  last_x_assum (assume_tac o GSYM) >>
  rveq >> fs [set_globals_def]
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




(*
(*
Theorem butlast_cons:
  !xs x. xs <> [] ==>
    butlast (x::xs) = x::butlast xs
Proof
  Induct >>
  rw [] >>
  fs [butlast_def]
QED


Theorem last_cons:
  !xs x. xs <> [] ==>
    last (x::xs) = LAST xs
Proof
  Induct >>
  rw [] >>
  fs [last_def] >>
  cases_on ‘xs’ >>
  fs [LAST_DEF, EL]
QED

Theorem butlast_front_eq:
  !xs. xs <> [] ==>
  butlast xs = FRONT xs
Proof
  Induct >>
  rw [] >>
  fs [FRONT_DEF] >>
  every_case_tac >> fs []
  >- fs [butlast_def] >>
  metis_tac [butlast_cons]
QED

Theorem last_last_eq:
  !xs. xs <> [] ==>
  last xs = LAST xs
Proof
  Induct >>
  rw [] >>
  fs [LAST_DEF] >>
  every_case_tac >> fs []
  >- fs [last_def] >>
  metis_tac [last_cons]
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
*)

Theorem comp_correct:
  !prog s res s1 l. loopSem$evaluate (prog,s) = (res,s1) ∧
  res ≠ SOME Error ∧
  (∀n x. lookup n l = SOME x ==> lookup n s.locals = SOME (Loc x 0)) /\
  comp l prog = (np, nl) /\ evaluate (np,s) = (res',s1') ==>
   (res = res' /\ s1 = s1' /\
    (∀n x. lookup n nl = SOME x ==> lookup n s1.locals = SOME (Loc x 0)))
Proof
  ho_match_mp_tac loopSemTheory.evaluate_ind >>



  cases_on ‘prog’ >>
  fs [loop_callTheory.comp_def]
  >- (fs [evaluate_def] >> rveq >> fs [])
  >- (
   fs [evaluate_def] >>
   every_case_tac >> fs [] >> rveq  >> fs [] >>
   rw []
   >- (
    fs [set_var_def] >>
    fs [lookup_insert] >>
    TOP_CASE_TAC >> fs []) >>
   fs [set_var_def] >>
   fs [lookup_insert] >>
   TOP_CASE_TAC >> fs [] >> rveq >>
   fs [lookup_delete])
  >- (
   fs [evaluate_def] >>
   every_case_tac >> fs [] >> rveq  >> fs [] >>
   rw [] >>
   fs [mem_store_def] >>
   pop_assum mp_tac >>
   pop_assum (assume_tac o GSYM) >>
   fs [])
  >- (
   fs [evaluate_def] >>
   every_case_tac >> fs [] >> rveq  >> fs [] >>
   rw [] >>
   fs [set_globals_def])
  >- (
   fs [evaluate_def] >>
   every_case_tac >> fs [] >> rveq  >> fs [] >>
   rw [] >>
   fs [set_var_def, lookup_insert] >>
   TOP_CASE_TAC >> fs [] >>
   rveq >> fs [lookup_delete])
  >- (
   fs [evaluate_def] >>
   every_case_tac >> fs [] >> rveq  >> fs [])



  >- (
   fs [evaluate_def] >>
   pairarg_tac >> fs [] >>
   rveq >> fs [] >>
   cases_on ‘res' = NONE’ >> fs [] >>
   rveq >> fs []


   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >>
   pairarg_tac >> fs [] >> rveq >>
   every_case_tac >> fs [] >> rveq  >> fs [] >>
   pairarg_tac >> fs [] >> rveq >>
   pairarg_tac >> fs [] >> rveq >>
   every_case_tac >> fs [] >>


   )

   )




   )






   )



   )

    )

      rveq >> fs [])




  qmatch_goalsub_rename_tac ‘Call ret dest args hdl’ >>
  cases_on ‘dest’ >>
  fs [loop_callTheory.comp_def] >>
  ‘args <> []’ by (
    CCONTR_TAC >> fs [] >> rveq >>
    fs [evaluate_def, get_vars_def, find_code_def]) >>
  fs [] >>
  TOP_CASE_TAC >> fs [] >>
  fs [evaluate_def] >>
  cases_on ‘get_vars args s’ >> fs [] >>
  qmatch_asmsub_rename_tac ‘get_vars args _ = SOME argsval’ >>
  cases_on ‘find_code NONE argsval s.code’ >>
  fs [] >>
  ‘get_vars (butlast args) s = SOME (FRONT argsval)’ by (
    fs [] >>
    drule butlast_front_eq >>
    fs [] >>
    strip_tac >>
    metis_tac [get_vars_front]) >>
  fs [] >>
  ‘find_code (SOME x) (FRONT argsval) s.code = SOME x'’ suffices_by fs [] >>
  ‘LAST argsval = (Loc x 0)’ by (
    ‘LAST argsval = THE(lookup (last args) s.locals)’ by (
      ‘last args = LAST args’ by metis_tac [last_last_eq] >>
      fs [] >>
      pop_assum mp_tac >>
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
*)

val _ = export_theory();
