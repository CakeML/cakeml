(*
   loop_call proof
*)
Theory loop_callProof
Ancestors
  loopSem loopProps loop_call
Libs
  preamble


Definition labels_in_def:
  labels_in l locals =
    !n x. lookup n l = SOME x ==> lookup n locals = SOME (Loc x 0)
End

Theorem compile_correct:
  ∀v v1 res s1 l p nl.
    evaluate (v,v1) = (res,s1) ∧ res ≠ SOME Error ∧
    comp l v = (p,nl) ∧ labels_in l v1.locals ⇒
    evaluate (p,v1) = (res,s1) ∧ labels_in nl s1.locals
Proof
  recInduct loopSemTheory.evaluate_ind
  \\ rpt conj_tac
  >~ [`loopLang$Skip`] >- suspend "Skip"
  >~ [`loopLang$Fail`] >- suspend "Fail"
  >~ [`loopLang$Tick`] >- suspend "Tick"
  >~ [`loopLang$Continue`] >- suspend "Continue"
  >~ [`loopLang$Break`] >- suspend "Break"
  >~ [`loopLang$Mark`] >- suspend "Mark"
  >~ [`loopLang$Return`] >- suspend "Return"
  >~ [`loopLang$Raise`] >- suspend "Raise"
  >~ [`loopLang$Seq`] >- suspend "Seq"
  >~ [`loopLang$Loop`] >- suspend "Loop"
  >~ [`loopLang$Assign`] >- suspend "Assign"
  >~ [`loopLang$SetGlobal`] >- suspend "SetGlobal"
  >~ [`loopLang$LocValue`] >- suspend "LocValue"
  >~ [`loopLang$If`] >- suspend "If"
  >~ [`loopLang$Call`] >- suspend "Call"
  >~ [`loopLang$Store`] >- suspend "Store"
  >~ [`loopLang$Store32`] >- suspend "Store32"
  >~ [`loopLang$StoreByte`] >- suspend "StoreByte"
  >~ [`loopLang$Load32`] >- suspend "Load32"
  >~ [`loopLang$LoadByte`] >- suspend "LoadByte"
  >~ [`loopLang$FFI`] >- suspend "FFI"
  >~ [`loopLang$Arith`] >- suspend "Arith"
  >~ [`loopLang$ShMem`] >- suspend "ShMem"
QED

Resume compile_correct[Seq]:
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


Resume compile_correct[LocValue]:
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


Resume compile_correct[Assign]:
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

Resume compile_correct[Load32]:
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

Resume compile_correct[LoadByte]:
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


Resume compile_correct[Mark]:
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


Resume compile_correct[FFI]:
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


Resume compile_correct[If]:
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

Resume compile_correct[Store32]:
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

Resume compile_correct[StoreByte]:
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

Resume compile_correct[Store]:
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

Resume compile_correct[Call]:
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


Resume compile_correct[Loop]:
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

Resume compile_correct[Arith]:
  rpt conj_tac >>
  rpt gen_tac >> strip_tac >>
  gvs [evaluate_def, labels_in_def, comp_def,AllCaseEqs(),
      DefnBase.one_line_ify NONE loop_arith_def
      ] >>
  rw[set_var_def,lookup_insert,lookup_delete]
QED

Theorem evaluate_ShMem_neq_locals:
  evaluate (ShMem op v ad, s) = (res, s') ∧ v ≠ n ∧
  ¬ (∃x. res = SOME (FinalFFI x)) ∧ lookup n s.locals = x ⇒
  lookup n s'.locals = x
Proof
  strip_tac>>
  cases_on ‘op’>>fs[evaluate_def]>>
  fs[sh_mem_op_def,sh_mem_load_def,sh_mem_store_def,set_var_def,call_env_def]>>
  fs[AllCaseEqs()]>>
  rveq>>fs[lookup_insert,lookup_fromList]
QED

Theorem evaluate_ShMem_not_load_locals:
  loopSem$evaluate (ShMem op v ad, s) = (res, s') ∧ ¬is_load op ∧
  ¬ (∃x. res = SOME (FinalFFI x))⇒
  s.locals = s'.locals
Proof
  strip_tac>>
  cases_on ‘op’>>fs[evaluate_def,is_load_def]>>
  fs[sh_mem_op_def,sh_mem_load_def,sh_mem_store_def,set_var_def,call_env_def]>>
  fs[ffiTheory.call_FFI_def,AllCaseEqs()]>>
  rveq>>fs[]
QED

Resume compile_correct[ShMem]:
  rpt conj_tac >>
  rpt gen_tac >> strip_tac >>
  fs [evaluate_def, labels_in_def, comp_def] >>
  rveq >> fs [eval_def] >>
  fs [evaluate_def,is_load_def] >>
  rpt strip_tac>>every_case_tac>>fs[]
QED

Resume compile_correct[Skip]:
  rpt gen_tac >> strip_tac >>
  fs [evaluate_def, labels_in_def, comp_def] >>
  rveq >> fs [] >>
  fs [evaluate_def] >>
  every_case_tac >> fs [dec_clock_def] >>
  last_x_assum (assume_tac o GSYM) >>
  rveq >> fs [set_globals_def, lookup_def]
QED

Resume compile_correct[Fail]:
  rpt gen_tac >> strip_tac >>
  fs [evaluate_def, labels_in_def, comp_def] >>
  rveq >> fs [] >>
  fs [evaluate_def] >>
  every_case_tac >> fs [dec_clock_def] >>
  last_x_assum (assume_tac o GSYM) >>
  rveq >> fs [set_globals_def, lookup_def]
QED

Resume compile_correct[SetGlobal]:
  rpt gen_tac >> strip_tac >>
  fs [evaluate_def, labels_in_def, comp_def] >>
  rveq >> fs [] >>
  fs [evaluate_def] >>
  every_case_tac >> fs [dec_clock_def] >>
  last_x_assum (assume_tac o GSYM) >>
  rveq >> fs [set_globals_def, lookup_def]
QED

Resume compile_correct[Tick]:
  rpt gen_tac >> strip_tac >>
  fs [evaluate_def, labels_in_def, comp_def] >>
  rveq >> fs [] >>
  fs [evaluate_def] >>
  every_case_tac >> fs [dec_clock_def] >>
  last_x_assum (assume_tac o GSYM) >>
  rveq >> fs [set_globals_def, lookup_def]
QED

Resume compile_correct[Break]:
  rpt gen_tac >> strip_tac >>
  fs [evaluate_def, labels_in_def, comp_def] >>
  rveq >> fs [] >>
  fs [evaluate_def] >>
  every_case_tac >> fs [dec_clock_def] >>
  last_x_assum (assume_tac o GSYM) >>
  rveq >> fs [set_globals_def, lookup_def]
QED

Resume compile_correct[Continue]:
  rpt gen_tac >> strip_tac >>
  fs [evaluate_def, labels_in_def, comp_def] >>
  rveq >> fs [] >>
  fs [evaluate_def] >>
  every_case_tac >> fs [dec_clock_def] >>
  last_x_assum (assume_tac o GSYM) >>
  rveq >> fs [set_globals_def, lookup_def]
QED

Resume compile_correct[Return]:
  rpt gen_tac >> strip_tac >>
  fs [evaluate_def, labels_in_def, comp_def] >>
  rveq >> fs [] >>
  fs [evaluate_def] >>
  every_case_tac >> fs [dec_clock_def] >>
  last_x_assum (assume_tac o GSYM) >>
  rveq >> fs [set_globals_def, lookup_def]
QED

Resume compile_correct[Raise]:
  rpt gen_tac >> strip_tac >>
  fs [evaluate_def, labels_in_def, comp_def] >>
  rveq >> fs [] >>
  fs [evaluate_def] >>
  every_case_tac >> fs [dec_clock_def] >>
  last_x_assum (assume_tac o GSYM) >>
  rveq >> fs [set_globals_def, lookup_def]
QED

Finalise compile_correct;


