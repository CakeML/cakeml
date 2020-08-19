(*
   loop_call proof
*)

open preamble
     loopSemTheory loopPropsTheory
     loop_callTheory

val _ = new_theory "loop_callProof";


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


(* l is still unspecified *)

Theorem comp_correct:
  loopSem$evaluate (prog,s) = (res,s1) ∧
  res ≠ SOME Error ∧
  (∀n x. lookup n l = SOME x ==> lookup n s.locals = SOME (Loc x 0)) ⇒
  evaluate (comp l prog,s) = (res,s1)
Proof
  rw [] >>
  cases_on ‘prog’ >>
  fs [loop_callTheory.comp_def] >>
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


val _ = export_theory();
