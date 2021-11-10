(*
  Correctness proof for clos_op
*)

open preamble;
open closLangTheory closSemTheory closPropsTheory clos_opTheory;

val _ = new_theory "clos_opProof";

val _ = set_grammar_ancestry ["closLang", "closSem", "closProps", "clos_op"];

Triviality list_split3:
  ∀P. P [] ∧ (∀x y z zs. P (x::y::z::zs)) ∧ (∀x. P [x]) ∧ (∀x y. P [x; y]) ⇒
      ∀xs. P xs
Proof
  rw[] \\ Cases_on ‘xs’ \\ fs [] \\ Cases_on ‘t’ \\ fs [] \\ Cases_on ‘t'’ \\ fs []
QED

Triviality evaluate_MakeBool:
  ∀b. evaluate ([MakeBool b],vs,s) = (Rval [Boolv b],s)
Proof
  Cases \\ EVAL_TAC
QED

Theorem SmartOp_thm:
  evaluate ([Op t op xs], env, s) = (res,s1) ∧ res ≠ Rerr (Rabort Rtype_error) ⇒
  evaluate ([SmartOp t op xs], env, s) = (res,s1)
Proof
  fs [SmartOp_def] \\ CASE_TAC \\ fs [] \\ rename [‘_ = SOME z’]
  \\ pop_assum mp_tac \\ qid_spec_tac ‘xs’ \\ ho_match_mp_tac list_split3
  \\ fs [SmartOp'_def] \\ rpt strip_tac
  THEN1
   (gvs [AllCaseEqs()]
    \\ Cases_on ‘x’ \\ fs [dest_Op_def] \\ gvs [AllCaseEqs()]
    \\ Cases_on ‘o'’ \\ gvs [dest_Cons_def]
    \\ Cases_on ‘∃k. op = ElemAt k’
    THEN1
     (gvs [cons_op_def,dest_ElemAt_def]
      \\ qmatch_asmsub_abbrev_tac ‘if b then _ else _’
      \\ reverse (fs [AllCaseEqs()])
      THEN1 (pop_assum kall_tac \\ gvs []
             \\ gvs [evaluate_def,AllCaseEqs(),do_app_def])
      \\ fs [Abbr‘b’] \\ gvs []
      \\ gvs [evaluate_def,AllCaseEqs(),do_app_def]
      \\ qspecl_then [‘l’,‘env’,‘s’] assume_tac EVERY_pure_correct
      \\ gvs [] \\ rename [‘ee ≠ _’]
      \\ Cases_on ‘ee’ \\ fs [])
    \\ Cases_on ‘∃k1 k2. op = TagLenEq k1 k2’
    THEN1
     (gvs [cons_op_def,dest_ElemAt_def,dest_TagLenEq_def]
      \\ reverse (fs [AllCaseEqs()])
      \\ gvs [evaluate_def,AllCaseEqs(),do_app_def,evaluate_MakeBool]
      \\ TRY (rw [] \\ eq_tac \\ rw []
              \\ imp_res_tac evaluate_IMP_LENGTH \\ fs [])
      \\ qspecl_then [‘l’,‘env’,‘s’] assume_tac EVERY_pure_correct
      \\ gvs [] \\ rename [‘ee ≠ _’]
      \\ Cases_on ‘ee’ \\ fs [])
    \\ Cases_on ‘∃k. op = TagEq k’
    THEN1
     (gvs [cons_op_def,dest_ElemAt_def,dest_TagLenEq_def,dest_TagEq_def]
      \\ reverse (fs [AllCaseEqs()])
      \\ gvs [evaluate_def,AllCaseEqs(),do_app_def,evaluate_MakeBool]
      \\ TRY (rw [] \\ eq_tac \\ rw []
              \\ imp_res_tac evaluate_IMP_LENGTH \\ fs [])
      \\ qspecl_then [‘l’,‘env’,‘s’] assume_tac EVERY_pure_correct
      \\ gvs [] \\ rename [‘ee ≠ _’]
      \\ Cases_on ‘ee’ \\ fs [])
    \\ Cases_on ‘∃k. op = LenEq k’
    THEN1
     (gvs [cons_op_def,dest_ElemAt_def,dest_TagLenEq_def,dest_TagEq_def,dest_LenEq_def]
      \\ reverse (fs [AllCaseEqs()])
      \\ gvs [evaluate_def,AllCaseEqs(),do_app_def,evaluate_MakeBool]
      \\ TRY (rw [] \\ eq_tac \\ rw []
              \\ imp_res_tac evaluate_IMP_LENGTH \\ fs [])
      \\ qspecl_then [‘l’,‘env’,‘s’] assume_tac EVERY_pure_correct
      \\ gvs [] \\ rename [‘ee ≠ _’]
      \\ Cases_on ‘ee’ \\ fs [])
    \\ last_x_assum mp_tac
    \\ Cases_on ‘op’ \\ fs [] \\ EVAL_TAC)
  \\ reverse (Cases_on ‘dest_Op_Consts x y’) \\ gvs []
  THEN1
   (gvs [AllCaseEqs()]
    \\ Cases_on ‘x’ \\ fs [dest_Op_Consts_def,dest_Op_def,dest_Const_def]
    \\ Cases_on ‘o'’ \\ fs [dest_Op_Consts_def,dest_Op_def,dest_Const_def]
    \\ Cases_on ‘y’ \\ fs [dest_Op_Consts_def,dest_Op_def,dest_Const_def]
    \\ Cases_on ‘o'’ \\ fs [dest_Op_Consts_def,dest_Op_def,dest_Const_def]
    \\ Cases_on ‘l’ \\ gvs []
    \\ Cases_on ‘l'’ \\ gvs []
    \\ gvs [int_op_def,AllCaseEqs(),MakeInt_def]
    \\ gvs [evaluate_def,AllCaseEqs(),do_app_def,evaluate_MakeBool]
    \\ gvs [do_eq_def] \\ intLib.COOPER_TAC)
  \\ cheat
QED

Theorem SmartOp_simp:
  set_globals (SmartOp t op xs) = set_globals (Op t op xs) ∧
  esgc_free (SmartOp t op xs) = esgc_free (Op t op xs) ∧
  pure (SmartOp t op xs) = pure (Op t op xs)
Proof
  cheat
QED

Theorem SmartOp_Const:
  ∀xs. SmartOp t (Const i) xs = Op t (Const i) xs
Proof
  ho_match_mp_tac list_split3 \\ EVAL_TAC \\ rw []
  \\ rpt ((Cases_on ‘x’ \\ fs [] \\ EVAL_TAC) ORELSE
          (Cases_on ‘o'’ \\ fs [] \\ EVAL_TAC) ORELSE
          (Cases_on ‘y’ \\ fs [] \\ EVAL_TAC))
  \\ every_case_tac \\ fs []
QED

Theorem SmartOp_Cons:
  ∀xs. SmartOp t (Cons n) xs = Op t (Cons n) xs
Proof
  ho_match_mp_tac list_split3 \\ EVAL_TAC \\ rw []
  \\ rpt ((Cases_on ‘x’ \\ fs [] \\ EVAL_TAC) ORELSE
          (Cases_on ‘o'’ \\ fs [] \\ EVAL_TAC) ORELSE
          (Cases_on ‘y’ \\ fs [] \\ EVAL_TAC))
  \\ every_case_tac \\ fs []
QED

Theorem SmartOp_Install:
  SmartOp t Install = Op t Install
Proof
  fs [FUN_EQ_THM] \\ ho_match_mp_tac list_split3 \\ EVAL_TAC \\ rw []
  \\ rpt ((Cases_on ‘x’ \\ fs [] \\ EVAL_TAC) ORELSE
          (Cases_on ‘o'’ \\ fs [] \\ EVAL_TAC) ORELSE
          (Cases_on ‘y’ \\ fs [] \\ EVAL_TAC))
  \\ every_case_tac \\ fs []
QED

Theorem fv_max_SmartOp:
  fv_max n [Op t op xs] ⇒ fv_max n [SmartOp t op xs]
Proof
  cheat
QED

Theorem code_locs_SmartOp:
  LIST_TO_BAG (code_locs [SmartOp t op xs]) =
  LIST_TO_BAG (code_locs [Op t op xs])
Proof
  cheat
QED

Theorem every_Fn_SOME_SmartOp:
  every_Fn_SOME [SmartOp t op xs] = every_Fn_SOME [Op t op xs]
Proof
  cheat
QED

Theorem every_Fn_vs_NONE_SmartOp:
  every_Fn_vs_NONE xs ⇒ every_Fn_vs_NONE [SmartOp t op xs]
Proof
  cheat
QED

Theorem no_Labels_SmartOp:
  EVERY no_Labels xs ⇒ no_Labels (SmartOp t op xs)
Proof
  cheat
QED

Theorem obeys_max_app_SmartOp:
  EVERY (obeys_max_app k) xs ⇒ obeys_max_app k (SmartOp t op xs)
Proof
  cheat
QED

val _ = export_theory();
