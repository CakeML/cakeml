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

Theorem dest_Op_thm:
  dest_Op f x = SOME (i,ys) ⇔
  ∃tra y. x = Op tra y ys ∧ f y = SOME i
Proof
  Cases_on ‘x’ \\ gvs [dest_Op_Nil_def,dest_Op_def,AllCaseEqs()]
  \\ rw [] \\ eq_tac \\ rw []
QED

Theorem dest_Op_Nil_thm:
  dest_Op_Nil f x = SOME i ⇔
  ∃tra y. x = Op tra y [] ∧ f y = SOME i
Proof
  Cases_on ‘x’ \\ gvs [dest_Op_Nil_def,dest_Op_def,AllCaseEqs()]
  \\ fs [PULL_EXISTS] \\ Cases_on ‘l’ \\ fs []
QED

Theorem dest_Const_thm:
  dest_Const x = SOME i ⇔ x = Const i
Proof
  Cases_on ‘x’ \\ fs [dest_Const_def]
QED

Theorem dest_Constant_thm:
  dest_Constant x = SOME i ⇔
  ∃s w j.
    x = Constant (ConstStr s) ∧ i = Str s ∨
    x = Constant (ConstInt j) ∧ i = Int j ∨
    x = Constant (ConstWord64 w) ∧ i = W64 w
Proof
  Cases_on ‘x’ \\ fs [dest_Constant_def]
  \\ Cases_on ‘c’ \\ fs [dest_Constant_def]
  \\ eq_tac \\ rw []
QED

Theorem dest_Cons_thm:
  dest_Cons x = SOME i ⇔ x = Cons i
Proof
  Cases_on ‘x’ \\ fs [dest_Cons_def]
QED

Theorem eq_direct_thm:
  ∀x y env s res s1 t z.
    evaluate ([Op t Equal [x; y]],env,s) = (res,s1) ∧
    res ≠ Rerr (Rabort Rtype_error) ∧
    eq_direct x y = SOME z ⇒
    evaluate ([z],env,s) = (res,s1)
Proof
  rpt gen_tac \\ fs [eq_direct_def]
  \\ reverse (Cases_on ‘eq_direct_const x y’) \\ fs []
  THEN1
   (gvs [eq_direct_const_def,AllCaseEqs(),dest_Op_Nil_thm,dest_Const_thm]
    \\ fs [evaluate_def,do_app_def]
    THEN1
     (Cases_on ‘evaluate ([x],env,s)’ \\ fs [] \\ Cases_on ‘q’ \\ fs []
      \\ rw [] \\ fs [evaluate_def]
      \\ imp_res_tac evaluate_SING \\ gvs []
      \\ Cases_on ‘r1’ \\ gvs [do_eq_def,do_app_def])
    THEN1
     (Cases_on ‘evaluate ([y],env,s)’ \\ fs [] \\ Cases_on ‘q’ \\ fs []
      \\ rw [] \\ fs [evaluate_def]
      \\ imp_res_tac evaluate_SING \\ gvs []
      \\ Cases_on ‘r1’ \\ gvs [do_eq_def,do_app_def]
      \\ rw [] \\ eq_tac \\ rw [])
    \\ EVAL_TAC \\ rw [] \\ fs [] \\ EVAL_TAC)
  \\ reverse (Cases_on ‘eq_direct_constant x y’) \\ fs []
  THEN1
   (gvs [eq_direct_constant_def,AllCaseEqs(),dest_Op_Nil_thm,dest_Constant_thm]
    \\ rw []
    \\ fs [evaluate_def,do_app_def] \\ rw []
    \\ gvs [AllCaseEqs(),PULL_EXISTS,make_const_def,do_eq_def]
    \\ fs [do_eq_def] \\ rw [evaluate_MakeBool]
    \\ imp_res_tac evaluate_SING \\ gvs []
    \\ TRY (eq_tac \\ fs [] \\ NO_TAC)
    \\ once_rewrite_tac [EQ_SYM_EQ]
    \\ rename [‘MAP _ _ = MAP _ _ ⇔ t1 = t2’]
    \\ Cases_on ‘t1’
    \\ Cases_on ‘t2’ \\ fs []
    \\ pop_assum kall_tac
    \\ qid_spec_tac ‘s’
    \\ qid_spec_tac ‘s'’
    \\ Induct \\ Cases_on ‘s’ \\ fs []
    \\ fs [ORD_BOUND,ORD_11])
  \\ reverse (Cases_on ‘eq_direct_nil x y’) \\ fs []
  THEN1
   (gvs [eq_direct_nil_def,AllCaseEqs(),dest_Op_Nil_thm,dest_Cons_thm]
    \\ fs [evaluate_def,do_app_def]
    THEN1
     (Cases_on ‘evaluate ([x],env,s)’ \\ fs [] \\ Cases_on ‘q’ \\ fs []
      \\ rw [] \\ fs [evaluate_def]
      \\ imp_res_tac evaluate_SING \\ gvs [AllCaseEqs()]
      \\ gvs[do_eq_def,AllCaseEqs(),do_app_def])
    THEN1
     (Cases_on ‘evaluate ([y],env,s)’ \\ fs [] \\ Cases_on ‘q’ \\ fs []
      \\ rw [] \\ fs [evaluate_def]
      \\ imp_res_tac evaluate_SING \\ gvs [AllCaseEqs()]
      \\ gvs[do_eq_def,AllCaseEqs(),do_app_def])
    \\ EVAL_TAC \\ rw [] \\ fs [] \\ EVAL_TAC)
  \\ fs []
QED

Theorem dont_lift_thm:
  dont_lift x ⇔
  (∃t n. x = Op t (Cons n) []) ∨
  (∃t i. x = Op t (Const i) []) ∨
  (∃t s. x = Op t (Constant (ConstStr s)) []) ∨
  (∃t i. x = Op t (Constant (ConstInt i)) []) ∨
  (∃t w. x = Op t (Constant (ConstWord64 w)) [])
Proof
  Cases_on ‘x’ \\ fs [dont_lift_def,dest_Op_Nil_def,dest_Op_def]
  \\ Cases_on ‘o'’ \\ fs [dest_Const_def,dest_Cons_def,dest_Constant_def]
  \\ Cases_on ‘l’ \\ fs [dest_Const_def,dest_Cons_def,dest_Constant_def]
  \\ rename [‘Constant ll’]
  \\ Cases_on ‘ll’ \\ fs [dest_Const_def,dest_Cons_def,dest_Constant_def]
QED

Theorem dont_lift_pure:
  dont_lift x ⇒ pure x
Proof
  rw [dont_lift_thm] \\ EVAL_TAC
QED

Theorem dont_lift_Rval:
  dont_lift x ∧ evaluate ([x],env,s1) = (res,s2) ⇒
  ∃v. res = Rval [v] ∧ s2 = s1
Proof
  rw [dont_lift_thm] \\ pop_assum mp_tac
  \\ EVAL_TAC \\ rw[] \\ gvs []
QED

Theorem evaluate_dont_lift:
  evaluate ([x],env,s1) = (Rval [v],s2:('a,'b) state) ∧ dont_lift x ⇒
  evaluate ([x],env1,s) = (Rval [v],s:('a,'b) state)
Proof
  rw [dont_lift_thm] \\ pop_assum mp_tac
  \\ EVAL_TAC \\ rw[] \\ gvs []
QED

Theorem lift_exps_acc:
  ∀xs n binds ys k binds2.
    lift_exps xs n binds = (ys,k,binds2) ⇒
    ∃binds1. binds2 = binds ++ binds1
Proof
  ho_match_mp_tac lift_exps_ind \\ rw []
  \\ fs [lift_exps_def] \\ gvs [AllCaseEqs()]
  \\ rpt (pairarg_tac \\ gvs [])
QED

Theorem lift_exps_n:
  ∀xs n binds ys k binds2.
    lift_exps xs n binds = (ys,k,binds2) ∧ n = LENGTH binds ⇒
    k = LENGTH binds2
Proof
  ho_match_mp_tac lift_exps_ind \\ rpt strip_tac
  \\ qpat_x_assum ‘lift_exps _ _ _ = _’ mp_tac
  \\ rewrite_tac [lift_exps_def] THEN1 rw []
  \\ Cases_on ‘dont_lift x’ \\ fs []
  THEN1 (gvs [] \\ rpt (pairarg_tac \\ gvs []) \\ rw [])
  \\ CASE_TAC \\ fs []
  THEN1 (gvs [] \\ rpt (pairarg_tac \\ gvs []) \\ rw [])
  \\ FULL_CASE_TAC \\ gvs []
  \\ gvs [] \\ rpt (pairarg_tac \\ gvs []) \\ rw []
QED

Theorem lift_exps_length:
  ∀xs n binds ys k binds2.
    lift_exps xs n binds = (ys,k,binds2) ⇒
    LENGTH xs = LENGTH ys
Proof
  ho_match_mp_tac lift_exps_ind \\ rw []
  \\ fs [lift_exps_def] \\ gvs [AllCaseEqs()]
  \\ rpt (pairarg_tac \\ gvs [])
QED

Theorem lift_exps_thm:
  ∀xs n binds env s0 ys k vs0 binds2 s1 (s2:('a,'b) state) res0.
    evaluate (binds,env,s0) = (Rval vs0,s1) ∧
    evaluate (xs,env,s1) = (res0,s2) ∧ n = LENGTH binds ∧
    lift_exps xs n binds = (ys,k,binds2) ⇒
    ∃res.
      evaluate (binds2,env,s0) = (res,s2) ∧
      (∀err. res = Rerr err ⇒ res0 = res) ∧
      ∀ws (s3:('a,'b) state) bind_vals.
        res = Rval bind_vals ⇒
        ∃vs. res0 = Rval vs ∧
             evaluate (ys,bind_vals++ws,s3) = (Rval vs,s3)
Proof
  ho_match_mp_tac lift_exps_ind \\ rpt strip_tac
  THEN1 gvs [lift_exps_def,evaluate_def]
  \\ gvs [] \\ pop_assum mp_tac
  \\ simp [lift_exps_def]
  \\ IF_CASES_TAC
  THEN1
   (pairarg_tac \\ gvs [] \\ strip_tac \\ gvs []
    \\ first_x_assum drule
    \\ qpat_x_assum ‘evaluate (_::_,_) = _’ mp_tac
    \\ simp [Once evaluate_CONS]
    \\ Cases_on ‘evaluate (xs,env,s1)’ \\ gvs []
    \\ strip_tac \\ gvs [] \\ strip_tac \\ gvs []
    \\ Cases_on ‘evaluate ([x],env,s1)’ \\ gvs []
    \\ drule_all dont_lift_Rval
    \\ strip_tac \\ gvs []
    \\ Cases_on ‘res’ \\ gvs [] \\ rw []
    \\ Cases_on ‘q’ \\ gvs []
    \\ simp [Once evaluate_CONS]
    \\ drule_all evaluate_dont_lift \\ fs [])
  \\ Cases_on ‘dest_Op dest_Cons x’ \\ fs []
  THEN1
   (pairarg_tac \\ gvs [] \\ strip_tac \\ gvs []
    \\ qpat_x_assum ‘evaluate _ = _’ mp_tac
    \\ simp [Once evaluate_CONS]
    \\ Cases_on ‘evaluate ([x],env,s1)’
    \\ reverse (Cases_on ‘q’) \\ rw []
    THEN1
     (drule lift_exps_acc \\ rw [] \\ fs []
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
      \\ simp [Once evaluate_APPEND]
      \\ simp [Once evaluate_CONS])
    \\ imp_res_tac evaluate_SING \\ gvs []
    \\ Cases_on ‘evaluate (xs,env,r)’ \\ fs []
    \\ last_x_assum (qspecl_then [‘env’,‘s0’] mp_tac)
    \\ simp [Once evaluate_APPEND]
    \\ rw [] \\ fs []
    \\ reverse (Cases_on ‘res’) \\ gvs []
    \\ reverse (Cases_on ‘q’) \\ gvs []
    \\ drule lift_exps_n \\ rw []
    \\ imp_res_tac lift_exps_acc \\ gvs []
    \\ gvs [evaluate_APPEND] \\ gvs [AllCaseEqs()]
    \\ rw [] \\ pop_assum (qspec_then ‘ws’ strip_assume_tac)
    \\ gvs [] \\ last_x_assum assume_tac
    \\ imp_res_tac evaluate_IMP_LENGTH \\ gvs []
    \\ simp [Once evaluate_CONS]
    \\ fs [evaluate_def]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND] \\ gvs []
    \\ gvs [EL_APPEND2])
  \\ rename [‘_ = SOME c’] \\ PairCases_on ‘c’ \\ fs []
  \\ pairarg_tac \\ fs []
  \\ pairarg_tac \\ fs []
  \\ strip_tac \\ gvs [dest_Op_thm,dest_Cons_thm]
  \\ imp_res_tac lift_exps_acc \\ gvs []
  \\ first_x_assum drule \\ fs []
  \\ Cases_on ‘evaluate (c1,env,s1)’ \\ fs [] \\ strip_tac
  \\ reverse (Cases_on ‘res’) \\ gvs []
  THEN1
   (simp [Once evaluate_APPEND]
    \\ qpat_x_assum ‘evaluate (Op _ _ _ :: _ , _) = _’ mp_tac
    \\ simp [Once evaluate_CONS]
    \\ fs [evaluate_def])
  \\ qpat_x_assum ‘evaluate (Op _ _ _ :: _ , _) = _’ mp_tac
  \\ simp [Once evaluate_CONS]
  \\ fs [evaluate_def,do_app_def]
  \\ reverse (Cases_on ‘q’) THEN1 gvs [] \\ gvs []
  \\ Cases_on ‘evaluate (xs,env,r)’ \\ fs [] \\ strip_tac
  \\ imp_res_tac lift_exps_n \\ rw [] \\ gvs []
  \\ first_x_assum drule_all \\ strip_tac \\ gvs []
  \\ Cases_on ‘res’ \\ gvs []
  \\ Cases_on ‘q’ \\ gvs []
  \\ rw []
  \\ simp [Once evaluate_CONS]
  \\ fs [evaluate_def,do_app_def]
  \\ gvs [evaluate_APPEND] \\ gvs [AllCaseEqs()]
  \\ gvs [PULL_EXISTS]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
QED

Theorem lift_exps_Let:
  lift_exps [x] 0 [] = ([y],n,binds) ∧
  evaluate ([x],env,s1) = (res,s2) ⇒
  evaluate ([Let None binds y],env,s1) = (res,s2)
Proof
  strip_tac
  \\ drule_at (Pos last) lift_exps_thm
  \\ fs [evaluate_def]
  \\ disch_then drule
  \\ strip_tac \\ fs []
  \\ reverse (Cases_on ‘res'’) \\ gvs []
  \\ pop_assum (qspecl_then [‘env’,‘s2’] strip_assume_tac)
  \\ gvs []
QED

Inductive simple_exp:
  (∀t i. simple_exp (Var t i)) ∧
  (∀t x y z. simple_exp x ∧ simple_exp y ∧ simple_exp z ⇒ simple_exp (If t x y z)) ∧
  (∀t i. simple_exp (Op t (Const i) [])) ∧
  (∀t i. simple_exp (Op t (Constant (ConstInt i)) [])) ∧
  (∀t i. simple_exp (Op t (Constant (ConstStr i)) [])) ∧
  (∀t i. simple_exp (Op t (Constant (ConstWord64 i)) [])) ∧
  (∀t i xs. EVERY simple_exp xs ⇒ simple_exp (Op t (Cons i) xs)) ∧
  (∀t i x. simple_exp x ⇒ simple_exp (Op t (EqualConst (Int i)) [x])) ∧
  (∀t i x. simple_exp x ⇒ simple_exp (Op t (EqualConst (Str i)) [x])) ∧
  (∀t i x. simple_exp x ⇒ simple_exp (Op t (EqualConst (W64 i)) [x])) ∧
  (∀t i x. simple_exp x ⇒ simple_exp (Op t (ElemAt i) [x])) ∧
  (∀t x y. simple_exp x ∧ simple_exp y ⇒ simple_exp (Op t Equal [x;y])) ∧
  (∀t l y x. simple_exp x ⇒ simple_exp (Op t (TagLenEq l y) [x]))
End

Theorem simple_exp_pure:
  ∀x. simple_exp x ⇒ pure x
Proof
  Induct_on ‘simple_exp’ \\ fs [pure_def,pure_op_def,EVERY_MEM]
QED

Theorem simple_exp_pure_every:
  EVERY simple_exp xs ⇒ EVERY pure xs
Proof
  rw [EVERY_MEM] \\ res_tac \\ fs [simple_exp_pure]
QED

Theorem lift_exps_simple_exp:
  ∀xs n binds ys k binds2.
    lift_exps xs n binds = (ys,k,binds2) ⇒ EVERY simple_exp ys
Proof
  ho_match_mp_tac lift_exps_ind \\ rw []
  \\ fs [lift_exps_def] \\ gvs [AllCaseEqs()]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ gvs [dont_lift_thm]
  \\ once_rewrite_tac [simple_exp_cases] \\ fs []
QED

Theorem evaluate_ConjList_append_F:
  ∀xs ys.
    evaluate ([ConjList xs],env1,r) = (Rval [Boolv F],r) ∧ EVERY pure xs ⇒
    evaluate ([ConjList (xs ++ ys)],env1,r) = (Rval [Boolv F],r:('c,'ffi) state)
Proof
  Induct THEN1 (EVAL_TAC \\ rw [] \\ EVAL_TAC)
  \\ reverse (Cases_on ‘xs’) \\ fs [ConjList_def]
  THEN1
   (fs [evaluate_def] \\ rpt gen_tac
    \\ rpt (CASE_TAC \\ fs []) \\ rw []
    \\ imp_res_tac pure_correct
    \\ first_x_assum (qspecl_then [‘r’,‘env1’] assume_tac) \\ gvs [])
  \\ reverse (Cases_on ‘ys’) \\ fs [ConjList_def]
  \\ fs [evaluate_def] \\ rpt gen_tac \\ EVAL_TAC
QED

Theorem evaluate_ConjList_append_T:
  ∀xs ys.
    evaluate ([ConjList xs],env1,r) = (Rval [Boolv T],r) ∧ EVERY pure xs ⇒
    evaluate ([ConjList (xs ++ ys)],env1,r) =
    evaluate ([ConjList ys],env1,r:('c,'ffi) state)
Proof
  Induct THEN1 (EVAL_TAC \\ rw [] \\ EVAL_TAC)
  \\ reverse (Cases_on ‘xs’) \\ fs [ConjList_def]
  THEN1
   (fs [evaluate_def] \\ rpt gen_tac
    \\ rpt (CASE_TAC \\ fs []) \\ rw []
    \\ fs [evaluate_MakeBool]
    \\ imp_res_tac pure_correct
    \\ first_x_assum (qspecl_then [‘r’,‘env1’] assume_tac) \\ gvs [])
  \\ reverse (Cases_on ‘ys’) \\ fs [ConjList_def]
  \\ fs [evaluate_def] \\ rpt gen_tac \\ EVAL_TAC
QED

Theorem evaluate_ConjList_F:
  evaluate ([x],env,r) = (Rval [Boolv F],r) ⇒
  evaluate ([ConjList (x::xs)],env,r) = (Rval [Boolv F],r)
Proof
  Cases_on ‘xs’ \\ fs [ConjList_def]
  \\ fs [evaluate_def,MakeBool_def,do_app_def,Boolv_def] \\ EVAL_TAC
QED

Theorem evaluate_ConjList_T:
  evaluate ([x],env,r) = (Rval [Boolv T],r) ∧
  evaluate ([ConjList xs],env,r) = res ⇒
  evaluate ([ConjList (x::xs)],env,r) = res
Proof
  Cases_on ‘xs’ \\ fs [ConjList_def]
  \\ fs [evaluate_def,MakeBool_def,do_app_def,Boolv_def] \\ rw [] \\ EVAL_TAC
QED

Theorem eq_direct_simple_exp:
  eq_direct x y = SOME z ∧ simple_exp x ∧ simple_exp y ⇒ simple_exp z
Proof
  fs [eq_direct_def,AllCaseEqs(),eq_direct_const_def,eq_direct_nil_def,eq_direct_constant_def]
  \\ rw [MakeBool_def] \\ simp [Once simple_exp_cases]
  \\ gvs [dest_Op_Nil_thm,dest_Constant_thm]
QED

Theorem simple_exp_eq_pure_list:
  ∀xs.
    EVERY (λ(x,y). simple_exp x ∧ simple_exp y) xs ⇒
    EVERY simple_exp (append (eq_pure_list xs))
Proof
  ho_match_mp_tac eq_pure_list_ind \\ rpt strip_tac
  THEN1 (simp [eq_pure_list_def])
  THENL [all_tac, fs [eq_pure_list_def] \\ NO_TAC]
  \\ pop_assum mp_tac
  \\ simp [Once eq_pure_list_def]
  \\ reverse (Cases_on ‘eq_direct x y’) \\ fs []
  THEN1 (imp_res_tac eq_direct_simple_exp \\ fs [])
  \\ rw []
  \\ Cases_on ‘dest_Op dest_Cons x’ \\ fs []
  \\ Cases_on ‘dest_Op dest_Cons y’ \\ fs []
  \\ rpt (qpat_x_assum ‘_ = NONE’ kall_tac)
  THEN1 (simp [Once simple_exp_cases])
  THEN1
   (PairCases_on ‘x'’ \\ gvs [dest_Op_thm,dest_Cons_thm]
    \\ simp [Once simple_exp_cases]
    \\ first_x_assum match_mp_tac
    \\ fs [EVERY_MEM,MEM_MAPi,PULL_EXISTS,EL_REVERSE]
    \\ last_x_assum mp_tac
    \\ simp [Once simple_exp_cases,EVERY_EL]
    \\ rw [] \\ simp [Once simple_exp_cases])
  \\ PairCases_on ‘x'’
  \\ PairCases_on ‘x''’
  \\ gvs [dest_Op_thm,dest_Cons_thm,MakeBool_def]
  \\ IF_CASES_TAC
  THEN1 (EVAL_TAC \\ simp [Once simple_exp_cases])
  \\ last_x_assum irule
  \\ Cases_on ‘x''0 = x'0’ \\ gvs []
  \\ last_x_assum mp_tac \\ simp [Once simple_exp_cases]
  \\ last_x_assum mp_tac \\ simp [Once simple_exp_cases]
  \\ gvs [miscTheory.every_zip_split]
QED

Theorem evaluate_EL:
  ∀xs i vs.
    evaluate (xs,env,s) = (Rval vs,s) ∧ i < LENGTH xs ∧ EVERY pure xs ⇒
    evaluate ([EL i xs],env,s) = (Rval [EL i vs],s)
Proof
  Induct \\ fs [evaluate_def]
  \\ simp [Once evaluate_CONS]
  \\ fs [AllCaseEqs()] \\ rw []
  \\ Cases_on ‘i’ \\ fs []
  \\ imp_res_tac evaluate_SING \\ gvs []
  \\ res_tac \\ fs []
  \\ imp_res_tac evaluate_pure \\ gvs []
QED

Theorem simpl_exp_Cons_EL:
  simple_exp (Op tra (Cons n) xs) ∧ i < LENGTH xs ⇒
  simple_exp (EL i xs)
Proof
  simp [Once simple_exp_cases,EVERY_EL]
QED

Theorem eq_pure_thm:
  evaluate ([x1; y1],env1,r) = (Rval [h1; h2],r) ∧ simple_exp x1 ∧ simple_exp y1 ∧
  do_eq h1 h2 = Eq_val b ⇒
  evaluate ([eq_pure x1 y1],env1,r) = (Rval [Boolv b],r)
Proof
  fs [eq_pure_def]
  \\ qsuff_tac ‘
      ∀xs hs b.
        LIST_REL (λ(x1,y1) (h1,h2). evaluate ([x1; y1],env1,r) = (Rval [h1; h2],r) ∧
                                    simple_exp x1 ∧ simple_exp y1) xs hs ∧
        do_eq_list (MAP FST hs) (MAP SND hs) = Eq_val b ∧
        EVERY simple_exp (append (eq_pure_list xs)) ⇒
        evaluate ([ConjList (append (eq_pure_list xs))],env1,r) = (Rval [Boolv b],r)’
  THEN1
   (disch_then (qspecl_then [‘[(x1,y1)]’,‘[(h1,h2)]’,‘b’] mp_tac)
    \\ rw [] \\ gvs[do_eq_def |> CONJUNCT2]
    \\ Cases_on ‘b’ \\ gvs []
    \\ last_x_assum irule
    \\ irule simple_exp_eq_pure_list \\ fs [])
  \\ ho_match_mp_tac eq_pure_list_ind
  \\ rpt strip_tac
  THEN1 (gvs [do_eq_def |> CONJUNCT2] \\ EVAL_TAC)
  THEN1
   (simp [Once eq_pure_list_def]
    \\ reverse (Cases_on ‘eq_direct x y’) \\ gvs [UNCURRY]
    THEN1
     (qspecl_then [‘x’,‘y’,‘env1’,‘r’] mp_tac eq_direct_thm
      \\ simp [Once evaluate_def,do_app_def]
      \\ simp [Once do_eq_sym] \\ fs [do_eq_def |> CONJUNCT2]
      \\ Cases_on ‘do_eq (FST y') (SND y')’ \\ fs [ConjList_def]
      \\ Cases_on ‘b'’ \\ fs [])
    \\ Cases_on ‘dest_Op dest_Cons x’ \\ fs []
    \\ Cases_on ‘dest_Op dest_Cons y’ \\ fs []
    THEN1
     (simp [Once evaluate_def,do_app_def,ConjList_def]
      \\ simp [Once do_eq_sym] \\ fs [do_eq_def |> CONJUNCT2]
      \\ Cases_on ‘do_eq (FST y') (SND y')’ \\ fs [ConjList_def]
      \\ Cases_on ‘b'’ \\ fs [])
    THEN1
     (gvs [PULL_EXISTS] \\ last_x_assum irule
      \\ fs [evaluate_def,PULL_EXISTS]
      \\ gvs [AllCaseEqs()]
      \\ imp_res_tac simple_exp_pure
      \\ imp_res_tac evaluate_pure \\ gvs []
      \\ imp_res_tac evaluate_SING \\ gvs []
      \\ simp [Once do_eq_def]
      \\ simp [Once do_eq_sym]
      \\ fs [EXISTS_PROD]
      \\ conj_tac
      THEN1
       (qpat_x_assum ‘do_eq_list _ _ = _’ mp_tac
        \\ simp [Once do_eq_def])
      \\ irule simple_exp_eq_pure_list \\ fs [])
    THEN1 (
      PairCases_on ‘x'’ \\ fs []
      \\ qpat_x_assum ‘EVERY _ _’ mp_tac
      \\ simp [Once eq_pure_list_def]
      \\ qpat_x_assum ‘_ = NONE’ kall_tac
      \\ strip_tac
      \\ gvs [dest_Op_thm,dest_Cons_thm]
      \\ qpat_x_assum ‘evaluate _ = _’ mp_tac
      \\ ‘∃tt. evaluate ([Op tra (Cons x'0) x'1],env1,r) = tt’ by fs []
      \\ PairCases_on ‘tt’ \\ fs []
      \\ drule evaluate_pure
      \\ pop_assum mp_tac
      \\ imp_res_tac simple_exp_pure \\ fs []
      \\ simp [evaluate_def]
      \\ simp [evaluate_def,AllCaseEqs(),do_app_def]
      \\ rw [] \\ fs []
      \\ Cases_on ‘y'’ \\ gvs []
      \\ Cases_on ‘r'’ \\ fs [do_eq_def]
      \\ Cases_on ‘x'0 = n ⇒ LENGTH vs ≠ LENGTH l’
      THEN1
       (‘~b’ by gvs [AllCaseEqs()] \\ gvs []
        \\ irule evaluate_ConjList_F
        \\ imp_res_tac evaluate_IMP_LENGTH
        \\ fs [evaluate_def,do_app_def] \\ rw[] \\ gvs [])
      \\ irule evaluate_ConjList_T
      \\ conj_tac
      THEN1
       (imp_res_tac evaluate_IMP_LENGTH
        \\ fs [evaluate_def,do_app_def] \\ rw[] \\ gvs [])
      \\ last_x_assum irule
      \\ Cases_on ‘x'0 = n’ \\ gvs []
      \\ ‘do_eq_list (REVERSE vs) l = Eq_val b’ by gvs [AllCaseEqs()] \\ gvs []
      \\ qexists_tac ‘ZIP (REVERSE vs, l)’ \\ gvs [MAP_ZIP]
      \\ imp_res_tac evaluate_IMP_LENGTH
      \\ fs [LIST_REL_EL_EQN,listTheory.EL_ZIP]
      \\ strip_tac \\ rename [‘i < LENGTH l’]
      \\ simp [evaluate_def,AllCaseEqs(),PULL_EXISTS]
      \\ fs [pure_def,SF ETA_ss] \\ strip_tac
      \\ fs [EL_REVERSE,PRE_SUB1]
      \\ ‘LENGTH x'1 − (i + 1) < LENGTH x'1’ by fs []
      \\ drule_all evaluate_EL \\ fs []
      \\ strip_tac \\ fs [do_app_def]
      \\ conj_tac
      THEN1 (irule simpl_exp_Cons_EL \\ fs [] \\ metis_tac [])
      \\ simp [Once simple_exp_cases])
    \\ PairCases_on ‘x'’
    \\ PairCases_on ‘x''’
    \\ gvs [dest_Op_thm]
    \\ IF_CASES_TAC
    THEN1
     (EVAL_TAC \\ Cases_on ‘b’ \\ gvs [dest_Cons_thm]
      \\ Cases_on ‘y'’
      \\ gvs [evaluate_def,AllCaseEqs(),do_app_def]
      \\ qpat_x_assum ‘do_eq_list _ _ = _’ mp_tac
      \\ fs [do_eq_def]
      \\ rw [] \\ fs [] \\ imp_res_tac evaluate_IMP_LENGTH \\ gvs [])
    \\ last_x_assum irule
    \\ Cases_on ‘x''0 = x'0’ \\ gvs []
    \\ conj_tac
    THEN1
     (irule simple_exp_eq_pure_list
      \\ gvs [dest_Cons_thm]
      \\ qpat_x_assum ‘simple_exp _’ mp_tac \\ simp [Once simple_exp_cases]
      \\ qpat_x_assum ‘simple_exp _’ mp_tac \\ simp [Once simple_exp_cases]
      \\ rw [] \\ gvs []
      \\ fs [EVERY_EL,MEM_MAPi,PULL_EXISTS,MEM_ZIP,EL_ZIP,EL_REVERSE])
    \\ gvs [dest_Cons_thm]
    \\ rename [‘[FST a; SND a]’]
    \\ PairCases_on ‘a’ \\ fs []
    \\ qpat_x_assum ‘EVERY _ _’ kall_tac
    \\ qpat_x_assum ‘evaluate _ = _’ mp_tac
    \\ fs [evaluate_def,do_app_def,AllCaseEqs(),PULL_EXISTS]
    \\ rename [‘LENGTH b1 = LENGTH b2’] \\ rw []
    \\ qpat_x_assum ‘do_eq_list _ _ = _’ mp_tac
    \\ imp_res_tac evaluate_IMP_LENGTH \\ gvs []
    \\ gvs [do_eq_def]
    \\ strip_tac
    \\ ‘do_eq_list (REVERSE vs') (REVERSE vs) = Eq_val b’ by gvs [AllCaseEqs()]
    \\ pop_assum mp_tac \\ pop_assum kall_tac \\ strip_tac
    \\ qexists_tac ‘ZIP (REVERSE vs',REVERSE vs)’
    \\ fs [LIST_REL_EL_EQN,listTheory.EL_ZIP,MAP_ZIP]
    \\ strip_tac \\ rename [‘i < LENGTH l’]
    \\ imp_res_tac simple_exp_pure
    \\ fs [pure_def,SF ETA_ss] \\ strip_tac
    \\ fs [EL_REVERSE,PRE_SUB1]
    \\ imp_res_tac evaluate_pure \\ rgs [] \\ gvs []
    \\ ‘LENGTH b1 − (i + 1) < LENGTH b1’ by fs []
    \\ drule_all evaluate_EL \\ fs [] \\ disch_then kall_tac
    \\ ‘LENGTH b2 − (i + 1) < LENGTH b2’ by fs []
    \\ drule_all evaluate_EL \\ fs [] \\ disch_then kall_tac
    \\ conj_tac
    \\ irule simpl_exp_Cons_EL \\ fs [] \\ metis_tac [])
  \\ gvs [PULL_EXISTS,FORALL_PROD,UNCURRY,do_eq_def |> CONJUNCT2]
  \\ simp [Once eq_pure_list_def]
  \\ pop_assum mp_tac
  \\ simp [Once eq_pure_list_def] \\ rw []
  \\ Cases_on ‘do_eq (FST y) (SND y)’ \\ fs []
  \\ reverse (Cases_on ‘b'’) \\ gvs []
  \\ imp_res_tac simple_exp_pure_every
  \\ last_x_assum drule
  \\ Cases_on ‘do_eq (FST y') (SND y')’ \\ fs [] \\ rw []
  \\ fs [evaluate_ConjList_append_F,evaluate_ConjList_append_T]
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
      \\ gvs [evaluate_def,AllCaseEqs(),do_app_def]
      \\ imp_res_tac evaluate_IMP_LENGTH
      \\ fs [EL_REVERSE,PRE_SUB1,EL_APPEND1])
    \\ Cases_on ‘∃k1 k2. op = TagLenEq k1 k2’
    THEN1
     (gvs [cons_op_def,dest_ElemAt_def,dest_TagLenEq_def]
      \\ gvs [evaluate_def,AllCaseEqs(),do_app_def,evaluate_MakeBool]
      \\ rw [] \\ eq_tac \\ rw []
      \\ imp_res_tac evaluate_IMP_LENGTH \\ fs [])
    \\ Cases_on ‘∃k. op = TagEq k’
    THEN1
     (gvs [cons_op_def,dest_ElemAt_def,dest_TagLenEq_def,dest_TagEq_def]
      \\ gvs [evaluate_def,AllCaseEqs(),do_app_def,evaluate_MakeBool])
    \\ Cases_on ‘∃k. op = LenEq k’
    THEN1
     (gvs [cons_op_def,dest_ElemAt_def,dest_TagLenEq_def,dest_TagEq_def,dest_LenEq_def]
      \\ gvs [evaluate_def,AllCaseEqs(),do_app_def,evaluate_MakeBool]
      \\ rw [] \\ eq_tac \\ rw []
      \\ imp_res_tac evaluate_IMP_LENGTH \\ fs [])
    \\ last_x_assum mp_tac
    \\ Cases_on ‘op’ \\ fs [] \\ EVAL_TAC)
  \\ reverse (Cases_on ‘dest_Op_Consts x y’) \\ gvs []
  THEN1
   (gvs [AllCaseEqs()]
    \\ Cases_on ‘x’ \\ fs [dest_Op_Consts_def,dest_Op_Nil_def,dest_Op_def,dest_Const_def]
    \\ Cases_on ‘o'’ \\ fs [dest_Op_Consts_def,dest_Op_def,dest_Const_def]
    \\ Cases_on ‘l’ \\ fs [dest_Op_Consts_def,dest_Op_def,dest_Const_def]
    \\ Cases_on ‘y’ \\ fs [dest_Op_Consts_def,dest_Op_def,dest_Const_def]
    \\ Cases_on ‘o'’ \\ fs [dest_Op_Consts_def,dest_Op_def,dest_Const_def]
    \\ Cases_on ‘l’ \\ gvs []
    \\ gvs [int_op_def,AllCaseEqs(),MakeInt_def]
    \\ gvs [evaluate_def,AllCaseEqs(),do_app_def,evaluate_MakeBool]
    \\ gvs [do_eq_def] \\ intLib.COOPER_TAC)
  \\ last_x_assum mp_tac
  \\ simp [eq_op_def,GSYM AND_IMP_INTRO]
  \\ disch_then kall_tac \\ fs [AllCaseEqs()]
  \\ reverse (Cases_on ‘eq_direct x y’) \\ rw []
  THEN1 (drule_all eq_direct_thm \\ fs [])
  \\ gvs [eq_any_def,AllCaseEqs()]
  \\ drule_at Any lift_exps_thm
  \\ simp [Once evaluate_def]
  \\ last_x_assum mp_tac
  \\ simp [Once evaluate_def]
  \\ Cases_on ‘evaluate ([x; y],env,s)’ \\ fs []
  \\ strip_tac \\ disch_then drule
  \\ strip_tac
  \\ simp [Once evaluate_def]
  \\ reverse (Cases_on ‘q’) \\ gvs []
  \\ CASE_TAC \\ fs []
  \\ imp_res_tac evaluate_IMP_LENGTH
  \\ gvs [LENGTH_EQ_NUM_compute,do_app_def]
  \\ rename [‘do_eq h1 h2’]
  \\ reverse (Cases_on ‘do_eq h1 h2’) \\ gvs []
  \\ imp_res_tac lift_exps_length \\ gvs []
  \\ first_x_assum (qspecl_then [‘env’,‘r’] assume_tac)
  \\ irule eq_pure_thm \\ fs []
  \\ imp_res_tac lift_exps_simple_exp \\ fs []
  \\ simp [Once do_eq_sym]
QED

Inductive red_rel:
[red_rel_Op:]
  (∀xs ys t op i tag t1 t2 s w.
    red_rel xs ys ∧
    MEM op [Add;Sub;Mult;Div;Mod;Less;LessEq;Greater;GreaterEq;Equal;Const i;
            Cons tag; TagEq tag; TagLenEq t1 t2; LenEq n;
            EqualConst (Str s); EqualConst (W64 w); EqualConst (Int i);
            ElemAt t1; Constant (ConstInt i); Constant (ConstStr s);
            Constant (ConstWord64 w)] ⇒
    red_rel [Op t op xs] ys)
  ∧
  (red_rel [] [])
  ∧
  (∀x. red_rel [x] [x])
  ∧
  (∀v t. red_rel [Var t v] [])
  ∧
[red_rel_multi:]
  (∀x y zs x1 x2.
    red_rel [x] x1 ∧ red_rel (y::zs) x2 ⇒
    red_rel (x::y::zs) (x1 ++ x2)) ∧
[red_rel_Let:]
  (∀xs x x1 t.
    red_rel xs x1 ∧ red_rel [x] [] ⇒
    red_rel [Let t xs x] x1) ∧
  (∀x y z x1 x2 x3.
    red_rel [x] x1 ∧ red_rel [y] x2 ∧  red_rel [z] x3 ⇒
    red_rel [If t x y z] (x1 ++ x2 ++ x3))
End

Theorem red_rel_nil =
  “red_rel [] ys” |> SIMP_CONV (srw_ss()) [Once red_rel_cases];

Theorem red_rel_ConjList:
  ∀xs. red_rel xs [] ⇒ red_rel [ConjList xs] []
Proof
  ho_match_mp_tac ConjList_ind
  \\ fs [ConjList_def] \\ rw [MakeBool_def]
  \\ simp [Once red_rel_cases]
  \\ pop_assum mp_tac
  \\ simp [Once red_rel_cases]
  \\ fs [] \\ rw []
  \\ simp [Once red_rel_cases]
  \\ simp [Once red_rel_cases]
QED

Theorem red_rel_EVERY:
  ∀xs. EVERY (λh. red_rel [h] []) xs ⇒ red_rel xs []
Proof
  Induct THEN1 simp [Once red_rel_cases]
  \\ Cases_on ‘xs’ \\ fs []
  \\ rw [] \\ fs []
  \\ simp [Once red_rel_cases]
QED

Theorem simple_exp_red_rel:
  ∀xs. EVERY simple_exp xs ⇒ red_rel xs []
Proof
  rw [] \\ irule red_rel_EVERY
  \\ irule MONO_EVERY
  \\ pop_assum $ irule_at Any \\ fs []
  \\ ho_match_mp_tac simple_exp_ind
  \\ rw []
  \\ simp [Once red_rel_cases]
  \\ TRY (simp [Once red_rel_cases] \\ NO_TAC)
  \\ irule red_rel_EVERY \\ fs []
QED

Theorem red_rel_eq_pure:
  simple_exp x ∧ simple_exp y ⇒ red_rel [eq_pure x y] []
Proof
  fs [eq_pure_def] \\ rw []
  \\ irule red_rel_ConjList
  \\ irule simple_exp_red_rel
  \\ irule simple_exp_eq_pure_list \\ fs []
QED

Theorem IMP_red_rel_cons_0:
  red_rel [x] ys ∧ red_rel xs zs ⇒ red_rel (x::xs) (ys ++ zs)
Proof
  rw [] \\ Cases_on ‘xs’ \\ fs [red_rel_nil]
  \\ simp [Once red_rel_cases]
  \\ metis_tac []
QED

Theorem red_rel_exists_append:
  red_rel (h::xs) ys ⇔
  ∃ys1 ys2. red_rel [h] ys1 ∧ red_rel xs ys2 ∧ ys = ys1 ++ ys2
Proof
  Cases_on ‘xs’ \\ fs [red_rel_nil]
  \\ simp [Once red_rel_cases]
  \\ metis_tac []
QED

Theorem IMP_red_rel_append:
  ∀xs ys xs1 ys1.
    red_rel xs ys ∧ red_rel xs1 ys1 ⇒ red_rel (xs ++ xs1) (ys ++ ys1)
Proof
  Induct \\ gvs [red_rel_nil]
  \\ rw [] \\ rewrite_tac [GSYM APPEND |> CONJUNCT2]
  \\ fs [Once red_rel_exists_append] \\ gvs []
  \\ rpt (last_x_assum $ irule_at Any)
  \\ fs []
QED

Theorem IMP_red_rel_cons:
  red_rel [x] [] ∧ red_rel xs ys ⇒ red_rel (x::xs) ys
Proof
  rw [] \\ simp [Once red_rel_exists_append]
  \\ metis_tac [APPEND]
QED

Theorem IMP_red_rel_cons_1:
  red_rel xs ys ⇒ red_rel (x::xs) (x::ys)
Proof
  rw [] \\ simp [Once red_rel_exists_append]
  \\ qexists_tac ‘[x]’ \\ fs []
  \\ simp [Once red_rel_cases]
QED

Theorem lift_exps_red_rel:
  ∀xs n binds ys k binds2.
    lift_exps xs n binds = (ys,k,binds2) ⇒
    ∃zs. red_rel xs zs ∧ red_rel (DROP (LENGTH binds) binds2) zs
Proof
  ho_match_mp_tac lift_exps_ind
  \\ fs [lift_exps_def]
  \\ rw [DROP_LENGTH_NIL,red_rel_nil]
  \\ pairarg_tac \\ gvs []
  \\ imp_res_tac lift_exps_acc \\ gvs [DROP_LENGTH_APPEND]
  THEN1
   (last_x_assum $ irule_at Any
    \\ irule IMP_red_rel_cons \\ fs []
    \\ gvs [dont_lift_def,AllCaseEqs()]
    \\ Cases_on ‘dest_Op_Nil dest_Const x’ \\ gvs [dest_Op_Nil_thm]
    \\ Cases_on ‘dest_Op_Nil dest_Cons x’ \\ gvs [dest_Op_Nil_thm]
    \\ Cases_on ‘dest_Op_Nil dest_Constant x’ \\ gvs [dest_Op_Nil_thm]
    \\ gvs [dest_Cons_thm]
    \\ gvs [dest_Const_thm]
    \\ gvs [dest_Constant_thm]
    \\ simp [Once red_rel_cases]
    \\ simp [Once red_rel_cases])
  \\ Cases_on ‘dest_Op dest_Cons x’ \\ gvs []
  THEN1
   (full_simp_tac std_ss [APPEND,GSYM APPEND_ASSOC]
    \\ full_simp_tac std_ss [GSYM DROP_DROP_T |> ONCE_REWRITE_RULE [ADD_COMM]]
    \\ full_simp_tac std_ss [DROP_LENGTH_APPEND] \\ gvs []
    \\ drule IMP_red_rel_cons_1
    \\ disch_then (qspec_then ‘x’ $ irule_at Any)
    \\ irule_at Any IMP_red_rel_cons_1 \\ fs [])
  \\ PairCases_on ‘x'’ \\ gvs []
  \\ rpt (pairarg_tac \\ gvs [])
  \\ imp_res_tac lift_exps_acc \\ gvs [DROP_LENGTH_APPEND]
  \\ full_simp_tac std_ss [APPEND,GSYM APPEND_ASSOC]
  \\ full_simp_tac std_ss [DROP_LENGTH_APPEND]
  \\ full_simp_tac std_ss [GSYM DROP_DROP_T |> ONCE_REWRITE_RULE [ADD_COMM]]
  \\ full_simp_tac std_ss [DROP_LENGTH_APPEND] \\ gvs []
  \\ irule_at Any IMP_red_rel_cons_0
  \\ irule_at Any IMP_red_rel_append
  \\ rpt (first_x_assum $ irule_at Any)
  \\ gvs [dest_Op_thm,dest_Cons_thm]
  \\ irule_at Any red_rel_Op \\ fs []
QED

Theorem eq_direct_red_rel:
  eq_direct x y = SOME z ⇒
  ∃ys. red_rel [x; y] ys ∧ red_rel [z] ys
Proof
  rw [] \\ gvs [eq_direct_def,AllCaseEqs()]
  \\ gvs [eq_direct_const_def,AllCaseEqs()]
  \\ gvs [eq_direct_constant_def,AllCaseEqs()]
  \\ gvs [eq_direct_nil_def,AllCaseEqs(),MakeBool_def]
  \\ irule_at Any red_rel_Op \\ fs []
  \\ gvs [dest_Op_Nil_thm,dest_Cons_thm,dest_Const_thm,dest_Constant_thm]
  \\ TRY (irule_at Any red_rel_multi \\ fs []
  \\ rpt (irule_at Any red_rel_Op \\ fs [])
  \\ fs [red_rel_nil]
  \\ simp [Once red_rel_cases]
  \\ metis_tac [])
QED

Theorem red_rel_refl:
  ∀xs. red_rel xs xs
Proof
  Induct \\ fs [red_rel_nil,IMP_red_rel_cons_1]
QED

Theorem red_rel_exists:
  ∀t op xs. ∃ys. red_rel [Op t op xs] ys ∧ red_rel [SmartOp t op xs] ys
Proof
  rw [SmartOp_def]
  \\ Cases_on ‘SmartOp' t op xs’ \\ fs []
  THEN1 (simp [Once red_rel_cases] THEN1 metis_tac [])
  \\ gvs [SmartOp'_def,AllCaseEqs()]
  THEN1
   (Cases_on ‘op’ \\ gvs [cons_op_def,dest_ElemAt_def,dest_TagLenEq_def,
      dest_TagEq_def,dest_LenEq_def]
    \\ gvs [dest_Op_thm,dest_Cons_thm,MakeBool_def]
    \\ rpt (irule_at (Pos hd) red_rel_Op \\ fs [])
    \\ rpt (irule_at Any red_rel_Let \\ fs [])
    \\ simp [Once red_rel_cases,red_rel_nil]
    \\ metis_tac [red_rel_refl])
  THEN1
   (first_x_assum mp_tac
    \\ fs [eq_op_def,GSYM AND_IMP_INTRO]
    \\ disch_then kall_tac
    \\ fs [AllCaseEqs()]
    \\ rename [‘eq_any x y = SOME z’]
    \\ reverse (Cases_on ‘eq_direct x y’) \\ rw []
    THEN1 (irule_at Any red_rel_Op \\ fs []
           \\ irule eq_direct_red_rel \\ fs [])
    \\ gvs [eq_any_def,AllCaseEqs()]
    \\ irule_at Any red_rel_Let
    \\ drule lift_exps_simple_exp \\ rw [red_rel_eq_pure]
    \\ irule_at Any red_rel_Op \\ fs []
    \\ drule lift_exps_red_rel \\ fs [])
  \\ gvs [dest_Op_Consts_def,AllCaseEqs(),dest_Op_Nil_thm,dest_Const_thm]
  \\ qexists_tac ‘[]’
  \\ gvs [int_op_def,AllCaseEqs(),MakeInt_def,MakeBool_def]
  \\ rpt (simp [Once red_rel_cases])
QED

Theorem red_rel_pure:
  ∀xs ys. red_rel xs ys ⇒ (EVERY pure xs ⇔ EVERY pure ys)
Proof
  ho_match_mp_tac red_rel_ind
  \\ fs [pure_def] \\ rpt conj_tac
  \\ rpt gen_tac \\ rw []
  \\ fs [SF ETA_ss,pure_op_def]
  \\ eq_tac \\ rw []
QED

Theorem red_rel_elist_globals:
  ∀xs ys. red_rel xs ys ⇒ (elist_globals xs = elist_globals ys)
Proof
  ho_match_mp_tac red_rel_ind
  \\ fs [set_globals_def,closPropsTheory.elist_globals_append]
  \\ rw [] \\ rw [op_gbag_def]
QED

Theorem red_rel_esgc_free:
  ∀xs ys. red_rel xs ys ⇒ (EVERY esgc_free xs ⇔ EVERY esgc_free ys)
Proof
  ho_match_mp_tac red_rel_ind
  \\ fs [esgc_free_def]
  \\ rw [] \\ eq_tac \\ rw []
QED

Theorem SmartOp_simp:
  pure (SmartOp t op xs) = pure (Op t op xs) ∧
  set_globals (SmartOp t op xs) = set_globals (Op t op xs) ∧
  esgc_free (SmartOp t op xs) = esgc_free (Op t op xs)
Proof
  qspecl_then [‘t’,‘op’,‘xs’] strip_assume_tac red_rel_exists
  \\ imp_res_tac red_rel_pure \\ fs []
  \\ imp_res_tac red_rel_elist_globals \\ fs []
  \\ imp_res_tac red_rel_esgc_free \\ fs []
QED

Theorem SmartOp_Const:
  ∀xs. SmartOp t (Const i) xs = Op t (Const i) xs
Proof
  ho_match_mp_tac list_split3 \\ EVAL_TAC \\ rw []
  \\ Cases_on ‘x’ \\ fs [dest_Op_def,dest_Const_def]
  \\ Cases_on ‘o'’ \\ fs [dest_Op_def,dest_Const_def,dest_Cons_def]
  \\ Cases_on ‘l’ \\ fs [dest_Op_def,dest_Const_def]
  \\ Cases_on ‘y’ \\ fs [dest_Op_def,dest_Const_def]
  \\ Cases_on ‘o'’ \\ fs [dest_Op_def,dest_Const_def]
  \\ Cases_on ‘l’ \\ fs [dest_Op_def,dest_Const_def]
QED

Theorem SmartOp_Cons:
  ∀xs. SmartOp t (Cons n) xs = Op t (Cons n) xs
Proof
  ho_match_mp_tac list_split3 \\ EVAL_TAC \\ rw []
  \\ Cases_on ‘x’ \\ fs [dest_Op_def,dest_Const_def]
  \\ Cases_on ‘o'’ \\ fs [dest_Op_def,dest_Const_def,dest_Cons_def]
  \\ Cases_on ‘l’ \\ fs [dest_Op_def,dest_Const_def]
  \\ Cases_on ‘y’ \\ fs [dest_Op_def,dest_Const_def]
  \\ Cases_on ‘o'’ \\ fs [dest_Op_def,dest_Const_def]
  \\ Cases_on ‘l’ \\ fs [dest_Op_def,dest_Const_def]
QED

Theorem SmartOp_Install:
  SmartOp t Install = Op t Install
Proof
  simp [FUN_EQ_THM]
  \\ ho_match_mp_tac list_split3 \\ EVAL_TAC \\ rw []
  \\ Cases_on ‘x’ \\ fs [dest_Op_def,dest_Const_def]
  \\ Cases_on ‘o'’ \\ fs [dest_Op_def,dest_Const_def,dest_Cons_def]
  \\ Cases_on ‘l’ \\ fs [dest_Op_def,dest_Const_def]
  \\ Cases_on ‘y’ \\ fs [dest_Op_def,dest_Const_def]
  \\ Cases_on ‘o'’ \\ fs [dest_Op_def,dest_Const_def]
  \\ Cases_on ‘l’ \\ fs [dest_Op_def,dest_Const_def]
QED

Theorem code_locs_SmartOp:
  LIST_TO_BAG (code_locs [SmartOp t op xs]) =
  LIST_TO_BAG (code_locs [Op t op xs])
Proof
  qspecl_then [‘t’,‘op’,‘xs’] strip_assume_tac red_rel_exists
  \\ qsuff_tac ‘∀xs ys.
     red_rel xs ys ⇒ LIST_TO_BAG (code_locs xs) = LIST_TO_BAG (code_locs ys)’
  THEN1 (disch_then imp_res_tac \\ fs [])
  \\ ho_match_mp_tac red_rel_ind
  \\ fs [code_locs_def,code_locs_append,LIST_TO_BAG_APPEND]
QED

Theorem every_Fn_SOME_SmartOp:
  every_Fn_SOME [SmartOp t op xs] = every_Fn_SOME [Op t op xs]
Proof
  qspecl_then [‘t’,‘op’,‘xs’] strip_assume_tac red_rel_exists
  \\ qsuff_tac ‘∀xs ys. red_rel xs ys ⇒ every_Fn_SOME xs = every_Fn_SOME ys’
  THEN1 (disch_then imp_res_tac \\ fs [])
  \\ ho_match_mp_tac red_rel_ind
  \\ fs [every_Fn_SOME_def] \\ rw [] \\ eq_tac \\ rw []
QED

Theorem every_Fn_vs_NONE_SmartOp:
  every_Fn_vs_NONE xs ⇒ every_Fn_vs_NONE [SmartOp t op xs]
Proof
  qspecl_then [‘t’,‘op’,‘xs’] strip_assume_tac red_rel_exists
  \\ qsuff_tac ‘∀xs ys. red_rel xs ys ⇒ every_Fn_vs_NONE xs = every_Fn_vs_NONE ys’
  THEN1 (disch_then imp_res_tac \\ fs [every_Fn_vs_NONE_def] \\ rw [] \\ fs [])
  \\ ho_match_mp_tac red_rel_ind
  \\ fs [every_Fn_vs_NONE_def] \\ rw [] \\ eq_tac \\ rw []
QED

Theorem no_Labels_SmartOp:
  no_Labels (SmartOp t op xs) ⇔ no_Labels (Op t op xs)
Proof
  qspecl_then [‘t’,‘op’,‘xs’] strip_assume_tac red_rel_exists
  \\ qsuff_tac ‘∀xs ys. red_rel xs ys ⇒ EVERY no_Labels xs = EVERY no_Labels ys’
  THEN1 (disch_then imp_res_tac \\ fs [])
  \\ ho_match_mp_tac red_rel_ind
  \\ fs [no_Labels_def]
  \\ rw [] \\ fs [] \\ eq_tac \\ rw []
QED

Theorem obeys_max_app_SmartOp:
  EVERY (obeys_max_app k) xs ⇒ obeys_max_app k (SmartOp t op xs)
Proof
  qspecl_then [‘t’,‘op’,‘xs’] strip_assume_tac red_rel_exists
  \\ qsuff_tac ‘∀xs ys. red_rel xs ys ⇒
       EVERY (obeys_max_app k) xs = EVERY (obeys_max_app k) ys’
  THEN1 (disch_then imp_res_tac \\ fs [])
  \\ ho_match_mp_tac red_rel_ind
  \\ fs [no_Labels_def]
  \\ rw [] \\ fs [] \\ eq_tac \\ rw []
QED

Theorem lift_exps_fv:
  ∀xs n binds ys k binds2.
    lift_exps xs n binds = (ys,k,binds2) ∧ n = LENGTH binds ⇒
    k = LENGTH binds2 ∧
    (∀l. fv l binds2 ⇒ fv l xs ∨ fv l binds) ∧
    (∀l. fv l ys ⇒ l < k)
Proof
  ho_match_mp_tac lift_exps_ind \\ rpt conj_tac
  THEN1 fs [lift_exps_def]
  \\ rpt gen_tac \\ rpt conj_tac
  \\ strip_tac
  \\ rewrite_tac [lift_exps_def]
  \\ IF_CASES_TAC
  THEN1
   (fs [] \\ pairarg_tac \\ rpt strip_tac \\ gvs []
    \\ gvs [dont_lift_thm]
    \\ rewrite_tac [fv1_def,fv_def]
    \\ gvs [] \\ full_simp_tac std_ss [fv1_def,fv_def])
  \\ fs []
  \\ Cases_on ‘dest_Op dest_Cons x’ \\ gvs []
  THEN1
   (rpt (pairarg_tac \\ fs []) \\ strip_tac \\ gvs []
    \\ full_simp_tac std_ss [fv1_def,fv_def]
    \\ rw [] \\ res_tac \\ fs []
    \\ imp_res_tac lift_exps_acc
    \\ gvs [])
  \\ rpt (pairarg_tac \\ fs []) \\ strip_tac \\ gvs []
  \\ PairCases_on ‘x'’ \\ fs []
  \\ rpt (pairarg_tac \\ fs []) \\ strip_tac \\ gvs []
  \\ full_simp_tac std_ss [fv1_def,fv_def]
  \\ rw [] \\ res_tac \\ fs []
  \\ imp_res_tac lift_exps_acc
  \\ gvs [] \\ res_tac \\ fs []
  \\ gvs [dest_Op_thm,dest_Cons_thm]
  \\ full_simp_tac std_ss [fv1_def,fv_def]
QED

Theorem fv1_ConjList:
  ∀xs. fv1 n (ConjList xs) = fv n xs
Proof
  ho_match_mp_tac ConjList_ind \\ fs [ConjList_def]
  \\ full_simp_tac std_ss [fv1_def,fv_def,MakeBool_def]
QED

Theorem fv1_EL:
  ∀xs n k. fv1 n (EL k xs) ∧ k < LENGTH xs ⇒ fv n xs
Proof
  Induct \\ fs [] \\ Cases_on ‘k’ \\ fs []
  \\ rw [] \\ res_tac \\ fs []
QED

Theorem fv1_eq_pure:
  fv1 n (eq_pure x y) ⇒ fv1 n x ∨ fv1 n y
Proof
  fs [eq_pure_def,fv1_ConjList]
  \\ qsuff_tac ‘∀xs.
    fv n (append (eq_pure_list xs)) ⇒ EXISTS (λ(x,y). fv1 n x ∨ fv1 n y) xs’
  THEN1 (rw [] \\ res_tac \\ fs [])
  \\ ho_match_mp_tac eq_pure_list_ind \\ rw []
  THEN1 fs [eq_pure_list_def]
  \\ pop_assum mp_tac
  \\ simp [Once eq_pure_list_def]
  \\ rw [] \\ gvs []
  \\ reverse (Cases_on ‘eq_direct x y’ \\ fs [])
  THEN1
   (gvs [eq_direct_def,eq_direct_const_def,eq_direct_nil_def,eq_direct_constant_def,AllCaseEqs()]
    \\ gvs [dest_Op_Nil_thm]
    \\ full_simp_tac std_ss [fv1_def,fv_def,MakeBool_def])
  \\ Cases_on ‘dest_Op dest_Cons x’ \\ gvs []
  \\ Cases_on ‘dest_Op dest_Cons y’ \\ gvs []
  \\ full_simp_tac std_ss [fv1_def,fv_def,MakeBool_def]
  \\ PairCases_on ‘x'’
  \\ TRY (PairCases_on ‘x''’)
  \\ gvs [dest_Op_thm,dest_Cons_thm]
  \\ full_simp_tac std_ss [fv1_def,fv_def,MakeBool_def]
  \\ every_case_tac \\ gvs []
  \\ full_simp_tac std_ss [fv1_def,fv_def,MakeBool_def]
  \\ gvs [EXISTS_MEM,UNCURRY,MEM_MAPi,MEM_ZIP]
  \\ full_simp_tac std_ss [fv1_def,fv_def,MakeBool_def]
  \\ gvs [EL_REVERSE,PRE_SUB1]
  \\ drule fv1_EL \\ fs []
QED

Theorem eq_op_fv:
  eq_op x y = SOME z ⇒ fv n [z] ⇒ fv n [x] ∨ fv n [y]
Proof
  fs [eq_op_def,GSYM AND_IMP_INTRO]
  \\ disch_then kall_tac
  \\ reverse (Cases_on ‘eq_direct x y’) \\ fs [] \\ rw []
  THEN1
   (gvs [eq_direct_def,AllCaseEqs(),eq_direct_nil_def,eq_direct_const_def,eq_direct_constant_def]
    \\ pop_assum mp_tac
    \\ rewrite_tac [fv1_def,fv_def,MakeBool_def] \\ fs [])
  \\ gvs [eq_any_def,AllCaseEqs()]
  \\ pop_assum mp_tac
  \\ rewrite_tac [fv1_def,fv_def,MakeBool_def]
  \\ drule lift_exps_fv \\ gvs []
  \\ strip_tac \\ gvs []
  \\ rw [] \\ fs []
  \\ imp_res_tac fv1_eq_pure
  \\ res_tac \\ fs []
QED

Theorem fv1_SmartOp:
  fv1 n (SmartOp t op xs) ⇒ fv1 n (Op t op xs)
Proof
  simp [SmartOp_def]
  \\ CASE_TAC \\ fs []
  \\ gvs [SmartOp'_def,AllCaseEqs(),cons_op_def]
  \\ rewrite_tac [fv1_def,fv_def,MakeBool_def]
  \\ gvs [dest_Op_Consts_def,AllCaseEqs(),dest_Op_Nil_thm,dest_Op_thm,dest_Cons_def]
  \\ rewrite_tac [fv1_def,fv_def,MakeBool_def]
  THEN1 (imp_res_tac eq_op_fv \\ fs [])
  THEN1 (imp_res_tac eq_op_fv \\ gvs [dest_Const_thm]
         \\ pop_assum mp_tac \\ rewrite_tac [fv1_def,fv_def]
         \\ rw [] \\ res_tac \\ fs [])
  \\ gvs [int_op_def,AllCaseEqs(),MakeInt_def,MakeBool_def]
  \\ rewrite_tac [fv1_def,fv_def]
QED

val _ = export_theory();
