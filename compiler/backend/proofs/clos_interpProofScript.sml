(*
  Correctness proof for closLang interpreter used by the REPL, i.e. Install,
  to avoid spending time compiling simple run-once code in declarations.
*)
open preamble backendPropsTheory closLangTheory closSemTheory closPropsTheory
     clos_interpTheory;

val _ = new_theory "clos_interpProof";

val _ = set_grammar_ancestry ["closLang", "closProps", "clos_interp"];

(* ------------------------------------------------------------------------- *
   correctness of interpreter
 * ------------------------------------------------------------------------- *)

Definition state_rel_def:
  state_rel (s:('c,'ffi) closSem$state) (t:('c,'ffi) closSem$state) <=>
    (!n. SND (SND (s.compile_oracle n)) = []) ∧
    s.code = FEMPTY ∧ t.code = FEMPTY ∧
    t.max_app = s.max_app ∧ 1 <= s.max_app ∧
    t.clock = s.clock ∧
    t.ffi = s.ffi ∧
    s.globals = t.globals ∧
    s.refs = t.refs ∧
    s.compile = pure_cc (insert_interp ## I) t.compile ∧
    t.compile_oracle = pure_co (insert_interp ## I) o s.compile_oracle ∧
    oHD (s.globals) = SOME (SOME (Closure NONE [] [] 1 clos_interpreter))
End

Definition state_rel_1_def:
  state_rel_1 (s:('c,'ffi) closSem$state) (t:('c,'ffi) closSem$state) <=>
    (!n. SND (SND (s.compile_oracle n)) = []) ∧
    s.code = FEMPTY ∧ t.code = FEMPTY ∧
    t.max_app = s.max_app ∧ 1 <= s.max_app ∧
    t.clock = s.clock ∧
    t.ffi = s.ffi ∧
    s.globals = t.globals ∧
    s.refs = t.refs ∧
    s.compile = pure_cc (insert_interp ## I) t.compile ∧
    t.compile_oracle = pure_co (insert_interp ## I) o s.compile_oracle
End

Triviality LIST_REL_eq:
  ∀xs ys. LIST_REL (λv1 v2. v1 = v2) xs ys ⇔ xs = ys
Proof
  Induct \\ fs []
  \\ Cases_on ‘ys’ \\ fs []
  \\ rw [] \\ eq_tac \\ rw []
QED

Triviality LIST_REL_OPTREL_eq:
  ∀xs ys. LIST_REL (OPTREL (λv1 v2. v1 = v2)) xs ys ⇔ xs = ys
Proof
  Induct \\ fs []
  \\ Cases_on ‘ys’ \\ fs []
  \\ rw [] \\ eq_tac \\ rw []
  \\ Cases_on ‘h’
  \\ Cases_on ‘h'’
  \\ gvs []
QED

Theorem do_app_oHD_globals:
  do_app p vs s1 = Rval (v,s2) ⇒
  oHD s1.globals = SOME (SOME x) ⇒
  oHD s2.globals = SOME (SOME x)
Proof
  strip_tac
  \\ gvs [do_app_def,AllCaseEqs()]
  \\ Cases_on ‘s1.globals’ \\ fs []
  \\ fs [get_global_def] \\ rw []
  \\ rename [‘LUPDATE _ nn’]
  \\ Cases_on ‘nn’ \\ gvs [LUPDATE_def]
QED

Theorem evaluate_insert_interp:
  (∀xs s1 env (t1:('c,'ffi) closSem$state) res s2.
     s1.clock ≤ s4.clock ∧
     evaluate (xs,env,s1) = (res,s2) ∧
     res ≠ Rerr (Rabort Rtype_error) ⇒
     state_rel s1 t1 ⇒
     ∃ck t2.
       evaluate (xs,env,t1 with clock := ck + t1.clock) = (res,t2) ∧
       state_rel s2 t2) ∧
  (∀args s1 loc f (t1:('c,'ffi) closSem$state) res s2.
     s1.clock ≤ s4.clock ∧
     evaluate_app loc f args s1 = (res,s2) ∧
     res ≠ Rerr (Rabort Rtype_error) ⇒
     state_rel s1 t1 ⇒
     ∃ck t2.
       evaluate_app loc f args (t1 with clock := ck + t1.clock) =
       (res,t2) ∧ state_rel s2 t2) ∧
  evaluate (exps,[],s4) = (r,s5) ∧ state_rel s4 t4 ∧ r ≠ Rerr (Rabort Rtype_error) ⇒
  ∃ck (t5:('c,'ffi) closSem$state).
    evaluate (insert_interp exps,[],t4 with clock := t4.clock + ck) = (r,t5) ∧
    state_rel s5 t5
Proof
  cheat
QED

Theorem evaluate_interp_lemma:
  (∀xs (s1:('c,'ffi) closSem$state) env t1 res s2.
     (evaluate (xs,env,s1) = (res,s2)) ∧ res <> Rerr (Rabort Rtype_error) ⇒
     state_rel s1 t1 ⇒
     ?ck t2.
       (evaluate (xs,env,(t1 with clock := t1.clock + ck)) = (res,t2)) ∧
       state_rel s2 t2) ∧
  (∀args (s1:('c,'ffi) closSem$state) loc f t1 res s2.
     evaluate_app loc f args s1 = (res,s2) ∧ res <> Rerr (Rabort Rtype_error) ⇒
     state_rel s1 t1 ⇒
     ?ck t2.
       (evaluate_app loc f args (t1 with clock := t1.clock + ck) = (res,t2)) ∧
       state_rel s2 t2)
Proof
  ho_match_mp_tac evaluate_better_ind \\ gvs [PULL_FORALL, GSYM CONJ_ASSOC] \\ rw []
  >~ [‘evaluate_app _ _ args s1’] >-
   (rename [‘state_rel s1 t1’]
    \\ Cases_on ‘args’ \\ gvs [] \\ rw []
    >- (qexists_tac ‘0’ \\ fs [state_rel_def])
    \\ fs [evaluate_def]
    \\ ‘s1.max_app = t1.max_app ∧
        s1.clock = t1.clock’ by fs [state_rel_def]
    \\ CASE_TAC >- gvs []
    \\ CASE_TAC
    >- (qexists_tac ‘0’ \\ gvs [state_rel_def,dec_clock_def,AllCaseEqs(),PULL_EXISTS])
    \\ gvs [CaseEq"bool"]
    >- (qexists_tac ‘0’ \\ gvs [state_rel_def,dec_clock_def,AllCaseEqs(),PULL_EXISTS])
    \\ gvs [CaseEq"prod"]
    \\ last_x_assum $ drule_at $ Pos $ el 3
    \\ disch_then $ qspec_then ‘(dec_clock (SUC (LENGTH t) − LENGTH l0) t1)’ mp_tac
    \\ ‘(dec_clock (SUC (LENGTH t) − LENGTH l0) s1).clock < t1.clock’ by
      (fs [dec_clock_def] \\ imp_res_tac dest_closure_length \\ fs [])
    \\ impl_tac
    >- (gvs [] \\ gvs [dec_clock_def,state_rel_def,NOT_LESS] \\ strip_tac \\ gvs [])
    \\ strip_tac \\ fs [PULL_EXISTS]
    \\ reverse (gvs [AllCaseEqs()])
    >- (qexists_tac ‘ck’ \\ gvs [dec_clock_def,PULL_EXISTS] \\ gvs [AllCaseEqs()])
    >- (qexists_tac ‘ck’ \\ gvs [dec_clock_def,PULL_EXISTS] \\ gvs [AllCaseEqs()])
    \\ gvs [PULL_EXISTS]
    \\ first_assum $ drule_at $ Pos $ el 3
    \\ disch_then $ drule_at $ Pos last
    \\ imp_res_tac dest_closure_length \\ fs []
    \\ imp_res_tac evaluate_clock \\ fs []
    \\ strip_tac \\ fs []
    \\ qpat_x_assum ‘evaluate ([_],_) = _’ assume_tac
    \\ drule evaluate_add_clock \\ fs []
    \\ disch_then $ qspec_then ‘ck'’ assume_tac
    \\ qexists_tac ‘ck+ck'’ \\ gvs [dec_clock_def])
  \\ Cases_on ‘xs’ \\ fs []
  >- (qexists_tac ‘0’ \\ gvs [evaluate_def,state_rel_def])
  \\ rename [‘evaluate (x::xs,_)’]
  \\ reverse (Cases_on ‘xs’) \\ fs []
  >-
   (gvs [evaluate_def,CaseEq"prod",PULL_EXISTS]
    \\ first_assum $ drule_at $ Pos $ el 3
    \\ disch_then $ drule_at $ Pos last
    \\ impl_tac >- (fs [exp_size_def] \\ strip_tac \\ gvs [])
    \\ strip_tac \\ fs []
    \\ reverse (gvs [CaseEq"result"])
    >- (qexists_tac ‘ck’ \\ fs [])
    \\ gvs [CaseEq"prod"]
    \\ qpat_x_assum ‘evaluate (h::t,_) = _’ assume_tac
    \\ first_assum $ drule_at $ Pos $ el 3
    \\ disch_then $ drule_at $ Pos last
    \\ impl_tac >- (fs [exp_size_def]
                    \\  imp_res_tac evaluate_clock \\ fs []
                    \\ strip_tac \\ gvs [])
    \\ strip_tac
    \\ qpat_x_assum ‘evaluate ([_],_) = _’ assume_tac
    \\ drule evaluate_add_clock \\ fs []
    \\ disch_then $ qspec_then ‘ck'’ assume_tac
    \\ qexists_tac ‘ck+ck'’ \\ fs []
    \\ gvs [AllCaseEqs()])
  \\ Cases_on ‘x’ \\ gvs []
  >~ [‘App t opt x xs’] >-
   (gvs [evaluate_def,CaseEq"prod",PULL_EXISTS]
    \\ gvs [evaluate_def,CaseEq"bool",PULL_EXISTS]
    \\ gvs [evaluate_def,CaseEq"prod",PULL_EXISTS]
    \\ first_assum $ drule_at $ Pos $ el 3
    \\ disch_then $ drule_at $ Pos last
    \\ impl_tac >- (fs [exp_size_def] \\ strip_tac \\ gvs [])
    \\ strip_tac \\ fs []
    \\ reverse (gvs [CaseEq"result"])
    >- (qexists_tac ‘ck’ \\ fs [])
    \\ gvs [evaluate_def,CaseEq"prod",PULL_EXISTS]
    \\ qpat_x_assum ‘evaluate ([x],_) = _’ assume_tac
    \\ first_assum $ drule_at $ Pos $ el 3
    \\ disch_then $ drule_at $ Pos last
    \\ imp_res_tac evaluate_clock \\ fs []
    \\ impl_tac >- (fs [exp_size_def] \\ strip_tac \\ gvs [])
    \\ strip_tac \\ fs []
    \\ qpat_x_assum ‘evaluate (xs,_) = _’ assume_tac
    \\ drule evaluate_add_clock \\ fs []
    \\ disch_then $ qspec_then ‘ck'’ assume_tac
    \\ reverse (gvs [CaseEq"result"])
    >- (qexists_tac ‘ck+ck'’ \\ fs [])
    \\ last_x_assum kall_tac
    \\ first_assum $ drule_at $ Pos $ el 3
    \\ disch_then $ drule_at $ Pos last
    \\ impl_tac >-
     (fs [exp_size_def]
      \\ rw [] \\ imp_res_tac evaluate_IMP_LENGTH \\ fs []
      \\ qsuff_tac ‘LENGTH xs ≤ exp3_size xs’ >- fs []
      \\ qid_spec_tac ‘xs’ \\ Induct \\ fs [])
    \\ strip_tac
    \\ qpat_x_assum ‘evaluate (xs,_) = _’ assume_tac
    \\ drule evaluate_add_clock \\ fs []
    \\ disch_then $ qspec_then ‘ck''’ assume_tac
    \\ qpat_x_assum ‘evaluate ([_],_) = _’ assume_tac
    \\ drule evaluate_add_clock \\ fs []
    \\ disch_then $ qspec_then ‘ck''’ assume_tac
    \\ qexists_tac ‘ck+ck'+ck''’ \\ fs [])
  >~ [‘Var’] >-
   (qexists_tac ‘0’ \\ gvs [evaluate_def,AllCaseEqs(),state_rel_def])
  >~ [‘Fn’] >-
   (qexists_tac ‘0’ \\ gvs [evaluate_def,AllCaseEqs(),state_rel_def])
  >~ [‘Tick’] >-
   (gvs [evaluate_def,AllCaseEqs()]
    >- (qexists_tac ‘0’ \\ fs [state_rel_def])
    \\ first_assum $ drule_at $ Pos $ el 3
    \\ disch_then $ qspec_then ‘dec_clock 1 t1’ mp_tac
    \\ impl_tac >- (fs [exp_size_def,dec_clock_def] \\ gvs [state_rel_def])
    \\ strip_tac
    \\ qexists_tac ‘ck’
    \\ ‘s1.clock = t1.clock’ by fs [state_rel_def]
    \\ fs [dec_clock_def]
    \\ first_assum $ irule_at Any
    \\ ‘(ck + (t1.clock − 1)) = (ck + t1.clock) − 1’ by fs []
    \\ fs [])
  >~ [‘Raise’] >-
   (gvs [evaluate_def,CaseEq"prod",PULL_EXISTS]
    \\ first_assum $ drule_at $ Pos $ el 3
    \\ disch_then $ drule_at $ Pos last
    \\ impl_tac >- (fs [exp_size_def,dec_clock_def] \\ strip_tac \\ gvs [])
    \\ strip_tac \\ qexists_tac ‘ck’ \\ fs []
    \\ gvs [AllCaseEqs()])
  >~ [‘If’] >-
   (gvs [evaluate_def,CaseEq"prod",PULL_EXISTS]
    \\ first_assum $ drule_at $ Pos $ el 3
    \\ disch_then $ drule_at $ Pos last
    \\ impl_tac >- (fs [exp_size_def,dec_clock_def] \\ strip_tac \\ gvs [])
    \\ strip_tac
    \\ reverse $ gvs [CaseEq"result"]
    >- (qexists_tac ‘ck’ \\ fs [])
    \\ imp_res_tac evaluate_SING \\ gvs []
    \\ reverse $ gvs [CaseEq"bool"]
    \\ ntac 2 $ pop_assum mp_tac
    \\ first_assum $ drule_at $ Pos $ el 3
    \\ rw []
    \\ first_assum $ drule_at $ Pos last
    \\ imp_res_tac evaluate_clock
    \\ (impl_tac >- fs [])
    \\ strip_tac \\ fs []
    \\ ntac 2 $ pop_assum mp_tac
    \\ drule evaluate_add_clock \\ fs []
    \\ disch_then $ qspec_then ‘ck'’ assume_tac \\ rw []
    \\ qexists_tac ‘ck+ck'’ \\ gvs [dec_clock_def])
  >~ [‘Let’] >-
   (gvs [evaluate_def,CaseEq"prod",PULL_EXISTS]
    \\ first_assum $ drule_at $ Pos $ el 3
    \\ disch_then $ drule_at $ Pos last
    \\ impl_tac >- (fs [exp_size_def,dec_clock_def] \\ strip_tac \\ gvs [])
    \\ strip_tac
    \\ reverse $ gvs [CaseEq"result"]
    >- (qexists_tac ‘ck’ \\ fs [])
    \\ qpat_x_assum ‘evaluate ([_],_) = _’ assume_tac
    \\ first_assum $ drule_at $ Pos $ el 3
    \\ disch_then $ drule_at $ Pos last
    \\ imp_res_tac evaluate_clock
    \\ impl_tac >- fs []
    \\ strip_tac \\ fs []
    \\ qpat_x_assum ‘evaluate _ = (Rval _,_)’ assume_tac
    \\ drule evaluate_add_clock \\ fs []
    \\ disch_then $ qspec_then ‘ck'’ assume_tac \\ rw []
    \\ qexists_tac ‘ck+ck'’ \\ gvs [dec_clock_def])
  >~ [‘Handle’] >-
   (gvs [evaluate_def,CaseEq"prod",PULL_EXISTS]
    \\ first_assum $ drule_at $ Pos $ el 3
    \\ disch_then $ drule_at $ Pos last
    \\ impl_tac >- (fs [exp_size_def,dec_clock_def] \\ strip_tac \\ gvs [])
    \\ strip_tac
    \\ gvs [AllCaseEqs()]
    \\ TRY (qexists_tac ‘ck’ \\ fs [] \\ NO_TAC)
    \\ qpat_x_assum ‘evaluate ([e0],_) = _’ assume_tac
    \\ first_assum $ drule_at $ Pos $ el 3
    \\ disch_then $ drule_at $ Pos last
    \\ imp_res_tac evaluate_clock
    \\ impl_tac >- fs []
    \\ strip_tac \\ fs []
    \\ qpat_x_assum ‘evaluate _ = (Rerr _,_)’ assume_tac
    \\ drule evaluate_add_clock \\ fs []
    \\ disch_then $ qspec_then ‘ck'’ assume_tac \\ rw []
    \\ qexists_tac ‘ck+ck'’ \\ gvs [dec_clock_def])
  >~ [‘Call’] >-
   (gvs [evaluate_def,CaseEq"prod",PULL_EXISTS]
    \\ first_assum $ drule_at $ Pos $ el 3
    \\ disch_then $ drule_at $ Pos last
    \\ impl_tac >- (fs [exp_size_def,dec_clock_def] \\ strip_tac \\ gvs [])
    \\ strip_tac
    \\ reverse $ gvs [CaseEq"result"]
    >- (qexists_tac ‘ck’ \\ fs [])
    \\ gvs [CaseEq"option"]
    \\ gvs [find_code_def,state_rel_def])
  >~ [‘Letrec’] >-
   (gvs [evaluate_def,CaseEq"prod",PULL_EXISTS]
    \\ ‘s1.max_app = t1.max_app’ by fs [state_rel_def]
    \\ gvs [CaseEq"bool",CaseEq"option"]
    \\ first_assum $ drule_at $ Pos $ el 3
    \\ disch_then $ drule_at $ Pos last
    \\ (impl_tac >- (fs [exp_size_def,dec_clock_def] \\ strip_tac \\ gvs []))
    \\ strip_tac
    \\ qexists_tac ‘ck’ \\ fs [])
  \\ rename [‘Op t p xs’]
  \\ gvs [evaluate_def,CaseEq"prod",PULL_EXISTS]
  \\ first_assum $ drule_at $ Pos $ el 3
  \\ disch_then $ drule_at $ Pos last
  \\ impl_tac >- (fs [exp_size_def,dec_clock_def] \\ strip_tac \\ gvs [])
  \\ strip_tac
  \\ reverse $ gvs [CaseEq"result"]
  >- (qexists_tac ‘ck’ \\ fs [])
  \\ Cases_on ‘p ≠ Install’ \\ gvs []
  \\ gvs [evaluate_def,CaseEq"prod",PULL_EXISTS]
  >-
   (qabbrev_tac ‘vr = λv1 v2. v1 = v2:closSem$v’
    \\ ‘simple_val_rel vr’ by
      (fs [simple_val_rel_def]
       \\ rw [] \\ fs [Abbr‘vr’] \\ gvs [LIST_REL_eq])
    \\ rename [‘state_rel s3 t3’]
    \\ ‘state_rel_1 s3 t3’ by fs [state_rel_def,state_rel_1_def]
    \\ drule_at (Pos $ el 3) simple_val_rel_do_app
    \\ disch_then drule
    \\ rename [‘Rval vs’]
    \\ disch_then $ qspecl_then [‘REVERSE vs’,‘REVERSE vs’,‘p’] mp_tac
    \\ impl_tac >-
     (reverse conj_tac >- (qid_spec_tac ‘vs’ \\ Induct \\ gvs [Abbr‘vr’])
      \\ fs [simple_state_rel_def] \\ simp [Abbr‘vr’] \\ rpt $ pop_assum kall_tac
      \\ rw [] \\ gvs [state_rel_1_def]
      \\ TRY $ drule_all FEVERY_FLOOKUP \\ fs [LIST_REL_eq,LIST_REL_OPTREL_eq])
    \\ strip_tac
    \\ qexists_tac ‘ck’ \\ fs []
    \\ reverse $ gvs [AllCaseEqs()]
    \\ gvs [Abbr‘vr’] >- (Cases_on ‘err’ \\ gvs [])
    \\ fs [state_rel_def,state_rel_1_def]
    \\ drule_then irule do_app_oHD_globals \\ fs [])
  \\ rename [‘state_rel s3 t3’]
  \\ qpat_x_assum ‘do_install _ _ = _’ mp_tac
  \\ simp [Once do_install_def]
  \\ simp [AllCaseEqs()] \\ strip_tac \\ gvs []
  \\ pairarg_tac \\ gvs []
  \\ gvs [CaseEq"bool"]
  \\ gvs [CaseEq"option"]
  \\ gvs [CaseEq"prod"]
  \\ ‘s3.compile = pure_cc (insert_interp ## I) t3.compile ∧
      t3.compile_oracle = pure_co (insert_interp ## I) ∘ s3.compile_oracle ∧
      t3.clock = s3.clock ∧
      FDOM t3.code = EMPTY ∧ FDOM s3.code = EMPTY’
        by fs [state_rel_def]
  \\ ‘insert_interp exps ≠ []’ by (gvs [insert_interp_def] \\ gvs [AllCaseEqs()])
  \\ gvs [CaseEq"bool"]
  >-
   (qexists_tac ‘ck’ \\ fs []
    \\ simp [do_install_def]
    \\ fs [pure_co_def,pure_cc_def]
    \\ fs [o_DEF,shift_seq_def]
    \\ fs [state_rel_def,FUN_EQ_THM]
    \\ rpt (first_x_assum (qspec_then ‘0:num’ assume_tac) \\ gvs [FUPDATE_LIST]))
  \\ ‘aux = []’ by
   (fs [state_rel_def,FUN_EQ_THM]
    \\ rpt (first_x_assum (qspec_then ‘0:num’ assume_tac) \\ gvs [FUPDATE_LIST]))
  \\ gvs [SWAP_REVERSE_SYM,CaseEq"prod"]
  \\ drule_at (Pos $ el 3) evaluate_insert_interp \\ fs [FUPDATE_LIST]
  \\ disch_then $ qspec_then ‘t3 with
              <|clock := t3.clock − 1;
                compile_oracle := shift_seq 1 t3.compile_oracle;
                code := t3.code |>’ mp_tac
  \\ impl_tac
  >-
   (rpt strip_tac
    >-
     (last_x_assum irule \\ fs []
      \\ first_assum $ irule_at Any \\ fs []
      \\ imp_res_tac evaluate_clock \\ fs [])
    >-
     (last_x_assum irule \\ fs []
      \\ first_assum $ irule_at Any \\ fs []
      \\ imp_res_tac evaluate_clock \\ fs [])
    \\ gvs [FUN_EQ_THM,shift_seq_def,state_rel_def])
  \\ strip_tac
  \\ qpat_x_assum ‘evaluate _ = (Rval _,_)’ assume_tac
  \\ drule evaluate_add_clock \\ fs []
  \\ disch_then $ qspec_then ‘ck'’ assume_tac
  \\ qexists_tac ‘ck+ck'’ \\ fs [PULL_EXISTS]
  \\ fs [do_install_def,pure_co_def,shift_seq_def,pure_cc_def,pure_co_def,PULL_EXISTS]
  \\ gvs [FUPDATE_LIST]
  \\ gvs [AllCaseEqs()]
QED

Theorem evaluate_interp_thm:
   ∀xs env (s1:('c,'ffi) closSem$state) t1 res s2.
     evaluate (xs,env,s1) = (res,s2) ∧ res <> Rerr (Rabort Rtype_error) ∧
     state_rel s1 t1 ⇒
     ∃ck t2.
        evaluate (xs,env,(t1 with clock := t1.clock + ck)) = (res,t2) ∧
        state_rel s2 t2
Proof
  rw [] \\ imp_res_tac evaluate_interp_lemma
  \\ qexists_tac ‘ck’ \\ fs []
QED

(* ------------------------------------------------------------------------- *
   not has_install ignores compiler oracle
 * ------------------------------------------------------------------------- *)

Definition v_ok_def[simp]:
  (v_ok (Number i) ⇔ T) ∧
  (v_ok (Word64 w) ⇔ T) ∧
  (v_ok (Block n vs) ⇔ EVERY v_ok vs) ∧
  (v_ok (ByteVector ws) ⇔ T) ∧
  (v_ok (RefPtr n) ⇔ T) ∧
  (v_ok (Closure loco vs1 env1 n bod1) ⇔
    ~ has_install bod1 ∧ EVERY v_ok env1 ∧ EVERY v_ok vs1) ∧
  (v_ok (Recclosure loco vs1 env1 fns1 i) ⇔
    EVERY v_ok env1 ∧ EVERY v_ok vs1 ∧ i < LENGTH fns1 ∧
    EVERY ($~ o has_install o SND) fns1)
Termination
  WF_REL_TAC ‘measure v_size’ \\ simp[v_size_def]
End

Definition res_ok_def[simp]:
  res_ok (Rerr (Rabort _)) = T ∧
  res_ok (Rerr (Rraise v)) = v_ok v ∧
  res_ok (Rval v) = EVERY v_ok v
End

Definition state_rel'_def:
  state_rel' (s:('c,'ffi) closSem$state) (t:('c,'ffi) closSem$state) <=>
    (!n. SND (SND (s.compile_oracle n)) = []) ∧
    s.code = FEMPTY ∧ t.code = FEMPTY ∧
    t.max_app = s.max_app ∧ 1 <= s.max_app ∧
    t.clock = s.clock ∧
    t.ffi = s.ffi ∧
    s.globals = t.globals ∧ EVERY (OPTION_ALL v_ok) t.globals ∧
    s.refs = t.refs ∧ FEVERY (λ(k,v). ∀vs. v = ValueArray vs ⇒ EVERY v_ok vs) t.refs ∧
    s.compile = pure_cc (insert_interp ## I) t.compile ∧
    t.compile_oracle = pure_co (insert_interp ## I) o s.compile_oracle
End

Theorem lookup_vars_ok:
  ∀vs env env'. lookup_vars vs env = SOME env' ∧ EVERY v_ok env ⇒ EVERY v_ok env'
Proof
  Induct \\ fs [lookup_vars_def]
  \\ rw [] \\ gvs [AllCaseEqs()]
  \\ res_tac \\ fs []
  \\ gvs [EVERY_EL]
QED

Triviality state_rel'_clock:
  state_rel' s t ⇒ t.clock = s.clock
Proof
  fs [state_rel'_def]
QED

Triviality has_install_list_eq:
  ∀xs. has_install_list xs ⇔ EXISTS has_install xs
Proof
  Induct \\ fs [has_install_def]
QED

Theorem evaluate_change_oracle:
   (!tmp xs env (s1:('c,'ffi) closSem$state) t1 res s2 n.
     tmp = (xs,env,s1) ∧
     (evaluate (xs,env,s1) = (res,s2)) ∧ res <> Rerr (Rabort Rtype_error) ⇒
     state_rel' s1 t1 ∧ ~(has_install_list xs) ∧ EVERY v_ok env ==>
     ?t2.
        (evaluate (xs,env,t1) = (res,t2)) ∧
        state_rel' s2 t2 ∧ res_ok res) ∧
   (!loc f args (s:('c,'ffi) closSem$state) res s2 t1.
       evaluate_app loc f args s = (res,s2) ∧ res <> Rerr (Rabort Rtype_error) ⇒
       state_rel' s t1 ∧ EVERY v_ok args ∧ v_ok f
       ⇒
       ?t2.
          (evaluate_app loc f args t1 = (res,t2)) ∧
          state_rel' s2 t2 ∧ res_ok res)
Proof
  ho_match_mp_tac evaluate_ind \\ srw_tac[][]
  \\ fs [has_install_def]
  >~ [‘evaluate ([],env,t1)’] >-
   (gvs [evaluate_def])
  >~ [‘evaluate ((_::_::_),env,t1)’] >-
   (gvs [evaluate_def,AllCaseEqs()]
    \\ res_tac \\ gvs []
    \\ res_tac \\ gvs []
    \\ imp_res_tac evaluate_SING \\ gvs [])
  >~ [‘evaluate ([Var _ _],env,t1)’] >-
    gvs [evaluate_def,AllCaseEqs(),EVERY_EL]
  >~ [‘evaluate ([If _ _ _ _],env,t1)’] >-
   (gvs [evaluate_def,AllCaseEqs(),EVERY_EL]
    \\ res_tac \\ gvs [])
  >~ [‘evaluate ([Let _ _ _],env,t1)’] >-
   (gvs [evaluate_def,AllCaseEqs(),EVERY_EL]
    \\ res_tac \\ gvs [])
  >~ [‘Tick’] >-
   (gvs [evaluate_def,AllCaseEqs(),EVERY_EL]
    >- fs [state_rel'_def]
    \\ ‘state_rel' (dec_clock 1 s) (dec_clock 1 t1)’ by
         fs [state_rel'_def,dec_clock_def]
    \\ res_tac \\ fs []
    \\ fs [state_rel'_def])
  >~ [‘evaluate ([Raise _ _],env,t1)’] >-
   (gvs [evaluate_def,AllCaseEqs(),EVERY_EL]
    \\ res_tac \\ gvs []
    \\ imp_res_tac evaluate_SING \\ gvs [])
  >~ [‘evaluate ([Handle _ _ _],env,t1)’] >-
   (gvs [evaluate_def,AllCaseEqs(),EVERY_EL]
    \\ res_tac \\ gvs [])
  >~ [‘Fn’] >-
   (gvs [evaluate_def,AllCaseEqs(),state_rel'_def]
    \\ res_tac \\ gvs [SF ETA_ss]
    \\ imp_res_tac lookup_vars_ok \\ fs [])
  >~ [‘Call’] >-
   (gvs [evaluate_def,AllCaseEqs()]
    \\ res_tac \\ fs [EXISTS_PROD,PULL_EXISTS]
    \\ gvs [find_code_def,state_rel'_def])
  >~ [‘Op’] >-
   (gvs [evaluate_def,CaseEq"prod"]
    \\ rename [‘evaluate (xs,env,s) = (vvv,rr)’]
    \\ Cases_on ‘vvv ≠ Rerr (Rabort Rtype_error)’ \\ gvs []
    \\ first_x_assum drule \\ rw [] \\ fs []
    \\ Cases_on ‘vvv’ \\ fs [] \\ gvs []
    \\ qabbrev_tac ‘vr = λv1 v2. v1 = v2 ∧ v_ok v1’
    \\ ‘simple_val_rel vr’ by
      (fs [simple_val_rel_def]
       \\ rw [] \\ fs [Abbr‘vr’] \\ gvs []
       \\ eq_tac \\ gvs [] \\ rw [] \\ fs []
       \\ pop_assum mp_tac
       >- (rename [‘LIST_REL _ _ xs’] \\ Induct_on ‘xs’ \\ fs [])
       >- (rename [‘LIST_REL _ ys xs’]
           \\ qid_spec_tac ‘xs’ \\ qid_spec_tac ‘ys’
           \\ Induct \\ gvs [PULL_EXISTS])
       >- (rename [‘LIST_REL _ ys xs’]
           \\ qid_spec_tac ‘xs’ \\ qid_spec_tac ‘ys’
           \\ Induct \\ gvs [PULL_EXISTS] \\ rw [] \\ res_tac \\ fs []))
    \\ drule_at (Pos $ el 3) simple_val_rel_do_app
    \\ disch_then drule
    \\ rename [‘Rval vs’]
    \\ disch_then $ qspecl_then [‘REVERSE vs’,‘REVERSE vs’,‘op’] mp_tac
    \\ impl_tac >-
     (reverse conj_tac >-
        (qpat_x_assum ‘EVERY _ _’ mp_tac
         \\ qid_spec_tac ‘vs’ \\ Induct \\ gvs [Abbr‘vr’])
      \\ fs [simple_state_rel_def] \\ simp [Abbr‘vr’] \\ rpt $ pop_assum kall_tac
      \\ rw [] \\ gvs [state_rel'_def]
      \\ TRY $ drule_all FEVERY_FLOOKUP \\ fs []
      >- (qid_spec_tac ‘w’ \\ Induct \\ fs [])
      >- (qpat_x_assum ‘EVERY _ _’ mp_tac
          \\ rename [‘EVERY _ xs’] \\ qid_spec_tac ‘xs’ \\ Induct
          \\ fs [] \\ Cases \\ fs [])
      >- (gvs [FEVERY_DEF,SF DNF_ss,FAPPLY_FUPDATE_THM] \\ rw []
          \\ res_tac \\ fs [])
      >- (gvs [FEVERY_DEF,SF DNF_ss,FAPPLY_FUPDATE_THM]
          \\ ‘xs = ys ∧ EVERY v_ok xs’ by
            (pop_assum mp_tac \\ qid_spec_tac ‘xs’ \\ qid_spec_tac ‘ys’
             \\ Induct \\ fs [PULL_EXISTS] \\ rw [] \\ gvs [] \\ res_tac \\ fs [])
          \\ gvs [] \\ rw [] \\ fs [] \\ res_tac \\ fs [])
      \\ pop_assum mp_tac
      \\ qid_spec_tac ‘xs’
      \\ qid_spec_tac ‘ys’
      \\ Induct \\ fs [PULL_EXISTS]
      \\ rw [] \\ res_tac \\ fs []
      \\ Cases_on ‘h’ \\ fs []
      \\ Cases_on ‘x’ \\ fs [] \\ gvs [])
    \\ strip_tac
    \\ gvs [AllCaseEqs()]
    \\ gvs [Abbr‘vr’]
    \\ Cases_on ‘err’ \\ gvs [])
  >~ [‘Letrec’] >-
   (gvs [evaluate_def,AllCaseEqs()]
    \\ first_x_assum drule
    \\ (impl_tac >-
     (gvs [EVERY_GENLIST,SF ETA_ss] \\ gvs [EVERY_EL]
      \\ rw []
      \\ TRY (drule lookup_vars_ok)
      \\ gvs [has_install_list_eq,EVERY_EL] \\ rw []
      \\ first_x_assum drule
      \\ Cases_on ‘EL n fns’ \\ fs []
      \\ gvs [EL_MAP]))
    \\ strip_tac \\ fs []
    \\ gvs [EVERY_EL] \\ rw [] \\ res_tac \\ gvs [state_rel'_def])
  >~ [‘App’] >-
   (gvs [evaluate_def,AllCaseEqs()]
    \\ res_tac \\ fs [EXISTS_PROD,PULL_EXISTS]
    \\ res_tac \\ fs []
    \\ imp_res_tac evaluate_SING \\ gvs [])
  >~ [‘evaluate_app’] >-
   (gvs [evaluate_def,AllCaseEqs()]
    \\ ‘s.max_app = t1.max_app’ by fs [state_rel'_def] \\ fs []
    \\ TRY (fs [state_rel'_def,dec_clock_def] \\ NO_TAC)
    >-
     (fs [state_rel'_def,dec_clock_def]
      \\ Cases_on ‘f’ \\ gvs [dest_closure_def,AllCaseEqs(),SF ETA_ss]
      \\ pairarg_tac \\ gvs [dest_closure_def,AllCaseEqs(),SF ETA_ss])
    \\ gvs [PULL_EXISTS]
    \\ rename [‘SUC (LENGTH vs)’]
    \\ ‘state_rel' (dec_clock (SUC (LENGTH vs) − LENGTH rest_args) s)
                   (dec_clock (SUC (LENGTH vs) − LENGTH rest_args) t1)’ by
             gvs [dec_clock_def,state_rel'_def]
    \\ rpt $ first_x_assum drule
    \\ ‘~has_install exp ∧ EVERY v_ok env ∧ EVERY v_ok rest_args’ by
     (Cases_on ‘f’ \\ gvs [dest_closure_def,AllCaseEqs(),SF ETA_ss]
      \\ rpt (pairarg_tac \\ gvs [dest_closure_def,AllCaseEqs(),SF ETA_ss])
      \\ rpt $ irule_at Any EVERY_TAKE
      \\ rpt $ irule_at Any EVERY_DROP \\ fs []
      \\ gvs [EVERY_GENLIST]
      \\ gvs [EVERY_EL]
      \\ res_tac
      \\ qpat_x_assum ‘EL n _ = _’ assume_tac \\ fs [])
    \\ fs []
    \\ strip_tac \\ gvs []
    \\ imp_res_tac state_rel'_clock
    \\ res_tac \\ fs []
    \\ first_x_assum $ irule_at $ Pos last
    \\ fs [])
QED

(* ------------------------------------------------------------------------- *
   preservation of observable semantics
 * ------------------------------------------------------------------------- *)

Triviality init_globals:
  (initial_state ffi max_app f co cc ck).globals = []
Proof
  EVAL_TAC
QED

Theorem semantics_attach_interpreter:
   semantics (ffi:'ffi ffi_state) max_app FEMPTY
     co (pure_cc (insert_interp ## I) cc) (attach_interpreter xs) <> Fail ==>
   (∀n. SND (SND (co n)) = []) ∧ 0 < max_app ==>
   semantics (ffi:'ffi ffi_state) max_app FEMPTY
     (pure_co (insert_interp ## I) ∘ co) cc (attach_interpreter xs) =
   semantics (ffi:'ffi ffi_state) max_app FEMPTY
     co (pure_cc (insert_interp ## I) cc) (attach_interpreter xs)
Proof
  strip_tac
  \\ ho_match_mp_tac IMP_semantics_eq \\ rw []
  \\ fs [] \\ fs [eval_sim_def] \\ rw []
  \\ Cases_on ‘has_install_list xs’ \\ fs []
  >-
   (gvs [attach_interpreter_def]
    \\ last_x_assum kall_tac
    \\ last_x_assum mp_tac
    \\ once_rewrite_tac [evaluate_CONS]
    \\ fs [compile_init_def,evaluate_def,do_app_def,init_globals,get_global_def,
           LUPDATE_def]
    \\ qmatch_goalsub_abbrev_tac ‘evaluate (_,_,iis)’
    \\ CASE_TAC \\ strip_tac
    \\ qspecl_then [‘xs’,‘[]’,‘iis’] mp_tac evaluate_interp_thm
    \\ disch_then drule \\ fs []
    \\ disch_then $ qspec_then ‘initial_state ffi max_app
                                FEMPTY (pure_co (insert_interp ## I) ∘ co) cc k with
                        globals := [SOME (Closure NONE [] [] 1 clos_interpreter)]’ mp_tac
    \\ impl_tac
    >- (simp [Abbr‘iis’,state_rel_def,initial_state_def]
        \\ strip_tac \\ gvs [])
    \\ strip_tac \\ fs [closPropsTheory.initial_state_clock]
    \\ qexists_tac ‘ck’ \\ fs []
    \\ gvs [AllCaseEqs()]
    \\ fs [state_rel_def])
  >-
   (qmatch_asmsub_abbrev_tac ‘evaluate (_,_,iis) = _’
    \\ qspecl_then [‘attach_interpreter xs’,‘[]’,‘iis’] mp_tac
                   (evaluate_change_oracle |> SIMP_RULE std_ss [] |> CONJUNCT1)
    \\ fs []
    \\ disch_then $ qspec_then ‘initial_state ffi max_app
                                FEMPTY (pure_co (insert_interp ## I) ∘ co) cc k’ mp_tac
    \\ impl_tac
    >- (simp [Abbr‘iis’,state_rel'_def,initial_state_def,FEVERY_FEMPTY]
        \\ fs [attach_interpreter_def,has_install_def] \\ EVAL_TAC)
    \\ strip_tac \\ fs [closPropsTheory.initial_state_clock]
    \\ qexists_tac ‘0’ \\ fs []
    \\ fs [state_rel'_def])
QED

(* ------------------------------------------------------------------------- *
   syntactic lemmas
 * ------------------------------------------------------------------------- *)

Theorem elist_globals_insert_interp:
  closProps$elist_globals (insert_interp xs) =
  closProps$elist_globals xs
Proof
  cheat
QED

Theorem contains_App_SOME_insert_interp:
  ¬contains_App_SOME max_app xs ⇒
  ¬contains_App_SOME max_app (insert_interp xs)
Proof
  cheat
QED

Theorem every_Fn_vs_NONE_insert_interp:
  every_Fn_vs_NONE xs ⇒ every_Fn_vs_NONE (insert_interp xs)
Proof
  cheat
QED

Theorem insert_interp_no_mti:
  MEM e (insert_interp xs) ⇒ EVERY no_mti xs ⇒ no_mti e
Proof
  cheat
QED

Theorem insert_interp_esgc_free:
  EVERY esgc_free (insert_interp xs) = EVERY esgc_free xs
Proof
  cheat
QED

val _ = export_theory();
