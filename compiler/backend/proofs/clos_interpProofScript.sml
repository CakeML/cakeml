(*
  Correctness proof for closLang interpreter used by the REPL, i.e. Install,
  to avoid spending time compiling simple run-once code in declarations.
*)
open preamble backendPropsTheory closLangTheory closSemTheory closPropsTheory
     clos_interpTheory;

val _ = new_theory "clos_interpProof";

val _ = set_grammar_ancestry ["closLang", "closProps", "clos_interp"];

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
    t.compile_oracle = pure_co (insert_interp ## I) o s.compile_oracle
End

Theorem evaluate_interp_thm:
   (!tmp xs env (s1:('c,'ffi) closSem$state) t1 res s2 n.
     tmp = (xs,env,s1) ∧
     (evaluate (xs,env,s1) = (res,s2)) ∧ res <> Rerr (Rabort Rtype_error) ⇒
     state_rel s1 t1 ==>
     ?ck t2.
        (evaluate (xs,env,(t1 with clock := t1.clock + ck)) = (res,t2)) ∧
        state_rel s2 t2) ∧
   (!loc f args (s:('c,'ffi) closSem$state) res s2 t1.
       evaluate_app loc f args s = (res,s2) ∧ res <> Rerr (Rabort Rtype_error) ⇒
       state_rel s t1
       ⇒
       ?ck t2.
          (evaluate_app loc f args (t1 with clock := t1.clock + ck) = (res,t2)) ∧
          state_rel s2 t2)
Proof
  ho_match_mp_tac evaluate_ind \\ srw_tac[][]
  \\ cheat
QED

(* preservation of observable semantics *)

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
   cheat
  >~ [‘Letrec’] >-
   (gvs [evaluate_def,AllCaseEqs()]
    \\ first_x_assum drule
    \\ impl_tac >-
     (gvs [EVERY_GENLIST,SF ETA_ss] \\ gvs [EVERY_EL]
      \\ rw []
      \\ first_x_assum drule
      \\ Cases_on ‘EL n fns’ \\ fs []
      \\ cheat)
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

(* preservation of observable semantics *)

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
   (qmatch_asmsub_abbrev_tac ‘evaluate (_,_,iis) = _’
    \\ qspecl_then [‘attach_interpreter xs’,‘[]’,‘iis’] mp_tac
                   (evaluate_interp_thm |> SIMP_RULE std_ss [] |> CONJUNCT1)
    \\ disch_then drule \\ fs []
    \\ disch_then $ qspec_then ‘initial_state ffi max_app
                                FEMPTY (pure_co (insert_interp ## I) ∘ co) cc k’ mp_tac
    \\ impl_tac
    >- simp [Abbr‘iis’,state_rel_def,initial_state_def]
    \\ strip_tac \\ fs [closPropsTheory.initial_state_clock]
    \\ first_x_assum $ irule_at $ Pos hd
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
