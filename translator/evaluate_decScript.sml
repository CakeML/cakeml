(*
  Defines evaluate_dec_list which is an alternative version of
  evaluate_decs from evaluateTheory.  This alternative version is
  adjusted to make translation faster.
*)

open preamble
open astTheory semanticPrimitivesTheory evaluateTheory
     semanticPrimitivesPropsTheory evaluatePropsTheory;
open mlstringTheory integerTheory;
open namespaceTheory;
open alist_treeTheory;

val _ = new_theory "evaluate_dec";

(* --- define an alternative to evaluate_decs --- *)

(* Same as evaluate_decs from evaluateTheory but modified to not have
   the cons checks (every_exp one_con_check) *)
Definition evaluate_dec_list_def:
  evaluate_dec_list st env [] = (st,Rval <|v := nsEmpty; c := nsEmpty|>)
  ∧
  evaluate_dec_list st env (d1::d2::ds) =
    (case evaluate_dec_list st env [d1] of
       (st1,Rval env1) =>
         (case evaluate_dec_list st1 (extend_dec_env env1 env) (d2::ds) of
            (st2,r) => (st2,combine_dec_result env1 r))
     | (st1,Rerr v7) => (st1,Rerr v7))
  ∧
  evaluate_dec_list st env [Dlet locs p e] =
    (if ALL_DISTINCT (pat_bindings p [])
     then
       case evaluate st env [e] of
         (st',Rval v) =>
           (st',
            case pmatch env.c st'.refs p (HD v) [] of
              No_match => Rerr (Rraise bind_exn_v)
            | Match_type_error => Rerr (Rabort Rtype_error)
            | Match new_vals =>
              Rval <|v := alist_to_ns new_vals; c := nsEmpty|>)
       | (st',Rerr err) => (st',Rerr err)
     else (st,Rerr (Rabort Rtype_error)))
  ∧
  evaluate_dec_list st env [Dletrec locs funs] =
    (st,
     if ALL_DISTINCT (MAP (λ(x,y,z). x) funs)
     then
       Rval <|v := build_rec_env funs env nsEmpty; c := nsEmpty|>
     else Rerr (Rabort Rtype_error))
  ∧
  evaluate_dec_list st env [Dtype locs tds] =
    (if EVERY check_dup_ctors tds then
       (st with next_type_stamp := st.next_type_stamp + LENGTH tds,
        Rval <|v := nsEmpty; c := build_tdefs st.next_type_stamp tds|>)
     else (st,Rerr (Rabort Rtype_error)))
  ∧
  evaluate_dec_list st env [Dtabbrev locs tvs tn t] =
    (st,Rval <|v := nsEmpty; c := nsEmpty|>)
  ∧
  evaluate_dec_list st env [Denv n] =
    (case declare_env st.eval_state env of
       NONE => (st,Rerr (Rabort Rtype_error))
     | SOME (x,es') =>
       (st with eval_state := es',Rval <|v := nsSing n x; c := nsEmpty|>))
  ∧
  evaluate_dec_list st env [Dexn locs cn ts] =
    (st with next_exn_stamp := st.next_exn_stamp + 1,
     Rval
       <|v := nsEmpty;
         c := nsSing cn (LENGTH ts,ExnStamp st.next_exn_stamp)|>)
  ∧
  evaluate_dec_list st env [Dmod mn ds] =
    (case evaluate_dec_list st env ds of
       (st',r) =>
         (st',
          case r of
            Rval env' =>
              Rval <|v := nsLift mn env'.v; c := nsLift mn env'.c|>
          | Rerr err => Rerr err))
  ∧
  evaluate_dec_list st env [Dlocal lds ds] =
    case evaluate_dec_list st env lds of
      (st1,Rval env1) => evaluate_dec_list st1 (extend_dec_env env1 env) ds
    | (st1,Rerr v7) => (st1,Rerr v7)
Termination
  WF_REL_TAC ‘measure $ list_size dec_size o SND o SND’
End

Definition evaluate_dec_list_with_clock_def:
  evaluate_dec_list_with_clock st env k prog =
    let (st',r) =
      evaluate_dec_list (st with clock := k) env prog
    in (st'.ffi,r)
End

Definition semantics_dec_list_def:
  (semantics_dec_list st env prog (Terminate outcome io_list) ⇔
    (* there is a clock for which evaluation terminates, either internally or via
       FFI, and the accumulated io events match the given io_list *)
    (?k ffi r.
      evaluate_dec_list_with_clock st env k prog = (ffi,r) ∧
      (case r of
       | Rerr (Rabort (Rffi_error outcome')) =>
         outcome = FFI_outcome (outcome')
       | r => r ≠ Rerr (Rabort Rtimeout_error) ∧ outcome = Success) ∧
      (io_list = ffi.io_events) ∧
      (r ≠ Rerr (Rabort Rtype_error)))) ∧
  (semantics_dec_list st env prog (Diverge io_trace) ⇔
    (* for all clocks, evaluation times out *)
    (!k. ?ffi.
      (evaluate_dec_list_with_clock st env k prog =
          (ffi, Rerr (Rabort Rtimeout_error)))) ∧
    (* the io_trace is the least upper bound of the set of traces
       produced for each clock *)
     lprefix_lub
       (IMAGE
         (λk. fromList (FST (evaluate_dec_list_with_clock st env k prog)).io_events)
         UNIV)
       io_trace) ∧
  (semantics_dec_list st env prog Fail ⇔
    (* there is a clock for which evaluation produces a runtime type error *)
    ∃k.
      SND(evaluate_dec_list_with_clock st env k prog) = Rerr (Rabort Rtype_error))
End

val env_c = “env_c: (string, string, num # stamp) namespace”

(* --- define a check that implies evaluate_dec_list is same as evalaute_decs --- *)

Definition check_cons_dec_list_def:
  check_cons_dec_list ^env_c [] = SOME nsEmpty
  ∧
  check_cons_dec_list env_c (d1::ds) =
    (case check_cons_dec env_c d1 of
     | NONE => NONE
     | SOME env_c0 =>
       case check_cons_dec_list (nsAppend env_c0 env_c) ds of
       | NONE => NONE
       | SOME env_c1 => SOME (nsAppend env_c1 env_c0))
  ∧
  check_cons_dec env_c (Dlet locs p e) =
    (if every_exp (one_con_check env_c) e
     then SOME nsEmpty else NONE)
  ∧
  check_cons_dec env_c (Dletrec locs funs) =
    (if EVERY (λ(f,n,e). every_exp (one_con_check env_c) e) funs
     then SOME nsEmpty else NONE)
  ∧
  check_cons_dec env_c (Dtype locs tds) =
    (SOME (build_tdefs 0 tds))
  ∧
  check_cons_dec env_c (Dtabbrev locs tvs tn t) = SOME nsEmpty
  ∧
  check_cons_dec env_c (Denv _) = SOME nsEmpty
  ∧
  check_cons_dec env_c (Dexn locs cn ts) =
    SOME (nsSing cn (LENGTH ts,ExnStamp 0))
  ∧
  check_cons_dec env_c (Dmod mn ds) =
    (case check_cons_dec_list env_c ds of
     | NONE => NONE
     | SOME env_c0 => SOME (nsLift mn env_c0))
  ∧
  check_cons_dec env_c (Dlocal lds ds) =
    case check_cons_dec_list env_c lds of
    | NONE => NONE
    | SOME env_c0 => check_cons_dec_list (nsAppend env_c0 env_c) ds
Termination
  WF_REL_TAC ‘measure $ λx. case x of INL (_,ds) => list_size dec_size ds
                                    | INR (_,d) => dec_size d’
End

Theorem check_cons_dec_list_isPREFIX:
  ∀env_c xs ys x.
    check_cons_dec_list env_c xs = SOME x ∧ isPREFIX ys xs ⇒
    ∃y. check_cons_dec_list env_c ys = SOME y
Proof
  Induct_on ‘xs’
  \\ gvs [check_cons_dec_list_def,AllCaseEqs()]
  \\ Cases_on ‘ys’ \\ gvs [check_cons_dec_list_def]
  \\ rw [] \\ gvs [AllCaseEqs()]
QED

Triviality check_cons_dec_list_sing[simp]:
  check_cons_dec_list env_c [d] = check_cons_dec env_c d
Proof
  simp [check_cons_dec_list_def] \\ CASE_TAC \\ gvs []
QED

(* --- theorems --- *)

Definition con_check_eqv_def:
  con_check_eqv (x: (string, string, num # stamp) namespace)
                (y: (string, string, num # stamp) namespace) ⇔
    case (x,y) of
    | (Bind xs ys, Bind xs1 ys1) =>
         LIST_REL (λ(a,x1,_) (b,y1,_). a = b ∧ x1 = y1) xs xs1 ∧
         LIST_REL (λ(a,x1) (b,y1). a = b ∧ con_check_eqv x1 y1) ys ys1
End

Theorem con_check_eqv_refl[local,simp]:
  ∀x. con_check_eqv x x
Proof
  qsuff_tac ‘∀x y. x = y ⇒ con_check_eqv x x’ >- gvs []
  \\ ho_match_mp_tac con_check_eqv_ind \\ gvs []
  \\ rw [] \\ Cases_on ‘y’ \\ gvs []
  \\ simp [Once con_check_eqv_def]
  \\ irule_at Any EVERY2_refl
  \\ irule_at Any EVERY2_refl
  \\ gvs [FORALL_PROD]
  \\ metis_tac []
QED

Theorem con_check_eqv_nsAppend:
  con_check_eqv x1 y1 ∧ con_check_eqv x2 y2 ⇒
  con_check_eqv (nsAppend x1 x2) (nsAppend y1 y2)
Proof
  once_rewrite_tac [con_check_eqv_def]
  \\ Cases_on ‘x1’ \\ Cases_on ‘y1’ \\ Cases_on ‘x2’ \\ Cases_on ‘y2’
  \\ gvs [nsAppend_def] \\ strip_tac
  \\ imp_res_tac LIST_REL_LENGTH
  \\ metis_tac [LIST_REL_APPEND]
QED

Theorem con_check_eqv_switch:
  con_check_eqv env2 env1 ⇒
  every_exp (one_con_check env1) e = every_exp (one_con_check env2) e
Proof
  strip_tac \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ gvs [FUN_EQ_THM]
  \\ Cases \\ gvs [one_con_check_def]
  \\ qsuff_tac ‘∀a l. do_con_check env2 a l = do_con_check env1 a l’
  \\ gvs []
  \\ Cases \\ gvs [do_con_check_def]
  \\ pop_assum mp_tac
  \\ qid_spec_tac ‘env1’
  \\ qid_spec_tac ‘env2’
  \\ Induct_on ‘x’ \\ gvs []
  >-
   (rw [] \\ Cases_on ‘env1’ \\ Cases_on ‘env2’
    \\ gvs [nsLookup_def]
    \\ pop_assum mp_tac
    \\ simp [Once con_check_eqv_def]
    \\ qid_spec_tac ‘l0’
    \\ qid_spec_tac ‘l0'’
    \\ Induct \\ gvs [PULL_EXISTS,FORALL_PROD]
    \\ rw [])
  \\ rw []
  \\ Cases_on ‘env1’ \\ Cases_on ‘env2’
  \\ gvs [nsLookup_def]
  \\ pop_assum mp_tac
  \\ simp [Once con_check_eqv_def]
  \\ rw []
  \\ rename [‘LIST_REL _ l1 l2’]
  \\ pop_assum mp_tac
  \\ qid_spec_tac ‘l2’
  \\ qid_spec_tac ‘l1’
  \\ Induct \\ gvs [PULL_EXISTS,FORALL_PROD] \\ rw []
QED

Theorem con_check_eqv_build_tdefs[local]:
  ∀m n. con_check_eqv (build_tdefs m tds) (build_tdefs n tds)
Proof
  Induct_on ‘tds’ \\ gvs [build_tdefs_def,FORALL_PROD]
  \\ rw [] \\ irule con_check_eqv_nsAppend \\ gvs []
  \\ gvs [alist_to_ns_def]
  \\ simp [Once con_check_eqv_def,build_constrs_def]
  \\ Induct_on ‘p_2’ \\ gvs [FORALL_PROD]
QED

Theorem evaluate_dec_list_eq_evaluate_decs:
  ∀(st:'ffi semanticPrimitives$state) env ds st1 res.
    IS_SOME (check_cons_dec_list env.c ds)
    ⇒
    evaluate_dec_list st env ds = evaluate_decs st env ds
Proof
  rpt gen_tac
  \\ qsuff_tac ‘
    ∀(st:'ffi semanticPrimitives$state) env ds n m env_1 st1 res env_c env_c1.
      check_cons_dec_list env_c ds = SOME env_c1 ∧
      con_check_eqv env.c env_c ∧
      evaluate_dec_list st env ds = (st1,res)
      ⇒
      evaluate_decs st env ds = (st1,res) ∧
      (∀r. res = Rval r ⇒  con_check_eqv r.c env_c1)’
  >- metis_tac [IS_SOME_EXISTS,EXISTS_PROD,PAIR,con_check_eqv_refl]
  \\ ho_match_mp_tac evaluate_dec_list_ind
  \\ rpt conj_tac
  >- gvs [evaluate_def,evaluate_dec_list_def,
          check_cons_dec_list_def]
  >-
   (rpt gen_tac \\ strip_tac
    \\ simp [Once check_cons_dec_list_def]
    \\ gvs [evaluate_def,evaluate_dec_list_def]
    \\ rpt gen_tac \\ strip_tac
    \\ simp [evaluate_decs_def]
    \\ Cases_on ‘evaluate_dec_list st env [d1]’
    \\ reverse $ Cases_on ‘r’
    >- (gvs [] \\ gvs [AllCaseEqs()] \\ last_x_assum drule \\ gvs [])
    \\ last_x_assum mp_tac \\ simp []
    \\ last_x_assum mp_tac \\ simp []
    \\ pop_assum mp_tac
    \\ pop_assum mp_tac
    \\ pop_assum mp_tac
    \\ pop_assum mp_tac
    \\ simp [AllCaseEqs(),EXISTS_PROD]
    \\ strip_tac \\ gvs []
    \\ rpt disch_tac
    \\ rfs [extend_dec_env_def]
    \\ last_x_assum drule \\ gvs [] \\ strip_tac
    \\ last_x_assum drule \\ gvs []
    \\ impl_tac
    >- (irule con_check_eqv_nsAppend \\ gvs [])
    \\ strip_tac
    \\ gvs [combine_dec_result_def,AllCaseEqs(),PULL_EXISTS]
    \\ Cases_on ‘r’ \\ gvs []
    \\ irule con_check_eqv_nsAppend \\ gvs [])
  >~ [‘Dlet’] >-
   (gvs [check_cons_dec_list_def,evaluate_decs_def,evaluate_dec_list_def]
    \\ rpt gen_tac \\ strip_tac
    \\ drule_all con_check_eqv_switch
    \\ gvs [] \\ rw [] \\ gvs [AllCaseEqs()])
  >~ [‘Dletrec’] >-
   (gvs [check_cons_dec_list_def,evaluate_decs_def,evaluate_dec_list_def]
    \\ rpt gen_tac \\ strip_tac
    \\ drule_all con_check_eqv_switch
    \\ strip_tac \\ gvs []
    \\ rw [] \\ gvs [AllCaseEqs()])
  >~ [‘Dtype’] >-
   (gvs [check_cons_dec_list_def,evaluate_decs_def,evaluate_dec_list_def]
    \\ rw [] \\ gvs [AllCaseEqs(),con_check_eqv_build_tdefs])
  >~ [‘Dtabbrev’] >-
   (gvs [check_cons_dec_list_def,evaluate_decs_def,evaluate_dec_list_def])
  >~ [‘Denv’] >-
   (gvs [check_cons_dec_list_def,evaluate_decs_def,evaluate_dec_list_def]
    \\ rw [] \\ gvs [AllCaseEqs()])
  >~ [‘Dexn’] >-
   (gvs [check_cons_dec_list_def,evaluate_decs_def,evaluate_dec_list_def]
    \\ rw [] \\ simp [Once con_check_eqv_def,nsSing_def])
  >~ [‘Dmod’] >-
   (gvs [check_cons_dec_list_def,evaluate_decs_def,evaluate_dec_list_def]
    \\ gvs [AllCaseEqs(),PULL_EXISTS]
    \\ rw [] \\ gvs []
    \\ res_tac \\ gvs [nsLift_def]
    \\ simp [Once con_check_eqv_def])
  >~ [‘Dlocal’] >-
   (gvs [check_cons_dec_list_def,evaluate_decs_def,evaluate_dec_list_def]
    \\ gvs [CaseEq "option",CaseEq "prod"]
    \\ rpt (gen_tac ORELSE disch_then strip_assume_tac)
    \\ reverse $ Cases_on ‘v1’
    >- (gvs [] \\ res_tac \\ gvs [])
    \\ pop_assum mp_tac \\ simp [extend_dec_env_def]
    \\ last_x_assum drule
    \\ last_x_assum drule
    \\ asm_rewrite_tac []
    \\ disch_then (strip_assume_tac o SRULE [])
    \\ asm_rewrite_tac []
    \\ simp [extend_dec_env_def]
    \\ disch_then drule
    \\ simp [con_check_eqv_nsAppend])
QED

Theorem evaluate_dec_list_set_clock:
  ∀s env decs s1 res.
    evaluate_dec_list s env decs = (s1,res) ∧
    res ≠ Rerr (Rabort Rtimeout_error) ⇒
    ∀ck. ∃ck1.
           evaluate_dec_list (s with clock := ck1) env decs =
           (s1 with clock := ck,res)
Proof
  ho_match_mp_tac evaluate_dec_list_ind \\ rpt strip_tac
  >- gvs [evaluate_dec_list_def,state_component_equality]
  >- (gvs [evaluate_dec_list_def]
      \\ reverse $ gvs [AllCaseEqs()]
      >- (first_x_assum $ qspec_then ‘ck’ strip_assume_tac
          \\ qexists_tac ‘ck1’ \\ gvs [])
      \\ Cases_on ‘r = Rerr (Rabort Rtimeout_error)’
      >- gvs [combine_dec_result_def] \\ gvs []
      \\ last_x_assum $ qspec_then ‘ck’ strip_assume_tac
      \\ last_x_assum $ qspec_then ‘ck1’ strip_assume_tac
      \\ qexists_tac ‘ck1'’ \\ gvs [])
  >~ [‘Dlet’] >-
   (gvs [evaluate_dec_list_def]
    \\ reverse $ gvs [AllCaseEqs()]
    >- gvs [state_component_equality]
    \\ drule evaluate_set_clock \\ gvs []
    \\ disch_then $ qspec_then ‘ck’ strip_assume_tac
    \\ qexists_tac ‘ck1’ \\ gvs [])
  >~ [‘Dmod’] >-
   (gvs [evaluate_dec_list_def,CaseEq"prod"]
    \\ Cases_on ‘r = Rerr (Rabort Rtimeout_error)’ \\ gvs []
    \\ last_x_assum $ qspec_then ‘ck’ strip_assume_tac
    \\ qexists_tac ‘ck1’ \\ gvs [])
  >~ [‘Dlocal’] >-
   (gvs [evaluate_dec_list_def,CaseEq"prod"]
    \\ Cases_on ‘v1 = Rerr (Rabort Rtimeout_error)’ \\ gvs []
    \\ reverse $ Cases_on ‘v1’ \\ gvs []
    >- (last_x_assum $ qspec_then ‘ck’ strip_assume_tac
        \\ qexists_tac ‘ck1’ \\ gvs [])
    \\ last_x_assum $ qspec_then ‘ck’ strip_assume_tac
    \\ last_x_assum $ qspec_then ‘ck1’ strip_assume_tac
    \\ qexists_tac ‘ck1'’ \\ gvs [])
  \\ gvs [evaluate_dec_list_def,state_component_equality,AllCaseEqs()]
QED

Theorem evaluate_dec_list_cons:
  ∀s env d ds.
    evaluate_dec_list s env (d::ds) =
    case evaluate_dec_list s env [d] of
    | (s1,Rval env1) =>
        (case evaluate_dec_list s1 (env1 +++ env) ds of
           (s2,r) => (s2,combine_dec_result env1 r))
    | (s1,Rerr v7) => (s1,Rerr v7)
Proof
  Cases_on ‘ds’
  \\ gvs [evaluate_dec_list_def,combine_dec_result_def]
  \\ rw [] \\ TOP_CASE_TAC \\ Cases_on ‘r’ \\ gvs []
QED

Theorem evaluate_dec_list_append:
  ∀s env xs ds.
    evaluate_dec_list s env (xs ++ ds) =
    case evaluate_dec_list s env xs of
    | (s1,Rval env1) =>
        (case evaluate_dec_list s1 (env1 +++ env) ds of
           (s2,r) => (s2,combine_dec_result env1 r))
    | (s1,Rerr v7) => (s1,Rerr v7)
Proof
  Induct_on ‘xs’ \\ gvs [evaluate_dec_list_def]
  >- (rw [] \\ TOP_CASE_TAC \\ gvs []
      \\ Cases_on ‘r’ \\ gvs [combine_dec_result_def,extend_dec_env_def])
  \\ once_rewrite_tac [evaluate_dec_list_cons]
  \\ rpt gen_tac \\ TOP_CASE_TAC \\ Cases_on ‘r’ \\ gvs []
  \\ Cases_on ‘evaluate_dec_list q (a +++ env) xs’ \\ Cases_on ‘r’ \\ gvs []
  \\ gvs [combine_dec_result_def,extend_dec_env_def]
  \\ ntac 5 (TOP_CASE_TAC \\ gvs [])
QED

Theorem evaluate_dec_list_add_to_clock:
  ∀s e p s' r extra.
    evaluate_dec_list s e p = (s',r) ∧ r ≠ Rerr (Rabort Rtimeout_error) ⇒
    evaluate_dec_list (s with clock := s.clock + extra) e p =
    (s' with clock := s'.clock + extra,r)
Proof
  ho_match_mp_tac evaluate_dec_list_ind \\ rpt strip_tac
  >- gvs [evaluate_dec_list_def,state_component_equality]
  >- (gvs [evaluate_dec_list_def]
      \\ reverse $ gvs [AllCaseEqs()]
      \\ last_x_assum $ qspec_then ‘extra’ strip_assume_tac
      \\ gvs [combine_dec_result_def,AllCaseEqs()]
      \\ Cases_on ‘r'’ \\ gvs [])
  >~ [‘Dlet’] >-
   (gvs [evaluate_dec_list_def]
    \\ reverse $ gvs [AllCaseEqs()]
    \\ drule evaluate_add_to_clock \\ gvs [])
  >~ [‘Dmod’] >-
   (gvs [evaluate_dec_list_def,CaseEq"prod"]
    \\ Cases_on ‘r' = Rerr (Rabort Rtimeout_error)’ \\ gvs [])
  >~ [‘Dlocal’] >-
   (gvs [evaluate_dec_list_def,CaseEq"prod"]
    \\ Cases_on ‘v1 = Rerr (Rabort Rtimeout_error)’ \\ gvs []
    \\ reverse $ Cases_on ‘v1’ \\ gvs [])
  \\ gvs [evaluate_dec_list_def,state_component_equality,AllCaseEqs()]
QED

Theorem eval_dec_list_no_eval_simulation:
  ∀s env decs s' res.
    evaluate_dec_list s env decs = (s',res) ∧ s.eval_state = NONE ∧
    res ≠ Rerr (Rabort Rtype_error) ⇒
    s'.eval_state = NONE ∧
    evaluate_dec_list (s with eval_state := es) env decs =
    (s' with eval_state := es,res)
Proof
  ho_match_mp_tac evaluate_dec_list_ind
  \\ rpt conj_tac \\ rpt gen_tac \\ rpt disch_tac \\ rpt gen_tac
  \\ rpt disch_tac \\ gvs []
  \\ gvs [evaluate_dec_list_def,AllCaseEqs()]
  \\ gvs [declare_env_def]
  >- (Cases_on ‘r = Rerr (Rabort Rtype_error)’ \\ gvs [combine_dec_result_def])
  \\ drule $ cj 1 evaluatePropsTheory.eval_no_eval_simulation
  \\ gvs []
QED

Theorem evaluate_dec_list_call_FFI_rel_imp:
  ∀s e p s' r. evaluate_dec_list s e p = (s',r) ⇒ RTC call_FFI_rel s.ffi s'.ffi
Proof
  ho_match_mp_tac evaluate_dec_list_ind \\ rpt strip_tac
  \\ gvs [evaluate_dec_list_def,AllCaseEqs()]
  \\ imp_res_tac evaluatePropsTheory.evaluate_call_FFI_rel_imp
  \\ imp_res_tac RTC_TRANS
QED

val _ = export_theory();
