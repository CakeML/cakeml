(*
  Properties of the operational semantics.
*)

open preamble evaluateTheory
     namespaceTheory namespacePropsTheory
     semanticPrimitivesTheory semanticPrimitivesPropsTheory
     fpSemPropsTheory evaluatePropsTheory;

(* TODO Proofs may rely on auto-generated names; fix using rename/namedCases *)
(* TODO Move to evaluateProps *)
val _ = new_theory "extension_evaluateProps";

Definition Seqs_def:
  Seqs [] = Con NONE [] ∧
  Seqs (x::xs) = Let NONE x (Seqs xs)
End

(* TODO rename apps -> Apps *)
Definition apps_def:
  apps f [] = f ∧
  apps f (x::xs) = apps (App Opapp [f; x]) xs
End

Theorem apps_append:
  ∀xs ys f. apps f (xs ++ ys) = apps (apps f xs) ys
Proof
  Induct \\ gvs [apps_def]
QED

Theorem evaluate_apps_Rerr:
  ∀xs f (st:'ffi state) env s1 e.
    evaluate st env xs = (s1,Rerr e) ⇒
    evaluate st env [apps f (REVERSE xs)] = (s1,Rerr e)
Proof
  Induct >- gvs [evaluate_def]
  \\ simp [Once evaluate_cons,apps_append,apps_def]
  \\ rpt gen_tac
  \\ gvs [evaluate_def]
  \\ Cases_on ‘evaluate st env [h]’ \\ gvs []
  \\ Cases_on ‘r’ \\ gvs []
  \\ gvs [AllCaseEqs()]
  \\ strip_tac
  \\ last_x_assum drule
  \\ strip_tac \\ gvs []
QED

Definition Funs_def:
  Funs [] e = e ∧
  Funs (x::xs) e = Fun x (Funs xs e)
End

Theorem evaluate_apps_Funs:
  ∀l x ns vs (st: 'ffi state) s1 s2 env env1 e.
    evaluate st env l = (s1,Rval vs) ∧
    evaluate s1 env [x] = (s2,Rval [Closure env1 (HD ns) (Funs (TL ns) e)]) ∧
    LENGTH l = LENGTH ns ∧ ns ≠ [] ∧ LENGTH ns ≤ s2.clock ⇒
    evaluate st env [apps x (REVERSE l)] =
    evaluate
      (s2 with clock := s2.clock - LENGTH ns)
      (env1 with v := nsAppend (alist_to_ns (ZIP (REVERSE ns,vs))) env1.v) [e]
Proof
  Induct using SNOC_INDUCT
  \\ gvs [] \\ rpt gen_tac
  \\ simp [SNOC_APPEND,evaluate_append,AllCaseEqs(),PULL_EXISTS]
  \\ gvs [] \\ rpt gen_tac \\ strip_tac \\ gvs []
  \\ Cases_on ‘ns’ \\ gvs [apps_def,apps_append]
  \\ gvs [REVERSE_APPEND,apps_def]
  \\ Cases_on ‘l = []’ \\ gvs [evaluate_def,apps_def]
  >-
   (gvs [do_opapp_def,dec_clock_def]
    \\ imp_res_tac evaluate_sing \\ gvs [Funs_def])
  \\ imp_res_tac evaluate_sing \\ gvs [Funs_def]
  \\ last_x_assum drule
  \\ strip_tac
  \\ irule EQ_TRANS
  \\ pop_assum $ irule_at $ Pos hd
  \\ simp [evaluate_def,do_opapp_def]
  \\ Cases_on ‘t’ \\ gvs [Funs_def,evaluate_def]
  \\ qrefine ‘a::as’ \\ gvs []
  \\ irule_at (Pos hd) EQ_REFL
  \\ gvs [dec_clock_def,ADD1]
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ gvs [sem_env_component_equality]
  \\ rewrite_tac [GSYM SNOC_APPEND]
  \\ DEP_REWRITE_TAC [ZIP_SNOC]
  \\ gvs [SNOC_APPEND]
  \\ imp_res_tac evaluate_length
  \\ Cases_on ‘env1.v’
  \\ gvs [alist_to_ns_def,nsBind_def,nsAppend_def]
QED

Theorem evaluate_apps_f_err:
  ∀xs vs (st:'ffi state) envs1 f s1 s2.
    evaluate st env xs = (s1,Rval vs) ∧
    evaluate s1 env [f] = (s2,Rerr r) ⇒
    evaluate st env [apps f (REVERSE xs)] = (s2,Rerr r)
Proof
  Induct using SNOC_INDUCT
  \\ gvs [evaluate_def,apps_def]
  \\ simp [evaluate_append,SNOC_APPEND]
  \\ gvs [AllCaseEqs()] \\ rw []
  \\ gvs [apps_append,apps_def,REVERSE_APPEND]
  \\ last_x_assum $ irule
  \\ gvs [evaluate_def]
QED

Theorem evaluate_apps_Funs_timeout:
  ∀l x ns vs (st: 'ffi state) s1 s2 env env1 e.
    evaluate st env l = (s1,Rval vs) ∧
    evaluate s1 env [x] = (s2,Rval [Closure env1 (HD ns) (Funs (TL ns) e)]) ∧
    LENGTH l = LENGTH ns ∧ ns ≠ [] ∧ s2.clock < LENGTH ns ⇒
    evaluate st env [apps x (REVERSE l)] =
      (s2 with clock := 0, Rerr (Rabort Rtimeout_error))
Proof
  Induct using SNOC_INDUCT
  \\ gvs [] \\ rpt gen_tac
  \\ simp [SNOC_APPEND,evaluate_append,AllCaseEqs(),PULL_EXISTS]
  \\ gvs [] \\ rpt gen_tac \\ strip_tac \\ gvs []
  \\ Cases_on ‘ns’ \\ gvs [apps_def,apps_append]
  \\ gvs [REVERSE_APPEND,apps_def]
  \\ Cases_on ‘l = []’ \\ gvs [evaluate_def,apps_def]
  >- (gvs [do_opapp_def,dec_clock_def,state_component_equality])
  \\ imp_res_tac evaluate_sing \\ gvs [Funs_def]
  \\ Cases_on ‘s2.clock’
  >-
   (irule evaluate_apps_f_err \\ gvs []
    \\ gvs [evaluate_def,do_opapp_def]
    \\ gvs [state_component_equality])
  \\ gvs []
  \\ last_x_assum drule
  \\ disch_then $ qspec_then ‘App Opapp [x'; x]’ mp_tac
  \\ gvs [evaluate_def,do_opapp_def]
  \\ Cases_on ‘t’ \\ gvs [Funs_def,evaluate_def,dec_clock_def]
  \\ disch_then irule
  \\ qrefinel [‘_’,‘_ :: _’] \\ gvs []
  \\ rpt $ irule_at Any EQ_REFL \\ gvs []
QED

Theorem evaluate_apps:
  ∀xs (st:'ffi state) env s1 s2 vs.
    evaluate st env xs = (s1,Rval vs) ∧
    LENGTH xs = SUC (LENGTH ns) ∧
    nsLookup env.v n = SOME clos_v ∧
    do_opapp [clos_v; LAST vs] = SOME (env1,Funs ns e) ⇒
    evaluate st env [apps (Var n) (REVERSE xs)] =
    if s1.clock < LENGTH xs then
      (s1 with clock := 0,Rerr (Rabort Rtimeout_error))
    else
      evaluate
        (s1 with clock := s1.clock - LENGTH xs)
        (env1 with v := nsAppend (alist_to_ns (ZIP (REVERSE ns,BUTLAST vs))) env1.v) [e]
Proof
  Cases using SNOC_CASES \\ gvs [REVERSE_SNOC,apps_def]
  \\ simp [Once SNOC_APPEND]
  \\ simp [evaluate_append,AllCaseEqs(),PULL_EXISTS]
  \\ rpt strip_tac
  \\ imp_res_tac evaluate_sing \\ gvs []
  \\ Cases_on ‘ns = []’
  \\ gvs [apps_def]
  >-
   (gvs [evaluate_def]
    \\ Cases_on ‘s1.clock’
    \\ gvs [dec_clock_def,Funs_def]
    \\ gvs [state_component_equality])
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ Cases_on ‘s1.clock < SUC (LENGTH ns)’ \\ gvs []
  >-
   (Cases_on ‘s1.clock’ \\ gvs []
    >- (irule evaluate_apps_f_err \\ gvs [evaluate_def]
        \\ gvs [state_component_equality])
    \\ irule EQ_TRANS
    \\ irule_at Any evaluate_apps_Funs_timeout \\ gvs []
    \\ gvs [evaluate_def]
    \\ Cases_on ‘ns’ \\ gvs [Funs_def,evaluate_def,dec_clock_def]
    \\ qrefinel [‘_ :: _’,‘_’] \\ gvs []
    \\ rpt $ irule_at Any EQ_REFL \\ gvs [])
  \\ rewrite_tac [GSYM SNOC_APPEND,FRONT_SNOC]
  \\ irule EQ_TRANS
  \\ irule_at (Pos hd) evaluate_apps_Funs
  \\ last_x_assum $ irule_at Any
  \\ simp [evaluate_def]
  \\ Cases_on ‘ns’ \\ gvs [Funs_def]
  \\ simp [evaluate_def]
  \\ qexists_tac ‘h::t’ \\ gvs []
  \\ irule_at (Pos hd) EQ_REFL
  \\ gvs [dec_clock_def,ADD1]
QED

val _ = export_theory();
