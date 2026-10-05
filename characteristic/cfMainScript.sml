(*
  The following section culminates in call_main_thm2 which takes a
  spec and some aspects of the current state, and proves a
  Semantics_prog statement.

  It also proves call_FFI_rel^* between the initial state, and the
  state after creating the prog and then calling the main function -
  this is useful for theorizing about the output of the program.
*)
Theory cfMain
Ancestors
  semanticPrimitives ml_translator ml_prog cfHeaps cf
  evaluateProps evaluate evaluate_dec
Libs
  preamble ml_translatorLib ml_progLib cfTacticsBaseLib
  cfTacticsLib

fun mk_main_call s =
(* TODO: don't use the parser so much here? *)
  ``Dlet NoLocs (Pcon NONE []) (App Opapp [Var (Short ^s); Con NONE []])``;
val fname = mk_var("fname",``:mlstring``);
val main_call = mk_main_call fname;

(* Running main may consume the oracle, unlike the declarations in Decls. *)
Theorem call_main_thm1:
 Decls env1 st1 prog env2 st2 ==> (* get this from the current ML prog state *)
 lookup_var fname env2 = SOME fv ==> (* get this by EVAL *)
  app p fv [Conv NONE []] P (POSTv uv. &UNIT_TYPE () uv * Q) ==> (* this should be the CF spec you prove for the "main" function *)
    SPLIT (st2heap p st2) (h1,h2) /\ P h1 ==>  (* this might need simplification, but some of it may need to stay on the final theorem *)
    ∃st3.
      (?ck1 ck2. evaluate_dec_list (st1 with clock := ck1) env1
                   (SNOC ^main_call prog) =
                   (st3 with clock := ck2, Rval env2)) /\
      (?h3 h4. SPLIT3 (st2heap p st3) (h3,h2,h4) /\ Q h3)
Proof
  rw [app_def,app_basic_def]
  \\ first_x_assum drule \\ fs [] \\ strip_tac \\ fs []
  \\ fs [cfHeapsBaseTheory.POSTv_def, cfHeapsBaseTheory.POST_def]
  \\ Cases_on `r` \\ fs [cond_STAR] \\ fs [cond_def]
  \\ fs [UNIT_TYPE_def] \\ rveq \\ fs []
  \\ fs [Decls_def,evaluate_to_heap_def, evaluate_ck_def]
  \\ drule evaluate_add_to_clock
  \\ disch_then (qspec_then `ck2` mp_tac) \\ simp []
  \\ qpat_x_assum `_ env1 prog = _` assume_tac
  \\ drule evaluate_dec_list_add_to_clock
  \\ disch_then (qspec_then `ck + 1` mp_tac) \\ simp []
  \\ rpt strip_tac
  \\ qexists_tac `st'`
  \\ conj_tac
  >- (MAP_EVERY qexists_tac [`ck + (ck1 + 1)`, `ck2 + st'.clock`]
      \\ simp [SNOC_APPEND,evaluate_dec_list_append,extend_dec_env_def]
      \\ simp [evaluate_dec_list_def,astTheory.pat_bindings_def]
      \\ NTAC 3 (simp [Once evaluate_def])
      \\ simp [do_con_check_def,build_conv_def]
      \\ fs [Once evaluate_def,lookup_var_def,nsLookup_nsAppend_Short]
      \\ simp [dec_clock_def,pmatch_def,combine_dec_result_def,
               merge_env_def,empty_env_def])
  \\ fs [] \\ asm_exists_tac \\ fs []
QED

Theorem prog_to_semantics_dec_list_determ[local]:
  !init_env inp prog st c r env2 s2.
     (?ck1 ck2. evaluate_dec_list (inp with clock := ck1) init_env prog =
                 (s2 with clock := ck2, Rval env2)) ==>
     (semantics_dec_list_determ inp init_env prog (Terminate Success s2.ffi.io_events))
Proof
  rw[]
  \\ fs[semantics_dec_list_determ_def,PULL_EXISTS]
  \\ fs[evaluate_dec_list_with_clock_def]
  \\ qexists_tac `ck1` \\ fs []
QED

Theorem clock_eq_lemma[local]:
  ∀c. st with clock := a = st2 with clock := b ==>
      st with clock := c = st2 with clock := c
Proof
  simp[state_component_equality]
QED

Theorem state_eq_semantics_dec_list_determ[local]:
  st with clock := a = st2 with clock := b ==>
   semantics_dec_list_determ st env prog r = semantics_dec_list_determ st2 env prog r
Proof
  strip_tac \\ Cases_on `r`
  \\ simp[semantics_dec_list_determ_def, evaluate_dec_list_with_clock_def]
  \\ imp_res_tac clock_eq_lemma
  \\ fs[]
QED

Theorem prog_SNOC_semantics_dec_list_determ[local]:
  ∀prog1 init_env decl st1 c outcome events env2 st2.
    Decls init_env st1 prog1 env2 st2 ∧
    semantics_dec_list_determ st2 (merge_env env2 init_env) [decl] (Terminate outcome events)
    ==>
    semantics_dec_list_determ st1 init_env (SNOC decl prog1) (Terminate outcome events)
Proof
  rw [semantics_dec_list_determ_def,Decls_def,SNOC_APPEND]
  \\ gvs [evaluate_dec_list_with_clock_def]
  \\ qpat_x_assum ‘_ = (_,_)’ mp_tac
  \\ dxrule evaluate_dec_list_set_clock
  \\ disch_then $ qspec_then ‘k’ assume_tac \\ gvs []
  \\ rename [‘evaluate_dec_list (st1 with clock := ck5) _ _ = (_,Rval env2)’]
  \\ pairarg_tac \\ gvs []
  \\ strip_tac \\ gvs []
  \\ qexists_tac ‘ck5’
  \\ gvs [evaluate_dec_list_append,extend_dec_env_def,merge_env_def]
  \\ Cases_on ‘r’ \\ gvs [combine_dec_result_def]
QED

Definition FFI_part_hprop_def:
  FFI_part_hprop Q =
   (!h. Q h ==> (?s u ns us. FFI_part s u ns us IN h))
End

Theorem FFI_part_hprop_STAR:
   FFI_part_hprop P \/ FFI_part_hprop Q ==> FFI_part_hprop (P * Q)
Proof
  rw[FFI_part_hprop_def]
  \\ fs[set_sepTheory.STAR_def,SPLIT_def] \\ rw[]
  \\ metis_tac[]
QED

Theorem FFI_part_hprop_SEP_EXISTS:
   (∀x. FFI_part_hprop (P x)) ⇒ FFI_part_hprop (SEP_EXISTS x. P x)
Proof
  rw[FFI_part_hprop_def,SEP_EXISTS_THM] \\ res_tac
QED

Theorem call_main_thm2_determ[local]:
  Decls env1 st1 prog env2 st2 ==>
  lookup_var fname env2 = SOME fv ==>
  app (proj1, proj2) fv [Conv NONE []] P (POSTv uv. &UNIT_TYPE () uv * Q) ==>
  FFI_part_hprop Q ==>
  SPLIT (st2heap (proj1, proj2) st2) (h1,h2) /\ P h1
  ==>
  ∃st3.
    semantics_dec_list_determ st1 env1 (SNOC ^main_call prog)
      (Terminate Success st3.ffi.io_events) /\
    (∃h3 h4. SPLIT3 (st2heap (proj1, proj2) st3) (h3,h2,h4) /\ Q h3) /\
    call_FFI_rel^* st1.ffi st3.ffi
Proof
  rw[]
  \\ drule (GEN_ALL call_main_thm1)
  \\ rpt (disch_then drule)
  \\ simp[] \\ strip_tac
  \\ qexists_tac `st3`
  \\ fs []
  \\ conj_tac >- metis_tac [prog_to_semantics_dec_list_determ]
  \\ imp_res_tac evaluate_dec_list_call_FFI_rel_imp \\ fs []
  \\ asm_exists_tac \\ fs []
QED

Theorem call_main_thm2_ffidiv_determ[local]:
   Decls env1 st1 prog env2 st2 ==>
   lookup_var fname env2 = SOME fv ==>
  app (proj1, proj2) fv [Conv NONE []] P (POSTf n. λ c b. Q n c b) ==>
  SPLIT (st2heap (proj1, proj2) st2) (h1,h2) /\ P h1
  ==>
    ∃st3 n c b.
    semantics_dec_list_determ st1 env1 (SNOC ^main_call prog)
      (Terminate (FFI_outcome(Final_event (ExtCall n) c b FFI_diverged))
                 st3.ffi.io_events) /\
    (?h3 h4. SPLIT3 (st2heap (proj1, proj2) st3) (h3,h2,h4) /\ Q n c b h3) /\
    call_FFI_rel^* st1.ffi st3.ffi
Proof
  rw[]
  \\ qho_match_abbrev_tac`?st3 n c b. A st3 n c b /\ B st3 n c b /\ C st1 st3`
  \\ `?st3 st4 n c b.  Decls env1 st1 prog env2 st3
                       /\ semantics_dec_list_determ st3 (merge_env env2 env1) [(^main_call)]
                          (Terminate (FFI_outcome(Final_event (ExtCall n) c b FFI_diverged))
                                     st4.ffi.io_events)
                       /\ B st4 n c b /\ C st1 st4`
       suffices_by metis_tac[prog_SNOC_semantics_dec_list_determ]
  \\ fs[]
  \\ asm_exists_tac \\ fs[app_def,app_basic_def]
  \\ first_x_assum drule \\ impl_tac >- simp[]
  \\ rpt strip_tac
  \\ Cases_on `r`
  >- (fs[cond_def])
  >- (fs[cond_def])
  >- (fs[evaluate_to_heap_def]
      \\ rename1 `Final_event (ExtCall name) conf bytes _`
      \\ rename1 `evaluate_ck _ _ _ _ = (st4,_)`
      \\ MAP_EVERY qexists_tac [`st4`,`name`,`conf`,`bytes`]
      \\ conj_tac
      >- (fs[semantics_dec_list_determ_def, evaluate_dec_list_with_clock_def,
             evaluate_dec_list_def]
          \\ simp[Once evaluate_def]
          \\ simp[astTheory.pat_bindings_def]
          \\ simp[Once evaluate_def]
          \\ simp[Once evaluate_def]
          \\ simp[do_con_check_def,build_conv_def]
          \\ simp[Once evaluate_def]
          \\ simp[nsLookup_merge_env]
          \\ fs[lookup_var_def,evaluate_ck_def]
          \\ Q.REFINE_EXISTS_TAC `SUC k` \\ fs[]
          \\ simp[evaluateTheory.dec_clock_def]
          \\ qexists_tac `ck` \\ simp[])
      \\ conj_tac
      >- metis_tac[]
      \\ unabbrev_all_tac
      \\ simp[]
      \\ fs[Decls_def]
      \\ drule evaluate_dec_list_call_FFI_rel_imp
      \\ strip_tac
      \\ fs[evaluate_ck_def]
      \\ imp_res_tac evaluate_call_FFI_rel_imp
      \\ fs[] \\ metis_tac[RTC_RTC])
  >- (fs[cond_def])
QED

(* A terminating run fixes the behavior for one pointer oracle. *)
Theorem evaluate_dec_list_clock_result[local]:
  evaluate_dec_list (st with clock := ck1) env prog = (s1,r1) ∧
  r1 ≠ Rerr (Rabort Rtimeout_error) ∧
  evaluate_dec_list (st with clock := ck2) env prog = (s2,r2) ∧
  r2 ≠ Rerr (Rabort Rtimeout_error) ⇒
  s1.ffi = s2.ffi ∧ r1 = r2
Proof
  strip_tac
  \\ qspecl_then [‘st with clock := ck1’,‘env’,‘prog’,‘s1’,‘r1’,‘ck2’]
       mp_tac evaluate_dec_list_add_to_clock
  \\ qspecl_then [‘st with clock := ck2’,‘env’,‘prog’,‘s2’,‘r2’,‘ck1’]
       mp_tac evaluate_dec_list_add_to_clock
  \\ simp [] \\ rpt strip_tac
  \\ gvs [AC arithmeticTheory.ADD_COMM arithmeticTheory.ADD_ASSOC,
          state_component_equality]
QED

Theorem semantics_dec_list_determ_terminate_unique[local]:
  semantics_dec_list_determ st env prog (Terminate outcome io) ∧
  semantics_dec_list_determ st env prog behavior ⇒
  behavior = Terminate outcome io
Proof
  strip_tac
  \\ Cases_on ‘behavior’
  \\ gvs [semantics_dec_list_determ_def,evaluate_dec_list_with_clock_def,
          pair_case_eq]
  >- (first_x_assum (qspec_then ‘k’ strip_assume_tac) \\ gvs [])
  \\ pairarg_tac \\ gvs []
  \\ pairarg_tac \\ gvs []
  \\ every_case_tac \\ gvs []
  \\ metis_tac [evaluate_dec_list_clock_result, result_distinct,
                error_result_distinct, abort_distinct,
                result_11, error_result_11, abort_11]
QED

(* Every pointer oracle terminates, but its trace and witnesses may differ. *)
Theorem semantics_dec_list_all_terminate[local]:
  (∀po. ∃outcome io.
    semantics_dec_list_determ (st with ptr_eq_oracle := po) env prog
      (Terminate outcome io) ∧ R (Terminate outcome io)) ⇒
  semantics_dec_list st env prog ≠ ∅ ∧
  ∀behavior. semantics_dec_list st env prog behavior ⇒ R behavior
Proof
  rw [semantics_dec_list_def,FUN_EQ_THM]
  \\ metis_tac [semantics_dec_list_determ_terminate_unique]
QED

Definition sem_satisfies_def:
  sem_satisfies s P ⇔ s ≠ {} ∧ ∀b:behaviour. b ∈ s ⇒ P b
End

Theorem call_main_thm2:
  Decls env1 st1 prog env2 st2 ⇒
  lookup_var fname env2 = SOME fv ⇒
  app (proj1,proj2) fv [Conv NONE []] P (POSTv uv. &UNIT_TYPE () uv * Q) ⇒
  FFI_part_hprop Q ⇒
  SPLIT (st2heap (proj1,proj2) st2) (h1,h2) ∧ P h1
  ⇒
  sem_satisfies (semantics_dec_list st1 env1 (SNOC ^main_call prog))
    (λbehavior.
      ∃st3.
        behavior = Terminate Success st3.ffi.io_events ∧
        (∃h3 h4. SPLIT3 (st2heap (proj1,proj2) st3) (h3,h2,h4) ∧ Q h3) ∧
        call_FFI_rel^* st1.ffi st3.ffi)
Proof
  rpt strip_tac
  \\ simp [sem_satisfies_def, IN_DEF]
  \\ ho_match_mp_tac semantics_dec_list_all_terminate
  \\ gen_tac
  \\ ‘Decls env1 (st1 with ptr_eq_oracle := po) prog env2
             (st2 with ptr_eq_oracle := po)’ by metis_tac [Decls_with_oracle]
  \\ ‘SPLIT (st2heap (proj1,proj2) (st2 with ptr_eq_oracle := po)) (h1,h2)’
       by fs [cfStoreTheory.st2heap_def]
  \\ drule_all (GEN_ALL call_main_thm2_determ)
  \\ simp [] \\ strip_tac
  \\ metis_tac []
QED

Theorem call_main_thm2_ffidiv:
  Decls env1 st1 prog env2 st2 ⇒
  lookup_var fname env2 = SOME fv ⇒
  app (proj1,proj2) fv [Conv NONE []] P (POSTf n. λc b. Q n c b) ⇒
  SPLIT (st2heap (proj1,proj2) st2) (h1,h2) ∧ P h1
  ⇒
  sem_satisfies (semantics_dec_list st1 env1 (SNOC ^main_call prog))
    (λbehavior.
      ∃st3 n c b.
        behavior = Terminate
          (FFI_outcome (Final_event (ExtCall n) c b FFI_diverged))
          st3.ffi.io_events ∧
        (∃h3 h4. SPLIT3 (st2heap (proj1,proj2) st3) (h3,h2,h4) ∧ Q n c b h3) ∧
        call_FFI_rel^* st1.ffi st3.ffi)
Proof
  rpt strip_tac
  \\ simp [sem_satisfies_def, IN_DEF]
  \\ ho_match_mp_tac semantics_dec_list_all_terminate
  \\ gen_tac
  \\ ‘Decls env1 (st1 with ptr_eq_oracle := po) prog env2
             (st2 with ptr_eq_oracle := po)’ by metis_tac [Decls_with_oracle]
  \\ ‘SPLIT (st2heap (proj1,proj2) (st2 with ptr_eq_oracle := po)) (h1,h2)’
       by fs [cfStoreTheory.st2heap_def]
  \\ drule_all (GEN_ALL call_main_thm2_ffidiv_determ)
  \\ simp [] \\ strip_tac
  \\ metis_tac []
QED
