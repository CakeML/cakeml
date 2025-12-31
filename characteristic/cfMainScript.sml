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
  ``Dlet unknown_loc (Pcon NONE []) (App Opapp [Var (Short ^s); Con NONE []])``;
val fname = mk_var("fname",``:string``);
val main_call = mk_main_call fname;

Theorem call_main_thm1:
 Decls env1 st1 prog env2 st2 ==> (* get this from the current ML prog state *)
 lookup_var fname env2 = SOME fv ==> (* get this by EVAL *)
  app p fv [Conv NONE []] P (POSTv uv. &UNIT_TYPE () uv * Q) ==> (* this should be the CF spec you prove for the "main" function *)
    SPLIT (st2heap p st2) (h1,h2) /\ P h1 ==>  (* this might need simplification, but some of it may need to stay on the final theorem *)
    ∃st3.
      Decls env1 st1 (SNOC ^main_call prog) env2 st3 /\
      (?h3 h4. SPLIT3 (st2heap p st3) (h3,h2,h4) /\ Q h3)
Proof
  rw[SNOC_APPEND,Decls_APPEND,PULL_EXISTS]
  \\ simp[Decls_def]
  \\ fs [evaluate_dec_list_def,PULL_EXISTS,
         EVAL ``(pat_bindings (Pcon NONE []) [])``,pair_case_eq,result_case_eq]
  \\ fs [evaluate_def,PULL_EXISTS,pair_case_eq,
         result_case_eq,do_con_check_def,build_conv_def,bool_case_eq,
         lookup_var_def,option_case_eq,match_result_case_eq,
         nsLookup_merge_env,app_def,app_basic_def]
  \\ first_x_assum drule \\ fs [] \\ strip_tac \\ fs []
  \\ fs [cfHeapsBaseTheory.POSTv_def, cfHeapsBaseTheory.POST_def]
  \\ Cases_on `r` \\ fs [cond_STAR] \\ fs [cond_def]
  \\ fs [UNIT_TYPE_def] \\ rveq \\ fs []
  \\ fs [Decls_def,evaluate_to_heap_def, evaluate_ck_def]
  \\ drule evaluate_add_to_clock
  \\ disch_then (qspec_then `ck2` mp_tac) \\ simp []
  \\ qpat_x_assum `_ env1 prog = _` assume_tac
  \\ drule evaluate_dec_list_add_to_clock
  \\ disch_then (qspec_then `ck` mp_tac) \\ simp []
  \\ rpt strip_tac
  \\ once_rewrite_tac [CONJ_COMM]
  \\ `evaluate_dec_list (st1 with clock := ck + ck1) env1 prog =
         (st2 with clock := ck + ck2,Rval env2)` by fs []
  \\ asm_exists_tac \\ fs []
  \\ once_rewrite_tac [CONJ_COMM] \\ rewrite_tac [GSYM CONJ_ASSOC]
  \\ once_rewrite_tac [CONJ_COMM] \\ rewrite_tac [GSYM CONJ_ASSOC]
  \\ fs [evaluateTheory.dec_clock_def]
  \\ `evaluate (st2 with clock := (ck + ck2 + 1) - 1) env [exp] =
        ((st' with clock := st2.clock) with clock := ck2 + st'.clock,
         Rval [Conv NONE []])` by fs []
  \\ asm_exists_tac \\ fs [pmatch_def]
  \\ fs [merge_env_def]
  \\ fs [cfStoreTheory.st2heap_clock]
  \\ asm_exists_tac \\ fs []
QED

Theorem prog_to_semantics_dec_list[local]:
  !init_env inp prog st c r env2 s2.
     Decls init_env inp prog env2 s2 ==>
     (semantics_dec_list inp init_env prog (Terminate Success s2.ffi.io_events))
Proof
  rw[Decls_def]
  \\ fs[semantics_dec_list_def,PULL_EXISTS]
  \\ fs[evaluate_dec_list_with_clock_def]
  \\ qexists_tac `ck1` \\ fs []
QED

Theorem clock_eq_lemma[local]:
  ∀c. st with clock := a = st2 with clock := b ==>
      st with clock := c = st2 with clock := c
Proof
  simp[state_component_equality]
QED

Theorem state_eq_semantics_dec_list[local]:
  st with clock := a = st2 with clock := b ==>
   semantics_dec_list st env prog r = semantics_dec_list st2 env prog r
Proof
  strip_tac \\ Cases_on `r`
  \\ simp[semantics_dec_list_def, evaluate_dec_list_with_clock_def]
  \\ imp_res_tac clock_eq_lemma
  \\ fs[]
QED

Theorem prog_SNOC_semantics_dec_list[local]:
  ∀prog1 init_env decl st1 c outcome events env2 st2.
    Decls init_env st1 prog1 env2 st2 ∧
    semantics_dec_list st2 (merge_env env2 init_env) [decl] (Terminate outcome events)
    ==>
    semantics_dec_list st1 init_env (SNOC decl prog1) (Terminate outcome events)
Proof
  rw [semantics_dec_list_def,Decls_def,SNOC_APPEND]
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

Theorem call_main_thm2:
   Decls env1 st1 prog env2 st2 ==>
   lookup_var fname env2 = SOME fv ==>
  app (proj1, proj2) fv [Conv NONE []] P (POSTv uv. &UNIT_TYPE () uv * Q) ==>
  FFI_part_hprop Q ==>
  SPLIT (st2heap (proj1, proj2) st2) (h1,h2) /\ P h1
  ==>
    ∃st3.
    semantics_dec_list st1 env1  (SNOC ^main_call prog) (Terminate Success st3.ffi.io_events) /\
    (?h3 h4. SPLIT3 (st2heap (proj1, proj2) st3) (h3,h2,h4) /\ Q h3) /\
    call_FFI_rel^* st1.ffi st3.ffi
Proof
  rw[]
  \\ qho_match_abbrev_tac`?st3. A st3 /\ B st3 /\ C st1 st3`
  \\ `?st3. Decls env1 st1 (SNOC ^main_call prog) env2 st3
            /\ B st3 /\ C st1 st3`
         suffices_by metis_tac[prog_to_semantics_dec_list]
  \\ reverse (sg `?st3. Decls env1 st1 (SNOC ^main_call prog) env2 st3 ∧ B st3`)
  THEN1 (asm_exists_tac \\ fs [Abbr`C`]
         \\ fs [Decls_def]
         \\ imp_res_tac evaluate_dec_list_call_FFI_rel_imp \\ fs [])
  \\ simp[Abbr`A`,Abbr`B`]
  \\ drule (GEN_ALL call_main_thm1)
  \\ rpt (disch_then drule)
  \\ simp[] \\ strip_tac
  \\ asm_exists_tac \\ simp[]
QED

Theorem call_main_thm2_ffidiv:
   Decls env1 st1 prog env2 st2 ==>
   lookup_var fname env2 = SOME fv ==>
  app (proj1, proj2) fv [Conv NONE []] P (POSTf n. λ c b. Q n c b) ==>
  SPLIT (st2heap (proj1, proj2) st2) (h1,h2) /\ P h1
  ==>
    ∃st3 n c b.
    semantics_dec_list st1 env1  (SNOC ^main_call prog)
                   (Terminate (FFI_outcome(Final_event (ExtCall n) c b FFI_diverged)) st3.ffi.io_events) /\
    (?h3 h4. SPLIT3 (st2heap (proj1, proj2) st3) (h3,h2,h4) /\ Q n c b h3) /\
    call_FFI_rel^* st1.ffi st3.ffi
Proof
  rw[]
  \\ qho_match_abbrev_tac`?st3 n c b. A st3 n c b /\ B st3 n c b /\ C st1 st3`
  \\ `?st3 st4 n c b.  Decls env1 st1 prog env2 st3
                       /\ semantics_dec_list st3 (merge_env env2 env1) [(^main_call)]
                          (Terminate (FFI_outcome(Final_event (ExtCall n) c b FFI_diverged))
                                     st4.ffi.io_events)
                       /\ B st4 n c b /\ C st1 st4`
       suffices_by metis_tac[prog_SNOC_semantics_dec_list]
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
      >- (fs[semantics_dec_list_def, evaluate_dec_list_with_clock_def,
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

