(*
  Correctness proof for bvi_inline
*)

open preamble backendPropsTheory
     bvlSemTheory bvlPropsTheory
     bvl_inlineTheory
local open bvl_handleProofTheory in end

val _ = new_theory"bvl_inlineProof";

val _ = set_grammar_ancestry [ "bvlSem", "bvlProps", "bvl_inline" ];

(* removal of ticks *)

val state_rel_def = Define `
  state_rel (s:('c,'ffi) bvlSem$state) (t:('c,'ffi) bvlSem$state) <=>
    t = s with <| code := map (I ## (\x. HD (remove_ticks [x]))) s.code
                ; compile := t.compile
                ; compile_oracle := (I ##
      MAP (I ## I ## (\x. HD (remove_ticks [x])))) o s.compile_oracle |> /\
    s.compile = \cfg prog. t.compile cfg
                   (MAP (I ## I ## (\x. HD (remove_ticks [x]))) prog)`

val state_rel_alt = state_rel_def

val state_rel_def =
  state_rel_def |> SIMP_RULE (srw_ss()) [state_component_equality,GSYM CONJ_ASSOC];

val do_app_lemma = prove(
  ``state_rel t' r ==>
    case do_app op (REVERSE a) r of
    | Rerr err => do_app op (REVERSE a) t' = Rerr err
    | Rval (v,r2) => ?t2. state_rel t2 r2 /\ do_app op (REVERSE a) t' = Rval (v,t2)``,
  Cases_on `op = Install` THEN1
   (rw [] \\ fs [do_app_def]
    \\ every_case_tac \\ fs []
    \\ fs [case_eq_thms,UNCURRY,do_install_def]
    \\ rveq \\ fs [PULL_EXISTS]
    \\ fs [SWAP_REVERSE_SYM] \\ rveq \\ fs []
    \\ fs [state_rel_def] \\ rveq \\ fs []
    \\ fs [domain_map]
    \\ fs [state_component_equality]
    THEN1
     (fs [shift_seq_def,o_DEF] \\ rfs []
      \\ Cases_on `t'.compile_oracle 0` \\ fs []
      \\ Cases_on `r'` \\ fs [] \\ Cases_on `h` \\ fs [] \\ rveq \\ fs []
      \\ fs [domain_map]
      \\ fs [map_union] \\ AP_TERM_TAC
      \\ fs [map_fromAList] \\ AP_TERM_TAC \\ fs []
      \\ rpt (AP_THM_TAC ORELSE AP_TERM_TAC)
      \\ fs [FUN_EQ_THM,FORALL_PROD])
    \\ CCONTR_TAC \\ fs []
    \\ rfs [FORALL_PROD,shift_seq_def,domain_map]
    \\ metis_tac [list_nchotomy,PAIR])
  \\ strip_tac \\ Cases_on `do_app op (REVERSE a) t'`
  THEN1
   (rename1 `_ = Rval aa`
    \\ PairCases_on `aa`
    \\ drule (Q.GENL [`c`,`cc`,`co`] do_app_with_code) \\ fs []
    \\ fs [state_rel_alt]
    \\ disch_then (qspecl_then [`map (I ## (λx. HD (remove_ticks [x]))) t'.code`,
        `r.compile`,`(I ## MAP (I ## I ## (λx. HD (remove_ticks [x])))) ∘
          t'.compile_oracle`] mp_tac)
    \\ qpat_x_assum `r = _` (assume_tac o GSYM) \\ fs []
    \\ impl_tac THEN1 fs [domain_map]
    \\ strip_tac \\ fs []
    \\ qpat_x_assum `_ = r` (assume_tac o GSYM) \\ fs []
    \\ rw [] \\ fs [state_component_equality]
    \\ imp_res_tac do_app_const \\ fs [])
  \\ drule (Q.GENL [`c`,`cc`,`co`] do_app_with_code_err_not_Install) \\ fs []
  \\ fs [state_rel_alt]
  \\ disch_then (qspecl_then [`map (I ## (λx. HD (remove_ticks [x]))) t'.code`,
      `r.compile`,`(I ## MAP (I ## I ## (λx. HD (remove_ticks [x])))) ∘
        t'.compile_oracle`] mp_tac)
  \\ qpat_x_assum `r = _` (assume_tac o GSYM) \\ fs []
  \\ impl_tac THEN1 fs [domain_map] \\ fs []);

Theorem evaluate_remove_ticks:
   !k xs env s (t:('c,'ffi) bvlSem$state) res s'.
      state_rel t s /\ s.clock = k /\
      evaluate (remove_ticks xs,env,s) = (res,s') ==>
      ?ck t'. evaluate (xs,env,t with clock := t.clock + ck) = (res,t') /\
              state_rel t' s'
Proof
  strip_tac \\ completeInduct_on `k` \\ fs [PULL_FORALL,AND_IMP_INTRO]
  \\ recInduct remove_ticks_ind \\ rw []
  THEN1 (* NIL *)
   (fs [evaluate_def,remove_ticks_def] \\ rveq
    \\ qexists_tac `0` \\ fs [state_rel_def,state_component_equality])
  THEN1 (* CONS *)
   (fs [evaluate_def,remove_ticks_def]
    \\ pop_assum mp_tac \\ simp [Once evaluate_CONS]
    \\ TOP_CASE_TAC
    \\ qpat_x_assum `!x. _` mp_tac
    \\ first_x_assum drule \\ fs []
    \\ disch_then drule \\ strip_tac
    \\ reverse (Cases_on `q`) \\ fs []
    THEN1 (rw [] \\ fs [] \\ qexists_tac `ck` \\ fs [])
    \\ strip_tac
    \\ `∀env s' (t:('c,'ffi) bvlSem$state) res s''.
         state_rel t s' ∧ s'.clock <= s.clock ∧
         evaluate (remove_ticks (y::xs),env,s') = (res,s'') ⇒
         ∃ck t'.
           evaluate (y::xs,env,t with clock := ck + t.clock) = (res,t') ∧
           state_rel t' s''` by metis_tac [LESS_OR_EQ]
    \\ pop_assum drule
    \\ imp_res_tac evaluate_clock \\ fs []
    \\ TOP_CASE_TAC \\ disch_then drule \\ strip_tac
    \\ rw [] \\ qexists_tac `ck+ck'`
    \\ qpat_x_assum `evaluate ([x],_) = _` assume_tac
    \\ drule evaluate_add_clock \\ fs [inc_clock_def]
    \\ disch_then kall_tac
    \\ CASE_TAC \\ fs [])
  THEN1 (* Var *)
   (fs [evaluate_def,remove_ticks_def]
    \\ CASE_TAC \\ fs [] \\ rveq
    \\ qexists_tac `0` \\ fs [state_rel_def,state_component_equality])
  THEN1 (* If *)
   (fs [evaluate_def,remove_ticks_def]
    \\ pop_assum mp_tac \\ TOP_CASE_TAC
    \\ qpat_x_assum `!x. _` mp_tac
    \\ qpat_x_assum `!x. _` mp_tac
    \\ first_x_assum drule \\ fs []
    \\ disch_then drule \\ strip_tac
    \\ reverse (Cases_on `q`) \\ fs []
    THEN1 (rw [] \\ fs [] \\ qexists_tac `ck` \\ fs [])
    \\ TOP_CASE_TAC THEN1
     (disch_then assume_tac \\ disch_then kall_tac \\ strip_tac
      \\ `∀env s' (t:('c,'ffi) bvlSem$state) res s''.
           state_rel t s' ∧ s'.clock <= s.clock ∧
           evaluate (remove_ticks [x2],env,s') = (res,s'') ⇒
           ∃ck t'.
             evaluate ([x2],env,t with clock := ck + t.clock) = (res,t') ∧
             state_rel t' s''` by metis_tac [LESS_OR_EQ]
      \\ first_x_assum drule
      \\ imp_res_tac evaluate_clock \\ fs []
      \\ disch_then drule \\ strip_tac
      \\ rw [] \\ qexists_tac `ck+ck'`
      \\ qpat_x_assum `evaluate ([x1],_) = _` assume_tac
      \\ drule evaluate_add_clock \\ fs [inc_clock_def]
      \\ disch_then kall_tac)
    \\ TOP_CASE_TAC THEN1
     (disch_then kall_tac \\ disch_then assume_tac \\ strip_tac
      \\ `∀env s' (t:('c,'ffi) bvlSem$state) res s''.
           state_rel t s' ∧ s'.clock <= s.clock ∧
           evaluate (remove_ticks [x3],env,s') = (res,s'') ⇒
           ∃ck t'.
             evaluate ([x3],env,t with clock := ck + t.clock) = (res,t') ∧
             state_rel t' s''` by metis_tac [LESS_OR_EQ]
      \\ first_x_assum drule
      \\ imp_res_tac evaluate_clock \\ fs []
      \\ disch_then drule \\ strip_tac
      \\ rw [] \\ qexists_tac `ck+ck'`
      \\ qpat_x_assum `evaluate ([x1],_) = _` assume_tac
      \\ drule evaluate_add_clock \\ fs [inc_clock_def]
      \\ disch_then kall_tac)
    \\ rw [] \\ qexists_tac `ck` \\ fs [])
  THEN1 (* Let *)
   (fs [evaluate_def,remove_ticks_def]
    \\ pop_assum mp_tac \\ TOP_CASE_TAC
    \\ qpat_x_assum `!x. _` mp_tac
    \\ first_x_assum drule \\ fs []
    \\ disch_then drule \\ strip_tac
    \\ reverse (Cases_on `q`) \\ fs []
    THEN1 (rw [] \\ fs [] \\ qexists_tac `ck` \\ fs [])
    \\ strip_tac
    \\ `∀env s' (t:('c,'ffi) bvlSem$state) res s''.
           state_rel t s' ∧ s'.clock <= s.clock ∧
           evaluate (remove_ticks [x2],env,s') = (res,s'') ⇒
           ∃ck t'.
             evaluate ([x2],env,t with clock := ck + t.clock) = (res,t') ∧
             state_rel t' s''` by metis_tac [LESS_OR_EQ]
    \\ first_x_assum drule
    \\ imp_res_tac evaluate_clock \\ fs []
    \\ rpt strip_tac \\ first_x_assum drule
    \\ rw [] \\ qexists_tac `ck+ck'`
    \\ qpat_x_assum `evaluate (xs,_) = _` assume_tac
    \\ drule evaluate_add_clock \\ fs [inc_clock_def])
  THEN1 (* Raise *)
   (fs [evaluate_def,remove_ticks_def]
    \\ pop_assum mp_tac \\ TOP_CASE_TAC
    \\ first_x_assum drule \\ fs []
    \\ disch_then drule \\ strip_tac
    \\ reverse (Cases_on `q`) \\ fs []
    \\ rw [] \\ fs [] \\ qexists_tac `ck` \\ fs [])
  THEN1 (* Handle *)
   (fs [evaluate_def,remove_ticks_def]
    \\ pop_assum mp_tac \\ TOP_CASE_TAC
    \\ qpat_x_assum `!x. _` mp_tac
    \\ first_x_assum drule \\ fs []
    \\ disch_then drule \\ strip_tac
    \\ Cases_on `q` \\ fs []
    THEN1 (rw [] \\ fs [] \\ qexists_tac `ck` \\ fs [])
    \\ reverse (Cases_on `e`) \\ fs []
    THEN1 (rw [] \\ fs [] \\ qexists_tac `ck` \\ fs [])
    \\ rpt strip_tac
    \\ `∀env s' (t:('c,'ffi) bvlSem$state) res s''.
           state_rel t s' ∧ s'.clock <= s.clock ∧
           evaluate (remove_ticks [x2],env,s') = (res,s'') ⇒
           ∃ck t'.
             evaluate ([x2],env,t with clock := ck + t.clock) = (res,t') ∧
             state_rel t' s''` by metis_tac [LESS_OR_EQ]
    \\ first_x_assum drule
    \\ imp_res_tac evaluate_clock \\ fs []
    \\ rpt strip_tac \\ first_x_assum drule
    \\ rw [] \\ qexists_tac `ck+ck'`
    \\ qpat_x_assum `evaluate ([x1],_) = _` assume_tac
    \\ drule evaluate_add_clock \\ fs [inc_clock_def])
  THEN1 (* Op *)
   (fs [remove_ticks_def,evaluate_def]
    \\ FULL_CASE_TAC \\ fs []
    \\ first_x_assum drule \\ fs []
    \\ disch_then drule \\ strip_tac
    \\ qexists_tac `ck` \\ fs []
    \\ reverse (Cases_on `q`) \\ fs [] \\ rveq \\ fs []
    \\ drule do_app_lemma \\ every_case_tac \\ fs []
    \\ rveq \\ fs [])
  THEN1 (* Tick *)
   (fs [remove_ticks_def]
    \\ first_x_assum drule \\ fs []
    \\ disch_then drule \\ strip_tac
    \\ fs [bvlSemTheory.evaluate_def]
    \\ qexists_tac `ck + 1` \\ fs [dec_clock_def])
  (* Call *)
  \\ fs [remove_ticks_def]
  \\ fs [bvlSemTheory.evaluate_def]
  \\ FULL_CASE_TAC \\ fs []
  \\ reverse (Cases_on `q`) \\ fs [] \\ rveq
  THEN1
   (first_x_assum drule \\ fs []
    \\ disch_then drule \\ strip_tac
    \\ qexists_tac `ck` \\ fs [])
  \\ pop_assum mp_tac
  \\ TOP_CASE_TAC \\ fs [] \\ rpt strip_tac \\ rveq \\ fs []
  THEN1
   (first_x_assum drule \\ fs []
    \\ disch_then drule \\ strip_tac
    \\ qexists_tac `ck` \\ fs []
    \\ qsuff_tac `find_code dest a t'.code = NONE` \\ fs []
    \\ Cases_on `dest` \\ fs [find_code_def]
    \\ every_case_tac \\ fs [state_rel_def]
    \\ rveq \\ fs [lookup_map]
    \\ rfs [lookup_map])
  \\ PairCases_on `x` \\ fs []
  \\ pop_assum mp_tac
  \\ IF_CASES_TAC \\ rw []
  THEN1
   (first_x_assum drule \\ fs []
    \\ disch_then drule \\ strip_tac
    \\ qexists_tac `ck` \\ fs []
    \\ qsuff_tac `?x1 x2. find_code dest a t'.code = SOME (x1,x2)`
    THEN1 (strip_tac \\ fs [] \\ fs [state_rel_def])
    \\ fs [state_rel_def] \\ rveq \\ fs []
    \\ Cases_on `dest` \\ fs [find_code_def]
    \\ every_case_tac \\ fs [] \\ rveq \\ fs [lookup_map] \\ fs []
    \\ PairCases_on `z` \\ fs [])
  \\ first_x_assum drule \\ fs []
  \\ disch_then drule \\ strip_tac
  \\ `(dec_clock 1 r).clock < s.clock` by
        (imp_res_tac evaluate_clock  \\ fs [dec_clock_def] \\ fs [])
  \\ first_x_assum drule
  \\ `state_rel (dec_clock 1 t') (dec_clock 1 r)` by fs [state_rel_def,dec_clock_def]
  \\ disch_then drule
  \\ `?a2. find_code dest a t'.code = SOME (x0,a2) /\
           [x1] = remove_ticks [a2]` by
   (Cases_on `dest` \\ fs [state_rel_def,find_code_def] \\ rveq \\ fs []
    \\ every_case_tac \\ fs [lookup_map] \\ rveq \\ fs []
    \\ rveq \\ fs [])
  \\ fs [] \\ disch_then drule \\ strip_tac
  \\ ntac 2 (pop_assum mp_tac)
  \\ drule evaluate_add_clock \\ fs [inc_clock_def]
  \\ disch_then (qspec_then `ticks+ck'` assume_tac)
  \\ rw [] \\ qexists_tac `ticks + ck+ck'` \\ fs [dec_clock_def]
  \\ qsuff_tac `t'.clock <> 0` \\ rpt strip_tac \\ fs []
  \\ fs [state_rel_def]
QED

val evaluate_remove_ticks_thm =
  evaluate_remove_ticks
  |> SIMP_RULE std_ss []
  |> Q.SPEC `[Call 0 (SOME start) []]`
  |> SIMP_RULE std_ss [remove_ticks_def];

val remove_ticks_cc_def = Define `
  remove_ticks_cc cc =
    (λcfg prog'. cc cfg (MAP (I ## I ## (λx. HD (remove_ticks [x]))) prog'))`;

val remove_ticks_co_def = Define `
  remove_ticks_co =
    (I ## MAP (I ## I ## (λx. HD (remove_ticks [x]))))`;

Theorem evaluate_compile_prog:
   evaluate ([Call 0 (SOME start) []], [],
             initial_state ffi0 (map
                (I ## (λx. HD (remove_ticks [x]))) prog)
                (remove_ticks_co ∘ co) cc k) = (r, s) ⇒
   ∃ck (s2:('c,'ffi) bvlSem$state).
     evaluate
      ([Call 0 (SOME start) []], [],
        initial_state ffi0 prog co (remove_ticks_cc cc) (k + ck)) = (r, s2) ∧
     s2.ffi = s.ffi
Proof
  strip_tac \\ fs [remove_ticks_co_def,remove_ticks_cc_def]
  \\ drule (ONCE_REWRITE_RULE [CONJ_COMM]
             (REWRITE_RULE [CONJ_ASSOC] evaluate_remove_ticks_thm))
  \\ disch_then (qspec_then `initial_state ffi0 prog co
        (λcfg prog'. cc cfg (MAP (I ## I ## (λx. HD (remove_ticks [x]))) prog'))
            k` mp_tac)
  \\ impl_tac THEN1 fs [state_rel_def]
  \\ strip_tac \\ fs []
  \\ qexists_tac `ck` \\ fs [state_rel_def]
QED

val FST_EQ_LEMMA = prove(
  ``FST x = y <=> ?y1. x = (y,y1)``,
  Cases_on `x` \\ fs []);

Theorem semantics_remove_ticks:
   semantics ffi (map (I ## (λx. HD (remove_ticks [x]))) prog)
                 (remove_ticks_co ∘ co)
                 cc start =
   semantics (ffi:'b ffi_state) prog co (remove_ticks_cc cc) start
Proof
  simp [Once semantics_def]
  \\ IF_CASES_TAC \\ fs []
  THEN1
   (simp [semantics_def] \\ IF_CASES_TAC \\ fs [FST_EQ_LEMMA]
    \\ drule evaluate_compile_prog \\ metis_tac [])
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ conj_tac
  >-
   (gen_tac \\ strip_tac \\ rveq \\ simp []
    \\ simp [semantics_def]
    \\ IF_CASES_TAC \\ fs []
    >-
      (first_assum
         (subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) o concl)
      \\ drule evaluate_add_clock
      \\ CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss()) [GSYM PULL_FORALL]))
      \\ impl_tac >- fs []
      \\ strip_tac
      \\ qpat_x_assum `evaluate (_,_,_ _ (_ prog) _ _ _) = _` kall_tac
      \\ last_assum (qspec_then `k'` mp_tac)
      \\ (fn g => subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) (#2 g) g )
      \\ drule (GEN_ALL evaluate_compile_prog) \\ simp []
      \\ strip_tac
      \\ first_x_assum (qspec_then `ck` mp_tac)
      \\ simp [inc_clock_def]
      \\ rw[] \\ fs [])
    \\ DEEP_INTRO_TAC some_intro \\ simp []
    \\ conj_tac
    >-
     (gen_tac \\ strip_tac \\ rveq \\ fs []
      \\ qabbrev_tac `opts = (map (I ## (λx. HD (remove_ticks [x]))) prog)`
      \\ qmatch_assum_abbrev_tac `bvlSem$evaluate (opts1,[],sopt1) = _`
      \\ qmatch_assum_abbrev_tac `bvlSem$evaluate (exps1,[],st1) = (r,s)`
      \\ qspecl_then [`opts1`,`[]`,`sopt1`] mp_tac
           evaluate_add_to_clock_io_events_mono
      \\ qspecl_then [`exps1`,`[]`,`st1`] mp_tac
           evaluate_add_to_clock_io_events_mono
      \\ simp [inc_clock_def, Abbr`sopt1`, Abbr`st1`]
      \\ ntac 2 strip_tac
      \\ Cases_on `r` \\ fs []
      >-
        (Cases_on `r'` \\ fs []
        >-
          (unabbrev_all_tac
          \\ drule (GEN_ALL evaluate_compile_prog) \\ simp []
          \\ strip_tac
          \\ drule evaluate_add_clock
          \\ simp[]
          \\ rveq
          \\ disch_then (qspec_then `k'` mp_tac) \\ simp [inc_clock_def]
          \\ qpat_x_assum `evaluate _ = _` kall_tac
          \\ drule evaluate_add_clock
          \\ simp[]
          \\ disch_then (qspec_then `ck+k` mp_tac) \\ simp [inc_clock_def]
          \\ ntac 2 strip_tac \\ rveq \\ fs []
          \\ fs [state_component_equality, state_rel_def])
        \\ qpat_x_assum `∀extra._` mp_tac
        \\ first_x_assum (qspec_then `k'` assume_tac)
        \\ first_assum (subterm
             (fn tm => Cases_on`^(assert has_pair_type tm)`) o concl)
        \\ strip_tac \\ fs []
        \\ unabbrev_all_tac
        \\ drule (GEN_ALL evaluate_compile_prog)
        \\ strip_tac
        \\ qhdtm_x_assum `evaluate` mp_tac
        \\ imp_res_tac evaluate_add_clock
        \\ pop_assum mp_tac
        \\ ntac 2 (pop_assum kall_tac)
        \\ impl_tac
        >- (strip_tac \\ fs [])
        \\ disch_then (qspec_then `k'` mp_tac) \\ simp [inc_clock_def]
        \\ first_x_assum (qspec_then `ck + k` mp_tac) \\ fs []
        \\ ntac 3 strip_tac
        \\ fs [state_rel_def] \\ rveq
        \\ every_case_tac \\ fs[]
        \\ drule evaluate_add_clock \\ disch_then (qspec_then `ck + k` mp_tac)
        \\ impl_tac >- simp[]
        \\ simp[inc_clock_def])
      \\ qpat_x_assum `∀extra._` mp_tac
      \\ first_x_assum (qspec_then `k'` assume_tac)
      \\ first_assum (subterm (fn tm =>
            Cases_on`^(assert has_pair_type tm)`) o concl)
      \\ fs []
      \\ unabbrev_all_tac
      \\ strip_tac
      \\ drule (GEN_ALL evaluate_compile_prog)
      \\ strip_tac \\ rveq \\ fs []
      \\ reverse (Cases_on `r'`) \\ fs [] \\ rfs []
      >-
        (first_x_assum (qspec_then `ck + k` mp_tac)
        \\ fs [ADD1]
        \\ strip_tac \\ fs [state_rel_def] \\ rfs []
        \\ `e ≠ Rabort Rtimeout_error` by(CCONTR_TAC >> fs[])
        \\ `e' ≠ Rabort Rtimeout_error` by(CCONTR_TAC >> fs[])
        \\ imp_res_tac evaluate_add_clock \\ rfs[]
        \\ rpt(qpat_x_assum `_ ==> !ck. _` kall_tac)
        \\ first_x_assum (qspec_then `k'` mp_tac)
        \\ first_x_assum (qspec_then `ck + k` mp_tac)
        \\ simp[inc_clock_def]
        \\ rpt strip_tac \\ Cases_on `e` \\ rveq \\ fs[]
        \\ PURE_FULL_CASE_TAC \\ fs[] )
      \\ qhdtm_x_assum `evaluate` mp_tac
      \\ imp_res_tac evaluate_add_clock
      \\ pop_assum kall_tac
      \\ pop_assum mp_tac
      \\ impl_tac
      >- (strip_tac \\ fs [])
      \\ disch_then (qspec_then `ck + k` mp_tac)
      \\ simp [inc_clock_def]
      \\ rpt strip_tac \\ rveq
      \\ CCONTR_TAC \\ fs []
      \\ rveq \\ fs [] \\ rfs []
      \\ every_case_tac \\ fs[] \\ rveq \\ fs[]
      \\ drule evaluate_add_clock \\ disch_then(qspec_then `k'` mp_tac)
      \\ impl_tac >- simp[] \\ fs[inc_clock_def])
    \\ qmatch_assum_abbrev_tac `bvlSem$evaluate (exps2,[],st2) = _`
    \\ qspecl_then [`exps2`,`[]`,`st2`] mp_tac evaluate_add_to_clock_io_events_mono
    \\ simp [inc_clock_def, Abbr`st2`]
    \\ disch_then (qspec_then `0` strip_assume_tac)
    \\ first_assum (subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) o concl)
    \\ unabbrev_all_tac
    \\ drule (GEN_ALL evaluate_compile_prog)
    \\ strip_tac
    \\ asm_exists_tac \\ fs []
    \\ every_case_tac \\ fs [] \\ rveq \\ fs [])
  \\ strip_tac
  \\ simp [semantics_def]
  \\ IF_CASES_TAC \\ fs []
  >-
    (last_x_assum (qspec_then `k` assume_tac) \\ rfs []
    \\ first_assum (qspec_then `e` assume_tac)
    \\ fs [] \\ rfs []
    \\ qmatch_assum_abbrev_tac `FST q ≠ _`
    \\ Cases_on `q` \\ fs [markerTheory.Abbrev_def]
    \\ pop_assum (assume_tac o SYM)
    \\ drule (GEN_ALL evaluate_compile_prog)
    \\ simp []
    \\ spose_not_then strip_assume_tac
    \\ qmatch_assum_abbrev_tac `FST q = _`
    \\ Cases_on `q` \\ fs [markerTheory.Abbrev_def]
    \\ pop_assum (assume_tac o SYM)
    \\ imp_res_tac evaluate_add_clock \\ rfs []
    \\ first_x_assum (qspec_then `ck` mp_tac)
    \\ simp [inc_clock_def])
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ conj_tac
  >-
    (spose_not_then assume_tac \\ rw []
    \\ fsrw_tac [QUANT_INST_ss[pair_default_qp]] []
    \\ last_assum (qspec_then `k` mp_tac)
    \\ (fn g => subterm (fn tm => Cases_on`^(assert (can dest_prod o type_of) tm)` g) (#2 g))
    \\ strip_tac
    \\ drule (GEN_ALL evaluate_compile_prog)
    \\ strip_tac
    \\ qmatch_assum_rename_tac `evaluate (_,[],_ k) = (_,rr)`
    \\ reverse (Cases_on `r`)
    >-
      (qpat_x_assum `evaluate _ = (Rerr _, _)` assume_tac
       \\ drule evaluate_add_clock
       \\ disch_then (qspec_then `ck` mp_tac)
       \\ impl_tac >- (every_case_tac >> fs[])
       \\ strip_tac \\ fs[inc_clock_def]
       \\ rveq \\ fs[]
       \\ first_x_assum (qspecl_then [`k`, `outcome`] mp_tac)
       \\ simp[])
    \\ qpat_x_assum `∀x y. ¬z` mp_tac \\ simp []
    \\ qexists_tac `k` \\ simp [] \\ fs[]
    \\ ntac 2 (reverse PURE_TOP_CASE_TAC \\ fs [])
    \\ qpat_x_assum `evaluate _ = (Rval _, _)` assume_tac
    \\ drule evaluate_add_clock
    \\ disch_then(qspec_then `ck` mp_tac)
    \\ impl_tac >- simp[]
    \\ simp[inc_clock_def])
  \\ strip_tac
  \\ qmatch_abbrev_tac `build_lprefix_lub l1 = build_lprefix_lub l2`
  \\ `(lprefix_chain l1 ∧ lprefix_chain l2) ∧ equiv_lprefix_chain l1 l2`
     suffices_by metis_tac [build_lprefix_lub_thm,
                            lprefix_lub_new_chain,
                            unique_lprefix_lub]
  \\ conj_asm1_tac
  >-
    (unabbrev_all_tac
    \\ conj_tac
    \\ Ho_Rewrite.ONCE_REWRITE_TAC [GSYM o_DEF]
    \\ REWRITE_TAC [IMAGE_COMPOSE]
    \\ match_mp_tac prefix_chain_lprefix_chain
    \\ simp [prefix_chain_def, PULL_EXISTS]
    \\ qx_genl_tac [`k1`,`k2`]
    \\ qspecl_then [`k1`,`k2`] mp_tac LESS_EQ_CASES
    \\ metis_tac [
         LESS_EQ_EXISTS,
         bvlPropsTheory.initial_state_with_simp,
         bvlPropsTheory.evaluate_add_to_clock_io_events_mono
           |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["s"]))
           |> Q.SPEC`s with clock := k`
           |> SIMP_RULE (srw_ss())[bvlPropsTheory.inc_clock_def]])
  \\ simp [equiv_lprefix_chain_thm]
  \\ unabbrev_all_tac \\ simp [PULL_EXISTS]
  \\ simp [LNTH_fromList, PULL_EXISTS, GSYM FORALL_AND_THM]
  \\ rpt gen_tac
  \\ Cases_on `(evaluate
         ([Call 0 (SOME start) []],[],
          initial_state ffi
            (map (I ## (λx. HD (remove_ticks [x]))) prog)
            (remove_ticks_co ∘ co) cc k))`
  \\ drule (GEN_ALL evaluate_compile_prog)
  \\ strip_tac \\ fs []
  \\ conj_tac \\ rw []
  >- (qexists_tac `ck + k`
      \\ fs [])
  \\ qexists_tac `k` \\ fs []
  \\ qmatch_assum_abbrev_tac `_ < (LENGTH (_ ffi1))`
  \\ `ffi1.io_events ≼ r.ffi.io_events` by
    (qunabbrev_tac `ffi1`
    \\ metis_tac [
       initial_state_with_simp, evaluate_add_to_clock_io_events_mono
         |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["s"]))
         |> Q.SPEC`s with clock := k`
         |> SIMP_RULE(srw_ss())[inc_clock_def],
       SND,ADD_SYM])
  \\ fs [IS_PREFIX_APPEND]
  \\ simp [EL_APPEND1]
QED

val remove_ticks_CONS = prove(
  ``!xs x. remove_ticks (x::xs) =
           HD (remove_ticks [x]) :: remove_ticks xs``,
  Cases \\ fs [remove_ticks_def]);

(* correctness of tick_inline *)

val (exp_rel_rules, exp_rel_ind, exp_rel_cases) = Hol_reln `
  (!cs v. exp_rel (cs: (num # bvl$exp) num_map) [bvl$Var v] [bvl$Var v]) /\
  (!cs. exp_rel cs [] []) /\
  (!cs x x1 xs y y1 ys.
     exp_rel cs [x] [y] /\
     exp_rel cs (x1::xs) (y1::ys) ==>
     exp_rel cs (x::x1::xs) (y::y1::ys)) /\
  (exp_rel cs [x1] [y1] /\
   exp_rel cs [x2] [y2] /\
   exp_rel cs [x3] [y3]==>
   exp_rel cs [If x1 x2 x3] [If y1 y2 y3]) /\
  (exp_rel cs xs ys /\
   exp_rel cs [x] [y] ==>
   exp_rel cs [Let xs x] [Let ys y]) /\
  (exp_rel cs [x1] [y1] /\
   exp_rel cs [x2] [y2] ==>
   exp_rel cs [Handle x1 x2] [Handle y1 y2]) /\
  (exp_rel cs [x] [y] ==>
   exp_rel cs [Raise x] [Raise y]) /\
  (exp_rel cs [x] [y] ==>
   exp_rel cs [Tick x] [Tick y]) /\
  (exp_rel cs xs ys ==>
   exp_rel cs [Op op xs] [Op op ys]) /\
  (exp_rel cs xs ys ==>
   exp_rel cs [Call ticks dest xs] [Call ticks dest ys]) /\
  (exp_rel cs xs ys /\ lookup n cs = SOME (arity, x) /\
   exp_rel cs [x] [y] ==>
   exp_rel cs [Call ticks (SOME n) xs]
              [Let ys (mk_tick (SUC ticks) y)])`;

val in_cc_def = Define `
  in_cc limit cc =
    (λ(cs,cfg) prog.
        let (cs1,prog1) = tick_compile_prog limit cs prog in
          case cc cfg prog1 of
          | NONE => NONE
          | SOME (code,data,cfg1) => SOME (code,data,(cs1,cfg1)))`

val in_state_rel_def = Define `
  in_state_rel limit s t <=>
    t.globals = s.globals ∧
    t.refs = s.refs ∧
    t.clock = s.clock ∧
    t.ffi = s.ffi ∧
    t.compile_oracle = (λn.
      let ((cs,cfg),progs) = s.compile_oracle n in
      let (cs1,progs) = tick_compile_prog limit cs progs in
        (cfg,progs)) ∧
    subspt (FST (FST (s.compile_oracle 0))) t.code /\
    s.compile = in_cc limit t.compile /\
    domain t.code = domain s.code /\
    (!k arity exp.
       lookup k s.code = SOME (arity,exp) ==>
       ?exp2. lookup k t.code = SOME (arity,exp2) /\
              exp_rel s.code [exp] [exp2])`;

Theorem subspt_exp_rel:
   !s1 s2 xs ys. subspt s1 s2 /\ exp_rel s1 xs ys ==> exp_rel s2 xs ys
Proof
  qsuff_tac `!s1 xs ys. exp_rel s1 xs ys ==> !s2. subspt s1 s2 ==> exp_rel s2 xs ys`
  THEN1 metis_tac []
  \\ ho_match_mp_tac exp_rel_ind \\ rw []
  \\ once_rewrite_tac [exp_rel_cases] \\ fs []
  \\ fs [subspt_def,domain_lookup,PULL_EXISTS]
  \\ res_tac \\ fs [] \\ metis_tac []
QED

val tick_inline_all_acc = prove(
  ``!limit cs t aux.
      tick_inline_all limit cs t aux =
        let (cs1,xs) = tick_inline_all limit cs t [] in
          (cs1, REVERSE aux ++ xs)``,
  Induct_on `t` \\ fs [tick_inline_all_def] \\ rpt strip_tac
  \\ PairCases_on `h` \\ simp_tac std_ss  [tick_inline_all_def]
  \\ pop_assum (fn th => once_rewrite_tac [th])
  \\ fs [] \\ pairarg_tac \\ fs []);

Theorem tick_inline_all_names:
   !limit cs t aux cs1 xs aux.
     tick_inline_all limit cs t aux = (cs1,xs) ==>
     MAP FST (REVERSE aux) ++ MAP FST t = MAP FST xs
Proof
  Induct_on `t` \\ fs [tick_inline_all_def,FORALL_PROD]
  \\ once_rewrite_tac [tick_inline_all_acc] \\ fs []
  \\ rpt strip_tac
  \\ pairarg_tac \\ fs [] \\ rveq \\ fs []
  \\ res_tac \\ fs[]
QED

val tick_compile_prog_IMP = prove(
  ``tick_compile_prog limit q0 ((k,prog)::t) = (cs1,prog1) ==>
    ?p1 vs. prog1 = (k,p1)::vs /\ MAP FST vs = MAP FST t``,
  Cases_on `prog` \\ strip_tac \\ fs [tick_compile_prog_def]
  \\ imp_res_tac tick_inline_all_names \\ fs []
  \\ Cases_on `prog1` \\ fs []
  \\ Cases_on `h` \\ fs []);

val subspt_union_lemma = prove(
  ``(!x. lookup x t1 = lookup x t2) ==>
    subspt x (union c t1) ==> subspt x (union c t2)``,
  fs [subspt_def,domain_union,lookup_union,domain_lookup]);

val tick_inline_all_domain = prove(
  ``!limit cs0 in1 cs1 xs.
      tick_inline_all limit cs0 in1 [] = (cs1,xs) ==>
      domain cs1 SUBSET domain cs0 UNION set (MAP FST xs)``,
  Induct_on `in1`
  \\ fs [tick_inline_all_def,FORALL_PROD] \\ rw []
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [tick_inline_all_acc]
  \\ fs [] \\ pairarg_tac \\ fs [] \\ rw []
  \\ res_tac \\ fs [MAP,SUBSET_DEF] \\ metis_tac []);

Theorem tick_compile_prog_res_range:
   !in1 limit in2 c cs0 cs1.
      tick_compile_prog limit cs0 in1 = (cs1,in2) /\
      ALL_DISTINCT (MAP FST in1) /\
      subspt cs0 c /\ domain c INTER set (MAP FST in1) = EMPTY ==>
      subspt cs1 (union c (fromAList in2))
Proof
  Induct \\ fs [tick_compile_prog_def]
  THEN1 (fs [tick_inline_all_def,fromAList_def])
  \\ fs [FORALL_PROD]
  \\ fs [tick_inline_all_def,fromAList_def]
  \\ rw []
  THEN1
   (qpat_x_assum `_ = (_,_)` mp_tac
    \\ once_rewrite_tac [tick_inline_all_acc]
    \\ fs [] \\ pairarg_tac \\ fs [] \\ rw [] \\ fs []
    \\ first_x_assum drule
    \\ disch_then (qspec_then `union c
          (insert p_1 (p_1',HD (tick_inline cs0 [p_2])) LN)` mp_tac)
    \\ impl_tac
    THEN1
     (fs [domain_union,EXTENSION]
      \\ reverse conj_tac THEN1 metis_tac []
      \\ fs [subspt_lookup,lookup_insert] \\ rw []
      \\ fs [lookup_union,lookup_insert,lookup_def,case_eq_thms]
      \\ metis_tac [lookup_NONE_domain])
    \\ fs [GSYM union_assoc]
    \\ match_mp_tac subspt_union_lemma
    \\ fs [lookup_union,lookup_insert,lookup_def,fromAList_def]
    \\ fs [case_eq_thms] \\ metis_tac [])
  \\ qpat_x_assum `_ = (_,_)` mp_tac
  \\ once_rewrite_tac [tick_inline_all_acc]
  \\ fs [] \\ pairarg_tac \\ fs [] \\ rw [] \\ fs []
  \\ first_x_assum drule
  \\ disch_then drule \\ fs []
  \\ impl_tac THEN1 (fs [EXTENSION] \\ metis_tac [])
  \\ imp_res_tac tick_inline_all_names \\ fs []
  \\ Cases_on `p_1 IN domain cs1`
  THEN1
   (sg `F` \\ fs []
    \\ imp_res_tac tick_inline_all_domain
    \\ fs [SUBSET_DEF] \\ res_tac
    \\ imp_res_tac subspt_domain_SUBSET
    \\ fs [EXTENSION,SUBSET_DEF] \\ metis_tac [])
  \\ fs [subspt_lookup]
  \\ fs [lookup_union,fromAList_def,lookup_insert]
  \\ rw [] \\ fs[domain_lookup]
  \\ rw [] \\ fs []
QED

val exp_rel_swap_lemma = prove(
  ``!x1 x2 x3. exp_rel x1 x2 x3 ==>
      !y1. (!k. lookup k x1 = lookup k y1) ==> exp_rel y1 x2 x3``,
  ho_match_mp_tac exp_rel_ind \\ rw []
  \\ once_rewrite_tac [exp_rel_cases] \\ fs []
  \\ res_tac \\ metis_tac []);

Theorem exp_rel_swap:
   !x1 x2 x3 y1.
      (!k. lookup k x1 = lookup k y1) ==> exp_rel x1 x2 x3 = exp_rel y1 x2 x3
Proof
  metis_tac [exp_rel_swap_lemma]
QED

val exp_rel_rw = prove(
  ``exp_rel (union (union src_code (insert p1 (p2,p3) LN)) (fromAList in1))
      [exp] [exp2] <=>
    exp_rel (union src_code (fromAList ((p1,p2,p3)::in1))) [exp] [exp2]``,
  match_mp_tac exp_rel_swap
  \\ fs [lookup_union,lookup_insert,fromAList_def,case_eq_thms,lookup_def]
  \\ Cases_on `lookup k src_code` \\ fs []
  \\ CCONTR_TAC \\ fs []);

Theorem exp_rel_tick_inline:
   !cs0 xs.
      (∀k arity v.
        lookup k cs0 = SOME (arity,v) ⇒
        ∃exp.
          lookup k src_code = SOME (arity,exp) ∧
          exp_rel src_code [exp] [v]) ==>
      exp_rel src_code xs (tick_inline cs0 xs)
Proof
  ho_match_mp_tac tick_inline_ind \\ fs [tick_inline_def] \\ rw []
  \\ once_rewrite_tac [exp_rel_cases] \\ fs []
  THEN1
   (sg `?y1 ys. tick_inline cs0 (y::xs) = y1::ys` \\ fs []
    \\ `LENGTH (tick_inline cs0 (y::xs)) = LENGTH (y::xs)` by
          rewrite_tac [LENGTH_tick_inline]
    \\ Cases_on `tick_inline cs0 (y::xs)` \\ fs [])
  \\ Cases_on `dest` \\ fs [] \\ fs [case_eq_thms]
  \\ Cases_on `lookup x cs0` \\ fs []
  \\ rename1 `_ = SOME aa` \\ PairCases_on `aa`
  \\ res_tac \\ fs []
  \\ qexists_tac `aa1` \\ fs []
QED

val tick_compile_prog_IMP_exp_rel = prove(
  ``!limit cs0 in1 cs1 in2 k arity exp src_code.
      tick_compile_prog limit cs0 in1 = (cs1,in2) /\
      ALOOKUP in1 k = SOME (arity,exp) /\
      ALL_DISTINCT (MAP FST in1) /\
      (!k arity v.
         lookup k cs0 = SOME (arity,v) ==>
         ?exp. lookup k src_code = SOME (arity,exp) /\
               exp_rel src_code [exp] [v]) /\
      DISJOINT (domain src_code) (set (MAP FST in1)) /\
      DISJOINT (domain cs0) (set (MAP FST in1)) ==>
      ∃exp2.
        ALOOKUP in2 k = SOME (arity,exp2) /\
        exp_rel (union src_code (fromAList in1)) [exp] [exp2]``,
  Induct_on `in1`
  \\ fs [FORALL_PROD,tick_compile_prog_def,tick_inline_all_def]
  \\ once_rewrite_tac [tick_inline_all_acc]
  \\ fs [] \\ rpt gen_tac
  \\ pairarg_tac \\ fs [] \\ strip_tac \\ rveq
  \\ fs [] \\ rw [] \\ fs []
  THEN1
   (match_mp_tac subspt_exp_rel
    \\ qexists_tac `src_code`
    \\ conj_tac THEN1 fs [subspt_lookup,lookup_union]
    \\ match_mp_tac exp_rel_tick_inline \\ metis_tac [])
  \\ first_x_assum drule
  \\ disch_then (qspec_then `k` mp_tac) \\ fs []
  \\ qmatch_goalsub_rename_tac `(p1,p2,p3)::in1`
  \\ disch_then (qspec_then `union src_code (insert p1 (p2,p3) LN)` mp_tac)
  \\ fs [exp_rel_rw] \\ disch_then match_mp_tac
  \\ reverse (IF_CASES_TAC \\ fs [])
  THEN1
   (fs [DISJOINT_DEF,EXTENSION,domain_union] \\ rw []
    \\ fs [lookup_union,lookup_insert,lookup_def,case_eq_thms]
    THEN1
     (first_x_assum drule \\ strip_tac \\ fs []
      \\ match_mp_tac (subspt_exp_rel |> ONCE_REWRITE_RULE [CONJ_COMM])
      \\ asm_exists_tac \\ fs []
      \\ fs [subspt_lookup,lookup_union])
    \\ CCONTR_TAC \\ fs [] \\ metis_tac [])
  \\ reverse (rw [])
  THEN1 (fs [DISJOINT_DEF,domain_union,EXTENSION] \\ metis_tac [])
  \\ fs [lookup_insert,case_eq_thms] \\ rveq
  THEN1
   (rename1 `must_inline k2 _ _`
    \\ fs [lookup_union,case_eq_thms,GSYM lookup_NONE_domain]
    \\ match_mp_tac subspt_exp_rel
    \\ qexists_tac `src_code`
    \\ conj_tac THEN1 fs [subspt_lookup,lookup_union]
    \\ match_mp_tac exp_rel_tick_inline \\ metis_tac [])
  \\ fs [lookup_union,case_eq_thms,GSYM lookup_NONE_domain,lookup_insert,lookup_def]
  \\ pop_assum (assume_tac o GSYM)
  \\ first_x_assum drule \\ strip_tac \\ fs []
  \\ match_mp_tac (subspt_exp_rel |> ONCE_REWRITE_RULE [CONJ_COMM])
  \\ asm_exists_tac \\ fs []
  \\ fs [subspt_lookup,lookup_union]);

val in_do_app_lemma = prove(
  ``in_state_rel limit s1 t1 ==>
    case do_app op a s1 of
    | Rerr err => (err <> Rabort Rtype_error ==> do_app op a t1 = Rerr err)
    | Rval (v,s2) => ?t2. in_state_rel limit s2 t2 /\
                          do_app op a t1 = Rval (v,t2)``,
  Cases_on `op = Install`
  THEN1
   (rw [] \\ fs [do_app_def]
    \\ every_case_tac \\ fs []
    \\ fs [case_eq_thms,UNCURRY,do_install_def]
    \\ rveq \\ fs [PULL_EXISTS]
    \\ fs [SWAP_REVERSE_SYM] \\ rveq \\ fs []
    \\ fs [state_rel_def] \\ rveq \\ fs []
    \\ fs [state_component_equality,in_state_rel_def]
    \\ fs [shift_seq_def,o_DEF] \\ rfs []
    \\ Cases_on `s1.compile_oracle 0` \\ fs []
    \\ Cases_on `r` \\ fs [] \\ Cases_on `h` \\ fs [] \\ rveq \\ fs []
    \\ PairCases_on `q` \\ fs [domain_union]
    \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
    \\ fs [domain_fromAList,in_cc_def]
    \\ pairarg_tac \\ fs [case_eq_thms] \\ rveq \\ fs []
    \\ qpat_x_assum `_ = FST _` (assume_tac o GSYM) \\ fs []
    \\ drule tick_compile_prog_IMP \\ strip_tac \\ fs []
    \\ rveq \\ fs []
    \\ qpat_abbrev_tac `in1 = (k,prog)::t`
    \\ qpat_abbrev_tac `in2 = (k,p1)::vs`
    \\ fs [lookup_union,case_eq_thms]
    \\ reverse (rw [])
    THEN1
     (first_x_assum drule \\ strip_tac \\ fs []
      \\ match_mp_tac subspt_exp_rel \\ metis_tac [subspt_union])
    THEN1
     (reverse (Cases_on `lookup k' t1.code`) \\ fs []
      THEN1 (fs [domain_lookup,EXTENSION] \\ metis_tac [NOT_SOME_NONE])
      \\ fs [lookup_fromAList]
      \\ `DISJOINT (domain q0) (set (MAP FST in1))` by
       (fs [subspt_def,EXTENSION,DISJOINT_DEF,Abbr`in1`] \\ metis_tac [])
      \\ `ALL_DISTINCT (MAP FST in1)` by fs [Abbr `in1`]
      \\ match_mp_tac tick_compile_prog_IMP_exp_rel
      \\ asm_exists_tac \\ fs []
      \\ reverse conj_tac
      THEN1 (unabbrev_all_tac \\ fs [DISJOINT_DEF,EXTENSION] \\ metis_tac [])
      \\ rw [] \\ fs [subspt_lookup]
      \\ first_x_assum drule \\ strip_tac
      \\ rename1 `lookup k2 t1.code = SOME (arity2,v)`
      \\ Cases_on `lookup k2 s1.code`
      THEN1 (fs [domain_eq] \\ res_tac \\ fs [])
      \\ PairCases_on `x` \\ res_tac \\ fs []
      \\ rveq \\ fs [])
    \\ drule (tick_compile_prog_res_range |> SIMP_RULE std_ss [])
    \\ disch_then match_mp_tac \\ fs []
    \\ unabbrev_all_tac \\ fs []
    \\ CCONTR_TAC \\ fs [EXTENSION] \\ rveq \\ fs []
    \\ fs [subspt_def] \\ res_tac
    \\ fs [DISJOINT_DEF,EXTENSION]
    \\ metis_tac [])
  \\ strip_tac \\ reverse (Cases_on `do_app op a s1`) \\ fs []
  \\ `t1 = t1 with <| globals := s1.globals ;
                               refs := s1.refs ;
                               clock := s1.clock ;
                               ffi := s1.ffi |>` by
         fs [in_state_rel_def,state_component_equality]
  \\ pop_assum (fn th => once_rewrite_tac [th])
  THEN1 (strip_tac \\ match_mp_tac do_app_Rerr_swap \\ fs [in_state_rel_def])
  \\ rename1 `_ = Rval x`
  \\ PairCases_on `x` \\ fs []
  \\ drule (do_app_Rval_swap |> GEN_ALL
      |> INST_TYPE [alpha|->gamma,beta|->delta,gamma|->alpha,delta|->beta])
  \\ fs []
  \\ disch_then (qspec_then `t1` mp_tac)
  \\ impl_tac THEN1 fs [in_state_rel_def]
  \\ fs [] \\ disch_then kall_tac
  \\ fs [in_state_rel_def]
  \\ imp_res_tac do_app_const \\ fs []);

Theorem evaluate_inline:
   !es env s1 res t1 s2 es2.
      in_state_rel limit s1 t1 /\ exp_rel s1.code es es2 /\
      evaluate (es,env,s1) = (res,s2) /\ res ≠ Rerr (Rabort Rtype_error) ==>
      ?t2. evaluate (es2,env,t1) = (res,t2) /\
           in_state_rel limit s2 t2
Proof
  recInduct evaluate_ind \\ rw [] \\ fs []
  \\ fs [evaluate_def] \\ rveq \\ fs []
  \\ qpat_x_assum `exp_rel _ _ _` mp_tac
  \\ once_rewrite_tac [exp_rel_cases] \\ fs [] \\ rw []
  THEN1
   (fs [evaluate_def])
  THEN1
   (fs [case_eq_thms] \\ rveq \\ fs []
    \\ first_x_assum drule
    \\ disch_then drule \\ strip_tac
    \\ fs [evaluate_def]
    \\ first_x_assum drule
    \\ imp_res_tac evaluate_mono
    \\ drule subspt_exp_rel \\ disch_then drule \\ rw []
    \\ pop_assum drule \\ rw [] \\ fs [])
  THEN1
   (fs [evaluate_def] \\ rw [] \\ fs [])
  THEN1
   (fs [case_eq_thms] \\ rveq \\ fs []
    \\ rpt (qpat_x_assum `_ = bvlSem$evaluate _` (assume_tac o GSYM)) \\ fs []
    \\ first_x_assum drule
    \\ disch_then drule \\ strip_tac
    \\ fs [evaluate_def]
    \\ first_x_assum drule
    \\ imp_res_tac evaluate_mono
    \\ imp_res_tac subspt_exp_rel
    \\ metis_tac [])
  THEN1
   (fs [case_eq_thms] \\ rveq \\ fs []
    \\ first_x_assum drule
    \\ disch_then drule \\ strip_tac
    \\ fs [evaluate_def]
    \\ first_x_assum drule
    \\ imp_res_tac evaluate_mono
    \\ drule subspt_exp_rel \\ disch_then drule \\ rw []
    \\ pop_assum drule \\ rw [] \\ fs [])
  THEN1
   (fs [case_eq_thms] \\ rveq \\ fs []
    \\ first_x_assum drule
    \\ disch_then drule \\ strip_tac
    \\ fs [evaluate_def])
  THEN1
   (fs [case_eq_thms] \\ rveq \\ fs []
    \\ first_x_assum drule
    \\ disch_then drule \\ strip_tac
    \\ fs [evaluate_def]
    \\ first_x_assum drule
    \\ imp_res_tac evaluate_mono
    \\ drule subspt_exp_rel \\ disch_then drule \\ rw []
    \\ pop_assum drule \\ rw [] \\ fs [])
  THEN1
   (fs [case_eq_thms] \\ rveq \\ fs []
    \\ first_x_assum drule
    \\ disch_then drule \\ strip_tac
    \\ fs [evaluate_def]
    \\ drule (Q.GEN `a` in_do_app_lemma)
    \\ disch_then (qspec_then `REVERSE vs` mp_tac) \\ fs []
    \\ strip_tac \\ fs [])
  THEN1
   (`s.clock = t1.clock` by fs [in_state_rel_def]
    \\ fs [case_eq_thms] \\ rveq
    \\ fs [evaluate_def]
    \\ rpt (qpat_x_assum `_ = bvlSem$evaluate _` (assume_tac o GSYM)) \\ fs []
    \\ `in_state_rel limit (dec_clock 1 s) (dec_clock 1 t1)`
          by fs [in_state_rel_def,dec_clock_def]
    \\ first_x_assum drule
    \\ disch_then drule \\ strip_tac
    \\ fs [evaluate_def])
  THEN1
   (reverse (fs [case_eq_thms] \\ rveq \\ fs [])
    \\ first_x_assum drule
    \\ disch_then drule \\ strip_tac
    \\ fs [evaluate_def]
    \\ rename1`_ = SOME (_,exp)`
    \\ rpt (qpat_x_assum `_ = bvlSem$evaluate _` (assume_tac o GSYM)) \\ fs []
    \\ `?exp2. find_code dest vs t2.code = SOME (args,exp2) /\
               exp_rel s.code [exp] [exp2]` by
     (Cases_on `dest` \\ fs [find_code_def,case_eq_thms]
      \\ fs [in_state_rel_def] \\ rveq
      \\ qpat_x_assum `!x._` drule
      \\ rw [] \\ fs [])
    \\ `s.clock = t2.clock` by fs [in_state_rel_def] \\ fs []
    \\ TRY (fs [in_state_rel_def] \\ NO_TAC)
    \\ `in_state_rel limit (dec_clock (ticks + 1) s) (dec_clock (ticks + 1) t2)`
              by fs [in_state_rel_def,dec_clock_def]
    \\ first_x_assum drule
    \\ disch_then match_mp_tac \\ fs [])
  \\ reverse (fs [case_eq_thms] \\ rveq \\ fs [])
  \\ first_x_assum drule
  \\ disch_then drule \\ strip_tac
  \\ `t2.clock = s.clock` by fs [in_state_rel_def]
  \\ fs [evaluate_def,evaluate_mk_tick]
  \\ rename1`find_code _ _ _ = SOME (_,exp)`
  \\ TRY (fs [in_state_rel_def] \\ NO_TAC)
  \\ fs [find_code_def,case_eq_thms] \\ rveq
  \\ `in_state_rel limit (dec_clock (ticks + 1) s) (dec_clock (ticks + 1) t2)`
              by fs [in_state_rel_def,dec_clock_def]
  \\ first_x_assum drule
  \\ imp_res_tac evaluate_mono
  \\ `lookup n s.code = lookup n s1.code` by fs [subspt_def,domain_lookup]
  \\ fs [] \\ rveq
  \\ `exp_rel s.code [exp] [y]` by imp_res_tac subspt_exp_rel
  \\ disch_then drule
  \\ rpt (qpat_x_assum `_ = bvlSem$evaluate _` (assume_tac o GSYM)) \\ fs []
  \\ strip_tac \\ fs [ADD1]
  \\ `FST (evaluate ([y],args,dec_clock (ticks + 1) t2)) <>
      Rerr (Rabort Rtype_error)` by fs []
  \\ drule evaluate_expand_env \\ fs []
QED

Theorem exp_rel_refl:
   !cs xs. exp_rel cs xs xs
Proof
  ho_match_mp_tac tick_inline_ind \\ rw []
  \\ once_rewrite_tac [exp_rel_cases] \\ fs []
  \\ Cases_on `dest` \\ fs []
  \\ Cases_on `lookup x cs` \\ fs []
  \\ Cases_on `x'` \\ fs []
QED

val in_co_def = Define `
  in_co limit co = (λn.
      (let
         ((cs,cfg),progs) = co n ;
         (cs1,progs) = tick_compile_prog limit cs progs
       in
         (cfg,progs)))`;

Theorem MAP_FST_tick_inline_all:
   !limit cs prog.
      MAP FST (SND (tick_inline_all limit cs prog [])) = MAP FST prog
Proof
  rw[] \\ Cases_on `tick_inline_all limit cs prog []`
  \\ imp_res_tac tick_inline_all_names \\ fs []
QED

val exp_rel_rw = prove(
  ``~MEM x (MAP FST prog) ==>
    exp_rel (union (insert x y (fromAList prog)) acc) [exp] [exp2] =
    exp_rel (union (fromAList prog) (insert x y acc)) [exp] [exp2]``,
  strip_tac
  \\ match_mp_tac exp_rel_swap
  \\ fs [lookup_union,lookup_insert,lookup_fromAList] \\ strip_tac
  \\ IF_CASES_TAC \\ fs []
  \\ every_case_tac \\ fs []
  \\ imp_res_tac ALOOKUP_MEM
  \\ fs [MEM_MAP,FORALL_PROD] \\ rfs []
  \\ Cases_on `x'` \\ rfs []);

val lookup_tick_inline_all = prove(
  ``!cs0 prog acc.
      (∀k arity v.
          lookup k cs0 = SOME (arity,v) ⇒
          ∃exp.
            lookup k (union (fromAList prog) acc) = SOME (arity,exp) ∧
            exp_rel (union (fromAList prog) acc) [exp] [v]) /\
      DISJOINT (set (MAP FST prog)) (domain cs0) /\
      DISJOINT (set (MAP FST prog)) (domain acc) /\
      ALL_DISTINCT (MAP FST prog) ==>
      ∀k arity exp.
        lookup k (fromAList prog) = SOME (arity,exp) ⇒
        ∃exp2.
          lookup k (fromAList (SND (tick_inline_all limit cs0 prog []))) =
          SOME (arity,exp2) ∧ exp_rel (union (fromAList prog) acc) [exp] [exp2]``,
  Induct_on `prog` THEN1 (fs [fromAList_def,lookup_def])
  \\ fs [FORALL_PROD] \\ rw []
  \\ qmatch_goalsub_rename_tac `(p1,p2,p3)::_`
  \\ fs [tick_inline_all_def]
  \\ once_rewrite_tac [tick_inline_all_acc] \\ fs [UNCURRY]
  \\ fs [fromAList_def,lookup_insert]
  \\ IF_CASES_TAC \\ rw []
  THEN1 (match_mp_tac exp_rel_tick_inline
         \\ fs [lookup_insert,lookup_union]
         \\ rw [] \\ fs [GSYM lookup_NONE_domain]
         \\ first_x_assum drule \\ fs [] \\ strip_tac \\ fs [])
  \\ fs [] \\ rveq
  \\ qmatch_goalsub_abbrev_tac `tick_inline_all _ cs1`
  \\ qpat_x_assum `!x cs. _ ==> _` (qspec_then `cs1` mp_tac)
  \\ disch_then (qspec_then `insert p1 (p2,p3) acc` mp_tac)
  \\ fs [PULL_FORALL,AND_IMP_INTRO]
  \\ disch_then (qspec_then `k` mp_tac) \\ fs [GSYM PULL_FORALL]
  \\ simp [exp_rel_rw]
  \\ disch_then match_mp_tac \\ fs []
  THEN1
   (unabbrev_all_tac \\ fs [lookup_insert] \\ rw []
    THEN1
     (fs [lookup_union,lookup_insert,lookup_fromAList]
      \\ reverse CASE_TAC \\ fs []
      THEN1 (Cases_on `x`
        \\ imp_res_tac ALOOKUP_MEM \\ fs [MEM_MAP,FORALL_PROD] \\ rfs [])
      \\ match_mp_tac exp_rel_tick_inline
      \\ rw [] \\ first_x_assum drule
      \\ IF_CASES_TAC THEN1 fs [GSYM lookup_NONE_domain]
      \\ fs [case_eq_thms] \\ strip_tac
      \\ fs [lookup_union,lookup_insert,lookup_fromAList]
      \\ rfs [exp_rel_rw])
    \\ rpt strip_tac \\ first_x_assum drule
    \\ fs [lookup_union,lookup_insert]
    \\ fs [GSYM lookup_NONE_domain] \\ fs [exp_rel_rw])
  \\ rpt strip_tac \\ first_x_assum drule
  \\ fs [lookup_union,lookup_insert]
  \\ IF_CASES_TAC \\ fs [GSYM lookup_NONE_domain] \\ fs [exp_rel_rw]);

val subspt_tick_inline = prove(
  ``!prog cs aux.
      subspt cs (fromAList (REVERSE aux)) /\
      EVERY (\x. ~(FST x IN domain cs)) prog /\
      ALL_DISTINCT (MAP FST prog ++ MAP FST aux) ==>
      subspt (FST (tick_inline_all limit cs prog aux))
             (fromAList (SND (tick_inline_all limit cs prog aux)))``,
  Induct \\ fs [tick_inline_all_def,FORALL_PROD] \\ rw []
  \\ first_x_assum match_mp_tac
  \\ fs [subspt_lookup,lookup_insert] \\ rw []
  \\ fs [ALL_DISTINCT_APPEND]
  \\ res_tac \\ fs []
  \\ fs [lookup_fromAList,ALOOKUP_APPEND]
  \\ fs [case_eq_thms,ALOOKUP_NONE,MAP_REVERSE]
  \\ fs [EVERY_MEM,MEM_MAP] \\ rw [] \\ res_tac \\ metis_tac [])

val evaluate_initial_state = prove(
  ``evaluate
     ([Call 0 (SOME start) []],env,
      initial_state ffi0 (fromAList prog) co cc k) = (res,s2) ∧
    in_co limit co = co1 /\ in_cc limit cc1 = cc /\
    FST (FST (co 0)) = FST (tick_compile_prog limit LN prog) /\
    ALL_DISTINCT (MAP FST prog) /\
    res ≠ Rerr (Rabort Rtype_error) ⇒
    ∃t2.
      evaluate
        ([Call 0 (SOME start) []],env,
         initial_state ffi0
          (fromAList (SND (tick_compile_prog limit LN prog))) co1 cc1 k) =
        (res,t2) ∧ in_state_rel limit s2 t2``,
  strip_tac
  \\ match_mp_tac evaluate_inline
  \\ qexists_tac `[Call 0 (SOME start) []]`
  \\ qexists_tac `initial_state ffi0 (fromAList prog) co cc k`
  \\ fs [exp_rel_refl]
  \\ fs [in_state_rel_def,initial_state_def,GSYM in_co_def]
  \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs []
  \\ fs [tick_compile_prog_def,domain_fromAList,MAP_FST_tick_inline_all]
  \\ conj_tac
  THEN1 (match_mp_tac subspt_tick_inline \\ fs [])
  \\ match_mp_tac (lookup_tick_inline_all
       |> Q.SPECL [`LN`,`prog`,`LN`] |> SIMP_RULE (srw_ss()) [lookup_def])
  \\ fs []) |> GEN_ALL |> SIMP_RULE std_ss [];

val in_evaluate_Call = prove(
  ``evaluate
     ([Call 0 (SOME start) []],env,
      initial_state ffi0 (fromAList prog) co (in_cc limit cc1) k) = (res,s2) ∧
    FST (FST (co 0)) = FST (tick_compile_prog limit LN prog) /\
    ALL_DISTINCT (MAP FST prog) /\
    res ≠ Rerr (Rabort Rtype_error) ⇒
    ∃t2.
      evaluate
        ([Call 0 (SOME start) []],env,
         initial_state ffi0
          (fromAList (SND (tick_compile_prog limit LN prog)))
            (in_co limit co) cc1 k) =
        (res,t2) ∧ s2.ffi = t2.ffi``,
  metis_tac [evaluate_initial_state,in_state_rel_def]);

val semantics_tick_inline = prove(
  ``FST (FST (co 0)) = FST (tick_compile_prog limit LN prog) /\
    ALL_DISTINCT (MAP FST prog) ==>
    semantics ffi (fromAList prog) co (in_cc limit cc) start <> Fail ==>
    semantics ffi (fromAList (SND (tick_compile_prog limit LN prog)))
                  (in_co limit co) cc start =
    semantics (ffi:'b ffi_state) (fromAList prog) co (in_cc limit cc) start``,
  strip_tac
  \\ simp [Once semantics_def]
  \\ simp [Once semantics_def, SimpRHS]
  \\ IF_CASES_TAC \\ fs []
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ conj_tac
  >-
   (gen_tac \\ strip_tac \\ rveq \\ simp []
    \\ simp [semantics_def]
    \\ IF_CASES_TAC \\ fs []
    >-
     (first_assum (subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) o concl)
      \\ drule evaluate_add_clock
      \\ disch_then (qspec_then `k` mp_tac)
      \\ impl_tac >- fs []
      \\ strip_tac
      \\ qpat_x_assum `evaluate (_,_,_ _ (_ prog) _ _ _) = _` kall_tac
      \\ last_assum (qspec_then `k'` mp_tac)
      \\ (fn g => subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) (#2 g) g )
      \\ rw [] \\ fs [] \\ rveq
      \\ CCONTR_TAC
      \\ drule (GEN_ALL in_evaluate_Call) \\ simp [])
    \\ DEEP_INTRO_TAC some_intro \\ simp []
    \\ conj_tac
    >-
     (gen_tac \\ strip_tac \\ rveq \\ fs []
      \\ qabbrev_tac `opts = (fromAList (SND (tick_compile_prog limit LN prog)))`
      \\ qmatch_assum_abbrev_tac `bvlSem$evaluate (opts1,[],sopt1) = _`
      \\ qmatch_assum_abbrev_tac `bvlSem$evaluate (exps1,[],st1) = (r,s)`
      \\ qspecl_then [`opts1`,`[]`,`sopt1`] mp_tac
          evaluate_add_to_clock_io_events_mono
      \\ qspecl_then [`exps1`,`[]`,`st1`] mp_tac
          (evaluate_add_to_clock_io_events_mono
           |> INST_TYPE [alpha|->``:(num # bvl$exp) num_map # 'a``])
      \\ simp [inc_clock_def, Abbr`sopt1`, Abbr`st1`]
      \\ ntac 2 strip_tac
      \\ Cases_on `r` \\ fs []
      >-
       (Cases_on `r'` \\ fs []
        >-
         (unabbrev_all_tac
          \\ drule (GEN_ALL in_evaluate_Call) \\ simp []
          \\ strip_tac
          \\ drule evaluate_add_clock
          \\ disch_then (qspec_then `k'` mp_tac)
          \\ impl_tac
          >- (every_case_tac \\ fs [])
          \\ rveq
          \\ simp [inc_clock_def]
          \\ qpat_x_assum `evaluate _ = _` kall_tac
          \\ drule evaluate_add_clock
          \\ disch_then (qspec_then `k` mp_tac)
          \\ impl_tac
          >- (spose_not_then strip_assume_tac \\ fs [evaluate_def])
          \\ simp [inc_clock_def]
          \\ ntac 2 strip_tac \\ rveq \\ fs []
          \\ fs [state_component_equality] \\ rfs [] \\ rfs [])
        \\ qpat_x_assum `∀extra._` mp_tac
        \\ first_x_assum (qspec_then `k'` assume_tac)
        \\ first_assum (subterm
             (fn tm => Cases_on`^(assert has_pair_type tm)`) o concl)
        \\ strip_tac \\ fs []
        \\ unabbrev_all_tac
        \\ drule (GEN_ALL in_evaluate_Call)
        \\ impl_tac
        >- (last_x_assum (qspec_then `k+k'` mp_tac) \\ fs [])
        \\ strip_tac
        \\ qhdtm_x_assum `evaluate` mp_tac
        \\ imp_res_tac evaluate_add_clock
        \\ pop_assum mp_tac
        \\ ntac 2 (pop_assum kall_tac)
        \\ impl_tac
        >- (strip_tac \\ fs [])
        \\ disch_then (qspec_then `k'` mp_tac) \\ simp [inc_clock_def]
        \\ first_x_assum (qspec_then `k` mp_tac) \\ fs []
        \\ ntac 3 strip_tac
        \\ fs [] \\ rveq
        \\ qpat_x_assum `evaluate _ = (Rerr _,_)` assume_tac
        \\ drule evaluate_add_clock
        \\ disch_then (qspec_then `k` mp_tac)
        \\ rpt(PURE_FULL_CASE_TAC >> fs[inc_clock_def]))
      \\ qpat_x_assum `∀extra._` mp_tac
      \\ first_x_assum (qspec_then `k'` assume_tac)
      \\ first_assum (subterm (fn tm =>
            Cases_on`^(assert has_pair_type tm)`) o concl)
      \\ fs []
      \\ unabbrev_all_tac
      \\ strip_tac
      \\ drule (GEN_ALL in_evaluate_Call)
      \\ impl_tac
      >- (last_x_assum (qspec_then `k+k'` mp_tac) \\ fs [])
      \\ strip_tac \\ rveq \\ fs []
      \\ reverse (Cases_on `r'`) \\ fs [] \\ rfs []
      >-
       (qpat_x_assum `evaluate _ = (Rerr e', _)` assume_tac
        \\ drule evaluate_add_clock
        \\ disch_then (qspec_then `k` assume_tac)
        \\ qpat_x_assum `evaluate _ = (Rerr e, _)` assume_tac
        \\ drule evaluate_add_clock
        \\ disch_then (qspec_then `k'` assume_tac)
        \\ rpt(PURE_FULL_CASE_TAC \\ fs[inc_clock_def] \\ rveq)
        \\ fs[])
      \\ qhdtm_x_assum `evaluate` mp_tac
      \\ imp_res_tac evaluate_add_clock
      \\ pop_assum kall_tac
      \\ pop_assum mp_tac
      \\ impl_tac
      >- (strip_tac \\ fs [])
      \\ disch_then (qspec_then `k` mp_tac)
      \\ simp [inc_clock_def]
      \\ rpt strip_tac \\ rveq
      \\ CCONTR_TAC \\ fs []
      \\ rveq \\ fs [] \\ rfs []
      \\ rpt(PURE_FULL_CASE_TAC \\ fs[] \\ rveq)
      \\ qpat_x_assum `evaluate _ = (Rerr _, _)` assume_tac
      \\ drule evaluate_add_clock
      \\ disch_then(qspec_then `k'` mp_tac)
      \\ simp[inc_clock_def])
    \\ qmatch_assum_abbrev_tac `bvlSem$evaluate (exps2,[],st2) = _`
    \\ qspecl_then [`exps2`,`[]`,`st2`] mp_tac
          (evaluate_add_to_clock_io_events_mono
           |> INST_TYPE [alpha|->``:(num # bvl$exp) num_map # 'a``])
    \\ simp [inc_clock_def, Abbr`st2`]
    \\ disch_then (qspec_then `0` strip_assume_tac)
    \\ first_assum (subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) o concl)
    \\ unabbrev_all_tac
    \\ drule (GEN_ALL in_evaluate_Call)
    \\ impl_tac
    >- (last_x_assum (qspec_then `k` mp_tac) \\ fs [])
    \\ strip_tac
    \\ asm_exists_tac \\ fs []
    \\ every_case_tac \\ fs [] \\ rveq \\ fs [])
  \\ strip_tac
  \\ simp [semantics_def]
  \\ IF_CASES_TAC \\ fs []
  >-
    (last_x_assum (qspec_then `k` assume_tac) \\ rfs []
    \\ first_assum (qspec_then `e` assume_tac)
    \\ fs [] \\ rfs []
    \\ qmatch_assum_abbrev_tac `FST q ≠ _`
    \\ Cases_on `q` \\ fs [markerTheory.Abbrev_def]
    \\ pop_assum (assume_tac o SYM)
    \\ drule (GEN_ALL in_evaluate_Call)
    \\ simp []
    \\ spose_not_then strip_assume_tac
    \\ qmatch_assum_abbrev_tac `FST q = _`
    \\ Cases_on `q` \\ fs [markerTheory.Abbrev_def]
    \\ pop_assum (assume_tac o SYM))
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ conj_tac
  >-
    (spose_not_then assume_tac \\ rw []
    \\ fsrw_tac [QUANT_INST_ss[pair_default_qp]] []
    \\ last_assum (qspec_then `k` mp_tac)
    \\ (fn g => subterm (fn tm => Cases_on`^(assert (can dest_prod o type_of) tm)` g) (#2 g))
    \\ strip_tac
    \\ qmatch_assum_rename_tac `evaluate (_,[],_ k) = (_,rr)`
    \\ drule (GEN_ALL in_evaluate_Call)
    \\ impl_tac >- (last_x_assum (qspec_then `k` mp_tac) \\ fs [])
    \\ strip_tac
    \\ fs[]
    \\ rveq
    \\ rpt(PURE_FULL_CASE_TAC \\ fs[] \\ rveq)
    \\ qmatch_asmsub_abbrev_tac `evaluate _ = (a1,_)`
    \\ first_assum (qspecl_then [`k`,`case a1 of Rerr (Rabort (Rffi_error e)) => FFI_outcome e
                                               | _ => Success`] mp_tac)
    \\ strip_tac \\ unabbrev_all_tac
    \\ fs[] \\ rfs[])
  \\ strip_tac
  \\ qmatch_abbrev_tac `build_lprefix_lub l1 = build_lprefix_lub l2`
  \\ `(lprefix_chain l1 ∧ lprefix_chain l2) ∧ equiv_lprefix_chain l1 l2`
     suffices_by metis_tac [build_lprefix_lub_thm,
                            lprefix_lub_new_chain,
                            unique_lprefix_lub]
  \\ conj_asm1_tac
  >-
    (unabbrev_all_tac
    \\ conj_tac
    \\ Ho_Rewrite.ONCE_REWRITE_TAC [GSYM o_DEF]
    \\ REWRITE_TAC [IMAGE_COMPOSE]
    \\ match_mp_tac prefix_chain_lprefix_chain
    \\ simp [prefix_chain_def, PULL_EXISTS]
    \\ qx_genl_tac [`k1`,`k2`]
    \\ qspecl_then [`k1`,`k2`] mp_tac LESS_EQ_CASES
    \\ metis_tac [
         LESS_EQ_EXISTS,
         bvlPropsTheory.initial_state_with_simp,
         bvlPropsTheory.evaluate_add_to_clock_io_events_mono
           |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["s"]))
           |> Q.SPEC`s with clock := k`
           |> SIMP_RULE (srw_ss())[bvlPropsTheory.inc_clock_def]])
  \\ simp [equiv_lprefix_chain_thm]
  \\ unabbrev_all_tac \\ simp [PULL_EXISTS]
  \\ simp [LNTH_fromList, PULL_EXISTS, GSYM FORALL_AND_THM]
  \\ rpt gen_tac
  \\ Cases_on `evaluate
         ([Call 0 (SOME start) []],[],
          initial_state ffi (fromAList prog) co (in_cc limit cc) k)`
  \\ drule (GEN_ALL in_evaluate_Call)
  \\ impl_tac >- (last_x_assum (qspec_then `k` mp_tac) \\ fs [])
  \\ strip_tac \\ fs []
  \\ conj_tac \\ rw []
  \\ qexists_tac `k` \\ fs []);

(* let_op *)

val let_opt_def = Define `
  let_opt split_seq cut_size (arity, prog) =
    (arity, compile_any split_seq cut_size arity (let_op_sing prog))`

val let_state_rel_def = Define `
  let_state_rel split_seq cut_size
           (s:('c,'ffi) bvlSem$state) (t:('c,'ffi) bvlSem$state) <=>
    t = s with <| code := map (let_opt split_seq cut_size) s.code
                ; compile := t.compile
                ; compile_oracle := (I ##
      MAP (I ## let_opt split_seq cut_size)) o s.compile_oracle |> /\
    s.compile = \cfg prog. t.compile cfg (MAP (I ## let_opt split_seq cut_size) prog)`

val let_state_rel_alt = let_state_rel_def

val let_state_rel_def = let_state_rel_def
  |> SIMP_RULE (srw_ss()) [state_component_equality,GSYM CONJ_ASSOC];

Theorem HD_let_op[simp]:
   [HD (let_op [x])] = let_op [x]
Proof
  Cases_on `x` \\ simp_tac std_ss [let_op_def] \\ fs []
  \\ CASE_TAC \\ fs []
QED

val let_op_sing_thm = prove(
  ``let_op_sing x = HD (let_op [x])``,
  fs [let_op_sing_def]
  \\ once_rewrite_tac [GSYM HD_let_op] \\ fs []);

val var_list_IMP_evaluate = prove(
  ``!a2 a1 l xs s.
      var_list (LENGTH a1) l xs /\ LENGTH (xs:bvl$exp list) = LENGTH a2 ==>
      evaluate (l,a1++a2++env,s) = (Rval a2,s)``,
  Induct THEN1
   (fs [APPEND_NIL,var_list_def]
    \\ Cases_on `l` \\ fs [var_list_def,evaluate_def]
    \\ Cases_on `h` \\ fs [var_list_def,evaluate_def])
  \\ Cases_on `xs` \\ fs [LENGTH]
  \\ Cases_on `l` \\ fs [var_list_def]
  \\ Cases_on `h'` \\ fs [var_list_def]
  \\ once_rewrite_tac [evaluate_CONS]
  \\ fs [evaluate_def,EL_LENGTH_APPEND] \\ rw []
  \\ simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ first_x_assum (qspec_then `a1 ++ [h']` mp_tac)
  \\ fs [] \\ rw [] \\ res_tac
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ fs [EL_LENGTH_APPEND]);

val var_list_IMP_evaluate = prove(
  ``var_list 0 l xs /\ LENGTH (xs:bvl$exp list) = LENGTH a ==>
    evaluate (l,a++env,s) = (Rval a,s)``,
  rw []
  \\ match_mp_tac (Q.SPECL [`xs`,`[]`] var_list_IMP_evaluate
       |> SIMP_RULE std_ss [APPEND,LENGTH])
  \\ asm_exists_tac \\ fs []);

Theorem LENGTH_let_op:
   !xs. LENGTH (let_op xs) = LENGTH xs
Proof
  ho_match_mp_tac let_op_ind \\ rw [let_op_def]
  \\ CASE_TAC \\ fs []
QED

val do_app_lemma = prove(
  ``let_state_rel q4 l4 s1 t1 ==>
    case do_app op a s1 of
    | Rerr err => do_app op a t1 = Rerr err
    | Rval (v,s2) => ?t2. let_state_rel q4 l4 s2 t2 /\ do_app op a t1 = Rval (v,t2)``,
  Cases_on `op = Install` THEN1
   (rw [] \\ fs [do_app_def]
    \\ every_case_tac \\ fs []
    \\ fs [case_eq_thms,UNCURRY,do_install_def]
    \\ rveq \\ fs [PULL_EXISTS]
    \\ fs [SWAP_REVERSE_SYM] \\ rveq \\ fs []
    \\ fs [let_state_rel_def] \\ rveq \\ fs []
    \\ fs [state_component_equality,domain_map]
    THEN1
     (fs [shift_seq_def,o_DEF] \\ rfs []
      \\ Cases_on `s1.compile_oracle 0` \\ fs []
      \\ Cases_on `r` \\ fs [] \\ Cases_on `h` \\ fs [] \\ rveq \\ fs []
      \\ fs [map_union] \\ AP_TERM_TAC
      \\ fs [map_fromAList] \\ AP_TERM_TAC \\ fs []
      \\ rpt (AP_THM_TAC ORELSE AP_TERM_TAC)
      \\ fs [FUN_EQ_THM,FORALL_PROD])
    \\ CCONTR_TAC \\ fs [] \\ rfs [FORALL_PROD,shift_seq_def])
  \\ strip_tac \\ Cases_on `do_app op a s1` \\ fs []
  THEN1
   (rename1 `_ = Rval aa`
    \\ PairCases_on `aa`
    \\ drule (Q.GENL [`c`,`cc`,`co`] do_app_with_code) \\ fs []
    \\ fs [let_state_rel_alt]
    \\ disch_then (qspecl_then [`map (let_opt q4 l4) s1.code`,
        `t1.compile`,`(I ## MAP (I ## let_opt q4 l4)) ∘
          s1.compile_oracle`] mp_tac)
    \\ qpat_x_assum `t1 = _` (assume_tac o GSYM) \\ fs []
    \\ impl_tac THEN1 fs [domain_map]
    \\ strip_tac \\ fs []
    \\ qpat_x_assum `_ = t1` (assume_tac o GSYM) \\ fs []
    \\ rw [] \\ fs [state_component_equality]
    \\ imp_res_tac do_app_const \\ fs [])
  \\ drule (Q.GENL [`c`,`cc`,`co`] do_app_with_code_err_not_Install) \\ fs []
  \\ fs [let_state_rel_alt]
  \\ disch_then (qspecl_then [`map (let_opt q4 l4) s1.code`,
      `t1.compile`,`(I ## MAP (I ##  let_opt q4 l4)) ∘
        s1.compile_oracle`] mp_tac)
  \\ qpat_x_assum `t1 = _` (assume_tac o GSYM) \\ fs []
  \\ impl_tac THEN1 fs [domain_map] \\ fs []);

Theorem evaluate_let_op:
   !es env s1 res t1 s2.
      let_state_rel q4 l4 s1 t1 /\
      evaluate (es,env,s1) = (res,s2) /\ res ≠ Rerr (Rabort Rtype_error) ==>
      ?t2. evaluate (let_op es,env,t1) = (res,t2) /\ let_state_rel q4 l4 s2 t2
Proof
  recInduct evaluate_ind \\ rw [] \\ fs [let_op_def]
  \\ fs [evaluate_def]
  THEN1
   (once_rewrite_tac [evaluate_CONS]
    \\ fs [case_eq_thms] \\ rveq \\ fs [] \\ fs[]
    \\ res_tac \\ fs [])
  THEN1 (rw [] \\ fs [])
  THEN1
   (fs [case_eq_thms] \\ rveq \\ fs [] \\ fs[]
    \\ rpt (qpat_x_assum `_ = bvlSem$evaluate _` (assume_tac o GSYM))
    \\ fs [] \\ res_tac \\ fs [] \\ res_tac \\ fs [])
  THEN1
   (fs [case_eq_thms] \\ rveq \\ fs [] \\ fs[]
    \\ first_x_assum drule \\ rw [] \\ fs []
    THEN1
     (first_x_assum drule \\ rw [] \\ fs []
      \\ TOP_CASE_TAC \\ fs []
      \\ fs [evaluate_def]
      \\ Cases_on `HD (let_op [x2])` \\ fs [dest_op_def] \\ rveq
      \\ drule (GEN_ALL var_list_IMP_evaluate) \\ fs [LENGTH_let_op]
      \\ imp_res_tac evaluate_IMP_LENGTH
      \\ disch_then drule \\ rw []
      \\ rename1 `_ = Op opname l`
      \\ qsuff_tac `let_op [x2] = [Op opname l]`
      THEN1 (rw [] \\ fs [evaluate_def])
      \\ once_rewrite_tac [GSYM HD_let_op] \\ fs [])
    \\ TOP_CASE_TAC \\ fs []
    \\ fs [evaluate_def])
  THEN1
   (fs [case_eq_thms] \\ rveq \\ fs [] \\ fs[]
    \\ rpt (qpat_x_assum `_ = bvlSem$evaluate _` (assume_tac o GSYM))
    \\ fs [] \\ res_tac \\ fs [] \\ res_tac \\ fs [])
  THEN1
   (fs [case_eq_thms] \\ rveq \\ fs [] \\ fs[]
    \\ rpt (qpat_x_assum `_ = bvlSem$evaluate _` (assume_tac o GSYM))
    \\ fs [] \\ res_tac \\ fs [] \\ res_tac \\ fs [])
  THEN1
   (fs [case_eq_thms] \\ rveq \\ fs [] \\ fs[]
    \\ rpt (qpat_x_assum `_ = bvlSem$evaluate _` (assume_tac o GSYM)) \\ fs []
    \\ fs [] \\ res_tac \\ fs [] \\ res_tac \\ fs []
    \\ rveq \\ fs []
    \\ drule (do_app_lemma |> Q.GEN `a` |> Q.SPEC `REVERSE vs`)
    \\ fs [] \\ rw [] \\ fs [])
  THEN1
   (fs [case_eq_thms] \\ rveq \\ fs [] \\ fs[]
    \\ rpt (qpat_x_assum `_ = bvlSem$evaluate _` (assume_tac o GSYM))
    \\ fs [] \\ res_tac \\ fs [] \\ res_tac \\ fs []
    THEN1 (fs [let_state_rel_def])
    \\ `let_state_rel q4 l4 (dec_clock 1 s) (dec_clock 1 t1)`
           by fs [let_state_rel_def,dec_clock_def]
    \\ fs [] \\ res_tac \\ fs [] \\ res_tac \\ fs []
    \\ rveq \\ fs []
    \\ qexists_tac `t2` \\ fs [] \\ fs [let_state_rel_def])
  THEN1
   (fs [case_eq_thms] \\ rveq \\ fs [] \\ fs[]
    \\ rpt (qpat_x_assum `_ = bvlSem$evaluate _` (assume_tac o GSYM))
    \\ fs [] \\ res_tac \\ fs [] \\ res_tac \\ fs [] \\ rveq
    \\ res_tac \\ fs [PULL_EXISTS]
    THEN1
     (qexists_tac `t2' with clock := 0` \\ fs [let_state_rel_def]
      \\ Cases_on `dest` \\ fs [find_code_def]
      \\ fs [case_eq_thms,lookup_map,let_opt_def])
    \\ rename1`find_code _ _ _ = SOME (_,exp)`
    \\ `find_code dest vs t2.code = SOME (args,
           compile_any q4 l4 (LENGTH args) (let_op_sing exp))` by
     (Cases_on `dest`
      \\ fs [find_code_def,case_eq_thms,let_state_rel_def,lookup_map]
      \\ fs [let_op_sing_thm,let_opt_def]
      \\ rveq \\ fs []
      \\ `?t ts. vs = SNOC t ts` by metis_tac [SNOC_CASES]
      \\ full_simp_tac std_ss [FRONT_SNOC,LAST_SNOC,LENGTH_SNOC,ADD1])
    \\ fs []
    \\ `let_state_rel q4 l4 (dec_clock (ticks + 1) s) (dec_clock (ticks + 1) t2)`
          by fs [let_state_rel_def,dec_clock_def]
    \\ res_tac \\ fs [] \\ rfs [let_state_rel_def]
    \\ rename1 `_ = (res,t9)`
    \\ qexists_tac `t9` \\ fs []
    \\ once_rewrite_tac [EQ_SYM_EQ]
    \\ match_mp_tac bvl_handleProofTheory.compile_any_correct \\ fs []
    \\ fs [let_op_sing_thm,HD_let_op])
QED

val let_op_cc_def = Define `
  let_op_cc q4 l4 cc =
     (λcfg prog. cc cfg (MAP (I ## let_opt q4 l4) prog))`;

val let_evaluate_Call = Q.prove(
  `evaluate ([Call 0 (SOME start) []], [],
             initial_state ffi0 prog co (let_op_cc q4 l4 cc) k) = (r, s) /\
   r <> Rerr (Rabort Rtype_error) ⇒
   ∃(s2:('c,'ffi) bvlSem$state).
     evaluate
      ([Call 0 (SOME start) []], [],
        initial_state ffi0 (map (let_opt q4 l4) prog)
          ((I ## MAP (I ## let_opt q4 l4)) o co)
          cc k) = (r, s2) ∧
     s2.ffi = s.ffi /\ s.clock = s2.clock`,
  strip_tac \\ fs [let_op_cc_def]
  \\ imp_res_tac evaluate_let_op
  \\ fs [let_op_def]
  \\ qmatch_goalsub_abbrev_tac `([_],[],t4)`
  \\ first_x_assum (qspecl_then [`t4`,`q4`,`l4`] mp_tac)
  \\ impl_tac \\ rw [] \\ fs []
  \\ fs [let_state_rel_def]
  \\ unabbrev_all_tac \\ fs [initial_state_def]);

val semantics_let_op = prove(
  ``semantics ffi prog co (let_op_cc q4 l4 cc) start <> Fail ==>
    semantics ffi (map (let_opt q4 l4) prog)
                  ((I ## MAP (I ## let_opt q4 l4)) o co) cc start =
    semantics (ffi:'b ffi_state) prog co (let_op_cc q4 l4 cc) start``,
  simp [Once semantics_def]
  \\ simp [Once semantics_def, SimpRHS]
  \\ IF_CASES_TAC \\ fs []
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ conj_tac
  >-
   (
    gen_tac \\ strip_tac \\ rveq \\ simp []
    \\ simp [semantics_def]
    \\ IF_CASES_TAC \\ fs []
    >-
     (first_assum (subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) o concl)
      \\ drule evaluate_add_clock
      \\ `q <> Rerr (Rabort Rtimeout_error)` by (CCONTR_TAC \\ fs []) \\ fs []
      \\ CCONTR_TAC \\ fs []
      \\ qpat_x_assum `evaluate (_,_,_ _ (_ prog) _ _ _) = _` kall_tac
      \\ last_assum (qspec_then `k'` mp_tac)
      \\ (fn g => subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) (#2 g) g )
      \\ rw [] \\ fs [] \\ rveq
      \\ CCONTR_TAC
      \\ drule (GEN_ALL let_evaluate_Call) \\ simp []
      \\ strip_tac
      \\ first_x_assum (qspec_then `0` mp_tac)
      \\ simp [inc_clock_def])
    \\ DEEP_INTRO_TAC some_intro \\ simp []
    \\ conj_tac
    >-
     (gen_tac \\ strip_tac \\ rveq \\ fs []
      \\ qabbrev_tac `opts = (map (I ## let_op_sing) prog)`
      \\ qmatch_assum_abbrev_tac `bvlSem$evaluate (opts1,[],sopt1) = _`
      \\ qmatch_assum_abbrev_tac `bvlSem$evaluate (exps1,[],st1) = (r,s)`
      \\ qspecl_then [`opts1`,`[]`,`sopt1`] mp_tac
           evaluate_add_to_clock_io_events_mono
      \\ qspecl_then [`exps1`,`[]`,`st1`] mp_tac
           evaluate_add_to_clock_io_events_mono
      \\ simp [inc_clock_def, Abbr`sopt1`, Abbr`st1`]
      \\ ntac 2 strip_tac
      \\ Cases_on `r` \\ fs []
      >-
       (Cases_on `r'` \\ fs []
        >-
         (unabbrev_all_tac
          \\ drule (GEN_ALL let_evaluate_Call) \\ simp []
          \\ strip_tac
          \\ drule evaluate_add_clock
          \\ disch_then (qspec_then `k'` mp_tac) \\ simp [inc_clock_def]
          \\ qpat_x_assum `evaluate _ = _` kall_tac
          \\ drule evaluate_add_clock
          \\ disch_then (qspec_then `k` mp_tac) \\ simp [inc_clock_def]
          \\ ntac 2 strip_tac \\ rveq \\ fs []
          \\ fs [state_component_equality] \\ rfs [] \\ rfs [])
        \\ qpat_x_assum `∀extra._` mp_tac
        \\ first_x_assum (qspec_then `k'` assume_tac)
        \\ first_assum (subterm
             (fn tm => Cases_on`^(assert has_pair_type tm)`) o concl)
        \\ strip_tac \\ fs []
        \\ unabbrev_all_tac
        \\ drule (GEN_ALL let_evaluate_Call)
        \\ impl_tac
        >- (last_x_assum (qspec_then `k+k'` mp_tac) \\ fs [])
        \\ strip_tac
        \\ qhdtm_x_assum `evaluate` mp_tac
        \\ imp_res_tac evaluate_add_clock
        \\ pop_assum mp_tac
        \\ ntac 2 (pop_assum kall_tac)
        \\ impl_tac
        >- (strip_tac \\ fs [])
        \\ disch_then (qspec_then `k'` mp_tac) \\ simp [inc_clock_def]
        \\ first_x_assum (qspec_then `k` mp_tac) \\ fs []
        \\ ntac 3 strip_tac
        \\ fs [let_state_rel_def] \\ rveq
        \\ qpat_x_assum `evaluate _ = (Rerr _, _)` assume_tac
        \\ drule evaluate_add_clock
        \\ disch_then (qspec_then `k` mp_tac)
        \\ impl_tac >- (CCONTR_TAC \\ fs[])
        \\ simp[inc_clock_def])
      \\ qpat_x_assum `∀extra._` mp_tac
      \\ first_x_assum (qspec_then `k'` assume_tac)
      \\ first_assum (subterm (fn tm =>
            Cases_on`^(assert has_pair_type tm)`) o concl)
      \\ fs []
      \\ unabbrev_all_tac
      \\ strip_tac
      \\ drule (GEN_ALL let_evaluate_Call)
      \\ impl_tac
      >- (last_x_assum (qspec_then `k+k'` mp_tac) \\ fs [])
      \\ strip_tac \\ rveq \\ fs []
      \\ reverse (Cases_on `r'`) \\ fs [] \\ rfs []
      >-
        (first_x_assum (qspec_then `k` mp_tac)
        \\ fs [ADD1]
        \\ strip_tac \\ fs [state_rel_def] \\ rfs []
        \\ qpat_x_assum `evaluate _ = (Rerr e, _)` assume_tac
        \\ drule evaluate_add_clock
        \\ disch_then (qspec_then `k'` mp_tac)
        \\ impl_tac >- (CCONTR_TAC \\ fs[])
        \\ qpat_x_assum `evaluate _ = (Rerr e', _)` assume_tac
        \\ drule evaluate_add_clock
        \\ disch_then (qspec_then `k` mp_tac)
        \\ impl_tac >- (CCONTR_TAC \\ fs[])
        \\ simp[inc_clock_def] \\ rpt strip_tac \\ fs[]
        \\ rpt(PURE_FULL_CASE_TAC \\ fs[] \\ rveq \\ fs[]))
      \\ qhdtm_x_assum `evaluate` mp_tac
      \\ imp_res_tac evaluate_add_clock
      \\ pop_assum kall_tac
      \\ pop_assum mp_tac
      \\ impl_tac
      >- (strip_tac \\ fs [])
      \\ disch_then (qspec_then `k` mp_tac)
      \\ simp [inc_clock_def]
      \\ rpt strip_tac \\ rveq
      \\ qpat_x_assum `evaluate _ = (Rerr e, _)` assume_tac
      \\ drule evaluate_add_clock
      \\ disch_then (qspec_then `k'` mp_tac)
      \\ impl_tac >- (CCONTR_TAC \\ fs[])
      \\ simp[inc_clock_def]
      \\ rpt(PURE_FULL_CASE_TAC \\ fs[]))
    \\ qmatch_assum_abbrev_tac `bvlSem$evaluate (exps2,[],st2) = _`
    \\ qspecl_then [`exps2`,`[]`,`st2`] mp_tac evaluate_add_to_clock_io_events_mono
    \\ simp [inc_clock_def, Abbr`st2`]
    \\ disch_then (qspec_then `0` strip_assume_tac)
    \\ first_assum (subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) o concl)
    \\ unabbrev_all_tac
    \\ drule (GEN_ALL let_evaluate_Call)
    \\ impl_tac
    >- (last_x_assum (qspec_then `k` mp_tac) \\ fs [])
    \\ strip_tac
    \\ asm_exists_tac \\ fs []
    \\ every_case_tac \\ fs [] \\ rveq \\ fs [])
  \\ strip_tac
  \\ simp [semantics_def]
  \\ IF_CASES_TAC \\ fs []
  >-
    (last_x_assum (qspec_then `k` assume_tac) \\ rfs []
    \\ first_assum (qspec_then `e` assume_tac)
    \\ fs [] \\ rfs []
    \\ qmatch_assum_abbrev_tac `FST q ≠ _`
    \\ Cases_on `q` \\ fs [markerTheory.Abbrev_def]
    \\ pop_assum (assume_tac o SYM)
    \\ drule (GEN_ALL let_evaluate_Call)
    \\ simp []
    \\ spose_not_then strip_assume_tac
    \\ qmatch_assum_abbrev_tac `FST q = _`
    \\ Cases_on `q` \\ fs [markerTheory.Abbrev_def]
    \\ pop_assum (assume_tac o SYM))
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ conj_tac
  >-
    (spose_not_then assume_tac \\ rw []
    \\ fsrw_tac [QUANT_INST_ss[pair_default_qp]] []
    \\ last_assum (qspec_then `k` mp_tac)
    \\ (fn g => subterm (fn tm => Cases_on`^(assert (can dest_prod o type_of) tm)` g) (#2 g))
    \\ strip_tac
    \\ qmatch_assum_rename_tac `evaluate (_,[],_ k) = (_,rr)`
    \\ drule (GEN_ALL let_evaluate_Call)
    \\ impl_tac >- (last_x_assum (qspec_then `k` mp_tac) \\ fs [])
    \\ strip_tac
    \\ first_assum (qspecl_then [`k`,`case r of Rerr (Rabort (Rffi_error e)) => FFI_outcome e
                                               | _ => Success`] mp_tac)
    \\ strip_tac \\ unabbrev_all_tac
    \\ rpt(PURE_FULL_CASE_TAC \\ fs[] \\ rveq) \\ rfs[])
  \\ strip_tac
  \\ qmatch_abbrev_tac `build_lprefix_lub l1 = build_lprefix_lub l2`
  \\ `(lprefix_chain l1 ∧ lprefix_chain l2) ∧ equiv_lprefix_chain l1 l2`
     suffices_by metis_tac [build_lprefix_lub_thm,
                            lprefix_lub_new_chain,
                            unique_lprefix_lub]
  \\ conj_asm1_tac
  >-
    (unabbrev_all_tac
    \\ conj_tac
    \\ Ho_Rewrite.ONCE_REWRITE_TAC [GSYM o_DEF]
    \\ REWRITE_TAC [IMAGE_COMPOSE]
    \\ match_mp_tac prefix_chain_lprefix_chain
    \\ simp [prefix_chain_def, PULL_EXISTS]
    \\ qx_genl_tac [`k1`,`k2`]
    \\ qspecl_then [`k1`,`k2`] mp_tac LESS_EQ_CASES
    \\ metis_tac [
         LESS_EQ_EXISTS,
         bvlPropsTheory.initial_state_with_simp,
         bvlPropsTheory.evaluate_add_to_clock_io_events_mono
           |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["s"]))
           |> Q.SPEC`s with clock := k`
           |> SIMP_RULE (srw_ss())[bvlPropsTheory.inc_clock_def]])
  \\ simp [equiv_lprefix_chain_thm]
  \\ unabbrev_all_tac \\ simp [PULL_EXISTS]
  \\ simp [LNTH_fromList, PULL_EXISTS, GSYM FORALL_AND_THM]
  \\ rpt gen_tac
  \\ Cases_on `evaluate
         ([Call 0 (SOME start) []],[],
          initial_state ffi prog co (let_op_cc q4 l4 cc) k)`
  \\ drule (GEN_ALL let_evaluate_Call)
  \\ impl_tac >- (last_x_assum (qspec_then `k` mp_tac) \\ fs [])
  \\ strip_tac \\ fs []
  \\ conj_tac \\ rw [] \\ qexists_tac `k` \\ fs []);

(* combined theorems *)

val remove_ticks_mk_tick = prove(
  ``!n r. remove_ticks [mk_tick n r] = remove_ticks [r]``,
  Induct THEN1 (EVAL_TAC \\ fs [])
  \\ fs [bvlTheory.mk_tick_def,FUNPOW,remove_ticks_def]);

val is_small_aux_0 = prove(
  ``!n:num xs. is_small_aux 0 xs = 0``,
  recInduct is_small_aux_ind
  \\ rw [] \\ fs [is_small_aux_def]);

val is_small_aux_CONS = prove(
  ``is_small_aux n (x::xs) =
    if n = 0 then n else
      let n = is_small_aux n [x] in
        if n = 0 then n else is_small_aux n xs``,
  Induct_on `xs` \\ fs [is_small_aux_def] \\ rw []
  \\ Cases_on `x` \\ fs [is_small_aux_def,is_small_aux_0]);

val is_small_aux_remove_ticks = prove(
  ``!limit d. is_small_aux limit (remove_ticks d) = is_small_aux limit d``,
  recInduct is_small_aux_ind \\ rw []
  \\ fs [is_small_aux_def,remove_ticks_def]
  \\ rw [] \\ fs []
  \\ once_rewrite_tac [is_small_aux_CONS] \\ fs []
  \\ simp [Once is_small_aux_CONS] \\ fs []);

val is_rec_CONS = prove(
  ``is_rec n (x::xs) <=> is_rec n [x] \/ is_rec n xs``,
  Cases_on `xs` \\ fs [is_rec_def]);

val is_rec_remove_ticks = prove(
  ``!p_1 xs. is_rec p_1 (remove_ticks xs) = is_rec p_1 xs``,
  recInduct is_rec_ind \\ rw []
  \\ fs [remove_ticks_def,is_rec_def]
  \\ simp [Once is_rec_CONS]
  \\ fs [] \\ fs [is_rec_def]
  \\ metis_tac []);

val must_inline_remove_ticks = prove(
  ``must_inline p_1 limit (HD (remove_ticks (tick_inline cs [p_2]))) =
    must_inline p_1 limit (HD ((tick_inline cs [p_2])))``,
  fs [must_inline_def]
  \\ `?d. tick_inline cs [p_2] = [d]` by
   (`LENGTH (tick_inline cs [p_2]) = LENGTH [p_2]`
       by metis_tac [LENGTH_tick_inline] \\ fs []
    \\ Cases_on `tick_inline cs [p_2]` \\ fs [])
  \\ fs [is_small_def,is_rec_def,is_small_aux_remove_ticks]
  \\ fs [is_rec_remove_ticks]);

val let_opt_remove_def = Define `
  let_opt_remove b l (arity,prog) =
    let_opt b l (arity,HD (remove_ticks [prog]))`;

val map_fromAList_HASH = prove(
  ``map f (fromAList ls) = fromAList (MAP (I ## f) ls)``,
  fs [map_fromAList]
  \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
  \\ fs [FUN_EQ_THM,FORALL_PROD]);

Theorem map_fromAList:
   !xs f. map f (fromAList xs) = fromAList (MAP (I ## f) xs)
Proof
  Induct \\ fs [fromAList_def,fromAList_def,FORALL_PROD,map_insert]
QED

val ticks =
  semantics_remove_ticks
  |> Q.INST [`prog`|->`fromAList p`]
  |> SIMP_RULE std_ss [map_fromAList]

val lets =
  semantics_let_op
  |> Q.INST [`prog`|->`fromAList p`]
  |> SIMP_RULE std_ss [map_fromAList]

val inline_ticks = prove(
  ``FST (FST (co 0)) = (FST (tick_compile_prog limit LN prog)) ∧
    ALL_DISTINCT (MAP FST prog) ⇒
    semantics ffi (fromAList prog) co
      (in_cc limit (remove_ticks_cc cc)) start ≠ Fail ⇒
    semantics ffi (fromAList (MAP (I ## I ## (λx. HD (remove_ticks [x])))
                                (SND (tick_compile_prog limit LN prog))))
      (remove_ticks_co ∘ in_co limit co) cc start =
    semantics ffi (fromAList prog) co (in_cc limit (remove_ticks_cc cc)) start``,
  fs [ticks] \\ strip_tac
  \\ match_mp_tac semantics_tick_inline \\ fs []);

val comp_lemma = prove(
  ``(I ## let_opt q4 l4) o (I ## I ## (λx. HD (remove_ticks [x]))) =
    (I ## let_opt_remove q4 l4)``,
  fs [FUN_EQ_THM,FORALL_PROD,let_opt_remove_def,let_opt_def]);

val bvl_inline_cc_def = Define `
  bvl_inline_cc limit q4 l4 cc =
    (in_cc limit (remove_ticks_cc (let_op_cc q4 l4 cc)))`;

val bvl_inline_co_def = Define `
  bvl_inline_co limit q4 l4 co =
   (λx. (I ## MAP (I ## let_opt q4 l4))
          (remove_ticks_co (in_co limit co x)))`;

val MAP_optimise = prove(
  ``!prog.
      MAP (optimise o1 o2) prog =
      MAP (I ## let_opt o1 o2)
        (MAP (I ## I ## (λx. HD (remove_ticks [x]))) prog)``,
  Induct \\ fs [FORALL_PROD,optimise_def,let_opt_def]);

Theorem state_cc_compile_inc_eq:
   (state_cc (compile_inc limit o1 o2) cc) =
      (in_cc limit (remove_ticks_cc (let_op_cc o1 o2 cc)))
Proof
  fs [state_cc_def,compile_inc_def,in_cc_def,FUN_EQ_THM,remove_ticks_cc_def,
      let_op_cc_def] \\ rw []
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ fs [MAP_optimise]
QED

Theorem state_co_compile_inc_eq:
   (state_co (compile_inc limit o1 o2) co) =
      ((I ## MAP (I ## let_opt o1 o2)) o remove_ticks_co ∘ in_co limit co)
Proof
  fs [state_co_def,compile_inc_def,in_co_def,FUN_EQ_THM,remove_ticks_co_def]
  \\ rw []
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ fs [MAP_optimise]
QED

Theorem compile_prog_semantics:
   compile_prog limit o1 o2 prog = (s1,prog1) /\
    FST (FST (co 0)) = s1 /\
    ALL_DISTINCT (MAP FST prog) ⇒
    semantics ffi (fromAList prog) co (state_cc (compile_inc limit o1 o2) cc)
      start ≠ Fail ⇒
    semantics ffi (fromAList prog1) (state_co (compile_inc limit o1 o2) co) cc
      start =
    semantics ffi (fromAList prog) co (state_cc (compile_inc limit o1 o2) cc)
      start
Proof
  fs [state_cc_compile_inc_eq,state_co_compile_inc_eq]
  \\ fs [compile_prog_def,compile_inc_def]
  \\ pairarg_tac \\ fs [] \\ rw []
  \\ rveq \\ fs [MAP_optimise]
  \\ drule (GEN_ALL (ONCE_REWRITE_RULE [CONJ_COMM]
     (REWRITE_RULE [CONJ_ASSOC,AND_IMP_INTRO] inline_ticks)))
  \\ fs [] \\ disch_then (assume_tac o GSYM) \\ fs []
  \\ drule (GEN_ALL lets)
  \\ fs [] \\ disch_then (assume_tac o GSYM) \\ fs []
QED

Theorem handle_ok_optimise:
   !prog. bvl_handleProof$handle_ok (MAP (SND ∘ SND ∘ optimise b i) prog)
Proof
  Induct \\ fs [bvl_handleProofTheory.handle_ok_def,FORALL_PROD]
  \\ once_rewrite_tac [bvl_handleProofTheory.handle_ok_CONS] \\ fs []
  \\ fs [bvl_handleProofTheory.compile_any_handle_ok,optimise_def]
QED

Theorem compile_prog_handle_ok:
   compile_prog l b i prog = (inlines,prog3) ==>
    bvl_handleProof$handle_ok (MAP (SND o SND) prog3)
Proof
  fs [compile_prog_def,compile_inc_def]
  \\ pairarg_tac \\ fs [] \\ rw []
  \\ fs [MAP_MAP_o,handle_ok_optimise]
QED

Theorem MAP_FST_MAP_optimise[simp]:
   MAP FST (MAP (optimise x y) z) = MAP FST z
Proof
  Induct_on`z` \\ fs[FORALL_PROD,optimise_def]
QED

Theorem compile_prog_names:
   compile_prog l b i prog = (inlines,prog3) ==>
    MAP FST prog3 = MAP FST prog
Proof
  fs [compile_prog_def,compile_inc_def] \\ pairarg_tac \\ fs []
  \\ fs [tick_compile_prog_def]
  \\ imp_res_tac tick_inline_all_names \\ rw []
  \\ rw[] \\ fs[]
QED

Theorem var_list_code_labels_imp:
   ∀n x y. var_list n x y ⇒ BIGUNION (set (MAP get_code_labels x)) = {}
Proof
  recInduct bvl_inlineTheory.var_list_ind
  \\ rw[bvl_inlineTheory.var_list_def] \\ fs[]
QED

Theorem let_op_code_labels:
   ∀x. BIGUNION (set (MAP get_code_labels (let_op x))) = BIGUNION (set (MAP get_code_labels x))
Proof
  recInduct bvl_inlineTheory.let_op_ind
  \\ rw[bvl_inlineTheory.let_op_def]
  \\ full_simp_tac std_ss [Once(GSYM HD_let_op)] \\ fs[]
  \\ PURE_CASE_TAC \\ fs[]
  \\ Cases_on`HD (let_op [x2])` \\ fs[bvl_inlineTheory.dest_op_def]
  \\ rveq
  \\ imp_res_tac var_list_code_labels_imp
  \\ fs[] \\ rveq \\ fs[]
  \\ simp[EXTENSION]
  \\ metis_tac[]
QED

Theorem let_op_sing_code_labels[simp]:
   get_code_labels (let_op_sing x) = get_code_labels x
Proof
  rw[bvl_inlineTheory.let_op_sing_def]
  \\ simp_tac std_ss [Once(GSYM HD_let_op)]
  \\ simp[]
  \\ specl_args_of_then``bvl_inline$let_op``let_op_code_labels mp_tac
  \\ simp_tac std_ss [Once(GSYM HD_let_op)]
  \\ rw[]
QED

Theorem remove_ticks_code_labels:
   ∀x.
     BIGUNION (set (MAP get_code_labels (remove_ticks x))) =
     BIGUNION (set (MAP get_code_labels x))
Proof
  recInduct bvl_inlineTheory.remove_ticks_ind
  \\ rw[bvl_inlineTheory.remove_ticks_def]
  \\ FULL_SIMP_TAC std_ss [Once (GSYM bvl_inlineTheory.remove_ticks_SING)] \\ fs[]
QED

Theorem optimise_get_code_labels:
   ∀x y z.
     get_code_labels (SND (SND (optimise x y z))) ⊆
     get_code_labels (SND (SND z))
Proof
  rpt gen_tac \\ PairCases_on`z`
  \\ reverse(rw[bvl_inlineTheory.optimise_def, bvl_handleTheory.compile_any_def, bvl_handleTheory.compile_exp_def])
  >- (
    specl_args_of_then``bvl_handle$compile``bvl_handleProofTheory.compile_code_labels mp_tac
    \\ rw[]
    \\ qmatch_goalsub_abbrev_tac`bvl_handle$compile a b c`
    \\ Cases_on`bvl_handle$compile a b c`
    \\ PairCases_on`r`
    \\ unabbrev_all_tac
    \\ imp_res_tac bvl_handleTheory.compile_sing
    \\ rveq
    \\ qpat_x_assum`_ ⊆ _`mp_tac
    \\ simp[]
    \\ strip_tac
    \\ match_mp_tac SUBSET_TRANS
    \\ asm_exists_tac \\ simp[]
    \\ match_mp_tac SUBSET_TRANS
    \\ specl_args_of_then``bvl_const$compile_exp`` bvl_constProofTheory.compile_exp_code_labels mp_tac
    \\ strip_tac \\ asm_exists_tac \\ simp[]
    \\ specl_args_of_then``bvl_inline$remove_ticks`` remove_ticks_code_labels mp_tac
    \\ SIMP_TAC std_ss [Once (GSYM bvl_inlineTheory.remove_ticks_SING)] \\ fs[] )
  \\ Cases_on `remove_ticks [z2]` \\ fs []
  \\ first_assum (assume_tac o Q.AP_TERM `LENGTH`) \\ fs [] \\ rw []
  \\ qspec_then `[z2]` assume_tac remove_ticks_code_labels \\ fs [] \\ rfs []
  \\ pop_assum (SUBST1_TAC o GSYM)
  \\ qspecl_then [`y`,`let_op_sing h`,`NONE`]
       assume_tac bvl_handleProofTheory.compile_seqs_code_labels \\ fs []
QED

Theorem tick_inline_code_labels:
   !cs xs.
     BIGUNION (set (MAP get_code_labels (tick_inline cs xs))) SUBSET
     BIGUNION (set (MAP get_code_labels xs)) UNION
     BIGUNION (set (MAP (get_code_labels o SND) (toList cs)))
Proof
  ho_match_mp_tac bvl_inlineTheory.tick_inline_ind
  \\ rw [bvl_inlineTheory.tick_inline_def]
  \\ TRY
   (qmatch_goalsub_rename_tac `_ (HD (tick_inline cs [x])) SUBSET _`
    \\ Cases_on `tick_inline cs [x]`
    \\ pop_assum (assume_tac o Q.AP_TERM `LENGTH`)
    \\ fs [bvl_inlineTheory.LENGTH_tick_inline] \\ rw []
    \\ fs [SUBSET_DEF] \\ rw [] \\ metis_tac [])
  \\ TRY
   (rename1 `closLang$assign_get_code_label op`
    \\ fs [SUBSET_DEF] \\ rw [] \\ metis_tac [])
  \\ TRY (* what... *)
   (rename1 `option_CASE dest`
    \\ rpt (PURE_FULL_CASE_TAC \\ fs []) \\ rw []
    \\ fs [SUBSET_DEF] \\ rw []
    \\ fs [MEM_MAP, MEM_toList]
    \\ metis_tac [FST, SND, PAIR])
  \\ Cases_on `tick_inline cs [x1]` \\ pop_assum (mp_tac o Q.AP_TERM `LENGTH`)
  \\ Cases_on `tick_inline cs [x2]` \\ pop_assum (mp_tac o Q.AP_TERM `LENGTH`)
  \\ Cases_on `tick_inline cs [x3]` \\ pop_assum (mp_tac o Q.AP_TERM `LENGTH`)
  \\ rw [bvl_inlineTheory.LENGTH_tick_inline]
  \\ fs [SUBSET_DEF] \\ rw [] \\ metis_tac []
QED

Theorem tick_inline_all_code_labels:
   !limit cs xs aux cs1 xs1.
     tick_inline_all limit cs xs aux = (cs1, xs1)
     ==>
     BIGUNION (set (MAP (get_code_labels o SND o SND) xs1)) SUBSET
     BIGUNION (set (MAP (get_code_labels o SND o SND) xs)) UNION
     BIGUNION (set (MAP (get_code_labels o SND o SND) aux)) UNION
     BIGUNION (set (MAP (get_code_labels o SND) (toList cs)))
Proof
  ho_match_mp_tac bvl_inlineTheory.tick_inline_all_ind
  \\ rw [bvl_inlineTheory.tick_inline_all_def]
  \\ fs [MAP_REVERSE]
  \\ Cases_on `tick_inline cs [e1]`
  \\ first_assum (assume_tac o Q.AP_TERM `LENGTH`)
  \\ fs [bvl_inlineTheory.LENGTH_tick_inline] \\ rw []
  \\ qispl_then [`cs`,`[e1]`] assume_tac tick_inline_code_labels \\ fs [] \\ rfs []
  \\ fs [AC UNION_COMM UNION_ASSOC]
  \\ qmatch_goalsub_abbrev_tac `s1 SUBSET s2 UNION (s3 UNION (s4 UNION s5))`
  \\ fs [SUBSET_DEF] \\ rw []
  \\ rpt (first_x_assum drule \\ rw []) \\ fs []
  \\ fs [MEM_MAP, MEM_toList, lookup_insert]
  \\ FULL_CASE_TAC \\ fs [] \\ rw [] \\ fs []
  \\ res_tac \\ fs []
  \\ fs [Abbr `s3`, MEM_MAP, MEM_toList, PULL_EXISTS]
  \\ metis_tac [PAIR, FST, SND]
QED

Theorem compile_prog_get_code_labels:
   bvl_inline$compile_prog x y z p = (inlines,q) ⇒
   BIGUNION (set (MAP (get_code_labels o SND o SND) q)) ⊆
   BIGUNION (set (MAP (get_code_labels o SND o SND) p))
Proof
  rw[bvl_inlineTheory.compile_prog_def, bvl_inlineTheory.compile_inc_def, bvl_inlineTheory.tick_compile_prog_def]
  \\ pairarg_tac \\ fs[] \\ rveq
  \\ simp[MAP_MAP_o, o_DEF]
  \\ match_mp_tac SUBSET_TRANS
  \\ qexists_tac`BIGUNION (set (MAP (get_code_labels o SND o SND) prog1))`
  \\ conj_tac
  >- (
    rw[SUBSET_DEF, MEM_MAP, PULL_EXISTS]
    \\ rpt(pop_assum mp_tac)
    \\ specl_args_of_then``bvl_inline$optimise``optimise_get_code_labels mp_tac
    \\ rw[SUBSET_DEF]
    \\ metis_tac[])
  \\ imp_res_tac tick_inline_all_code_labels
  \\ fs [o_DEF, toList_def, toListA_def]
QED

val _ = export_theory();
