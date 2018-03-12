open preamble
     bvlSemTheory bvlPropsTheory
     bvl_inlineTheory;

val _ = new_theory"bvl_inlineProof";

(* removal of ticks *)

val remove_ticks_def = tDefine "remove_ticks" `
  (remove_ticks [] = []) /\
  (remove_ticks (x::y::xs) =
     HD (remove_ticks [x]) :: remove_ticks (y::xs)) /\
  (remove_ticks [Var v] = [Var v]) /\
  (remove_ticks [If x1 x2 x3] =
     [If (HD (remove_ticks [x1]))
         (HD (remove_ticks [x2]))
         (HD (remove_ticks [x3]))]) /\
  (remove_ticks [Let xs x2] =
     [Let (remove_ticks xs) (HD (remove_ticks [x2]))]) /\
  (remove_ticks [Raise x1] =
     [Raise (HD (remove_ticks [x1]))]) /\
  (remove_ticks [Handle x1 x2] =
     [Handle (HD (remove_ticks [x1]))
             (HD (remove_ticks [x2]))]) /\
  (remove_ticks [Op op xs] =
     [Op op (remove_ticks xs)]) /\
  (remove_ticks [Tick x] = remove_ticks [x]) /\
  (remove_ticks [Call ticks dest xs] =
     [Call 0 dest (remove_ticks xs)])`
  (WF_REL_TAC `measure exp1_size`);

val LENGTH_remove_ticks = store_thm("LENGTH_remove_ticks[simp]",
  ``!xs. LENGTH (remove_ticks xs) = LENGTH xs``,
  recInduct (theorem "remove_ticks_ind") \\ fs [remove_ticks_def]);

val remove_ticks_SING = store_thm("remove_ticks_SING[simp]",
  ``[HD (remove_ticks [r])] = remove_ticks [r]``,
  qsuff_tac `?a. remove_ticks [r] = [a]` \\ rw[] \\ fs []
  \\ `LENGTH (remove_ticks [r]) = LENGTH [r]` by fs [LENGTH_remove_ticks]
  \\ Cases_on `remove_ticks [r]` \\ fs []);

val state_rel_def = Define `
  state_rel (s:'ffi bvlSem$state) (t:'ffi bvlSem$state) <=>
    t = s with code := map (I ## (\x. HD (remove_ticks [x]))) s.code`

val do_app_lemma = prove(
  ``state_rel t' r ==>
    case do_app op (REVERSE a) r of
    | Rerr err => do_app op (REVERSE a) t' = Rerr err
    | Rval (v,r2) => ?t2. state_rel t2 r2 /\ do_app op (REVERSE a) t' = Rval (v,t2)``,
  strip_tac \\ Cases_on `do_app op (REVERSE a) t'`
  THEN1
   (PairCases_on `a'`
    \\ drule (GEN_ALL bvlPropsTheory.do_app_with_code)
    \\ disch_then (qspec_then `r.code` mp_tac)
    \\ fs [state_rel_def,domain_map]
    \\ rw [] \\ fs [state_component_equality]
    \\ imp_res_tac do_app_const \\ fs [])
  \\ drule (GEN_ALL bvlPropsTheory.do_app_with_code_err)
  \\ disch_then (qspec_then `r.code` mp_tac)
  \\ fs [state_rel_def,domain_map]);

val evaluate_remove_ticks = Q.store_thm("evaluate_remove_ticks",
  `!k xs env s (t:'ffi bvlSem$state) res s'.
      state_rel t s /\ s.clock = k /\
      evaluate (remove_ticks xs,env,s) = (res,s') ==>
      ?ck t'. evaluate (xs,env,t with clock := t.clock + ck) = (res,t') /\
              state_rel t' s'`,
  strip_tac \\ completeInduct_on `k` \\ fs [PULL_FORALL,AND_IMP_INTRO]
  \\ recInduct (theorem "remove_ticks_ind") \\ rw []
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
    \\ `∀env s' (t:'ffi bvlSem$state) res s''.
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
      \\ `∀env s' (t:'ffi bvlSem$state) res s''.
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
      \\ `∀env s' (t:'ffi bvlSem$state) res s''.
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
    \\ `∀env s' (t:'ffi bvlSem$state) res s''.
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
    \\ `∀env s' (t:'ffi bvlSem$state) res s''.
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
    \\ PairCases_on `z` \\ fs [])
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
  \\ `state_rel (dec_clock 1 t') (dec_clock 1 r)` by fs [state_rel_def]
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
  \\ fs [state_rel_def]);

val evaluate_remove_ticks_thm =
  evaluate_remove_ticks
  |> SIMP_RULE std_ss []
  |> Q.SPEC `[Call 0 (SOME start) []]`
  |> SIMP_RULE std_ss [remove_ticks_def];

val evaluate_compile_prog = Q.store_thm ("evaluate_compile_prog",
  `evaluate ([Call 0 (SOME start) []], [],
             initial_state ffi0 (map
                (I ## (λx. HD (remove_ticks [x]))) prog) k) = (r, s) ⇒
   ∃ck (s2:'ffi bvlSem$state).
     evaluate
      ([Call 0 (SOME start) []], [],
        initial_state ffi0 prog (k + ck)) = (r, s2) ∧
     s2.ffi = s.ffi`,
  strip_tac
  \\ drule (ONCE_REWRITE_RULE [CONJ_COMM]
             (REWRITE_RULE [CONJ_ASSOC] evaluate_remove_ticks_thm))
  \\ disch_then (qspec_then `initial_state ffi0 prog k` mp_tac)
  \\ impl_tac THEN1 fs [state_rel_def]
  \\ strip_tac \\ fs []
  \\ qexists_tac `ck` \\ fs [state_rel_def]);

val FST_EQ_LEMMA = prove(
  ``FST x = y <=> ?y1. x = (y,y1)``,
  Cases_on `x` \\ fs []);

val compile_prog_semantics = Q.store_thm ("compile_prog_semantics",
  `semantics ffi (map (I ## (λx. HD (remove_ticks [x]))) prog) start =
   semantics ffi prog start`,
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
      \\ qpat_x_assum `evaluate (_,_,_ _ (_ prog) _) = _` kall_tac
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
      \\ Cases_on `s.ffi.final_event` \\ fs []
      >-
        (Cases_on `s'.ffi.final_event` \\ fs []
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
        \\ fs [state_rel_def] \\ rveq)
      \\ qpat_x_assum `∀extra._` mp_tac
      \\ first_x_assum (qspec_then `k'` assume_tac)
      \\ first_assum (subterm (fn tm =>
            Cases_on`^(assert has_pair_type tm)`) o concl)
      \\ fs []
      \\ unabbrev_all_tac
      \\ strip_tac
      \\ drule (GEN_ALL evaluate_compile_prog)
      \\ strip_tac \\ rveq \\ fs []
      \\ reverse (Cases_on `s'.ffi.final_event`) \\ fs [] \\ rfs []
      >-
        (first_x_assum (qspec_then `ck + k` mp_tac)
        \\ fs [ADD1]
        \\ strip_tac \\ fs [state_rel_def] \\ rfs [])
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
      \\ rveq \\ fs [] \\ rfs [])
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
    \\ reverse (Cases_on `rr.ffi.final_event`)
    >-
      (first_x_assum
        (qspecl_then
          [`k`, `FFI_outcome(THE rr.ffi.final_event)`] mp_tac)
      \\ simp [])
    \\ qpat_x_assum `∀x y. ¬z` mp_tac \\ simp []
    \\ qexists_tac `k` \\ simp []
    \\ reverse (Cases_on `s.ffi.final_event`) \\ fs []
    >-
      (qhdtm_x_assum `evaluate` mp_tac
      \\ qmatch_assum_abbrev_tac `bvlSem$evaluate (opts1,[],os1) = (r,_)`
      \\ qspecl_then [`opts1`,`[]`,`os1`] mp_tac evaluate_add_to_clock_io_events_mono
      \\ disch_then (qspec_then `ck` mp_tac)
      \\ fs [ADD1, inc_clock_def, Abbr`os1`]
      \\ rpt strip_tac \\ fs []
      \\ fs [state_rel_def] \\ rfs [])
    \\ qhdtm_x_assum `evaluate` mp_tac
    \\ imp_res_tac evaluate_add_clock
    \\ pop_assum mp_tac
    \\ impl_tac
    >- (strip_tac \\ fs [])
    \\ disch_then (qspec_then `ck` mp_tac)
    \\ simp [inc_clock_def]
    \\ fs [ADD1]
    \\ rpt strip_tac \\ rveq \\ fs [])
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
         bviPropsTheory.initial_state_with_simp,
         bvlPropsTheory.initial_state_with_simp,
         bviPropsTheory.evaluate_add_to_clock_io_events_mono
           |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["s"]))
           |> Q.SPEC`s with clock := k`
           |> SIMP_RULE (srw_ss())[bviPropsTheory.inc_clock_def],
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
            (map (I ## (λx. HD (remove_ticks [x]))) prog) k))`
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
  \\ simp [EL_APPEND1]);

val remove_ticks_CONS = prove(
  ``!xs x. remove_ticks (x::xs) =
           HD (remove_ticks [x]) :: remove_ticks xs``,
  Cases \\ fs [remove_ticks_def]);

(* inline implementation *)

val tick_inline_def = tDefine "tick_inline" `
  (tick_inline cs [] = []) /\
  (tick_inline cs (x::y::xs) =
     HD (tick_inline cs [x]) :: tick_inline cs (y::xs)) /\
  (tick_inline cs [Var v] = [Var v]) /\
  (tick_inline cs [If x1 x2 x3] =
     [If (HD (tick_inline cs [x1]))
         (HD (tick_inline cs [x2]))
         (HD (tick_inline cs [x3]))]) /\
  (tick_inline cs [Let xs x2] =
     [Let (tick_inline cs xs)
           (HD (tick_inline cs [x2]))]) /\
  (tick_inline cs [Raise x1] =
     [Raise (HD (tick_inline cs [x1]))]) /\
  (tick_inline cs [Handle x1 x2] =
     [Handle (HD (tick_inline cs [x1]))
              (HD (tick_inline cs [x2]))]) /\
  (tick_inline cs [Op op xs] =
     [Op op (tick_inline cs xs)]) /\
  (tick_inline cs [Tick x] =
     [Tick (HD (tick_inline cs [x]))]) /\
  (tick_inline cs [Call ticks dest xs] =
     case dest of NONE => [Call ticks dest (tick_inline cs xs)] | SOME n =>
     case lookup n cs of
     | NONE => [Call ticks dest (tick_inline cs xs)]
     | SOME (arity,code) => [Let (tick_inline cs xs) (mk_tick (SUC ticks) code)])`
  (WF_REL_TAC `measure (exp1_size o SND)`);

val tick_inline_ind = theorem"tick_inline_ind";

val tick_inline_all_def = Define `
  (tick_inline_all limit cs [] aux = (cs,REVERSE aux)) /\
  (tick_inline_all limit cs ((n,arity,e1)::xs) aux =
     let e2 = HD (tick_inline cs [e1]) in
     let cs2 = if must_inline n limit e2 then insert n (arity,e2) cs else cs in
       tick_inline_all limit cs2 xs ((n,arity,e2)::aux))`;

val tick_compile_prog_def = Define `
  tick_compile_prog limit prog = tick_inline_all limit LN prog []`

val LENGTH_tick_inline = Q.store_thm("LENGTH_tick_inline",
  `!cs xs. LENGTH (tick_inline cs xs) = LENGTH xs`,
  recInduct tick_inline_ind \\ REPEAT STRIP_TAC
  \\ fs [Once tick_inline_def,LET_DEF] \\ rw [] \\ every_case_tac \\ fs []);

val HD_tick_inline = Q.store_thm("HD_tick_inline[simp]",
  `[HD (tick_inline cs [x])] = tick_inline cs [x]`,
  `LENGTH (tick_inline cs [x]) = LENGTH [x]` by SRW_TAC [] [LENGTH_tick_inline]
  \\ Cases_on `tick_inline cs [x]` \\ FULL_SIMP_TAC std_ss [LENGTH]
  \\ Cases_on `t` \\ FULL_SIMP_TAC std_ss [LENGTH,HD] \\ `F` by DECIDE_TAC);

val tick_code_rel_def = Define `
  tick_code_rel (:'ffi) c1 c2 <=>
    !n arity e1.
      lookup n c1 = SOME (arity,e1) ==>
      ?e2. lookup n c2 = SOME (arity,e2) /\
           !(s:'ffi bvlSem$state) env res t.
             LENGTH env = arity /\ res <> Rerr (Rabort Rtype_error) /\
             evaluate ([e1],env,s with code := c1) = (res,t with code := c1) ==>
             evaluate ([e2],env,s with code := c2) = (res,t with code := c2)`

val tick_code_rel_refl = Q.store_thm("tick_code_rel_refl",
  `!c. tick_code_rel (:'ffi) c c`,
  fs [tick_code_rel_def]);

val tick_code_rel_trans = Q.store_thm("tick_code_rel_trans",
  `!c1 c2 c3.
      tick_code_rel (:'ffi) c1 c2 /\ tick_code_rel (:'ffi) c2 c3 ==>
      tick_code_rel (:'ffi) c1 c3`,
  fs [tick_code_rel_def] \\ rw [] \\ res_tac
  \\ first_x_assum drule \\ rw [] \\ fs []);

val exp_rel_def = Define `
  exp_rel (:'ffi) c e1 e2 <=>
    !(s:'ffi bvlSem$state) env res t.
      evaluate ([e1],env,s) = (res,t) /\ s.code = c /\
      res <> Rerr (Rabort Rtype_error) ==>
      evaluate ([e2],env,s) = (res,t)`

val evaluate_code_insert = Q.store_thm("evaluate_code_insert",
  `!xs env (s:'ffi bvlSem$state) res t e1 e2 n arity c.
      evaluate (xs,env,s) = (res,t) /\
      exp_rel (:'ffi) (insert n (arity,e2) c) e1 e2 /\
      res ≠ Rerr (Rabort Rtype_error) /\
      lookup n c = SOME (arity,e1) /\
      s.code = c ==>
      evaluate (xs,env,s with code := insert n (arity,e2) c) =
                  (res,t with code := insert n (arity,e2) c)`,
  recInduct bvlSemTheory.evaluate_ind \\ reverse (rw [])
  \\ fs [bvlSemTheory.evaluate_def]
  THEN1 (* Call *)
   (Cases_on `evaluate (xs,env,s1)` \\ fs []
    \\ `q <> Rerr (Rabort Rtype_error)` by (rpt strip_tac \\ fs [])
    \\ fs [] \\ first_x_assum drule
    \\ disch_then drule \\ fs []
    \\ Cases_on `q` \\ fs [] \\ rw []
    \\ Cases_on `find_code dest a (insert n (arity,e2) s1.code) =
                 find_code dest a r.code` \\ fs []
    THEN1
     (BasicProvers.TOP_CASE_TAC \\ fs []
      \\ PairCases_on `x` \\ fs [] \\ IF_CASES_TAC \\ fs [] \\ rw [] \\ fs []
      \\ rfs [] \\ imp_res_tac evaluate_code \\ fs [])
    \\ reverse (Cases_on `dest`) \\ fs [] THEN1
     (fs [find_code_def,lookup_insert]
      \\ Cases_on `lookup x r.code` \\ fs []
      \\ Cases_on `x'` \\ fs []
      \\ Cases_on `LENGTH a = q` \\ fs []
      \\ Cases_on `x = n` \\ fs []
      \\ rveq \\ fs [] \\ imp_res_tac evaluate_code \\ fs []
      \\ IF_CASES_TAC \\ fs [] \\ rveq \\ fs []
      \\ first_x_assum drule
      \\ disch_then drule
      \\ fs [exp_rel_def] \\ rw [])
    \\ fs [find_code_def,lookup_insert] \\ IF_CASES_TAC \\ fs []
    \\ Cases_on `LAST a` \\ fs []
    \\ Cases_on `lookup n' r.code` \\ fs []
    \\ PairCases_on `x` \\ fs []
    \\ Cases_on `LENGTH a = x0 + 1` \\ fs []
    \\ Cases_on `n' = n` \\ fs []
    \\ fs [] \\ rveq \\ fs [] \\ imp_res_tac evaluate_code \\ fs []
    \\ IF_CASES_TAC \\ fs [] \\ rveq \\ fs []
    \\ first_x_assum drule
    \\ disch_then drule
    \\ fs [exp_rel_def] \\ rw [])
  \\ TRY (IF_CASES_TAC \\ fs [] \\ fs [] \\ NO_TAC)
  THEN1
   (Cases_on `evaluate (xs,env,s)` \\ fs []
    \\ `q <> Rerr (Rabort Rtype_error)` by (rpt strip_tac \\ fs [])
    \\ fs [] \\ imp_res_tac evaluate_code \\ fs []
    \\ first_x_assum drule
    \\ disch_then drule \\ fs []
    \\ Cases_on `q` \\ fs []
    \\ Cases_on `do_app op (REVERSE a) r` \\ fs []
    \\ TRY (Cases_on `a'` \\ fs [] \\ rveq \\ fs []) \\ rveq \\ fs []
    \\ TRY (drule (GEN_ALL bvlPropsTheory.do_app_with_code) ORELSE
            drule (GEN_ALL bvlPropsTheory.do_app_with_code_err))
    \\ disch_then (qspec_then `insert n (arity,e2) s.code` mp_tac)
    \\ (impl_tac THEN1 fs [domain_insert,SUBSET_DEF])
    \\ rw [] \\ fs [])
  \\ TRY
   (Cases_on `evaluate ([x1],env,s)` \\ fs []
    \\ `q <> Rerr (Rabort Rtype_error)` by (rpt strip_tac \\ fs [])
    \\ Cases_on `q` \\ fs [] \\ rveq \\ fs [] \\ NO_TAC)
  \\ TRY
   (Cases_on `evaluate ([x1],env,s1)` \\ fs []
    \\ `q <> Rerr (Rabort Rtype_error)` by (rpt strip_tac \\ fs [])
    \\ Cases_on `q` \\ fs [] \\ rveq \\ fs [] \\ NO_TAC)
  THEN1
   (Cases_on `evaluate ([x1],env,s1)` \\ fs []
    \\ `q <> Rerr (Rabort Rtype_error)` by (rpt strip_tac \\ fs [])
    \\ Cases_on `q` \\ fs [] \\ rveq \\ fs []
    \\ every_case_tac \\ fs [] \\ rfs []
    \\ first_x_assum drule \\ fs []
    \\ imp_res_tac evaluate_code \\ fs [])
  THEN1
   (Cases_on `evaluate (xs,env,s)` \\ fs []
    \\ `q <> Rerr (Rabort Rtype_error)` by (rpt strip_tac \\ fs [])
    \\ Cases_on `q` \\ fs [] \\ rveq \\ fs []
    \\ first_x_assum drule \\ fs []
    \\ imp_res_tac evaluate_code \\ fs [])
  THEN1
   (Cases_on `evaluate ([x1],env,s)` \\ fs []
    \\ `q <> Rerr (Rabort Rtype_error)` by (rpt strip_tac \\ fs [])
    \\ Cases_on `q` \\ fs [] \\ rveq \\ fs []
    \\ rpt (IF_CASES_TAC \\ fs [])
    \\ first_x_assum drule \\ fs []
    \\ imp_res_tac evaluate_code \\ fs [])
  THEN1
   (Cases_on `evaluate ([x],env,s)` \\ fs []
    \\ `q <> Rerr (Rabort Rtype_error)` by (rpt strip_tac \\ fs [])
    \\ Cases_on `q` \\ fs [] \\ rveq \\ fs []
    \\ Cases_on `evaluate (y::xs,env,r)` \\ fs []
    \\ first_x_assum drule \\ fs []
    \\ imp_res_tac evaluate_code \\ fs []
    \\ Cases_on `q` \\ fs [] \\ rveq \\ fs []));

val tick_code_rel_insert = Q.store_thm("tick_code_rel_insert",
  `lookup n c = SOME (arity,e1) /\
    exp_rel (:'ffi) (insert n (arity,e2) c) e1 e2 ==>
    tick_code_rel (:'ffi) c (insert n (arity,e2) c)`,
  fs [tick_code_rel_def] \\ rw [lookup_insert] \\ rw [] \\ fs [] \\ rw []
  \\ TRY (drule evaluate_code_insert \\ fs [] \\ NO_TAC)
  \\ drule evaluate_code_insert \\ fs []
  \\ disch_then drule \\ fs [] \\ rw []
  \\ qpat_x_assum `exp_rel (:'ffi) _ e1 e2` (fn th => mp_tac th \\ assume_tac th)
  \\ simp_tac std_ss [exp_rel_def]
  \\ disch_then drule \\ fs []);

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

fun split_tac q = Cases_on q \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [];

val evaluate_tick_inline = Q.store_thm("evaluate_tick_inline",
  `!cs xs s env.
     subspt cs s.code /\
     FST (evaluate (xs,env,s)) <> Rerr(Rabort Rtype_error) ==>
     (evaluate (tick_inline cs xs,env,s) = evaluate (xs,env,s))`,
  recInduct tick_inline_ind \\ reverse (REPEAT STRIP_TAC)
  \\ POP_ASSUM MP_TAC \\ SIMP_TAC std_ss [Once tick_inline_def,LET_DEF] \\ RES_TAC
  THEN1
   (Cases_on `dest` \\ fs [] THEN1
     (ONCE_REWRITE_TAC [evaluate_def] \\ ASM_SIMP_TAC std_ss [HD_tick_inline]
      \\ Cases_on `evaluate (xs,env,s)` \\ FULL_SIMP_TAC std_ss []
      \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF])
    \\ Cases_on `lookup x cs` \\ fs [] THEN1
     (ONCE_REWRITE_TAC [evaluate_def] \\ ASM_SIMP_TAC std_ss [HD_tick_inline]
      \\ Cases_on `evaluate (xs,env,s)` \\ FULL_SIMP_TAC std_ss []
      \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF])
    \\ rename1 `lookup x cs = SOME args`
    \\ PairCases_on `args` \\ fs []
    \\ ONCE_REWRITE_TAC [evaluate_def] \\ ASM_SIMP_TAC std_ss [HD_tick_inline]
    \\ Cases_on `evaluate (xs,env,s)` \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `q` \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF]
    \\ IMP_RES_TAC evaluate_code
    \\ `lookup x s.code = SOME (args0,args1)` by fs [subspt_def,domain_lookup]
    \\ fs [find_code_def]
    \\ IMP_RES_TAC evaluate_IMP_LENGTH \\ fs []
    \\ IF_CASES_TAC \\ fs []
    \\ SIMP_TAC std_ss [evaluate_mk_tick] \\ SRW_TAC [] [] \\ fs [ADD1]
    \\ MATCH_MP_TAC evaluate_expand_env \\ FULL_SIMP_TAC std_ss [])
  \\ TRY (Cases_on `b`)
  \\ ONCE_REWRITE_TAC [evaluate_def] \\ ASM_SIMP_TAC std_ss [HD_tick_inline]
  \\ TRY (SRW_TAC [] [] \\ FIRST_X_ASSUM MATCH_MP_TAC
          \\ FULL_SIMP_TAC (srw_ss()) [dec_clock_def] \\ NO_TAC)
  \\ TRY (split_tac `evaluate (xs,env,s)`
     \\ IMP_RES_TAC evaluate_code \\ FULL_SIMP_TAC (srw_ss()) [] \\ NO_TAC)
  \\ TRY (split_tac `evaluate ([x1],env,s)` \\ SRW_TAC [] []
     \\ IMP_RES_TAC evaluate_code \\ FULL_SIMP_TAC (srw_ss()) []
     \\ Cases_on`e`>>fs[]>>NO_TAC)
  THEN (Cases_on `tick_inline cs (y::xs)` THEN1
      (`LENGTH (tick_inline cs (y::xs)) = 0` by METIS_TAC [LENGTH]
       \\ FULL_SIMP_TAC std_ss [LENGTH_tick_inline,LENGTH] \\ `F` by DECIDE_TAC)
     \\ SIMP_TAC std_ss [Once evaluate_def,HD_tick_inline]
     \\ POP_ASSUM (fn th => FULL_SIMP_TAC std_ss [GSYM th])
     \\ split_tac `evaluate ([x],env,s)` \\ split_tac `evaluate (y::xs,env,r)`
     \\ IMP_RES_TAC evaluate_code \\ FULL_SIMP_TAC (srw_ss()) []));

val exp_rel_tick_inline = Q.store_thm("exp_rel_tick_inline",
  `subspt cs c ==> exp_rel (:'ffi) c e (HD (tick_inline cs [e]))`,
  fs [exp_rel_def] \\ rw []
  \\ qpat_x_assum `_ = (_,_)` (fn th => assume_tac th THEN
        once_rewrite_tac [GSYM th])
  \\ match_mp_tac evaluate_tick_inline \\ fs []);

val tick_code_rel_insert_tick_inline = Q.store_thm("tick_code_rel_insert_tick_inline",
  `lookup n c = SOME (arity,e1) /\ subspt cs c /\ ~(n IN domain cs) ==>
    tick_code_rel (:'ffi) c (insert n (arity,(HD (tick_inline cs [e1]))) c)`,
  rw [] \\ match_mp_tac tick_code_rel_insert \\ fs []
  \\ match_mp_tac exp_rel_tick_inline
  \\ fs [subspt_def,domain_lookup,PULL_EXISTS,lookup_insert]
  \\ rw [] \\ res_tac \\ fs []);

val tick_code_rel_insert_insert_tick_inline = Q.store_thm("tick_code_rel_insert_insert_tick_inline",
  `subspt cs (insert n (arity,e1) c) /\ ~(n IN domain cs) ==>
    tick_code_rel (:'ffi) (insert n (arity,e1) c)
                          (insert n (arity,(HD (tick_inline cs [e1]))) c)`,
  `insert n (arity,HD (tick_inline cs [e1])) c =
   insert n (arity,HD (tick_inline cs [e1])) (insert n (arity,e1) c)` by fs [insert_shadow]
  \\ pop_assum (fn th => once_rewrite_tac [th]) \\ rw []
  \\ match_mp_tac tick_code_rel_insert_tick_inline \\ fs []);

val tick_inline_all_acc = Q.store_thm("tick_inline_all_acc",
  `!xs ys cs limit.
      SND (tick_inline_all limit cs xs ys) =
      REVERSE ys ++ SND (tick_inline_all limit cs xs [])`,
  Induct \\ fs [tick_inline_all_def] \\ strip_tac \\ PairCases_on `h` \\ fs []
  \\ once_rewrite_tac [tick_inline_all_def] \\ simp_tac std_ss [LET_THM]
  \\ rpt strip_tac \\ IF_CASES_TAC
  \\ qpat_x_assum `!x._` (fn th => once_rewrite_tac [th]) \\ fs []);

val fromAList_SWAP = Q.prove(
  `!xs x ys.
      ALL_DISTINCT (FST x::MAP FST xs) ==>
      fromAList (xs ++ x::ys) = fromAList (x::(xs ++ ys))`,
  Induct \\ fs [] \\ rw []
  \\ PairCases_on `h` \\ fs [fromAList_def]
  \\ PairCases_on `x` \\ fs [fromAList_def]
  \\ fs [spt_eq_thm,wf_insert,wf_fromAList]
  \\ rw [lookup_insert]);

val tick_code_rel_rearrange_lemma = Q.store_thm("tick_code_rel_rearrange_lemma",
  `ALL_DISTINCT (FST x::MAP FST xs) /\
    MAP FST zs = MAP FST xs /\
    tick_code_rel (:'ffi) (fromAList (xs++x::ys)) (fromAList (zs++x::ys)) ==>
    tick_code_rel (:'ffi) (fromAList (x::(xs++ys))) (fromAList (x::(zs++ys))) `,
  metis_tac [fromAList_SWAP,APPEND]);

val MAP_FST_tick_inline_all = Q.store_thm("MAP_FST_tick_inline_all",
  `!xs cs. MAP FST (SND (tick_inline_all limit cs xs [])) = MAP FST xs`,
  Induct \\ fs [tick_inline_all_def] \\ strip_tac
  \\ PairCases_on `h` \\ fs [tick_inline_all_def] \\ rw []
  \\ once_rewrite_tac [tick_inline_all_acc] \\ fs []);

val MEM_IMP_ALOOKUP_SOME = Q.store_thm("MEM_IMP_ALOOKUP_SOME",
  `!xs x y.
      ALL_DISTINCT (MAP FST xs) /\ MEM (x,y) xs ==>
      ALOOKUP xs x = SOME y`,
  Induct \\ fs [FORALL_PROD] \\ rw []
  \\ res_tac \\ fs [MEM_MAP,FORALL_PROD] \\ rfs []);

val tick_code_rel_tick_inline_all = Q.store_thm("tick_code_rel_tick_inline_all",
  `!xs ys cs.
      (!x y. lookup x cs = SOME y ==> MEM (x,y) ys /\ !y. ~MEM (x,y) xs) /\
      ALL_DISTINCT (MAP FST (ys ++ xs)) ==>
      tick_code_rel (:'ffi)
        (fromAList (xs ++ ys))
        (fromAList (SND (tick_inline_all limit cs xs []) ++ ys))`,
  Induct \\ fs [tick_inline_all_def,tick_code_rel_refl]
  \\ strip_tac \\ PairCases_on `h` \\ fs []
  \\ reverse (rw [tick_inline_all_def])
  \\ once_rewrite_tac [tick_inline_all_acc] \\ fs []
  \\ qpat_abbrev_tac `zs = tick_inline_all limit _ xs []`
  \\ match_mp_tac tick_code_rel_trans
  \\ qexists_tac `fromAList ((h0,h1,HD (tick_inline cs [h2]))::(xs ++ ys))`
  \\ rpt strip_tac
  \\ TRY
   (fs [fromAList_def]
    \\ match_mp_tac tick_code_rel_insert_insert_tick_inline
    \\ fs [domain_lookup,subspt_def,PULL_EXISTS,lookup_insert]
    \\ reverse (rpt strip_tac) THEN1 (res_tac \\ fs [])
    \\ IF_CASES_TAC \\ fs [] \\ rveq THEN1 (res_tac \\ fs [])
    \\ qexists_tac `v` \\ fs [] \\ res_tac
    \\ fs [lookup_fromAList]
    \\ match_mp_tac MEM_IMP_ALOOKUP_SOME \\ fs []
    \\ fs [ALL_DISTINCT_APPEND] \\ metis_tac [])
  \\ match_mp_tac tick_code_rel_rearrange_lemma \\ fs []
  \\ unabbrev_all_tac \\ fs [MAP_FST_tick_inline_all]
  \\ fs [ALL_DISTINCT_APPEND,ALL_DISTINCT]
  \\ first_x_assum match_mp_tac
  \\ fs [ALL_DISTINCT_APPEND,ALL_DISTINCT]
  \\ (reverse conj_tac THEN1 metis_tac [])
  THEN1 metis_tac []
  \\ fs [lookup_insert] \\ rw []
  \\ fs [MEM_MAP,FORALL_PROD,PULL_EXISTS]
  \\ Cases_on `y'` \\ fs [])
  |> Q.SPECL [`xs`,`[]`] |> SIMP_RULE std_ss [APPEND_NIL];

val tick_code_rel_tick_compile_prog = Q.store_thm("tick_code_rel_tick_compile_prog",
  `ALL_DISTINCT (MAP FST prog) ==>
    tick_code_rel (:'ffi) (fromAList prog)
       (fromAList (SND (tick_compile_prog limit prog)))`,
  fs [tick_compile_prog_def] \\ rw [tick_code_rel_refl]
  \\ match_mp_tac tick_code_rel_tick_inline_all \\ fs [lookup_def]);

val tick_code_rel_IMP_semantics_EQ = Q.store_thm("tick_code_rel_IMP_semantics_EQ",
  `!(ffi:'ffi ffi_state) c1 c2 start.
      tick_code_rel (:'ffi) c1 c2 /\ semantics ffi c1 start <> Fail ==>
      semantics ffi c2 start = semantics ffi c1 start`,
  rewrite_tac [GSYM AND_IMP_INTRO]
  \\ ntac 5 strip_tac \\ simp[bvlSemTheory.semantics_def]
  \\ IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
  `∀k. evaluate ([Call 0 (SOME start) []],[],initial_state ffi c2 k) =
    let (r,s) = bvlSem$evaluate ([Call 0 (SOME start) []],
         [],initial_state ffi c1 k) in
      (r, s with code := c2)` by
   (fs [evaluate_def,find_code_def]
    \\ Cases_on `lookup start c1` \\ fs []
    \\ PairCases_on `x` \\ fs []
    \\ IF_CASES_TAC \\ fs [] \\ rveq
    \\ strip_tac \\ fs [tick_code_rel_def]
    \\ first_x_assum drule \\ strip_tac \\ fs [LENGTH_NIL]
    \\ IF_CASES_TAC \\ fs []
    \\ qpat_x_assum `!x. _ <> _` (qspec_then `k` mp_tac) \\ fs [] \\ rw []
    \\ Cases_on `evaluate ([x1],[],dec_clock 1 (initial_state ffi c1 k))`
    \\ fs [] \\ first_x_assum drule
    \\ disch_then (qspec_then `dec_clock 1 (initial_state ffi c1 k)` mp_tac)
    \\ `dec_clock 1 (initial_state ffi c1 k) with code := c1 =
        dec_clock 1 (initial_state ffi c1 k) /\
        dec_clock 1 (initial_state ffi c1 k) with code := c2 =
        dec_clock 1 (initial_state ffi c2 k)` by
          fs [dec_clock_def,initial_state_def]
    \\ fs [] \\ disch_then (qspec_then `r` mp_tac)
    \\ impl_tac THEN1
     (imp_res_tac evaluate_code
      \\ fs [dec_clock_def,initial_state_def,bvlSemTheory.state_component_equality])
    \\ fs [])
  \\ simp []
  \\ qpat_x_assum `tick_code_rel (:'ffi) _ _` kall_tac
  \\ DEEP_INTRO_TAC some_intro >> simp[] >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  full_simp_tac(srw_ss())[UNCURRY,LET_THM] >>
  reverse conj_tac >- (
    simp_tac(srw_ss()++QUANT_INST_ss[pair_default_qp])[] ) >>
  gen_tac >> strip_tac >> var_eq_tac >>
  asm_simp_tac(srw_ss()++QUANT_INST_ss[pair_default_qp])[] >>
  reverse conj_tac >- METIS_TAC[] >>
  gen_tac >> strip_tac >>
  strip_tac >> full_simp_tac(srw_ss())[] >>
  qpat_abbrev_tac`abb2 = bvlSem$evaluate _` >>
  qpat_abbrev_tac`abb1 = bvlSem$evaluate _` >>
  qmatch_assum_abbrev_tac`Abbrev(abb2 = evaluate (e1,v1,s1))` >>
  qmatch_assum_abbrev_tac`Abbrev(abb1 = evaluate (e1,v1,s2))` >>
  map_every qunabbrev_tac[`abb1`,`abb2`] >>
  qmatch_assum_rename_tac`Abbrev(s1 = _ _ _ k1)` >>
  qmatch_assum_rename_tac`Abbrev(s2 = _ _ _ k2)` >>
  (fn g => subterm(fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g) >> full_simp_tac(srw_ss())[] >>
  (fn g => subterm(fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g) >> full_simp_tac(srw_ss())[] >>
  Q.ISPECL_THEN[`e1`,`v1`,`s1`]mp_tac bvlPropsTheory.evaluate_add_to_clock_io_events_mono >>
  disch_then(qspec_then`k2`mp_tac) >>
  Q.ISPECL_THEN[`e1`,`v1`,`s2`]mp_tac bvlPropsTheory.evaluate_add_to_clock_io_events_mono >>
  disch_then(qspec_then`k1`mp_tac) >>
  simp[bvlPropsTheory.inc_clock_def,Abbr`s1`,Abbr`s2`] >>
  ntac 2 strip_tac >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  imp_res_tac bvlPropsTheory.evaluate_add_clock >>
  rpt(first_x_assum (fn th => mp_tac th >> impl_tac >- (strip_tac >> full_simp_tac(srw_ss())[]))) >>
  simp[bvlPropsTheory.inc_clock_def] >>
  TRY (
    disch_then(qspec_then`k1`strip_assume_tac) >>
    disch_then(qspec_then`k2`strip_assume_tac) >>
    fsrw_tac[ARITH_ss][bvlSemTheory.state_component_equality] ) >>
  TRY (
    qexists_tac`k1` >>
    spose_not_then strip_assume_tac >> full_simp_tac(srw_ss())[] >> NO_TAC) >>
  TRY (
    qexists_tac`k2` >>
    spose_not_then strip_assume_tac >> fsrw_tac[ARITH_ss][] >>
    rev_full_simp_tac(srw_ss())[] >> NO_TAC) >>
  srw_tac[][] >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[]);

val tick_compile_prog_semantics = save_thm("tick_compile_prog_semantics",
  MATCH_MP (tick_code_rel_IMP_semantics_EQ |> REWRITE_RULE [GSYM AND_IMP_INTRO])
   (tick_code_rel_tick_compile_prog |> UNDISCH) |> SPEC_ALL
  |> DISCH_ALL |> REWRITE_RULE [AND_IMP_INTRO]);

val MAP_FST_tick_compile_prog = Q.store_thm("MAP_FST_tick_compile_prog",
  `MAP FST (SND (tick_compile_prog limit prog)) = MAP FST prog`,
  fs [tick_compile_prog_def] \\ rw [MAP_FST_tick_inline_all]);

val semantics_tick_inline =
  MATCH_MP (tick_code_rel_IMP_semantics_EQ |> REWRITE_RULE [GSYM AND_IMP_INTRO])
   (tick_code_rel_insert_insert_tick_inline |> UNDISCH) |> SPEC_ALL
  |> DISCH_ALL |> REWRITE_RULE [AND_IMP_INTRO];

(* let_op *)

val HD_let_op = store_thm("HD_let_op[simp]",
  ``[HD (let_op [x])] = let_op [x]``,
  Cases_on `x` \\ simp_tac std_ss [let_op_def] \\ fs []
  \\ CASE_TAC \\ fs []);

val let_opt_def = Define `
  let_opt split_seq cut_size (arity, prog) =
    (arity, optimise split_seq cut_size arity (let_op_sing prog))`

val evaluate_let_op = store_thm("evaluate_let_op",
  ``!es env s res t.
      evaluate (es,env,s) = (res,t) /\ res ≠ Rerr (Rabort Rtype_error) ==>
      evaluate
        (let_op es,env,s with code := map (let_opt split_seq cut_size) s.code) =
        (res,t with code := map (let_opt split_seq cut_size) s.code)``,
  recInduct evaluate_ind \\ rw [] \\ fs [let_op_def]
  \\ fs [evaluate_def]
  THEN1
   (once_rewrite_tac [evaluate_CONS]
    \\ Cases_on `evaluate ([x],env,s)` \\ fs []
    \\ Cases_on `q` \\ fs [] \\ rveq \\ fs []
    \\ Cases_on `evaluate (y::xs,env,r)` \\ fs []
    \\ Cases_on `q` \\ fs [] \\ rveq \\ fs []
    \\ imp_res_tac evaluate_SING \\ fs [] \\ rveq \\ fs []
    \\ imp_res_tac evaluate_code \\ fs [])
  THEN1 (rw [] \\ fs [])
  THEN1
   (Cases_on `evaluate ([x1],env,s)` \\ fs []
    \\ Cases_on `q` \\ fs [] \\ rveq \\ fs []
    \\ imp_res_tac evaluate_SING \\ fs [] \\ rveq \\ fs []
    \\ rw [] \\ fs [] \\ rfs []
    \\ imp_res_tac evaluate_code \\ fs [])
  THEN1
   (TOP_CASE_TAC \\ fs [] THEN1
     (Cases_on `evaluate (xs,env,s)` \\ fs [evaluate_def]
      \\ Cases_on `q` \\ fs [] \\ rveq \\ fs []
      \\ imp_res_tac evaluate_code \\ fs [])
    \\ Cases_on `evaluate (xs,env,s)` \\ fs [evaluate_def]
    \\ Cases_on `q` \\ fs [] \\ rveq \\ fs []
    \\ `?d. let_op [x2] = [d]` by
       (Cases_on `x2` \\ fs [let_op_def] \\ CASE_TAC \\ fs [])
    \\ rveq \\ fs []
    \\ Cases_on `d` \\ fs [dest_op_def] \\ rveq
    \\ fs [evaluate_def]
    \\ drule (Q.GENL [`l`,`a`,`env`,`s`] var_list_IMP_evaluate)
    \\ disch_then (qspecl_then [`a`,`env`] assume_tac)
    \\ imp_res_tac evaluate_IMP_LENGTH \\ fs []
    \\ imp_res_tac evaluate_code \\ fs [])
  THEN1
   (Cases_on `evaluate ([x1],env,s)` \\ fs []
    \\ Cases_on `q` \\ fs [] \\ rveq \\ fs [])
  THEN1
   (Cases_on `evaluate ([x1],env,s1)` \\ fs []
    \\ Cases_on `q` \\ fs [] \\ rveq \\ fs []
    \\ Cases_on `e` \\ fs [] \\ rveq \\ fs []
    \\ imp_res_tac evaluate_code \\ fs [])
  THEN1
   (Cases_on `evaluate (xs,env,s)` \\ fs []
    \\ Cases_on `q` \\ fs [] \\ rveq \\ fs []
    \\ Cases_on `do_app op (REVERSE a) r` \\ fs []
    \\ imp_res_tac evaluate_code
    THEN1
     (Cases_on `a'`
      \\ imp_res_tac do_app_with_code
      \\ pop_assum (qspec_then `map (let_opt split_seq cut_size) s.code` mp_tac)
      \\ fs [domain_map])
    \\ rveq \\ fs []
    \\ imp_res_tac do_app_with_code_err
    \\ pop_assum (qspec_then `map (let_opt split_seq cut_size) s.code` mp_tac)
    \\ fs [domain_map])
  THEN1
   (Cases_on `evaluate ([x],env,s)` \\ fs []
    \\ Cases_on `q` \\ fs [] \\ rveq \\ fs []
    \\ imp_res_tac evaluate_code \\ fs [] \\ rw [] \\ fs [])
  \\ Cases_on `evaluate (xs,env,s1)` \\ fs []
  \\ Cases_on `q` \\ fs [] \\ rveq \\ fs []
  \\ imp_res_tac evaluate_code \\ fs []
  \\ Cases_on `find_code dest a s1.code` \\ fs []
  \\ PairCases_on `x` \\ fs []
  \\ `find_code dest a (map (let_opt split_seq cut_size) s1.code) =
        SOME (x0,optimise split_seq cut_size (LENGTH x0) (let_op_sing x1))` by
   (Cases_on `dest` \\ fs [find_code_def]
    \\ every_case_tac \\ fs [] \\ rveq \\ fs [lookup_map,let_opt_def]
    \\ `?x xs. a = SNOC x xs` by metis_tac [SNOC_CASES]
    \\ full_simp_tac std_ss [FRONT_SNOC,LENGTH_SNOC,LAST_SNOC,ADD1])
  \\ fs [] \\ rw [] \\ fs []
  \\ fs [state_component_equality,optimise_def]
  \\ match_mp_tac bvl_handleProofTheory.compile_any_correct \\ fs []
  \\ qsuff_tac `[let_op_sing x1] = let_op [x1]` \\ rw [] \\ fs []
  \\ fs [let_op_sing_def]
  \\ Cases_on `x1` \\ fs [let_op_def]
  \\ rpt (pop_assum kall_tac) \\ every_case_tac \\ fs []);

val map_let_op = prove(
  ``semantics ffi prog start <> Fail ==>
    semantics ffi (map (let_opt split_seq cut_size) prog) start =
    semantics ffi prog start``,
  match_mp_tac (REWRITE_RULE [GSYM AND_IMP_INTRO] tick_code_rel_IMP_semantics_EQ)
  \\ fs [tick_code_rel_def,lookup_map,let_opt_def] \\ rw []
  \\ fs [optimise_def]
  \\ match_mp_tac bvl_handleProofTheory.compile_any_correct \\ fs []
  \\ drule evaluate_let_op \\ fs []
  \\ fs [let_op_sing_def]
  \\ qsuff_tac `?d. let_op [e1] = [d]` \\ rw [] \\ fs [] \\ rfs []
  \\ Cases_on `e1` \\ fs [let_op_def] \\ every_case_tac \\ fs []);

(* combined theorems *)

val remove_ticks_mk_tick = prove(
  ``!n r. remove_ticks [mk_tick n r] = remove_ticks [r]``,
  Induct THEN1 (EVAL_TAC \\ fs [])
  \\ fs [bvlTheory.mk_tick_def,FUNPOW,remove_ticks_def]);

val remove_ticks_tick_inline = prove(
  ``!cs xs.
      inline (map (I ## (λx. HD (remove_ticks [x]))) cs) xs =
      remove_ticks (tick_inline cs xs)``,
  ho_match_mp_tac inline_ind \\ rw []
  \\ fs [tick_inline_def,remove_ticks_def,inline_def]
  THEN1 (once_rewrite_tac [EQ_SYM_EQ] \\ simp [Once remove_ticks_CONS])
  \\ TOP_CASE_TAC \\ fs [tick_inline_def,remove_ticks_def,inline_def]
  \\ Cases_on `lookup x cs` \\ fs [lookup_map]
  \\ fs [tick_inline_def,remove_ticks_def,inline_def]
  \\ Cases_on `x'` \\ fs []
  \\ fs [remove_ticks_def,remove_ticks_mk_tick]);

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

val tick_inline_all_rel = prove(
  ``!prog cs xs.
      MAP (I ## let_opt_remove b l)
        (SND (tick_inline_all limit cs prog xs)) =
      SND (inline_all limit b l (map (I ## (λx. HD (remove_ticks [x]))) cs)
        prog (MAP (I ## let_opt_remove b l) xs))``,
  Induct
  \\ fs [tick_inline_all_def,inline_all_def,MAP_REVERSE,FORALL_PROD]
  \\ fs [remove_ticks_tick_inline,must_inline_remove_ticks]
  \\ rw [] \\ fs [map_insert,optimise_def,let_opt_remove_def,let_opt_def])
  |> Q.SPECL [`prog`,`LN`,`[]`]
  |> SIMP_RULE std_ss [MAP,map_def] |> GSYM
  |> REWRITE_RULE [GSYM compile_prog_def];

val map_fromAList_HASH = prove(
  ``map f (fromAList ls) = fromAList (MAP (I ## f) ls)``,
  fs [map_fromAList]
  \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
  \\ fs [FUN_EQ_THM,FORALL_PROD]);

val compile_prog_semantics = store_thm("compile_prog_semantics",
  ``ALL_DISTINCT (MAP FST prog) /\
    semantics ffi (fromAList prog) start <> Fail ==>
    semantics ffi (fromAList (SND (bvl_inline$compile_prog limit b l prog))) start =
    semantics ffi (fromAList prog) start``,
  fs [tick_inline_all_rel] \\ rw []
  \\ drule (tick_compile_prog_semantics |> UNDISCH_ALL
      |> SIMP_RULE std_ss [Once (GSYM compile_prog_semantics)]
      |> DISCH_ALL |> ONCE_REWRITE_RULE [CONJ_COMM]) \\ fs []
  \\ disch_then (fn th => fs [GSYM th])
  \\ qmatch_goalsub_abbrev_tac `MAP ff`
  \\ `ff = (I ## let_opt b l) o (I ## I ## \x. (HD (remove_ticks [x])))`
       by fs [FUN_EQ_THM,Abbr `ff`,FORALL_PROD,let_opt_remove_def]
  \\ fs [GSYM MAP_MAP_o]
  \\ fs [GSYM map_fromAList_HASH,tick_compile_prog_def]
  \\ ntac 2 (pop_assum kall_tac)
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ qpat_assum `_` (fn th => CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [GSYM th])))
  \\ match_mp_tac (GSYM map_let_op) \\ fs []);

val map_fromAList = store_thm("map_fromAList",
  ``!xs f. map f (fromAList xs) = fromAList (MAP (I ## f) xs)``,
  Induct \\ fs [fromAList_def,fromAList_def,FORALL_PROD,map_insert]);

val inline_all_acc = Q.store_thm("inline_all_acc",
  `!xs ys cs limit.
      SND (inline_all limit b l cs xs ys) =
      REVERSE ys ++ SND (inline_all limit b l cs xs [])`,
  Induct \\ fs [inline_all_def] \\ strip_tac \\ PairCases_on `h` \\ fs []
  \\ once_rewrite_tac [inline_all_def] \\ simp_tac std_ss [LET_THM]
  \\ rpt strip_tac \\ IF_CASES_TAC
  \\ qpat_x_assum `!x._` (fn th => once_rewrite_tac [th]) \\ fs []);

val MAP_FST_inline_all = Q.store_thm("MAP_FST_inline_all",
  `!xs cs. MAP FST (SND (inline_all limit b l cs xs [])) = MAP FST xs`,
  Induct \\ fs [inline_all_def] \\ strip_tac
  \\ PairCases_on `h` \\ fs [inline_all_def] \\ rw []
  \\ once_rewrite_tac [inline_all_acc] \\ fs []);

val MAP_FST_compile_prog = Q.store_thm("MAP_FST_compile_prog",
  `MAP FST (SND (compile_prog limit b l prog)) = MAP FST prog`,
  fs [bvl_inlineTheory.compile_prog_def] \\ rw [MAP_FST_inline_all]);

val handle_ok_inline_all = prove(
  ``!prog cs aux.
      handle_ok (MAP (SND o SND) aux) ==>
      handle_ok (MAP (SND o SND)
        (SND (inline_all limit split_seq cut_size cs prog aux)))``,
  Induct
  \\ fs [inline_all_def,FORALL_PROD] \\ rw []
  \\ rpt (pop_assum mp_tac)
  \\ once_rewrite_tac [bvl_handleProofTheory.handle_ok_EVERY]
  \\ fs [EVERY_REVERSE,EVERY_MAP] \\ rw []
  \\ first_x_assum match_mp_tac
  \\ fs [optimise_def,bvl_handleProofTheory.compile_any_handle_ok])
  |> Q.SPECL [`p`,`c`,`[]`]
  |> REWRITE_RULE [MAP,bvl_handleProofTheory.handle_ok_def];

val compile_prog_handle_ok = store_thm("compile_prog_handle_ok",
  ``compile_prog l b i prog = (inlines,prog3) ==>
    handle_ok (MAP (SND o SND) prog3)``,
  fs [compile_prog_def]
  \\ metis_tac [handle_ok_inline_all,PAIR,FST,SND]);

val _ = export_theory();
