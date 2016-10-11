open preamble
open set_sepTheory helperLib semanticPrimitivesTheory
open cfHeapsBaseTheory cfHeapsTheory cfHeapsBaseLib cfStoreTheory cfNormalizeTheory
open cfTacticsBaseLib cfHeapsLib
open funBigStepTheory

val _ = new_theory "cfApp"

val _ = temp_type_abbrev("state",``:'ffi semanticPrimitives$state``);

(*------------------------------------------------------------------*)
(** App: [app] is used to give a specification for the application of
    a value to one or multiple value arguments. It is in particular
    used in cf to abstract from the concrete representation of
    closures.
*)

val evaluate_ck_def = Define `
  evaluate_ck ck (st: 'ffi state) = evaluate (st with clock := ck)`

(* [app_basic]: application with one argument *)
val app_basic_def = Define `
  app_basic (p:'ffi ffi_proj) (f: v) (x: v) (H: hprop) (Q: res -> hprop) =
    !(h_i: heap) (h_k: heap) (st: 'ffi state).
      SPLIT (st2heap p st) (h_i, h_k) ==> H h_i ==>
      ?env exp (r: res) (h_f: heap) (h_g: heap) (st': 'ffi state) ck.
        SPLIT3 (st2heap p st') (h_f, h_k, h_g) /\
        Q r h_f /\
        do_opapp [f;x] = SOME (env, exp) /\
        case r of
          | Val v' => evaluate_ck ck st env [exp] = (st', Rval [v'])
          | Exn e  => evaluate_ck ck st env [exp] = (st', Rerr (Rraise e))`

val app_basic_local = prove (
  ``!f x. is_local (app_basic p f x)``,
  simp [is_local_def] \\ rpt strip_tac \\
  irule EQ_EXT \\ qx_gen_tac `H` \\ irule EQ_EXT \\ qx_gen_tac `Q` \\
  eq_tac \\ fs [local_elim] \\
  simp [local_def] \\ strip_tac \\ simp [app_basic_def] \\ rpt strip_tac \\
  first_assum progress \\
  qpat_assum `(H1 * H2) h_i` (strip_assume_tac o REWRITE_RULE [STAR_def]) \\
  fs [] \\ rename1 `H1 h_i_1` \\ rename1 `H2 h_i_2` \\
  qpat_assum `app_basic _ _ _ _ _` (mp_tac o REWRITE_RULE [app_basic_def]) \\
  disch_then (qspecl_then [`h_i_1`, `h_k UNION h_i_2`, `st`] mp_tac) \\
  impl_tac THEN1 SPLIT_TAC \\ disch_then progress \\
  rename1 `Q1 r' h_f_1` \\
  qpat_x_assum `_ ==+> _` mp_tac \\
  disch_then (mp_tac o REWRITE_RULE [SEP_IMPPOST_def, STARPOST_def]) \\
  disch_then (mp_tac o REWRITE_RULE [SEP_IMP_def]) \\
  disch_then (qspecl_then [`r'`, `h_f_1 UNION h_i_2`] mp_tac) \\ simp [] \\
  impl_tac
  THEN1 (simp [STAR_def] \\ Q.LIST_EXISTS_TAC [`h_f_1`, `h_i_2`] \\ SPLIT_TAC) \\
  disch_then (assume_tac o REWRITE_RULE [STAR_def]) \\ fs [] \\
  instantiate \\ rename1 `GC h_g'` \\ qexists_tac `h_g' UNION h_g` \\
  SPLIT_TAC
);

(* [app]: n-ary application *)
val app_def = Define `
  app (p:'ffi ffi_proj) (f: v) ([]: v list) (H: hprop) (Q: res -> hprop) = F /\
  app (p:'ffi ffi_proj) f [x] H Q = app_basic p f x H Q /\
  app (p:'ffi ffi_proj) f (x::xs) H Q =
    app_basic p f x H
      (POSTv g. SEP_EXISTS H'. H' * cond (app p g xs H' Q))`

val app_alt_ind = store_thm ("app_alt_ind",
  ``!f xs x H Q.
     xs <> [] ==>
     app (p:'ffi ffi_proj) f (xs ++ [x]) H Q =
     app (p:'ffi ffi_proj) f xs H
       (POSTv g. SEP_EXISTS H'. H' * cond (app_basic p g x H' Q))``,
  Induct_on `xs` \\ fs [] \\ rpt strip_tac \\
  Cases_on `xs` \\ fs [app_def]
);

val app_alt_ind_w = store_thm ("app_alt_ind_w",
  ``!f xs x H Q.
     app (p:'ffi ffi_proj) f (xs ++ [x]) H Q ==> xs <> [] ==>
     app (p:'ffi ffi_proj) f xs H
       (POSTv g. SEP_EXISTS H'. H' * cond (app_basic (p:'ffi ffi_proj) g x H' Q))``,
  rpt strip_tac \\ fs [app_alt_ind]
)

val app_ge_2_unfold = store_thm ("app_ge_2_unfold",
  ``!f x xs H Q.
      xs <> [] ==>
      app (p:'ffi ffi_proj) f (x::xs) H Q =
      app_basic p f x H (POSTv g. SEP_EXISTS H'. H' * cond (app p g xs H' Q))``,
  rpt strip_tac \\ Cases_on `xs` \\ fs [app_def]
);

val app_ge_2_unfold_extens = store_thm ("app_ge_2_unfold_extens",
  ``!f x xs.
      xs <> [] ==>
      app (p:'ffi ffi_proj) f (x::xs) =
      \H Q. app_basic p f x H (POSTv g. SEP_EXISTS H'. H' * cond (app p g xs H' Q))``,
  rpt strip_tac \\ NTAC 2 (irule EQ_EXT \\ gen_tac) \\ fs [app_ge_2_unfold]
);

(* Weaken-frame-gc for [app]; auxiliary lemma for [app_local] *)

val app_wgframe = store_thm ("app_wgframe",
  ``!f xs H H1 H2 Q1 Q.
      app (p:'ffi ffi_proj) f xs H1 Q1 ==>
      H ==>> (H1 * H2) ==>
      (Q1 *+ H2) ==+> (Q *+ GC) ==>
      app p f xs H Q``,
  NTAC 2 gen_tac \\ Q.SPEC_TAC (`f`, `f`) \\
  Induct_on `xs` THEN1 (fs [app_def]) \\ rpt strip_tac \\ rename1 `x::xs` \\
  Cases_on `xs = []`
  THEN1 (
    fs [app_def] \\ irule local_frame_gc THEN1 (fs [app_basic_local]) \\
    instantiate
  )
  THEN1 (
    fs [app_ge_2_unfold] \\ irule local_frame THEN1 (fs [app_basic_local]) \\
    instantiate \\ simp [SEP_IMPPOST_def, STARPOST_def] \\ qx_gen_tac `r` \\
    Cases_on `r` \\ simp [POSTv_def] \\ hpull \\ hsimpl \\
    qx_gen_tac `HR` \\ strip_tac \\ qexists_tac `HR * H2` \\ hsimpl \\
    first_assum irule \\ instantiate \\ hsimpl
  )
);

val app_weaken = store_thm ("app_weaken",
  ``!f xs H Q Q'.
      app (p:'ffi ffi_proj) f xs H Q ==>
      Q ==+> Q' ==>
      app p f xs H Q'``,
  rpt strip_tac \\ irule app_wgframe \\ instantiate \\ fs [SEP_IMPPOST_def] \\
  rpt (hsimpl \\ TRY hinst) \\ simp [GC_def] \\ hsimpl \\
  gen_tac \\ qexists_tac `emp` \\ hsimpl \\ fs []
);

val app_local = store_thm ("app_local",
  ``!f xs. xs <> [] ==> is_local (app (p:'ffi ffi_proj) f xs)``,
  rpt strip_tac \\ irule is_local_prove \\ rpt strip_tac \\
  Cases_on `xs` \\ fs [] \\ rename1 `x1::xs` \\
  Cases_on `xs` \\ fs []
  THEN1 (
    `!x. app p f [x] = app_basic p f x` by
      (gen_tac \\ NTAC 2 (irule EQ_EXT \\ gen_tac) \\ fs [app_def]) \\
    fs [Once (REWRITE_RULE [is_local_def] app_basic_local)]
  )
  THEN1 (
    rename1 `x1::x2::xs` \\ simp [app_ge_2_unfold_extens] \\
    eq_tac \\ strip_tac THEN1 (irule local_elim \\ fs []) \\
    simp [Once (REWRITE_RULE [is_local_def] app_basic_local)] \\
    fs [local_def] \\ rpt strip_tac \\ first_x_assum progress \\
    rename1 `(H1 * H2) h` \\ instantiate \\ simp [SEP_IMPPOST_def] \\
    Cases \\ simp [STARPOST_def, POSTv_def] \\ hsimpl \\
    qx_gen_tac `H'` \\ strip_tac \\ qexists_tac `H' * H2` \\ hsimpl \\
    irule app_wgframe \\ instantiate \\ hsimpl
  )
);

(* [curried (p:'ffi ffi_proj) n f] states that [f] is curried [n] times *)
val curried_def = Define `
  curried (p:'ffi ffi_proj) (n: num) (f: v) =
    case n of
     | 0 => F
     | SUC 0 => T
     | SUC n =>
       !x. app_basic (p:'ffi ffi_proj) f x emp
             (POSTv g. cond (curried (p:'ffi ffi_proj) n g /\
                  !xs H Q.
                    LENGTH xs = n ==>
                    app (p:'ffi ffi_proj) f (x::xs) H Q ==>
                    app (p:'ffi ffi_proj) g xs H Q))`;

val curried_ge_2_unfold = store_thm ("curried_ge_2_unfold",
  ``!n f.
      n > 1 ==>
      curried (p:'ffi ffi_proj) n f =
      !x. app_basic p f x emp
            (POSTv g. cond (curried p (PRE n) g /\
                 !xs H Q.
                   LENGTH xs = PRE n ==>
                   app p f (x::xs) H Q ==> app p g xs H Q))``,
  rpt strip_tac \\ Cases_on `n` \\ fs [] \\ rename1 `SUC n > 1` \\
  Cases_on `n` \\ fs [Once curried_def]
);

(* app_over_app / app_over_take *)

(** When [curried n f] holds and the number of the arguments [xs] is less than
    [n], then [app f xs] is a function [g] such that [app g ys] has the same
    behavior as [app f (xs++ys)]. *)
(*
val app_partial = prove (
  ``!n xs f. curried (p:'ffi ffi_proj) n f ==> (0 < LENGTH xs /\ LENGTH xs < n) ==>
    app (p:'ffi ffi_proj) f xs emp (\g. cond (
      curried (p:'ffi ffi_proj) (n - LENGTH xs) g /\
      !ys H Q. (LENGTH xs + LENGTH ys = n) ==>
        app (p:'ffi ffi_proj) f (xs ++ ys) H Q ==> app (p:'ffi ffi_proj) g ys H Q))``,
  completeInduct_on `n` \\ Cases_on `n`
  THEN1 (rpt strip_tac \\ fs [])

  THEN1 (
    Cases_on `xs` \\ rpt strip_tac \\ fs [] \\
    rename1 `x::zs` \\ rename1 `LENGTH zs < n` \\
    Cases_on `zs` \\ fs []

    THEN1 (
      (* xs = x :: zs = [x] *)
      fs [app_def] \\ cheat
    )
    THEN1 (
      (* xs = x :: zs = [x::y::t] *)
      rename1 `x::y::t` \\ fs [app_def] \\ cheat
    )
  )
)
*)

(*------------------------------------------------------------------*)
(** Packaging *)

(* [spec (p:'ffi ffi_proj) f n P] asserts that [curried (p:'ffi ffi_proj) f n] is true and
that [P] is a valid specification for [f]. Useful for conciseness and
tactics. *)
val spec_def = Define `
  spec (p:'ffi ffi_proj) f n P = (curried (p:'ffi ffi_proj) n f /\ P)`

(*------------------------------------------------------------------*)
(* Relating [app] to [_ --> _] from the translator *)

val app_basic_weaken = store_thm("app_basic_weaken",
  ``(!x v. P x v ==> Q x v) ==>
    (app_basic p v v1 x P ==>
     app_basic p v v1 x Q)``,
  fs [app_basic_def] \\ metis_tac []);

val evaluate_list_SING = prove(
  ``bigStep$evaluate_list b env st [exp] (st', Rval [v]) <=>
    bigStep$evaluate b env st exp (st', Rval v)``,
  simp [Once bigStepTheory.evaluate_cases, PULL_EXISTS]
  \\ once_rewrite_tac [CONJ_COMM]
  \\ simp [Once bigStepTheory.evaluate_cases, PULL_EXISTS]);

val evaluate_list_raise_SING = prove(
  ``bigStep$evaluate_list b env st [exp] (st', Rerr (Rraise v)) <=>
    bigStep$evaluate b env st exp (st', Rerr (Rraise v))``,
  simp [Once bigStepTheory.evaluate_cases, PULL_EXISTS]
  \\ eq_tac \\ fs [] \\ strip_tac
  \\ pop_assum (assume_tac o
                SIMP_RULE std_ss [Once bigStepTheory.evaluate_cases])
  \\ fs []);

val app_basic_rel = store_thm("app_basic_rel",
  ``app_basic (p:'ffi ffi_proj) (f: v) (x: v) (H: hprop) (Q: res -> hprop) =
    !(h_i: heap) (h_k: heap) (st: 'ffi state).
      SPLIT (st2heap p st) (h_i, h_k) ==> H h_i ==>
      ?env exp (r: res) (h_f: heap) (h_g: heap) (st': 'ffi state).
        SPLIT3 (st2heap p st') (h_f, h_k, h_g) /\
        Q r h_f /\
        do_opapp [f;x] = SOME (env, exp) /\
        case r of
          | Val v' => bigStep$evaluate F env st exp (st', Rval v')
          | Exn e  => bigStep$evaluate F env st exp (st', Rerr (Rraise e))``,
  fs [app_basic_def,evaluate_ck_def,evaluate_list_SING,evaluate_list_raise_SING,
      funBigStepEquivTheory.functional_evaluate_list,
      bigClockTheory.big_clocked_unclocked_equiv,PULL_EXISTS]
  \\ rw [] \\ eq_tac \\ rw []
  \\ first_x_assum drule \\ fs [] \\ strip_tac
  \\ GEN_EXISTS_TAC "r" `r`
  \\ Cases_on `r` \\ fs []
  \\ rename1 `evaluate _ _ (_ with clock := ck) _ _` \\ fs []
  \\ try_finally
   (rename1 `SPLIT3 (st2heap p st1) (h_f,h_k,h_g)`
    \\ qabbrev_tac `st2 = st1 with clock := st.clock`
    \\ `SPLIT3 (st2heap p st2) (h_f,h_k,h_g)` by (fs [st2heap_def,Abbr `st2`] \\ NO_TAC)
    \\ rpt (asm_exists_tac \\ fs []) \\ fs [Abbr `st2`]
    \\ qexists_tac `ck - st1.clock`
    \\ drule bigClockTheory.clocked_min_counter \\ fs [])
  \\ try_finally
   (rewrite_tac [CONJ_ASSOC] \\ once_rewrite_tac [CONJ_COMM]
    \\ asm_exists_tac \\ fs []
    \\ fs [st2heap_def] \\ asm_exists_tac \\ fs []));

(* TODO: move to appropriate locations *)

val FFI_part_NOT_IN_store2heap = Q.store_thm("FFI_part_NOT_IN_store2heap",
  `FFI_part x1 x2 x3 ∉ store2heap refs`,
  rw[store2heap_def,FFI_part_NOT_IN_store2heap_aux]);

val store2heap_aux_MAPi = Q.store_thm("store2heap_aux_MAPi",
  `∀n s. store2heap_aux n s = set (MAPi (λi v. Mem (n+i) v) s)`,
  Induct_on`s`
  \\ rw[store2heap_aux_def,o_DEF,ADD1]
  \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
  \\ rw[FUN_EQ_THM]);

val store2heap_MAPi = Q.store_thm("store2heap_MAPi",
  `store2heap s = set (MAPi Mem s)`,
  rw[store2heap_def,store2heap_aux_MAPi]
  \\ srw_tac[ETA_ss][]);

val store2heap_aux_append_many = Q.store_thm("store2heap_aux_append_many",
  `∀s n x.
    store2heap_aux n (s ++ x) =
    store2heap_aux (n + LENGTH s) x ∪ store2heap_aux n s`,
  Induct \\ rw[store2heap_aux_def,ADD1,EXTENSION]
  \\ metis_tac[]);

val store2heap_append_many = Q.store_thm("store2heap_append_many",
  `∀s x.
    store2heap (s ++ x) = store2heap s ∪ store2heap_aux (LENGTH s) x`,
  rw[store2heap_def,store2heap_aux_append_many,UNION_COMM]);

val st2heap_with_refs_append = Q.store_thm("st2heap_with_refs_append",
  `st2heap p (st with refs := r1 ++ r2) =
   st2heap p (st with refs := r1) ∪ store2heap_aux (LENGTH r1) r2`,
  rw[st2heap_def,store2heap_append_many]
  \\ metis_tac[UNION_COMM,UNION_ASSOC]);

val POSTv_cond = Q.store_thm("POSTv_cond",
  `(POSTv v. &f v) r h ⇔ ∃v. r = Val v ∧ f v ∧ h = ∅`,
  rw[POSTv_def]
  \\ Cases_on`r` \\ fs[cond_def,EQ_IMP_THM]);

open terminationTheory funBigStepPropsTheory
val functional_evaluate = ml_translatorTheory.functional_evaluate
val evaluate_ffi_intro = ml_translatorTheory.evaluate_ffi_intro
val evaluate_empty_state_IMP = ml_translatorTheory.evaluate_empty_state_IMP

val big_remove_clock = Q.store_thm("big_remove_clock",
  `∀c ck env s e s' r.
     evaluate ck env s e (s',r) ∧
     r ≠ Rerr (Rabort Rtimeout_error)
     ⇒
     evaluate F env (s with clock := c) e (s' with clock := c,r)`,
  gen_tac \\ reverse Cases
  >- (
    rw[] \\
    imp_res_tac bigClockTheory.big_unclocked \\
    `∀s. s = s with clock := s.clock` by simp[state_component_equality] \\
    metis_tac[bigClockTheory.big_unclocked] ) \\
  rw[bigClockTheory.big_clocked_unclocked_equiv] \\
  metis_tac[bigClockTheory.clocked_min_counter]);

val evaluate_refs_length_mono = Q.store_thm("evaluate_refs_length_mono",`
  (∀(s:'a state) env e s' r.
     evaluate s env e = (s',r) ⇒ LENGTH s.refs ≤ LENGTH s'.refs) ∧
  (∀(s:'a state) env v pes errv s' r.
     evaluate_match s env v pes errv = (s',r) ⇒ LENGTH s.refs ≤ LENGTH s'.refs)`,
  ho_match_mp_tac evaluate_ind
  \\ rw[] \\ fs[evaluate_def]
  \\ every_case_tac \\ fs[] \\ rw[] \\ rfs[]
  \\ fs[dec_clock_def]
  \\ fs[evalPropsTheory.do_app_cases] \\ rw[]
  \\ fs[semanticPrimitivesTheory.store_alloc_def,semanticPrimitivesTheory.store_assign_def]
  \\ rw[]);

val big_refs_length_mono = Q.store_thm("big_refs_length_mono",
  `evaluate ck env s exp (s',r) ⇒ LENGTH s.refs ≤ LENGTH s'.refs`,
  Cases_on`ck`
  \\ rw[functional_evaluate]
  \\ fs[bigClockTheory.big_clocked_unclocked_equiv,functional_evaluate]
  \\ imp_res_tac evaluate_refs_length_mono
  \\ fs[]);

val SPLIT_st2heap_length_leq = Q.store_thm("SPLIT_st2heap_length_leq",
  `SPLIT (st2heap p s') (st2heap p s, h_g) ∧
   LENGTH s.refs ≤ LENGTH s'.refs ∧ s'.ffi = s.ffi ⇒
   s.refs ≼ s'.refs`,
  rw[SPLIT_def,st2heap_def]
  \\ `store2heap s'.refs = store2heap s.refs ∪ h_g`
  by (
    fs[EXTENSION]
    \\ reverse Cases \\ fs[FFI_part_NOT_IN_store2heap]
    >- (
      fs[IN_DISJOINT]
      \\ metis_tac[FFI_part_NOT_IN_store2heap] )
    \\ metis_tac[Mem_NOT_IN_ffi2heap] )
  \\ fs[IS_PREFIX_APPEND]
  \\ qexists_tac`DROP (LENGTH s.refs) s'.refs`
  \\ simp[LIST_EQ_REWRITE]
  \\ qx_gen_tac`n` \\ strip_tac
  \\ reverse(Cases_on`n < LENGTH s.refs`)
  >- ( simp[EL_APPEND2,EL_DROP] )
  \\ simp[EL_APPEND1]
  \\ fs[store2heap_MAPi,EXTENSION,MEM_MAPi]
  \\ first_x_assum(qspec_then`Mem n (EL n s.refs)`mp_tac)
  \\ simp[]);

val SPLIT_st2heap_ffi = Q.store_thm("SPLIT_st2heap_ffi",
  `SPLIT (st2heap p st') (st2heap p st, h_g) ⇒
   st'.ffi.io_events = st.ffi.io_events ∧
   st'.ffi.final_event = st.ffi.final_event`,
   cheat);

val SPLIT_st2heap_evaluate_ffi_same = Q.store_thm("SPLIT_st2heap_evaluate_ffi_same",
  `evaluate F env st exp (st',Rval res) ∧
   SPLIT (st2heap p st') (st2heap p st, h_g) ⇒
   st'.ffi = st.ffi`,
  rw[] \\
  imp_res_tac SPLIT_st2heap_ffi \\
  fs[bigClockTheory.big_clocked_unclocked_equiv] \\
  fs[functional_evaluate] \\
  imp_res_tac evaluate_io_events_mono_imp \\
  fs[io_events_mono_def] \\
  Cases_on`st.ffi.final_event` \\ fs[]);

val evaluate_imp_evaluate_empty_state = Q.store_thm("evaluate_imp_evaluate_empty_state",
  `evaluate F env s es (s',Rval r) ∧ s.refs ≼ s'.refs ∧ s'.ffi = s.ffi ∧ s.ffi.final_event = NONE ∧
   t = empty_state with <| refs := s.refs |> ∧
   t' = empty_state with <| refs := s'.refs |>
   ⇒
   evaluate F env t es (t',Rval r)`,
  rw[Once bigClockTheory.big_clocked_unclocked_equiv]
  \\ fs[functional_evaluate]
  \\ drule (REWRITE_RULE[GSYM AND_IMP_INTRO](
              INST_TYPE[beta|->oneSyntax.one_ty](
                CONJUNCT1 evaluate_ffi_intro)))
  \\ simp[]
  \\ disch_then(qspec_then`empty_state with <| clock := c; refs := s.refs |>`mp_tac)
  \\ simp[] \\ strip_tac
  \\ `Rval [r] = list_result ((Rval r):(v,v) result)` by EVAL_TAC
  \\ pop_assum SUBST_ALL_TAC
  \\ fs[GSYM functional_evaluate]
  \\ simp[bigClockTheory.big_clocked_unclocked_equiv]
  \\ asm_exists_tac \\ fs[]);

val Arrow_IMP_app_basic = store_thm("Arrow_IMP_app_basic",
  ``(Arrow a b) f v ==>
    !x v1.
      a x v1 ==>
      app_basic (p:'ffi ffi_proj) v v1 emp (POSTv v. &b (f x) v)``,
  fs [app_basic_def,emp_def,cfHeapsBaseTheory.SPLIT_emp1,
      ml_translatorTheory.Arrow_def,ml_translatorTheory.AppReturns_def,PULL_EXISTS]
  \\ fs [evaluate_ck_def, funBigStepEquivTheory.functional_evaluate_list]
  \\ rw []
  \\ first_x_assum drule \\ strip_tac
  \\ first_x_assum (qspec_then`st.refs`strip_assume_tac)
  \\ instantiate
  \\ simp [Once bigStepTheory.evaluate_cases, PULL_EXISTS]
  \\ simp [Once (CONJUNCT2 bigStepTheory.evaluate_cases)]
  \\ drule evaluate_empty_state_IMP \\ strip_tac
  \\ fs [bigClockTheory.big_clocked_unclocked_equiv]
  \\ rename1 `evaluate _ _ (st with clock := ck) _ _`
  \\ simp[POSTv_cond,PULL_EXISTS]
  \\ instantiate
  \\ fs[st2heap_clock]
  \\ fs[SPLIT3_emp1]
  \\ fs[st2heap_with_refs_append]
  \\ `st with refs := st.refs = st` by fs[state_component_equality]
  \\ pop_assum SUBST_ALL_TAC
  \\ qexists_tac`store2heap_aux (LENGTH st.refs) refs'`
  \\ fs[SPLIT_def]
  \\ fs[IN_DISJOINT]
  \\ Cases \\ fs[FFI_part_NOT_IN_store2heap_aux,st2heap_def,Mem_NOT_IN_ffi2heap]
  \\ spose_not_then strip_assume_tac
  \\ imp_res_tac store2heap_IN_LENGTH
  \\ imp_res_tac store2heap_aux_IN_bound
  \\ decide_tac);

val app_basic_IMP_Arrow = Q.store_thm("app_basic_IMP_Arrow",
  `(∀x v1. a x v1 ⇒ app_basic p v v1 emp (POSTv v. cond (b (f x) v))) ⇒ Arrow a b f v`,
  rw[app_basic_def,ml_translatorTheory.Arrow_def,ml_translatorTheory.AppReturns_def,emp_def,SPLIT_emp1] \\
  first_x_assum drule \\
  fs[evaluate_ck_def,funBigStepEquivTheory.functional_evaluate_list] \\
  fs[POSTv_cond,SPLIT3_emp1,PULL_EXISTS] \\
  disch_then( qspec_then`ARB with <| refs := refs; ffi := <| final_event := NONE |> |>` mp_tac) \\
  rw[] \\ instantiate \\
  fs[Once (CONJUNCT2 bigStepTheory.evaluate_cases)] \\
  fs[Once (CONJUNCT2 bigStepTheory.evaluate_cases)] \\ rw[] \\
  drule big_remove_clock \\ rw[] \\
  first_x_assum(qspec_then`0`strip_assume_tac) \\
  drule SPLIT_st2heap_evaluate_ffi_same \\
  fs[st2heap_clock] \\ strip_tac \\
  drule SPLIT_st2heap_length_leq \\ simp[] \\
  imp_res_tac big_refs_length_mono \\ fs[] \\
  rw[IS_PREFIX_APPEND] \\
  qexists_tac`l` \\
  match_mp_tac (INST_TYPE[alpha|->beta](GEN_ALL evaluate_imp_evaluate_empty_state)) \\
  instantiate);

val Arrow_eq_app_basic = Q.store_thm("Arrow_eq_app_basic",
  `Arrow a b f v ⇔ (∀x v1. a x v1 ⇒ app_basic p v v1 emp (POSTv v. &b (f x) v))`,
  metis_tac[Arrow_IMP_app_basic,app_basic_IMP_Arrow]);

val _ = export_theory ()
