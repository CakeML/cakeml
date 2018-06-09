open preamble
open set_sepTheory helperLib semanticPrimitivesTheory
open cfHeapsBaseTheory cfHeapsTheory cfHeapsBaseLib cfStoreTheory cfNormaliseTheory
open cfTacticsBaseLib cfHeapsLib

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

val evaluate_to_res_def = Define `
  evaluate_to_res st env exp st' (r:res) <=>
    case r of
    | Val v => (?ck. evaluate_ck ck st env [exp] = (st', Rval [v]))
    | Exn e => (?ck. evaluate_ck ck st env [exp] = (st', Rerr (Rraise e)))
    | Div =>   ?rel (sts: num->'ffi state) (cks: num->num).
                 (* clocks increase *)
                 (!i. cks i < cks (i+1)) /\
                 (* all clocks in the sequence produce timeout and a state in sts *)
                 (!i. evaluate_ck (cks i) st env [exp] =
                        (sts i, Rerr (Rabort Rtimeout_error))) /\
                 (* relation rel relates each state in the sts sequence *)
                 (!i. rel (sts i) (sts (i+1))) /\
                 (* the limit state st' approximates all states in the sequence *)
                 (!i. rel (sts i) st')`

(* [app_basic]: application with one argument *)
val app_basic_def = Define `
  app_basic (p:'ffi ffi_proj) (f: v) (x: v) (H: hprop) (Q: res -> hprop) =
    !(h_i: heap) (h_k: heap) (st: 'ffi state).
      SPLIT (st2heap p st) (h_i, h_k) ==> H h_i ==>
      ?env exp (r: res) (h_f: heap) (h_g: heap) (st': 'ffi state).
        SPLIT3 (st2heap p st') (h_f, h_k, h_g) /\
        do_opapp [f;x] = SOME (env, exp) /\
        Q r h_f /\ evaluate_to_res st env exp st' r`;

val app_basic_local = Q.prove (
  `!f x. is_local (app_basic p f x)`,
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

val app_alt_ind = Q.store_thm ("app_alt_ind",
  `!f xs x H Q.
     xs <> [] ==>
     app (p:'ffi ffi_proj) f (xs ++ [x]) H Q =
     app (p:'ffi ffi_proj) f xs H
       (POSTv g. SEP_EXISTS H'. H' * cond (app_basic p g x H' Q))`,
  Induct_on `xs` \\ fs [] \\ rpt strip_tac \\
  Cases_on `xs` \\ fs [app_def]
);

val app_alt_ind_w = Q.store_thm ("app_alt_ind_w",
  `!f xs x H Q.
     app (p:'ffi ffi_proj) f (xs ++ [x]) H Q ==> xs <> [] ==>
     app (p:'ffi ffi_proj) f xs H
       (POSTv g. SEP_EXISTS H'. H' * cond (app_basic (p:'ffi ffi_proj) g x H' Q))`,
  rpt strip_tac \\ fs [app_alt_ind]
)

val app_ge_2_unfold = Q.store_thm ("app_ge_2_unfold",
  `!f x xs H Q.
      xs <> [] ==>
      app (p:'ffi ffi_proj) f (x::xs) H Q =
      app_basic p f x H (POSTv g. SEP_EXISTS H'. H' * cond (app p g xs H' Q))`,
  rpt strip_tac \\ Cases_on `xs` \\ fs [app_def]
);

val app_ge_2_unfold_extens = Q.store_thm ("app_ge_2_unfold_extens",
  `!f x xs.
      xs <> [] ==>
      app (p:'ffi ffi_proj) f (x::xs) =
      \H Q. app_basic p f x H (POSTv g. SEP_EXISTS H'. H' * cond (app p g xs H' Q))`,
  rpt strip_tac \\ NTAC 2 (irule EQ_EXT \\ gen_tac) \\ fs [app_ge_2_unfold]
);

(* Weaken-frame-gc for [app]; auxiliary lemma for [app_local] *)

val app_wgframe = Q.store_thm ("app_wgframe",
  `!f xs H H1 H2 Q1 Q.
      app (p:'ffi ffi_proj) f xs H1 Q1 ==>
      H ==>> (H1 * H2) ==>
      (Q1 *+ H2) ==+> (Q *+ GC) ==>
      app p f xs H Q`,
  NTAC 2 gen_tac \\ Q.SPEC_TAC (`f`, `f`) \\
  Induct_on `xs` THEN1 (fs [app_def]) \\ rpt strip_tac \\ rename1 `x::xs` \\
  Cases_on `xs = []`
  THEN1 (
    fs [app_def] \\ irule local_frame_gc \\ rpt conj_tac
    THEN1 fs [app_basic_local] \\
    instantiate
  )
  THEN1 (
    fs [app_ge_2_unfold] \\ irule local_frame \\ rpt conj_tac
    THEN1 (fs [app_basic_local]) \\
    instantiate \\ simp [SEP_IMPPOST_def, STARPOST_def] \\ qx_gen_tac `r` \\
    Cases_on `r` \\ simp [POSTv_def] \\ hpull \\ hsimpl \\
    qx_gen_tac `HR` \\ strip_tac \\ qexists_tac `HR * H2` \\ hsimpl \\
    first_assum irule \\ instantiate \\ hsimpl
  )
);

val app_weaken = Q.store_thm ("app_weaken",
  `!f xs H Q Q'.
      app (p:'ffi ffi_proj) f xs H Q ==>
      Q ==+> Q' ==>
      app p f xs H Q'`,
  rpt strip_tac \\ irule app_wgframe \\ instantiate \\ fs [SEP_IMPPOST_def] \\
  rpt (hsimpl \\ TRY hinst) \\ simp [GC_def] \\ hsimpl \\
  gen_tac \\ qexists_tac `emp` \\ hsimpl \\ fs []
);

val app_local = Q.store_thm ("app_local",
  `!f xs. xs <> [] ==> is_local (app (p:'ffi ffi_proj) f xs)`,
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

val curried_ge_2_unfold = Q.store_thm ("curried_ge_2_unfold",
  `!n f.
      n > 1 ==>
      curried (p:'ffi ffi_proj) n f =
      !x. app_basic p f x emp
            (POSTv g. cond (curried p (PRE n) g /\
                 !xs H Q.
                   LENGTH xs = PRE n ==>
                   app p f (x::xs) H Q ==> app p g xs H Q))`,
  rpt strip_tac \\ Cases_on `n` \\ fs [] \\ rename1 `SUC n > 1` \\
  Cases_on `n` \\ fs [Once curried_def]
);

(* app_over_app / app_over_take *)

(** When [curried n f] holds and the number of the arguments [xs] is less than
    [n], then [app f xs] is a function [g] such that [app g ys] has the same
    behavior as [app f (xs++ys)]. *)
(*
val app_partial = Q.prove (
  `!n xs f. curried (p:'ffi ffi_proj) n f ==> (0 < LENGTH xs /\ LENGTH xs < n) ==>
    app (p:'ffi ffi_proj) f xs emp (\g. cond (
      curried (p:'ffi ffi_proj) (n - LENGTH xs) g /\
      !ys H Q. (LENGTH xs + LENGTH ys = n) ==>
        app (p:'ffi ffi_proj) f (xs ++ ys) H Q ==> app (p:'ffi ffi_proj) g ys H Q))`,
  completeInduct_on `n` \\ Cases_on `n`
  THEN1 (rpt strip_tac \\ fs [])

  THEN1 (
    Cases_on `xs` \\ rpt strip_tac \\ fs [] \\
    rename1 `x::zs` \\ rename1 `LENGTH zs < n` \\
    Cases_on `zs` \\ fs []

    THEN1 (
      (* xs = x :: zs = [x] *)
      fs [app_def] \\ ...
    )
    THEN1 (
      (* xs = x :: zs = [x::y::t] *)
      rename1 `x::y::t` \\ fs [app_def] \\ ..
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

val app_basic_weaken = Q.store_thm("app_basic_weaken",
  `(!x v. P x v ==> Q x v) ==>
    (app_basic p v v1 x P ==>
     app_basic p v v1 x Q)`,
  fs [app_basic_def] \\ metis_tac []);

val evaluate_list_SING = Q.prove(
  `bigStep$evaluate_list b env st [exp] (st', Rval [v]) <=>
    bigStep$evaluate b env st exp (st', Rval v)`,
  simp [Once bigStepTheory.evaluate_cases, PULL_EXISTS]
  \\ once_rewrite_tac [CONJ_COMM]
  \\ simp [Once bigStepTheory.evaluate_cases, PULL_EXISTS]);

val evaluate_list_raise_SING = Q.prove(
  `bigStep$evaluate_list b env st [exp] (st', Rerr (Rraise v)) <=>
    bigStep$evaluate b env st exp (st', Rerr (Rraise v))`,
  simp [Once bigStepTheory.evaluate_cases, PULL_EXISTS]
  \\ eq_tac \\ fs [] \\ strip_tac
  \\ pop_assum (assume_tac o
                SIMP_RULE std_ss [Once bigStepTheory.evaluate_cases])
  \\ fs []);

(*
val app_basic_rel = Q.store_thm("app_basic_rel",
  `app_basic (p:'ffi ffi_proj) (f: v) (x: v) (H: hprop) (Q: res -> hprop) =
    !(h_i: heap) (h_k: heap) (st: 'ffi state).
      SPLIT (st2heap p st) (h_i, h_k) ==> H h_i ==>
      ?env exp (r: res) (h_f: heap) (h_g: heap) (st': 'ffi state).
        SPLIT3 (st2heap p st') (h_f, h_k, h_g) /\
        Q r h_f /\
        do_opapp [f;x] = SOME (env, exp) /\
        case r of
          | Val v' => bigStep$evaluate F env st exp (st', Rval v')
          | Exn e  => bigStep$evaluate F env st exp (st', Rerr (Rraise e))`,
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
*)

(* TODO: move to appropriate locations *)

val FFI_part_NOT_IN_store2heap = Q.store_thm("FFI_part_NOT_IN_store2heap",
  `FFI_part x1 x2 x3 x4 ∉ store2heap refs`,
  rw[store2heap_def,FFI_part_NOT_IN_store2heap_aux]);

val FFI_full_NOT_IN_store2heap = Q.store_thm("FFI_full_NOT_IN_store2heap",
  `FFI_full x1 x2 ∉ store2heap refs`,
  rw[store2heap_def,FFI_full_NOT_IN_store2heap_aux]);

val FFI_split_NOT_IN_store2heap = Q.store_thm("FFI_split_NOT_IN_store2heap",
  `FFI_split ∉ store2heap refs`,
  rw[store2heap_def,FFI_split_NOT_IN_store2heap_aux]);

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

open terminationTheory evaluatePropsTheory
val dec_clock_def = evaluateTheory.dec_clock_def
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
  \\ fs[semanticPrimitivesPropsTheory.do_app_cases] \\ rw[]
  \\ fs[semanticPrimitivesTheory.store_alloc_def,semanticPrimitivesTheory.store_assign_def]
  \\ rw[]);

val big_refs_length_mono = Q.store_thm("big_refs_length_mono",
  `evaluate ck env s exp (s',r) ⇒ LENGTH s.refs ≤ LENGTH s'.refs`,
  Cases_on`ck`
  \\ rw[funBigStepEquivTheory.functional_evaluate]
  \\ fs[bigClockTheory.big_clocked_unclocked_equiv,funBigStepEquivTheory.functional_evaluate]
  \\ imp_res_tac evaluate_refs_length_mono
  \\ fs[]);

val SPLIT_st2heap_length_leq = Q.store_thm("SPLIT_st2heap_length_leq",
  `SPLIT (st2heap p s') (st2heap p s, h_g) ∧
   LENGTH s.refs ≤ LENGTH s'.refs ∧ s'.ffi = s.ffi ⇒
   s.refs ≼ s'.refs`,
  rw[SPLIT_def,st2heap_def]
  \\ `store2heap s'.refs = store2heap s.refs ∪ h_g` by (
    fs[EXTENSION]
    \\ reverse Cases \\ fs[FFI_part_NOT_IN_store2heap]
    \\ fs[IN_DISJOINT]
    \\ metis_tac[Mem_NOT_IN_ffi2heap,FFI_part_NOT_IN_store2heap,
                 FFI_split_NOT_IN_store2heap,
                 FFI_full_NOT_IN_store2heap])
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

val forall_cases = Q.prove(
  `(!x. P x) <=> (!x1 x2. P (Mem x1 x2)) /\
                  (P FFI_split) /\
                  (!x3 x4 x2 x1. P (FFI_part x1 x2 x3 x4)) /\
                  (!x1 x2. P (FFI_full x1 x2))`,
  EQ_TAC \\ rw [] \\ Cases_on `x` \\ fs []);

val SPLIT_UNION_IMP_SUBSET = Q.prove(
  `SPLIT x (y UNION y1,y2) ==> y1 SUBSET x`,
  SPLIT_TAC);

val FILTER_ffi_has_index_in_EQ_NIL = Q.prove(
  `~(MEM n xs) /\ EVERY (ffi_has_index_in xs) ys ==>
    FILTER (ffi_has_index_in [n]) ys = []`,
  Induct_on `ys` \\ fs [] \\ rw [] \\ fs []
  \\ Cases_on `h` \\ fs [ffi_has_index_in_def] \\ rw []
  \\ CCONTR_TAC \\ fs [] \\ fs []);

val FILTER_ffi_has_index_in_MEM = Q.prove(
  `!ys zs xs x.
      MEM x xs /\
      FILTER (ffi_has_index_in xs) ys = FILTER (ffi_has_index_in xs) zs ==>
      FILTER (ffi_has_index_in [x]) ys = FILTER (ffi_has_index_in [x]) zs`,
  once_rewrite_tac [EQ_SYM_EQ] \\ Induct \\ fs [] THEN1
   (fs [listTheory.FILTER_EQ_NIL] \\ fs [EVERY_MEM] \\ rw []
    \\ res_tac \\ Cases_on `x'` \\ fs [ffi_has_index_in_def]
    \\ CCONTR_TAC \\ fs [])
  \\ rpt strip_tac
  \\ reverse (Cases_on `ffi_has_index_in xs h` \\ fs [])
  THEN1
   (`~ffi_has_index_in [x] h` by
        (Cases_on `h` \\ fs [ffi_has_index_in_def] \\ CCONTR_TAC \\ fs [])
    \\ fs [] \\ metis_tac [])
  \\ IF_CASES_TAC \\ fs []
  \\ fs [FILTER_EQ_CONS]
  THEN1
   (qexists_tac `l1` \\ qexists_tac `l2` \\ fs [] \\ rveq \\ fs []
    \\ fs [listTheory.FILTER_EQ_NIL] \\ fs [EVERY_MEM]
    \\ reverse conj_tac
    THEN1 (first_x_assum match_mp_tac \\ fs [] \\ asm_exists_tac \\ fs [])
    \\ rw [] \\ res_tac
    \\ Cases_on `x'` \\ fs [ffi_has_index_in_def]
    \\ CCONTR_TAC \\ fs [])
  \\ fs [FILTER_APPEND]
  \\ fs [GSYM FILTER_APPEND]
  \\ first_x_assum match_mp_tac \\ fs [] \\ asm_exists_tac \\ fs []
  \\ fs [FILTER_APPEND]);

val LENGTH_FILTER_EQ_IMP_LENGTH_EQ = Q.prove(
  `!xs ys.
      (∀n. LENGTH (FILTER (ffi_has_index_in [n]) xs) =
           LENGTH (FILTER (ffi_has_index_in [n]) ys)) ==>
      LENGTH xs = LENGTH ys`,
  Induct \\ fs [] THEN1
   (Cases_on `ys` \\ fs [] \\ Cases_on `h` \\ fs [ffi_has_index_in_def]
    \\ qexists_tac `s` \\ fs [])
  \\ Cases \\ fs [ffi_has_index_in_def] \\ rw []
  \\ qpat_assum `_` (qspec_then `s` mp_tac)
  \\ rewrite_tac [] \\ fs [LENGTH]
  \\ strip_tac
  \\ `LENGTH (FILTER (ffi_has_index_in [s]) ys) <> 0` by decide_tac
  \\ fs [LENGTH_NIL]
  \\ fs [FILTER_NEQ_NIL]
  \\ fs [MEM_SPLIT]
  \\ rveq \\ fs [FILTER_APPEND,ADD1]
  \\ first_x_assum (qspec_then `l1 ++ l2` mp_tac)
  \\ impl_tac \\ fs []
  \\ Cases_on `x` \\ fs [ffi_has_index_in_def] \\ rveq
  \\ rw [] \\ first_x_assum (qspec_then `n` mp_tac)
  \\ rw [] \\ fs [FILTER_APPEND]);

val IN_DISJOINT_LEMMA1 = Q.prove(
  `!s. x IN h_g /\ DISJOINT s h_g ==> ~(x IN s)`,
  SPLIT_TAC);

val FFI_part_EXISTS = Q.prove(
  `parts_ok s1 (p0,p1) /\ parts_ok s2 (p0,p1) /\
    FFI_part x1 x2 x3 x4 ∈ ffi2heap (p0,p1) s1 ==>
    ?y1 y2 y4. FFI_part y1 y2 x3 y4 ∈ ffi2heap (p0,p1) s2`,
  strip_tac \\ rfs [ffi2heap_def] \\ asm_exists_tac \\ fs []
  \\ fs [parts_ok_def] \\ metis_tac []);

val ALL_DISTINCT_FLAT_MEM_IMP = Q.prove(
  `!p1 x x2 y2.
      ALL_DISTINCT (FLAT (MAP FST p1)) /\ x <> [] /\
      MEM (x,x2) p1 /\ MEM (x,y2) p1 ==> x2 = y2`,
  Induct \\ fs [] \\ Cases \\ fs [ALL_DISTINCT_APPEND]
  \\ rw [] \\ res_tac \\ rveq
  \\ Cases_on `MEM (q,r) p1` \\ fs [] \\ res_tac
  \\ fs [MEM_FLAT,MEM_MAP,FORALL_PROD]
  \\ Cases_on `q` \\ fs []
  \\ metis_tac [MEM]);

val FFI_part_11 = Q.prove(
  `parts_ok s1 (p0,p1) /\ parts_ok s2 (p0,p1) /\
    FFI_part x1 x2 x3 x4 ∈ ffi2heap (p0,p1) s1 /\
    FFI_part y1 y2 x3 y4 ∈ ffi2heap (p0,p1) s1 ==>
    x1 = y1 /\ x2 = y2 /\ x4 = y4`,
  strip_tac \\ rfs [ffi2heap_def]
  \\ Cases_on `x3` \\ fs [] \\ fs [parts_ok_def]
  \\ imp_res_tac ALL_DISTINCT_FLAT_MEM_IMP \\ fs []);

val SPLIT_st2heap_ffi = Q.store_thm("SPLIT_st2heap_ffi",
  `SPLIT (st2heap p st') (st2heap p st, h_g) ⇒
   st'.ffi.final_event = st.ffi.final_event /\
   !n. FILTER (ffi_has_index_in [n]) st'.ffi.io_events =
       FILTER (ffi_has_index_in [n]) st.ffi.io_events`,
  PairCases_on `p` \\ strip_tac
  \\ reverse (Cases_on `parts_ok st.ffi (p0,p1) = parts_ok st'.ffi (p0,p1)`)
  THEN1
   (reverse (Cases_on `parts_ok st.ffi (p0,p1)`)
    \\ fs [ffi2heap_def,st2heap_def]
    THEN1
     (fs [SPLIT_def] \\ fs [EXTENSION] \\ fs [st2heap_def]
      \\ qpat_x_assum `!x._` (assume_tac o GSYM)
      \\ fs [forall_cases,FFI_full_NOT_IN_store2heap,FFI_part_NOT_IN_store2heap]
      \\ fs [Mem_NOT_IN_ffi2heap] \\ metis_tac [])
    \\ drule SPLIT_UNION_IMP_SUBSET
    \\ fs [SUBSET_DEF,PULL_EXISTS,FFI_split_NOT_IN_store2heap])
  \\ fs [SPLIT_def] \\ fs [EXTENSION] \\ fs [st2heap_def]
  \\ qpat_x_assum `!x._` (assume_tac o GSYM)
  \\ fs [forall_cases,FFI_full_NOT_IN_store2heap,FFI_part_NOT_IN_store2heap]
  \\ fs [Mem_NOT_IN_ffi2heap]
  \\ reverse (Cases_on `parts_ok st.ffi (p0,p1)`) \\ fs [] THEN1
   (fs [ffi2heap_def]
    \\ first_x_assum (qspecl_then [`st.ffi.final_event`,`st.ffi.io_events`] mp_tac)
    \\ fs [])
  \\ conj_tac THEN1 fs [parts_ok_def] \\ rw []
  \\ ntac 2 (qpat_x_assum `!x1 x2. _ <=> _` kall_tac)
  \\ qpat_x_assum `_ <=> _` kall_tac
  \\ `∀x3 x4 x2 x1.
        FFI_part x1 x2 x3 x4 ∈ ffi2heap (p0,p1) st'.ffi ⇔
        FFI_part x1 x2 x3 x4 ∈ ffi2heap (p0,p1) st.ffi` by
   (rw [] \\ eq_tac \\ rw []
    \\ `FFI_part x1 x2 x3 x4 ∈ ffi2heap (p0,p1) st'.ffi` by metis_tac []
    \\ `?y1 y2 y4. FFI_part y1 y2 x3 y4 ∈ ffi2heap (p0,p1) st.ffi` by
          metis_tac [FFI_part_EXISTS]
    \\ `FFI_part y1 y2 x3 y4 ∈ ffi2heap (p0,p1) st'.ffi` by metis_tac []
    \\ `x1 = y1 /\ x2 = y2 /\ x4 = y4` by metis_tac [FFI_part_11]
    \\ rveq \\ fs [] \\ NO_TAC)
  \\ pop_assum mp_tac \\ qpat_x_assum `!x. _` kall_tac \\ rw []
  \\ fs [ffi2heap_def] \\ rfs []
  \\ fs [parts_ok_def]
  \\ reverse (Cases_on `MEM n ((FLAT (MAP FST p1)))`)
  THEN1 (imp_res_tac FILTER_ffi_has_index_in_EQ_NIL \\ fs [])
  \\ fs [MEM_FLAT,MEM_MAP]
  \\ rpt var_eq_tac
  \\ PairCases_on `y` \\ fs []
  \\ qpat_x_assum `∀ns u. _ ==> _` mp_tac
  \\ qpat_assum `!x1 x2. _ ==> _` drule
  \\ strip_tac
  \\ first_assum (qspecl_then [`y0`,
       `FILTER (ffi_has_index_in y0) st'.ffi.io_events`,`y1`,`s`] mp_tac)
  \\ `y0 <> []` by (CCONTR_TAC \\ fs [])
  \\ rewrite_tac [] \\ simp []
  \\ strip_tac
  \\ rpt strip_tac
  \\ match_mp_tac FILTER_ffi_has_index_in_MEM
  \\ fs [] \\ asm_exists_tac \\ fs [])

val SPLIT_st2heap_evaluate_ffi_same = Q.store_thm("SPLIT_st2heap_evaluate_ffi_same",
  `evaluate F env st exp (st',Rval res) ∧
   SPLIT (st2heap p st') (st2heap p st, h_g) ⇒
   st'.ffi = st.ffi`,
  rw[] \\ imp_res_tac SPLIT_st2heap_ffi
  \\ fs[bigClockTheory.big_clocked_unclocked_equiv]
  \\ fs[funBigStepEquivTheory.functional_evaluate]
  \\ imp_res_tac evaluate_io_events_mono_imp
  \\ fs[io_events_mono_def]
  \\ Cases_on`st.ffi.final_event` \\ fs[] \\ rfs []
  \\ `LENGTH st.ffi.io_events = LENGTH st'.ffi.io_events`
        by metis_tac [LENGTH_FILTER_EQ_IMP_LENGTH_EQ]
  \\ metis_tac [IS_PREFIX_LENGTH_ANTI]);

val evaluate_imp_evaluate_empty_state = Q.store_thm("evaluate_imp_evaluate_empty_state",
  `evaluate F env s es (s',Rval r) ∧ s.refs ≼ s'.refs ∧ s'.ffi = s.ffi ∧ s.ffi.final_event = NONE ∧
   t = empty_state with <| refs := s.refs |> ∧
   t' = empty_state with <| refs := s'.refs |>
   ⇒
   evaluate F env t es (t',Rval r)`,
  rw[Once bigClockTheory.big_clocked_unclocked_equiv]
  \\ fs[funBigStepEquivTheory.functional_evaluate]
  \\ drule (REWRITE_RULE[GSYM AND_IMP_INTRO](
              INST_TYPE[beta|->oneSyntax.one_ty](
                CONJUNCT1 evaluate_ffi_intro)))
  \\ simp[]
  \\ disch_then(qspec_then`empty_state with <| clock := c; refs := s.refs |>`mp_tac)
  \\ simp[] \\ strip_tac
  \\ `Rval [r] = list_result ((Rval r):(v,v) result)` by EVAL_TAC
  \\ pop_assum SUBST_ALL_TAC
  \\ fs[GSYM funBigStepEquivTheory.functional_evaluate]
  \\ simp[bigClockTheory.big_clocked_unclocked_equiv]
  \\ asm_exists_tac \\ fs[]);

val Arrow_IMP_app_basic = Q.store_thm("Arrow_IMP_app_basic",
  `(Arrow a b) f v ==>
    !x v1.
      a x v1 ==>
      app_basic (p:'ffi ffi_proj) v v1 emp (POSTv v. &b (f x) v)`,
  fs [app_basic_def,emp_def,cfHeapsBaseTheory.SPLIT_emp1,
      ml_translatorTheory.Arrow_def,ml_translatorTheory.AppReturns_def,PULL_EXISTS]
  \\ fs [evaluate_ck_def, funBigStepEquivTheory.functional_evaluate_list,
         evaluate_to_res_def]
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
  \\ Cases \\ fs[FFI_split_NOT_IN_store2heap_aux,
                 FFI_part_NOT_IN_store2heap_aux,
                 FFI_full_NOT_IN_store2heap_aux,
                 st2heap_def,Mem_NOT_IN_ffi2heap]
  \\ spose_not_then strip_assume_tac
  \\ imp_res_tac store2heap_IN_LENGTH
  \\ imp_res_tac store2heap_aux_IN_bound
  \\ decide_tac);

val app_basic_IMP_Arrow = Q.store_thm("app_basic_IMP_Arrow",
  `(∀x v1. a x v1 ⇒ app_basic p v v1 emp (POSTv v. cond (b (f x) v))) ⇒ Arrow a b f v`,
  rw[app_basic_def,ml_translatorTheory.Arrow_def,ml_translatorTheory.AppReturns_def,emp_def,SPLIT_emp1,evaluate_to_res_def] \\
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
  `Arrow a b f fv ⇔ (∀x xv. a x xv ⇒ app_basic p fv xv emp (POSTv v'. &b (f x) v'))`,
  metis_tac[GEN_ALL Arrow_IMP_app_basic, GEN_ALL app_basic_IMP_Arrow]);

val _ = export_theory ()
