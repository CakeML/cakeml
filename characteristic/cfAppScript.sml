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
    !(h: heap) (i: heap) (st: 'ffi state).
      SPLIT (st2heap p st) (h, i) ==> H h ==>
      ?env exp (r: res) (h': heap) (g: heap) (st': 'ffi state) ck.
        SPLIT3 (st2heap p st') (h', g, i) /\
        Q r h' /\
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
  qpat_assum `(H1 * H2) h` (strip_assume_tac o REWRITE_RULE [STAR_def]) \\
  fs [] \\ rename1 `H1 h1` \\ rename1 `H2 h2` \\
  qpat_assum `app_basic _ _ _ _ _` (mp_tac o REWRITE_RULE [app_basic_def]) \\
  disch_then (qspecl_then [`h1`, `i UNION h2`, `st`] mp_tac) \\
  impl_tac THEN1 SPLIT_TAC \\ disch_then progress \\
  rename1 `Q1 r' h1'` \\
  qpat_x_assum `_ ==+> _` mp_tac \\
  disch_then (mp_tac o REWRITE_RULE [SEP_IMPPOST_def, STARPOST_def]) \\
  disch_then (mp_tac o REWRITE_RULE [SEP_IMP_def]) \\
  disch_then (qspecl_then [`r'`, `h1' UNION h2`] mp_tac) \\ simp [] \\
  impl_tac
  THEN1 (simp [STAR_def] \\ Q.LIST_EXISTS_TAC [`h1'`, `h2`] \\ SPLIT_TAC) \\
  disch_then (assume_tac o REWRITE_RULE [STAR_def]) \\ fs [] \\
  instantiate \\ rename1 `GC gc` \\ rename1 `SPLIT3 _ (h1', i', i UNION h2)` \\
  qexists_tac `gc UNION i'` \\ SPLIT_TAC
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

val Arrow_IMP_app_basic = store_thm("Arrow_IMP_app_basic",
  ``(a --> b) f v ==>
    !x v1.
      a x v1 ==>
      app_basic (p:'ffi ffi_proj) v v1 emp (POSTv v. & b (f x) v)``,
  fs [app_basic_def,emp_def,cfHeapsBaseTheory.SPLIT_emp1,
      ml_translatorTheory.Arrow_def,ml_translatorTheory.AppReturns_def,
      ml_translatorTheory.evaluate_closure_def,POSTv_def, PULL_EXISTS]
  \\ fs [evaluate_ck_def, funBigStepEquivTheory.functional_evaluate_list]
  \\ rw [] \\ res_tac \\ instantiate
  \\ simp [Once bigStepTheory.evaluate_cases, PULL_EXISTS]
  \\ drule ml_translatorTheory.evaluate_empty_state_IMP
  \\ disch_then (qspec_then `st` assume_tac)
  \\ fs [bigClockTheory.big_clocked_unclocked_equiv]
  \\ rename1 `evaluate _ _ (st with clock := ck) _ (_, Rval v')`
  \\ GEN_EXISTS_TAC "ck" `ck` \\ qexists_tac `Val v'` \\ simp [cond_def]
  \\ Q.LIST_EXISTS_TAC [`{}`, `st with clock := 0`]
  \\ CONJ_TAC THEN_LT REVERSE_LT
  THEN1 (prove_tac [bigStepTheory.evaluate_rules])
  THEN1 (fs [st2heap_clock] \\ SPLIT_TAC)
);

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
    !(h: heap) (i: heap) (st: 'ffi state).
      SPLIT (st2heap p st) (h, i) ==> H h ==>
      ?env exp (r: res) (h': heap) (g: heap) (st': 'ffi state).
        SPLIT3 (st2heap p st') (h', g, i) /\
        Q r h' /\
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
   (rename1 `SPLIT3 (st2heap p st1) (h1,g,i)`
    \\ qabbrev_tac `st2 = st1 with clock := st.clock`
    \\ `SPLIT3 (st2heap p st2) (h1,g,i)` by (fs [st2heap_def,Abbr `st2`] \\ NO_TAC)
    \\ rpt (asm_exists_tac \\ fs []) \\ fs [Abbr `st2`]
    \\ qexists_tac `ck - st1.clock`
    \\ drule bigClockTheory.clocked_min_counter \\ fs [])
  \\ try_finally
   (rewrite_tac [CONJ_ASSOC] \\ once_rewrite_tac [CONJ_COMM]
    \\ asm_exists_tac \\ fs []
    \\ fs [st2heap_def] \\ asm_exists_tac \\ fs []));

val Eval_def = Define `
  Eval env exp P =
    ?res refs.
      evaluate F env empty_state exp (empty_state with refs := refs,Rval res) /\
          P (res:v)`;

val evaluate_closure_def = Define `
  evaluate_closure input cl output =
    ?env exp refs.
      (do_opapp [cl;input] = SOME (env,exp)) /\
      evaluate F env empty_state exp
          (empty_state with refs := refs,Rval (output))`;

val AppReturns_def = Define ` (* think of this as a Hoare triple {P} cl {Q} *)
  AppReturns P cl Q =
    !v. P v ==> ?u. evaluate_closure v cl u /\ Q u`;

val Arrow_def = Define `
  Arrow a b =
    \f v. !x. AppReturns (a x) v (b (f x))`;

val evaluate_empty_state_IMP = Q.store_thm("evaluate_empty_state_IMP",
  `evaluate F env empty_state exp (empty_state with refs := refs,Rval x) ⇒
   ∀s. evaluate F env s exp (s with refs := s.refs ++ refs,Rval x)`,
  cheat);

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

val Arrow_IMP_app_basic = store_thm("Arrow_IMP_app_basic",
  ``(Arrow a b) f v ==>
    !x v1.
      a x v1 ==>
      app_basic (p:'ffi ffi_proj) v v1 emp ((&) o b (f x))``,
  fs [app_basic_def,emp_def,cfHeapsBaseTheory.SPLIT_emp1,
      Arrow_def,AppReturns_def,
      evaluate_closure_def,PULL_EXISTS]
  \\ fs [evaluate_ck_def, funBigStepEquivTheory.functional_evaluate_list]
  \\ rw [] \\ res_tac \\ instantiate
  \\ simp [Once bigStepTheory.evaluate_cases, PULL_EXISTS]
  \\ simp [Once (CONJUNCT2 bigStepTheory.evaluate_cases)]
  \\ drule (INST_TYPE[alpha|->``:'ffi``]evaluate_empty_state_IMP)
  \\ disch_then (qspec_then `st` assume_tac)
  \\ fs [bigClockTheory.big_clocked_unclocked_equiv]
  \\ rename1 `evaluate _ _ (st with clock := ck) _ _`
  \\ GEN_EXISTS_TAC "ck" `ck` \\ instantiate \\ simp [cond_def]
  \\ fs[st2heap_clock]
  \\ fs[SPLIT3_emp1]
  \\ fs[st2heap_with_refs_append]
  \\ `st with refs := st.refs = st` by fs[state_component_equality]
  \\ pop_assum SUBST_ALL_TAC
  \\ qexists_tac`store2heap_aux (LENGTH st.refs) refs`
  \\ fs[SPLIT_def]
  \\ conj_tac >- SPLIT_TAC
  \\ fs[IN_DISJOINT]
  \\ Cases
  \\ fs[FFI_part_NOT_IN_store2heap_aux,st2heap_def,Mem_NOT_IN_ffi2heap]
  \\ spose_not_then strip_assume_tac
  \\ imp_res_tac store2heap_IN_LENGTH
  \\ imp_res_tac store2heap_aux_IN_bound
  \\ decide_tac);

val functional_evaluate = Q.store_thm("functional_evaluate",
  `evaluate T env s e (s',r) ⇔ evaluate s env [e] = (s',list_result r)`,
  funBigStepEquivTheory.functional_evaluate_list |> Q.GENL[`r`,`es`] |> qspec_then`[e]`mp_tac \\
  ntac 6 (simp[Once (CONJUNCT2 bigStepTheory.evaluate_cases)]) \\
  Cases_on`r` \\ fs[]);

val evaluate_imp_evaluate_empty_state = Q.store_thm("evaluate_imp_evaluate_empty_state",
  `evaluate s env es = (s',Rval r) ∧
   s.refs = [] ∧ (∀m x bytes. s.ffi.oracle m x bytes = Oracle_fail) ∧
   (* s'.ffi.final_event = NONE ∧ this is probably necessary *)
   t = empty_state with clock := s.clock ∧
   t' = empty_state with <| clock := s'.clock; refs := s'.refs |>
   ⇒
   evaluate t env es = (t',Rval r)`,
  cheat);

val app_basic_IMP_Arrow = Q.store_thm("app_basic_IMP_Arrow",
  `(∀x v1. a x v1 ⇒ app_basic p v v1 emp (cond o b (f x))) ⇒ Arrow a b f v`,
  rw[app_basic_def,Arrow_def,AppReturns_def,evaluate_closure_def,emp_def,SPLIT_emp1] \\
  first_x_assum drule \\
  fs[evaluate_ck_def,funBigStepEquivTheory.functional_evaluate_list] \\
  fs[cond_def,SPLIT3_emp1] \\
  ffi2heap_def
  disch_then(
    qspec_then`ARB with
      <| refs := [];
         ffi := ARB with <| final_event := NONE ; oracle := λm x bytes. Oracle_fail |> |>`
    mp_tac) \\
  rw[] \\ instantiate \\
  fs[Once (CONJUNCT2 bigStepTheory.evaluate_cases)] \\
  fs[Once (CONJUNCT2 bigStepTheory.evaluate_cases)] \\ rw[] \\
  imp_res_tac bigClockTheory.clocked_min_counter \\ fs[] \\
  pop_assum mp_tac \\ pop_assum kall_tac \\
  fs[bigClockTheory.big_clocked_unclocked_equiv,functional_evaluate] \\
  rw[] \\
  qexists_tac`s2.refs` \\
  qexists_tac`ck - s2.clock` \\
  match_mp_tac (INST_TYPE[alpha|->beta](GEN_ALL evaluate_imp_evaluate_empty_state)) \\
  instantiate);

val Arrow_eq_app_basic = Q.store_thm("Arrow_eq_app_basic",
  `Arrow a b f v ⇔ (∀x v1. a x v1 ⇒ app_basic p v v1 emp (cond o b (f x)))`,
  metis_tac[Arrow_IMP_app_basic,app_basic_IMP_Arrow]);

val _ = export_theory ()
