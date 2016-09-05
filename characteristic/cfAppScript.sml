open preamble
open set_sepTheory helperLib semanticPrimitivesTheory
open cfHeapsBaseTheory cfHeapsTheory cfHeapsBaseLib cfStoreTheory cfNormalizeTheory
open cfTacticsBaseLib cfHeapsLib

val _ = new_theory "cfApp"

val _ = temp_type_abbrev("state",``:'ffi semanticPrimitives$state``);

(*------------------------------------------------------------------*)
(** App: [app] is used to give a specification for the application of
    a value to one or multiple value arguments. It is in particular
    used in cf to abstract from the concrete representation of
    closures.
*)

(* [app_basic]: application with one argument *)
val app_basic_def = Define `
  app_basic (p:'ffi ffi_proj) (f: v) (x: v) (H: hprop) (Q: v -> hprop) =
    !(h: heap) (i: heap) (st: 'ffi state).
      SPLIT (st2heap p st) (h, i) ==> H h ==>
      ?env exp (v': v) (h': heap) (g: heap) (st': 'ffi state).
        SPLIT3 (st2heap p st') (h', g, i) /\
        Q v' h' /\
        (do_opapp [f;x] = SOME (env, exp)) /\
        evaluate F env st exp (st', Rval v')`

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
  rename1 `Q' v' h1'` \\
  qpat_x_assum `_ ==+> _` mp_tac \\
  disch_then (mp_tac o REWRITE_RULE [SEP_IMPPOST_def, STARPOST_def]) \\
  disch_then (mp_tac o REWRITE_RULE [SEP_IMP_def]) \\
  disch_then (qspecl_then [`v'`, `h1' UNION h2`] mp_tac) \\ simp [] \\
  impl_tac
  THEN1 (simp [STAR_def] \\ Q.LIST_EXISTS_TAC [`h1'`, `h2`] \\ SPLIT_TAC) \\
  disch_then (assume_tac o REWRITE_RULE [STAR_def]) \\ fs [] \\
  instantiate \\ rename1 `GC gc` \\ rename1 `SPLIT3 _ (h1', i', i UNION h2)` \\
  qexists_tac `gc UNION i'` \\ SPLIT_TAC);

(* [app]: n-ary application *)
val app_def = Define `
  app (p:'ffi ffi_proj) (f: v) ([]: v list) (H: hprop) (Q: v -> hprop) = F /\
  app (p:'ffi ffi_proj) f [x] H Q = app_basic p f x H Q /\
  app (p:'ffi ffi_proj) f (x::xs) H Q =
    app_basic p f x H
      (\g. SEP_EXISTS H'. H' * cond (app p g xs H' Q))`

val app_alt_ind = store_thm ("app_alt_ind",
  ``!f xs x H Q.
     xs <> [] ==>
     app (p:'ffi ffi_proj) f (xs ++ [x]) H Q =
     app (p:'ffi ffi_proj) f xs H
       (\g. SEP_EXISTS H'. H' * cond (app_basic p g x H' Q))``,
  Induct_on `xs` \\ fs [] \\ rpt strip_tac \\
  Cases_on `xs` \\ fs [app_def]
);

val app_alt_ind_w = store_thm ("app_alt_ind_w",
  ``!f xs x H Q.
     app (p:'ffi ffi_proj) f (xs ++ [x]) H Q ==> xs <> [] ==>
     app (p:'ffi ffi_proj) f xs H
       (\g. SEP_EXISTS H'. H' * cond (app_basic (p:'ffi ffi_proj) g x H' Q))``,
  rpt strip_tac \\ fs [app_alt_ind]
)

val app_ge_2_unfold = store_thm ("app_ge_2_unfold",
  ``!f x xs H Q.
      xs <> [] ==>
      app (p:'ffi ffi_proj) f (x::xs) H Q =
      app_basic p f x H (\g. SEP_EXISTS H'. H' * cond (app p g xs H' Q))``,
  rpt strip_tac \\ Cases_on `xs` \\ fs [app_def]
);

val app_ge_2_unfold_extens = store_thm ("app_ge_2_unfold_extens",
  ``!f x xs.
      xs <> [] ==>
      app (p:'ffi ffi_proj) f (x::xs) =
      \H Q. app_basic p f x H (\g. SEP_EXISTS H'. H' * cond (app p g xs H' Q))``,
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
    instantiate \\ simp [SEP_IMPPOST_def] \\ qx_gen_tac `g` \\
    hpull \\ qx_gen_tac `HR` \\ strip_tac \\ hsimpl \\ qexists_tac `HR * H2` \\
    hsimpl \\ first_assum irule \\ instantiate \\ hsimpl
  )
);

val app_weaken = store_thm ("app_weaken",
  ``!f xs H Q Q'.
      app (p:'ffi ffi_proj) f xs H Q ==>
      Q ==+> Q' ==>
      app p f xs H Q'``,
  rpt strip_tac \\ fs [SEP_IMPPOST_def] \\ irule app_wgframe \\ instantiate \\
  hsimpl \\ (*fixme*) qexists_tac `emp` \\ simp [GC_def] \\ hsimpl \\
  gen_tac \\ qexists_tac `emp` \\ hsimpl \\ fs [] (* uhh *)
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
    qx_gen_tac `g` \\ hpull \\ qx_gen_tac `H'` \\ strip_tac \\ hsimpl \\
    qexists_tac `H' * H2` \\ hsimpl \\ irule app_wgframe \\ instantiate \\
    hsimpl
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
             (\g. cond (curried (p:'ffi ffi_proj) n g /\
                  !xs H Q.
                    LENGTH xs = n ==>
                    app (p:'ffi ffi_proj) f (x::xs) H Q ==>
                    app (p:'ffi ffi_proj) g xs H Q))`

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
      app_basic (p:'ffi ffi_proj) v v1 emp ((&) o b (f x))``,
  fs [app_basic_def,emp_def,cfHeapsBaseTheory.SPLIT_emp1,
      ml_translatorTheory.Arrow_def,ml_translatorTheory.AppReturns_def,
      ml_translatorTheory.evaluate_closure_def,PULL_EXISTS]
  \\ rw [] \\ res_tac \\ instantiate
  \\ drule ml_translatorTheory.evaluate_empty_state_IMP
  \\ disch_then (qspec_then `st` assume_tac)
  \\ instantiate \\ fs [cond_def]
  \\ qexists_tac `{}` \\ SPLIT_TAC);

val app_basic_weaken = store_thm("app_basic_weaken",
  ``(!x v. P x v ==> Q x v) ==>
    (app_basic p v v1 x P ==>
     app_basic p v v1 x Q)``,
  fs [app_basic_def] \\ metis_tac []);

val _ = export_theory ()
