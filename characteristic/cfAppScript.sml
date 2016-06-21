open HolKernel Parse boolLib bossLib preamble
open set_sepTheory helperLib semanticPrimitivesTheory
open cfHeapsTheory cfHeapsBaseLib cfStoreTheory cfNormalizeTheory

val _ = new_theory "cfApp"

(*------------------------------------------------------------------*)
(** App: [app] is used to give a specification for the application of
    a value to one or multiple value arguments. It is in particular
    used in cf to abstract from the concrete representation of
    closures.
*)

(* [app_basic]: application with one argument *)
val app_basic_def = Define `
  app_basic (:'ffi) (f: v) (x: v) (H: hprop) (Q: v -> hprop) =
    !(h: heap) (i: heap) (st: 'ffi state).
      SPLIT (st2heap (:'ffi) st) (h, i) ==> H h ==>
      ?env exp (v': v) (h': heap) (g: heap) (st': 'ffi state).
        SPLIT3 (st2heap (:'ffi) st') (h', g, i) /\
        Q v' h' /\
        (do_opapp [f;x] = SOME (env, exp)) /\
        evaluate F env st exp (st', Rval v')`

val app_basic_local = prove (
  ``!f x. is_local (app_basic (:'ffi) f x)``,
  cheat)


(* [app]: n-ary application *)
val app_def = Define `
  app (:'ffi) (f: v) ([]: v list) (H: hprop) (Q: v -> hprop) = F /\
  app (:'ffi) f [x] H Q = app_basic (:'ffi) f x H Q /\
  app (:'ffi) f (x::xs) H Q =
    app_basic (:'ffi) f x H
      (\g. SEP_EXISTS H'. H' * cond (app (:'ffi) g xs H' Q))`

val app_alt_ind = store_thm ("app_alt_ind",
  ``!f xs x H Q.
     xs <> [] ==>
     app (:'ffi) f (xs ++ [x]) H Q =
     app (:'ffi) f xs H
       (\g. SEP_EXISTS H'. H' * cond (app_basic (:'ffi) g x H' Q))``,
  Induct_on `xs` \\ fs [] \\ rpt strip_tac \\
  Cases_on `xs` \\ fs [app_def]
)

val app_alt_ind_w = store_thm ("app_alt_ind_w",
  ``!f xs x H Q.
     app (:'ffi) f (xs ++ [x]) H Q ==> xs <> [] ==>
     app (:'ffi) f xs H
       (\g. SEP_EXISTS H'. H' * cond (app_basic (:'ffi) g x H' Q))``,
  rpt strip_tac \\ fs [app_alt_ind]
)

val app_local = store_thm ("app_local",
  ``!f xs. xs <> [] ==> is_local (app (:'ffi) f xs)``,
  cheat)


(* [curried (:'ffi) n f] states that [f] is curried [n] times *)
val curried_def = Define `
  curried (:'ffi) (n: num) (f: v) =
    case n of
     | 0 => F
     | SUC 0 => T
     | SUC n =>
       !x. app_basic (:'ffi) f x emp
             (\g. cond (curried (:'ffi) n g /\
                  !xs H Q.
                    LENGTH xs = n ==>
                    app (:'ffi) f (x::xs) H Q ==>
                    app (:'ffi) g xs H Q))`

(* app_over_app / app_over_take *)

(** When [curried n f] holds and the number of the arguments [xs] is less than
    [n], then [app f xs] is a function [g] such that [app g ys] has the same
    behavior as [app f (xs++ys)]. *)
val app_partial = prove (
  ``!n xs f. curried (:'ffi) n f ==> (0 < LENGTH xs /\ LENGTH xs < n) ==>
    app (:'ffi) f xs emp (\g. cond (
      curried (:'ffi) (n - LENGTH xs) g /\
      !ys H Q. (LENGTH xs + LENGTH ys = n) ==>
        app (:'ffi) f (xs ++ ys) H Q ==> app (:'ffi) g ys H Q))``,
  completeInduct_on `n` \\ Cases_on `n`
  THEN1 (rpt strip_tac \\ fs [])

  THEN1 (
    Cases_on `xs` \\ rpt strip_tac \\ fs [] \\
    qcase_tac `x::zs` \\ qcase_tac `LENGTH zs < n` \\
    Cases_on `zs` \\ fs []

    THEN1 (
      (* xs = x :: zs = [x] *)
      fs [app_def] \\ cheat
    )
    THEN1 (
      (* xs = x :: zs = [x::y::t] *)
      qcase_tac `x::y::t` \\ fs [app_def] \\ cheat
    )
  )
)

(*------------------------------------------------------------------*)
(** Packaging *)

(* [spec (:'ffi) f n P] asserts that [curried (:'ffi) f n] is true and
that [P] is a valid specification for [f]. Useful for conciseness and
tactics. *)
val spec_def = Define `
  spec (:'ffi) f n P = (curried (:'ffi) n f /\ P)`

val _ = export_theory ()
