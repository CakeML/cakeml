open HolKernel Parse boolLib bossLib preamble
open set_sepTheory helperLib semanticPrimitivesTheory
open cfHeapsTheory cfHeapsLib cfStoreTheory cfNormalizeTheory

val _ = new_theory "cfApp"

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
  ``!f x. is_local (\env. app_basic p f x)``,
  cheat)


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
)

val app_alt_ind_w = store_thm ("app_alt_ind_w",
  ``!f xs x H Q.
     app (p:'ffi ffi_proj) f (xs ++ [x]) H Q ==> xs <> [] ==>
     app (p:'ffi ffi_proj) f xs H
       (\g. SEP_EXISTS H'. H' * cond (app_basic (p:'ffi ffi_proj) g x H' Q))``,
  rpt strip_tac \\ fs [app_alt_ind]
)

val app_local = prove (
  ``!f xs. is_local (\env. app (p:'ffi ffi_proj) f xs)``,
  cheat)


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

(*------------------------------------------------------------------*)
(** Packaging *)

(* [spec (p:'ffi ffi_proj) f n P] asserts that [curried (p:'ffi ffi_proj) f n] is true and
that [P] is a valid specification for [f]. Useful for conciseness and
tactics. *)
val spec_def = Define `
  spec (p:'ffi ffi_proj) f n P = (curried (p:'ffi ffi_proj) n f /\ P)`

val _ = export_theory ()
