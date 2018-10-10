open preamble
open set_sepTheory helperLib ml_translatorTheory
open ml_translatorTheory semanticPrimitivesTheory
open cfHeapsBaseTheory cfHeapsTheory cfHeapsBaseLib cfStoreTheory
open cfNormaliseTheory cfAppTheory
open cfTacticsBaseLib cfTheory

val _ = new_theory "cfDiv";

val POSTd_eq = store_thm("POSTd_eq",
  ``POSTd Q r h <=> ?io1. r = Div io1 /\ Q io1 /\ emp h``,
  Cases_on `r` \\ fs [POSTd_def,POST_def,cond_def,emp_def]
  \\ eq_tac \\ rw []);

val app_POSTd = store_thm("app_POSTd",
  ``!p f xvs H Q.
      (?io events (Hs: num -> hprop).
        Q io /\
        H ==>> Hs 0 /\
        (!i. ?P. Hs i = P * one (FFI_full (events i))) /\
        (!i. LENGTH (events i) < LENGTH (events (i+1))) /\
        (!i. app p f xvs (Hs (SUC i)) (POSTd Q) ==>
             app p f xvs (Hs i) (POSTd Q)) /\
        (!i. LPREFIX (fromList (events i)) io)) /\
      LENGTH xvs = 1 /\
      IS_SOME (do_opapp [f; HD xvs])
      ==>
      app p f xvs H (POSTd Q)``,
  rw []
  \\ `?v. xvs = [v]` by (Cases_on `xvs` \\ fs []) \\ rveq
  \\ simp [app_def,app_basic_def,POSTd_eq,PULL_EXISTS]
  \\ rw [emp_def]
  \\ fs [IS_SOME_EXISTS]
  \\ rename [`SOME ee`] \\ PairCases_on `ee` \\ fs []
  \\ qexists_tac `UNIV DIFF h_k`
  \\ qexists_tac `UNIV`
  \\ qexists_tac `io` \\ fs []
  \\ conj_tac THEN1 fs [SPLIT3_def,IN_DISJOINT,EXTENSION]
  \\ fs [evaluate_to_heap_def]
  \\ qsuff_tac `!ck. ?st1. evaluate_ck ck st ee0 [ee1] =
                             (st1,Rerr (Rabort Rtimeout_error))`
  THEN1 cheat
  \\ rw []
  \\ cheat);

(*

fun repeat f x = repeat f (f x);

repeat (fn x => print "y") ()

repeat (fn x => (if x then print "#" else print "&"; not x)) true

repeat (fn x => (print_int x; x+1)) 0

*)

val repeat_POSTd = store_thm("repeat_POSTd",
  ``!p fv xv H Q.
      (?step P.
         !v events v1 io_events1.
           step v = (v1,io_events1) ==>
           (app p fv [v] (P * one (FFI_full events))
                         (POSTv v'. &(v' = v1) * P *
                                    one (FFI_full (events ++ io_events1)))))
      ==>
      app p repeat_v [fv; xv] H (POSTd Q)``,
  cheat);

val repeat_POSTd = store_thm("repeat_POSTd", (* productive version *)
  ``!p fv xv H Q.
      (?Hs events vs io.
         vs 0 = v /\ H ==>> HS 0 /\
         (!n. ?i. n < LENGTH (events i)) /\
         (!i. ?P. Hs i = P * one (FFI_full (events i))) /\
         (!i.
            (app p fv [vs i] (Hs i)
                             (POSTv v'. &(v' = vs (SUC i)) * Hs (SUC i)))) /\
        (!i. LPREFIX (fromList (events i)) io) /\ Q io)
      ==>
      app p repeat_v [fv; xv] H (POSTd Q)``,
  cheat);

val _ = export_theory();
