(*
  Examples of non-termination.
*)
open preamble basis
open integerTheory cfDivTheory

val _ = new_theory "div";

val _ = translation_extends "basisProg";

(* A simple pure non-terminating loop *)

val _ = process_topdecs `
  fun loop x = repeat (fn x => x) x;
  ` |> append_prog

val st = get_ml_prog_state ();

val loop_spec = store_thm("loop_spec",
  ``!xv.
      app (p:'ffi ffi_proj) ^(fetch_v "loop" st) [xv]
        (one (FFI_full [])) (POSTd io. io = [||])``,
  xcf "loop" st
  \\ xfun_spec `f`
    `!xv.
       app p f [xv]
         (one (FFI_full [])) (POSTv v. cond (v = xv) * one (FFI_full []))`
  THEN1 (strip_tac \\ xapp \\ xvar \\ xsimpl)
  \\ xapp
  \\ qexists_tac `\n. one (FFI_full [])`
  \\ qexists_tac `\n. []`
  \\ qexists_tac `\n. xv`
  \\ qexists_tac `[||]`
  \\ rpt strip_tac \\ xsimpl
  THEN1 (qexists_tac `emp` \\ rw [SEP_CLAUSES])
  \\ rw [lprefix_lub_def]);

(* Conditional termination *)

val _ = process_topdecs `
  exception Terminate;
  fun condBody n = if n = 0 then raise Terminate else n - 1;
  fun condLoop n = repeat condBody n;
  ` |> append_prog

val st = get_ml_prog_state ();

val condBody_spec = store_thm("condBody_spec",
  ``!n nv.
      INT n nv ==>
      app (p:'ffi ffi_proj) ^(fetch_v "condBody" st) [nv]
        (one (FFI_full []))
        (POSTve
          (\v. &(INT (n - 1) v /\ n <> 0) * one (FFI_full []))
          (\e. &(n = 0) * one (FFI_full [])))``,
  xcf "condBody" st
  \\ Cases_on `n = 0`
  THEN1 (
    xlet_auto THEN1 (qexists_tac `one (FFI_full [])` \\ xsimpl)
    \\ xif \\ qexists_tac `T` \\ rw []
    \\ xlet_auto THEN1 (xcon \\ xsimpl)
    \\ xraise \\ xsimpl)
  \\ xlet_auto THEN1 (qexists_tac `one (FFI_full [])` \\ xsimpl)
  \\ xif \\ qexists_tac `F` \\ rw [] \\ xapp
  \\ qexists_tac `one (FFI_full [])`
  \\ qexists_tac `1`
  \\ qexists_tac `n`
  \\ rw [INT_def] \\ xsimpl);

val repeat_POSTe = store_thm("repeat_POSTe",
  ``!p fv xv H Q.
      (?Hs vs j.
         vs 0 = xv /\ H ==>> Hs 0 /\
         (!i. i < j ==>
            app p fv [vs i] (Hs i)
                            (POSTv v. &(v = vs (SUC i)) * Hs (SUC i))) /\
         app p fv [vs j] (Hs j) ($POSTe Q))
      ==>
      app p ^(fetch_v "repeat" st) [fv; xv] H ($POSTe Q)``,
  rpt strip_tac
  \\ `!i. i <= j ==> app p ^(fetch_v "repeat" st) [fv; vs i] (Hs i) ($POSTe Q)` by (
    rpt strip_tac
    \\ Induct_on `j - i`
    THEN1 (
      xcf "repeat" st
      \\ `i = j` by decide_tac \\ rveq
      \\ xlet `$POSTe Q` THEN1 xapp
      \\ xsimpl)
    \\ xcf "repeat" st
    \\ `i < j` by decide_tac
    \\ xlet `POSTv v. &(v = vs (SUC i)) * Hs (SUC i)`
    THEN1 (
      `app p fv [vs i] (Hs i) (POSTv v. &(v = vs (SUC i)) * Hs (SUC i))`
        by (first_assum irule \\ rw [])
      \\ xapp)
    \\ rveq
    \\ `app p repeat_v [fv; vs (SUC i)] (Hs (SUC i)) ($POSTe Q)`
         by (first_assum irule \\ qexists_tac `j` \\ rw [])
    \\ xapp)
  \\ `app p repeat_v [fv; vs 0] (Hs 0) ($POSTe Q)`
       by (first_assum irule \\ rw [])
  \\ rveq \\ xapp
  \\ qexists_tac `emp`
  \\ xsimpl);

val condLoop_spec = store_thm("condLoop_spec",
  ``!n nv.
      INT n nv ==>
      app (p:'ffi ffi_proj) ^(fetch_v "condLoop" st) [nv]
        (one (FFI_full []))
        (POSTed (\e. cond (0 <= n)) (\io. io = [||] /\ n < 0))``,
  xcf "condLoop" st
  \\ Cases_on `0 <= n`
  THEN1 (
    `~(n < 0)` by intLib.COOPER_TAC
    \\ rw [POSTed_def, GSYM POSTe_def]
    \\ xapp_spec repeat_POSTe
    \\ qexists_tac `\i. one (FFI_full [])`
    \\ qexists_tac `\i. Litv (IntLit (n - &i))`
    \\ `?m. n = &m` by (irule NUM_POSINT_EXISTS \\ rw [])
    \\ qexists_tac `m`
    \\ rpt strip_tac \\ xsimpl
    THEN1 fs [INT_def]
    THEN1 (
      xapp
      \\ qexists_tac `emp`
      \\ qexists_tac `&m - &i`
      \\ fs [INT_def] \\ xsimpl
      \\ intLib.COOPER_TAC)
    \\ xapp \\ xsimpl)
  \\ rw [POSTed_def, GSYM POSTd_def]
  \\ xapp
  \\ qexists_tac `\i. one (FFI_full [])`
  \\ qexists_tac `\i. []`
  \\ qexists_tac `\i. Litv (IntLit (n - &i))`
  \\ qexists_tac `[||]`
  \\ rpt strip_tac \\ xsimpl
  THEN1 fs [INT_def]
  THEN1 (qexists_tac `emp` \\ rw [SEP_CLAUSES])
  THEN1 (
    xapp
    \\ qexists_tac `emp`
    \\ qexists_tac `n - &i`
    \\ fs [INT_def] \\ xsimpl
    \\ intLib.COOPER_TAC)
  THEN1 rw [lprefix_lub_def]
  \\ intLib.COOPER_TAC);

(* Non-terminating loop with output *)

val _ = process_topdecs `
  fun printLoop c = repeat (fn c => (putChar c; c)) c;
  ` |> append_prog

val st = get_ml_prog_state ();

val printLoop_spec = store_thm("printLoop_spec",
  ``!xv.
      app (p:'ffi ffi_proj) ^(fetch_v "printLoop" st) [xv]
        emp (POSTd io. T)``,
  cheat);

val _ = export_theory();
