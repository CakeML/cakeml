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
  \\ xfun `f`
  \\ xapp \\ xsimpl
  \\ MAP_EVERY qexists_tac [`\i. one (FFI_full [])`, `\i. []`, `\i. xv`]
  \\ xsimpl \\ qexists_tac `emp`
  \\ rw [SEP_CLAUSES, lprefix_lub_def]
  \\ xapp \\ xvar \\ xsimpl);

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
  \\ xlet_auto THEN1 xsimpl
  \\ xif
  THEN1 (
    xlet_auto THEN1 (xcon \\ xsimpl)
    \\ xraise \\ xsimpl)
  \\ xapp \\ xsimpl
  \\ qexists_tac `n` \\ xsimpl);

val condLoop_spec = store_thm("condLoop_spec",
  ``!n nv.
      INT n nv ==>
      app (p:'ffi ffi_proj) ^(fetch_v "condLoop" st) [nv]
        (one (FFI_full []))
        (POSTed (\e. &(0 <= n)) (\io. io = [||] /\ n < 0))``,
  xcf "condLoop" st
  \\ Cases_on `0 <= n`
  THEN1 (
    `~(n < 0)` by intLib.COOPER_TAC
    \\ rw [POSTed_def, GSYM POSTe_def]
    \\ xapp_spec repeat_POSTe
    \\ `?m. n = &m` by (irule NUM_POSINT_EXISTS \\ rw [])
    \\ MAP_EVERY qexists_tac
         [`\i. one (FFI_full [])`, `\i. Litv (IntLit (n - &i))`, `m`]
    \\ rpt strip_tac \\ fs [INT_def] \\ xsimpl
    \\ xapp \\ xsimpl \\ fs [INT_def]
    \\ intLib.COOPER_TAC)
  \\ rw [POSTed_def, GSYM POSTd_def]
  \\ xapp \\ xsimpl
  \\ MAP_EVERY qexists_tac
       [`\i. one (FFI_full [])`, `\i. []`, `\i. Litv (IntLit (n - &i))`]
  \\ xsimpl \\ qexists_tac `emp`
  \\ rw [SEP_CLAUSES, lprefix_lub_def]
  \\ TRY (xapp \\ xsimpl)
  \\ fs [INT_def] \\ intLib.COOPER_TAC);

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
