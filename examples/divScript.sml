(*
  Examples of non-termination.
*)
open preamble basis

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
  fun condLoop n = repeat (if n = 0 then raise Terminate else n - 1) n;
  ` |> append_prog

val st = get_ml_prog_state ();

val condLoop_spec = store_thm("condLoop_spec",
  ``!n nv.
      INT n nv ==>
      app (p:'ffi ffi_proj) ^(fetch_v "condLoop" st) [nv]
        (one (FFI_full []))
        (POSTed (\e. cond (0 <= n)) (\io. io = [||] /\ n < 0))``,
  cheat);

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
