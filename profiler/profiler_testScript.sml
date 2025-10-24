(*
  Simple theory to test the profiler.
*)

(* To use the profiler in your own theories, simply import the Profiler
 * library (ideally qualified to make sure there are no name clashes),
 * and libraries such as profiler_base to shadow definitions with
 * their profiling counterparts. Note that in the latter case we want
 * to shadow definitions, so you probably *do not* want to use qualified
 * for them. *)

Theory profiler_test
Libs
  (* Test whether the libraries can be successfully loaded. *)
  Profiler[qualified] profiler_base profiler_cfml

(* We only check whether this function is callable. That is,
 * we do not check whether it creates a (valid) file. *)
val _ = Profiler.export_cwd "profiler_test.txt";
