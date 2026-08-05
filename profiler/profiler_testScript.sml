(*
  Simple theory to test the profiler.
*)

(* To use the profiler in your own theories:
 * - add $(CAKEMLDIR)/profiler (this directory) to INCLUDES of your Holmakefile
 * - add Profiler[qualified] to Libs
 * - add libraries to Libs that shadow existing functions (which includes
 *   tactics) with a profiling variant. These should not have the qualified tag,
 *   as they are supposed to shadow their non-profiling variants.
 *   Examples: profiler_base and profiler_cfml
 * - add a call to Profiler.export (or Profiler.export_cwd) at the bottom of
     your file
 * - use FlameGraph on the exported data (check documentation of Profiler.export
 *   for more information) *)

Theory profiler_test
Libs
  (* Test whether the libraries can be successfully loaded. *)
  Profiler[qualified] profiler_base profiler_cfml

(* We only check whether this function is callable. That is,
 * we do not check whether it creates a (valid) file. *)
val _ = Profiler.export_cwd "profiler_test.txt";
