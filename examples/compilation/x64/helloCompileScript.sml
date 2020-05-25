(*
  Compiles the hello example by evaluation inside the logic of HOL
*)
open preamble compilationLib helloProgTheory

val _ = new_theory "helloCompile"

(*
val cs = compilation_compset()
val conf_def = x64_backend_config_def
val data_prog_name = "data_prog_x64"
val prog_def = hello_prog_def

time (compile_to_data cs conf_def prog_def) data_prog_name
but n.b. these cannot be trusted because of parallelism!
runtime: 2m35s,    gctime: 12.5s,     systime: 1.4s.
runtime: 2m28s,    gctime: 8.4s,     systime: 1.2s.
so, with wall clock time also:
wall: 1m22s, runtime: 2m38s,    gctime: 12.7s,     systime: 0.96333s.
wall: 1m23s, runtime: 2m37s,    gctime: 12.4s,     systime: 1.6s.
wall: 1m23s, runtime: 2m38s,    gctime: 13.8s,     systime: 1.5s.

time (cbv_compile_to_data cs conf_def prog_def) data_prog_name
runtime: 1m53s,    gctime: 13.9s,     systime: 0.87667s.
runtime: 1m49s,    gctime: 8.9s,     systime: 1.3s.
with wall clock time also:
wall: 1m50s, runtime: 1m50s,    gctime: 7.5s,     systime: 1.2s.
wall: 1m53s, runtime: 1m51s,    gctime: 9.2s,     systime: 1.4s.
wall: 1m51s, runtime: 1m50s,    gctime: 7.5s,     systime: 0.82000s.

(times taken on gemma 17 May 17 i7-4790 CPU @ 3.60GHz, 32GB RAM)
*)

(*

now, we use a smaller program, to get reasonable times for experimentation
val (hello_prog_tm,hello_prog_ls) = dest_eq (concl hello_prog_def)
val (ls,ty) = hello_prog_ls |> listSyntax.dest_list
val hello_prog_shorter_def =
  mk_thm([],mk_eq(hello_prog, listSyntax.mk_list(
    List.take(ls,20),ty)))

val to_data_shorter_thm =
  compile_to_data cs conf_def hello_prog_shorter_def "data_prog_shorter_x64";
val data_prog_shorter_x64_def = definition"data_prog_shorter_x64_def";

(*
val data_prog_x64_def = data_prog_shorter_x64_def
val to_data_thm = to_data_shorter_thm
*)

time (compile_to_lab_x64 data_prog_shorter_x64_def) to_data_shorter_thm
(these times are for taking the first 20 declarations - might want to try with even fewer)
wall: 1m56s, runtime: 2m28s,    gctime: 11.0s,     systime: 0.85667s.
wall: 1m46s, runtime: 2m13s,    gctime: 11.7s,     systime: 1.2s.
wall: 1m45s, runtime: 2m13s,    gctime: 10.8s,     systime: 1.0s.
wall: 1m45s, runtime: 2m13s,    gctime: 10.6s,     systime: 1.0s.

time (cbv_compile_to_lab_x64 data_prog_shorter_x64_def) to_data_shorter_thm
wall: 2m17s, runtime: 2m15s,    gctime: 9.6s,     systime: 1.1s.
wall: 2m03s, runtime: 2m02s,    gctime: 8.6s,     systime: 0.80333s.
wall: 2m04s, runtime: 2m03s,    gctime: 8.7s,     systime: 0.95000s.
wall: 2m06s, runtime: 2m04s,    gctime: 8.7s,     systime: 0.91333s.

(times taken on gemma 18 May 17 i7-4790 CPU @ 3.60GHz, 32GB RAM)
*)

(*
val stack_to_lab_thm =
  compile_to_lab_x64 data_prog_shorter_x64_def to_data_shorter_thm;
val lab_prog_def = definition"lab_prog_def";
val heap_mb = 500 val stack_mb = 500
val filename = "hello";

time (to_bytes_x64 stack_to_lab_thm lab_prog_def heap_mb stack_mb) filename
(these times are for the first 20 declarations above)
wall: 3m04s, runtime: 3m40s,    gctime: 23.5s,     systime: 2.3s. (this was cold, i.e., no encoder memoisation)
wall: 2m09s, runtime: 2m23s,    gctime: 11.7s,     systime: 1.5s.
wall: 2m12s, runtime: 2m26s,    gctime: 14.2s,     systime: 1.6s.

time (cbv_to_bytes_x64 stack_to_lab_thm lab_prog_def heap_mb stack_mb) filename
wall: 17s, runtime: 15.7s,    gctime: 2.9s,     systime: 0.26667s.  (hot, after the first run above)
wall: 17s, runtime: 16.5s,    gctime: 3.6s,     systime: 0.49333s.
wall: 16s, runtime: 15.8s,    gctime: 2.9s,     systime: 0.24333s.

(times taken on gemma 18 May 17 i7-4790 CPU @ 3.60GHz, 32GB RAM)
*)

val hello_compiled = save_thm("hello_compiled",
  compile_x64 "hello" hello_prog_def);

val _ = export_theory ();
