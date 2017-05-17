open preamble compilationLib helloProgTheory

val _ = new_theory "helloCompile"

val cs = compilation_compset()
val conf_def = x64_backend_config_def
val data_prog_name = "data_prog_x64"
val prog_def = hello_prog_def

(*
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
*)

val hello_compiled = save_thm("hello_compiled",
  compile_x64 500 500 "hello" hello_prog_def);

val _ = export_theory ();
