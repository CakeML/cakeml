open HolKernel Parse boolLib bossLib;

open wordsTheory llistTheory;

val _ = new_theory "ffi";

val () = Datatype `io_event = IO_event num ((word8 # word8) list)`;

val () = type_abbrev("io_trace",``:io_event llist``);

val () = type_abbrev("io_trace",``:io_event llist``);

val () = type_abbrev("inf_io_trace",``:num -> io_event``);

val () = type_abbrev("fin_io_trace",``:io_event list``);

val () = Datatype `
  behaviour =
      (* diverges after finite number of returning FFI calls *)
      Diverge fin_io_trace
      (* diverges and might perform infinite FFI calls *)
    | DivergeInf inf_io_trace
      (* terminate after some returning FFI calls *)
    | Terminate fin_io_trace
      (* eventually calls a non-returning FFI call *)
    | TerminateExt fin_io_trace num (word8 list)`

val _ = export_theory();
