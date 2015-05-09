open HolKernel Parse boolLib bossLib;

open wordsTheory llistTheory;

val _ = new_theory "ffi_simple";

val () = Datatype `io_event = IO_event num ((word8 # word8) list)`;

val () = type_abbrev("io_trace",``:io_event llist``);

val () = Datatype `behaviour = Behaviour io_trace`

val _ = export_theory();
