open HolKernel Parse boolLib bossLib;

open wordsTheory llistTheory;

val _ = new_theory "ffi";

(* I/O events *)

val () = Datatype `
  io_event =
    (* An I/O event, IO_event n bytes2, calls FFI function n with input
       MAP FST bytes2 in the passed array, and the call returns with
       MAP SND bytes2 in the array. *)
    IO_event num ((word8 # word8) list)`;

(* An I/O trace can either be infinite or finite. A finite trace can
   end in a non-returning FFI call. *)

val _ = type_abbrev("io_trace",``:io_event llist``);
val _ = type_abbrev("fin_io_trace",``:io_event list``);

(* A program can Diverge, Terminate, or Fail. We prove that Fail is
   avoided. For Diverge and Terminate, we keep track of what I/O
   events are valid I/O events for this behaviour. *)

val () = Datatype `
  behaviour =
      (* There cannot be any non-returning FFI calls in a diverging
         exeuction. The list of I/O events can be finite or infinite,
         hence the llist (lazy list) type. *)
      Diverge (io_event llist)
      (* Terminating executions can only perform a finite number of
         FFI calls. The execution can be terminated by a non-returning
         FFI call. *)
    | Terminate (io_event list)
      (* Failure is a behaviour which we prove cannot occur for any
         well-typed program. *)
    | Fail`

val call_FFI_def = Define `
  call_FFI n bytes io_trace =
    case LHD io_trace of
    | SOME (IO_event n' xs) =>
        if (n = n') /\ (MAP FST xs = bytes) then
          SOME (MAP SND xs, THE (LTL io_trace))
        else NONE
    | _ => NONE`

val _ = export_theory();
