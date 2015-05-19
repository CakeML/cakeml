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

val () = Datatype `
  io_event_no_return =
    (* An FFI call might not return: IO_event_no_return n bytes
       represents a non-returning FFI call to FFI function n with
       bytes in the array that is passed to the FFI function. *)
    IO_event_no_return num (word8 list)`;

(* An I/O trace can either be infinite or finite. A finite trace can
   end in a non-returning FFI call. *)

val () = Datatype `
  io_trace =
      IO_inf (num -> io_event)
    | IO_fin (io_event list) (io_event_no_return option)`;

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
    | Terminate (io_event list) (io_event_no_return option)
      (* Failure is a behaviour which we prove cannot occur for any
         well-typed program. *)
    | Fail`

val _ = export_theory();
