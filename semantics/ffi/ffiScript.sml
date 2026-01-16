(*
  Definition of the FFI type
*)
Theory ffi
Ancestors
  misc mlstring

val _ = numLib.temp_prefer_num();

(*
  An oracle says how to perform an FFI call based on its internal
  state, represented by the type variable 'ffi.
*)

Datatype:
  ffi_outcome = FFI_failed | FFI_diverged
End

Datatype:
  oracle_result = Oracle_return 'ffi (word8 list) | Oracle_final ffi_outcome
End

Datatype:
  shmem_op = MappedRead | MappedWrite
End

Datatype:
  ffiname = ExtCall mlstring | SharedMem shmem_op
End

Type oracle_function = “:'ffi -> word8 list -> word8 list -> 'ffi oracle_result”
Type oracle = “:ffiname -> 'ffi oracle_function”

(* An I/O event, IO_event s bytes bytes2, represents the call of FFI function s with
 * immutable input bytes and mutable input map fst bytes2,
 * returning map snd bytes2 in the mutable array. *)

Datatype:
  io_event = IO_event ffiname (word8 list) ((word8 # word8) list)
End

Datatype:
  final_event = Final_event ffiname (word8 list) (word8 list) ffi_outcome
End

Datatype:
  ffi_state =
  <| oracle      : 'ffi oracle
   ; ffi_state   : 'ffi
   ; io_events   : io_event list
   |>
End

Definition initial_ffi_state_def:
  initial_ffi_state oc (ffi:'ffi) =
    <| oracle := oc; ffi_state := ffi; io_events := [] |>
End

Datatype:
  ffi_result = FFI_return ('ffi ffi_state) (word8 list)
             | FFI_final final_event
End

Definition call_FFI_def:
  call_FFI (st:'ffi ffi_state) s conf bytes =
    if s ≠ ExtCall «» then
      case st.oracle s st.ffi_state conf bytes of
        Oracle_return ffi' bytes' =>
          if LENGTH bytes' = LENGTH bytes then
            FFI_return
              (st with
               <|ffi_state := ffi';
                 io_events :=
                   st.io_events ++ [IO_event s conf (ZIP (bytes,bytes'))]|>)
              bytes'
          else FFI_final (Final_event s conf bytes FFI_failed)
      | Oracle_final outcome =>
        FFI_final (Final_event s conf bytes outcome)
    else FFI_return st bytes
End

Datatype:
  outcome = Success | Resource_limit_hit | FFI_outcome final_event
End

(* A program can Diverge, Terminate, or Fail. We prove that Fail is
   avoided. For Diverge and Terminate, we keep track of what I/O
   events are valid I/O events for this behaviour. *)
Datatype:
  behaviour =
    (* There cannot be any non-returning FFI calls in a diverging
       exeuction. The list of I/O events can be finite or infinite,
       hence the llist (lazy list) type. *)
    Diverge (io_event llist)
    (* Terminating executions can only perform a finite number of
       FFI calls. The execution can be terminated by a non-returning
       FFI call. *)
  | Terminate outcome (io_event list)
    (* Failure is a behaviour which we prove cannot occur for any
       well-typed program. *)
  | Fail
End

(* trace-based semantics can be recovered as an instance of oracle-based
 * semantics as follows. *)

Definition trace_oracle_def:
  trace_oracle s io_trace conf input =
    case LHD io_trace of
    | NONE => Oracle_final FFI_failed
    | SOME (IO_event s' conf' bytes2) =>
      if s = s' ∧ MAP FST bytes2 = input ∧ conf = conf' then
        Oracle_return (THE (LTL io_trace)) (MAP SND bytes2)
      else Oracle_final FFI_failed
End
