(*
  A simple instantiation of the ffi type.
*)
open HolKernel Parse boolLib bossLib;
open miscTheory ffiTheory;

val _ = new_theory "simpleIO"

Datatype:
  simpleIO = <| input :  word8 llist; output :  word8 llist |>
End

Definition isEof_def:
  isEof st (conf :word8 list) input =
    case input of
    | [] => Oracle_final FFI_failed
    | x::xs => Oracle_return st ((if st.input = [||] then 1w else 0w)::xs)
End

Definition getChar_def:
  getChar st (conf :word8 list) input =
    case input of
    | [] => Oracle_final FFI_failed
    | x::xs =>
        case LHD st.input of
        | NONE => Oracle_final FFI_failed
        | SOME y =>
            Oracle_return (st with input := THE (LTL st.input)) (y::xs)
End

Definition putChar_def:
  putChar st (conf :word8 list) input =
    case input of
    | [] => Oracle_final FFI_failed
    | x::v1 => Oracle_return (st with output := x:::st.output) input
End

Definition exit_def:
  exit (st :simpleIO) (conf :word8 list) (input :word8 list) = Oracle_final FFI_diverged
End

Definition simpleIO_oracle_def:
  simpleIO_oracle s st conf input =
    if s = "isEof" then isEof st conf input
    else if s = "getChar" then getChar st conf input
    else if s = "putChar" then putChar st conf input
    else if s = "exit" then exit st conf input
    else Oracle_final FFI_failed
End

val _ = export_theory()
