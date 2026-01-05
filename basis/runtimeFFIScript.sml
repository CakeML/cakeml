(*
  Logical model of the Runtime module's exit function calls.
*)
Theory runtimeFFI
Ancestors
  cfHeapsBase
Libs
  preamble

Definition ffi_exit_def:
 ffi_exit (conf:word8 list) (bytes:word8 list) () = SOME(FFIdiverge:unit ffi_result)
End

Theorem ffi_exit_length:
    ffi_exit (conf:word8 list) (bytes:word8 list) u = SOME (FFIreturn bytes' args')
  ==> LENGTH bytes' = LENGTH bytes
Proof
  Cases_on `u` \\ rw[ffi_exit_def]
QED

(* FFI part for the runtime *)

Definition encode_def:
  encode = K (List []):unit -> ffi
End

Definition decode_def:
  decode = (K(SOME ())):ffi -> unit option
End

Theorem encode_11[local]:
    !x y. encode x = encode y <=> x = y
Proof
  rw [encode_def]
QED

Theorem decode_encode:
   decode(encode cls) = SOME cls
Proof
rw[decode_def,encode_def]
QED

Definition runtime_ffi_part_def:
  runtime_ffi_part = (encode,decode,
    [("exit",ffi_exit)])
End

