(*
  Logical model of the Runtime module's exit function calls.
*)
open preamble
     cfHeapsBaseTheory

val _ = new_theory"runtimeFFI";

val ffi_exit_def = Define `
 ffi_exit (conf:word8 list) (bytes:word8 list) () = SOME(FFIdiverge:unit ffi_result)
  `

Theorem ffi_exit_length:
    ffi_exit (conf:word8 list) (bytes:word8 list) u = SOME (FFIreturn bytes' args')
  ==> LENGTH bytes' = LENGTH bytes
Proof
  Cases_on `u` \\ rw[ffi_exit_def]
QED

(* FFI part for the runtime *)

val encode_def = Define `encode = K (List []):unit -> ffi`;

val decode_def = Define `decode = (K(SOME ())):ffi -> unit option`

val encode_11 = prove(
  ``!x y. encode x = encode y <=> x = y``,
  rw [encode_def]);

Theorem decode_encode:
   decode(encode cls) = SOME cls
Proof
rw[decode_def,encode_def]
QED

val runtime_ffi_part_def = Define`
  runtime_ffi_part = (encode,decode,
    [("exit",ffi_exit)])`;

val _ = export_theory();
