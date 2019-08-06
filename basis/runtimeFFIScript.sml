(*
  Logical model of the Runtime module's exit function calls.
*)
open preamble
     cfHeapsBaseTheory

val _ = new_theory"runtimeFFI";

val exit_sig_def = Define
  `exit_sig =
   <| mlname := "exit";
       cname  := "ffiexit";
       retty  := NONE;
       args   := [C_array <| mutable := F; with_length := T |>;
                  C_array <| mutable := T; with_length := T |>]
    |>`

val ffi_exit_def = Define `
 ffi_exit _ _ () = SOME(FFIdiverge:unit ffi_result)
  `

Theorem ffi_exit_length:
    ffi_exit args als u = SOME (FFIreturn bytes' retv args')
  ==> F
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
    [("exit",ffi_exit,exit_sig)])`;

val _ = export_theory();
