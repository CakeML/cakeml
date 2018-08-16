open preamble
     cfHeapsBaseTheory

val _ = new_theory"runtimeFFI";

val ffi_exit_def = Define `
 ffi_exit (conf:word8 list) (bytes:word8 list) () = SOME(FFIdiverge:unit ffi_result)
 `

(* FFI part for the runtime *)

val encode_def = Define `encode = K (List []):unit -> ffi`;

val decode_def = Define `decode = (K(SOME ())):ffi -> unit option`

val encode_11 = prove(
  ``!x y. encode x = encode y <=> x = y``,
  rw [encode_def]);

val decode_encode = Q.store_thm("decode_encode",
  `decode(encode cls) = SOME cls`, rw[decode_def,encode_def]);

val runtime_ffi_part_def = Define`
  runtime_ffi_part = (encode,decode,
    [("exit",ffi_exit)])`;

val _ = export_theory();
