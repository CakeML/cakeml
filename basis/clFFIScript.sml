(*
  Logical model of the commandline state: simply a list of mlstrings
*)
open preamble
     cfHeapsBaseTheory

val _ = new_theory"clFFI";


(* a valid argument has a length that fits 16 bits and no null bytes *)

val validArg_def = Define`
    validArg s <=> strlen s < 256 * 256 /\ ~MEM (CHR 0) (explode s)`;

(* there are 3 FFI functions over the commandline state: *)

val get_arg_count_sig_def = Define
  `get_arg_count_sig =
   <| mlname := "get_arg_count";
       cname  := "ffiget_arg_count";
       retty  := NONE;
       args   := [C_array <| mutable := F; with_length := T |>;
                  C_array <| mutable := T; with_length := T |>]
    |>`

val get_arg_length_sig_def = Define
  `get_arg_length_sig =
   <| mlname := "get_arg_length";
       cname  := "ffiget_arg_length";
       retty  := NONE;
       args   := [C_array <| mutable := F; with_length := T |>;
                  C_array <| mutable := T; with_length := T |>]
    |>`

val get_arg_sig_def = Define
  `get_arg_sig =
   <| mlname := "get_arg";
       cname  := "ffiget_arg";
       retty  := NONE;
       args   := [C_array <| mutable := F; with_length := T |>;
                  C_array <| mutable := T; with_length := T |>]
    |>`

val ffi_get_arg_count_def = Define `
  ffi_get_arg_count [C_arrayv conf; C_arrayv bytes] _ args =
    if LENGTH bytes = 2 /\ LENGTH args < 256 * 256 then
      SOME (FFIreturn [[n2w (LENGTH args);
             n2w (LENGTH args DIV 256)]] NONE args)
    else NONE`;

val ffi_get_arg_length_def = Define `
  ffi_get_arg_length [C_arrayv conf; C_arrayv bytes] _ args =
    if LENGTH bytes = 2 /\ LENGTH args < 256 * 256 then
      (let index = w2n (EL 1 bytes) * 256 + w2n (EL 0 bytes) in
         if index < LENGTH args then
           SOME (FFIreturn [[n2w (strlen (EL index args));
                  n2w (strlen (EL index args) DIV 256)]] NONE args)
         else NONE)
    else NONE`;

val ffi_get_arg_def = Define `
  ffi_get_arg [C_arrayv conf; C_arrayv bytes] _ args =
    if 2 <= LENGTH bytes then
      (let index = w2n (EL 1 bytes) * 256 + w2n (EL 0 bytes) in
       let arg = EL index args in
         if index < LENGTH args /\ strlen (EL index args) <= LENGTH bytes then
           SOME (FFIreturn [MAP (n2w o ORD) (explode arg) ++ DROP (strlen arg) bytes] NONE args)
         else NONE)
      else NONE`;

(* lengths *)

Theorem ffi_get_arg_count_length:
   ffi_get_arg_count [C_arrayv conf; C_arrayv bytes] als args = SOME (FFIreturn [bytes'] retv args') ==>
    LENGTH bytes' = LENGTH bytes
Proof
  fs [ffi_get_arg_count_def] \\ rw [] \\ fs []
QED

Theorem ffi_get_arg_length_length:
   ffi_get_arg_length [C_arrayv conf; C_arrayv bytes] als args = SOME (FFIreturn [bytes'] retv args') ==>
    LENGTH bytes' = LENGTH bytes
Proof
  fs [ffi_get_arg_length_def] \\ rw [] \\ fs []
QED

Theorem ffi_get_arg_length:
   ffi_get_arg [C_arrayv conf; C_arrayv bytes] als args = SOME (FFIreturn [bytes'] retv args') ==>
    LENGTH bytes' = LENGTH bytes
Proof
  fs [ffi_get_arg_def] \\ rw [] \\ fs [mlstringTheory.LENGTH_explode]
QED

(* FFI part for the commandline *)

val encode_def = Define `encode = encode_list (Str o explode)`;

val encode_11 = prove(
  ``!x y. encode x = encode y <=> x = y``,
  rw [] \\ eq_tac \\ fs [encode_def] \\ rw []
  \\ drule encode_list_11 \\ fs [mlstringTheory.explode_11]);

val decode_encode = new_specification("decode_encode",["decode"],
  prove(``?decode. !cls. decode (encode cls) = SOME cls``,
        qexists_tac `\f. some c. encode c = f` \\ fs [encode_11]));
val _ = export_rewrites ["decode_encode"];

val cl_ffi_part_def = Define`
  cl_ffi_part = (encode,decode,
    [("get_arg_count",ffi_get_arg_count,get_arg_count_sig);
     ("get_arg_length",ffi_get_arg_length,get_arg_length_sig);
     ("get_arg",ffi_get_arg,get_arg_sig)])`;

val _ = export_theory();
