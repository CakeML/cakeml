open preamble
     cfHeapsBaseTheory

val _ = new_theory"clFFI";

(* Logical model of the commandline state: simply a list of char lists *)

(* a valid argument has a length that fits 16 bits *)

val validArg_def = Define`
    validArg l <=> LENGTH l < 256 * 256`;

(* there are 3 FFI functions over the commandline state: *)

val ffi_get_arg_count_def = Define `
  ffi_get_arg_count (conf:word8 list) (bytes:word8 list) args =
    if LENGTH bytes = 2 /\ LENGTH args < 256 * 256 then
      SOME ([n2w (LENGTH args);
             n2w (LENGTH args DIV 256)]:word8 list,args)
    else NONE`;

val ffi_get_arg_length_def = Define `
  ffi_get_arg_length (conf:word8 list) (bytes:word8 list) args =
    if LENGTH bytes = 2 /\ LENGTH args < 256 * 256 then
      (let index = w2n (EL 1 bytes) * 256 + w2n (EL 0 bytes) in
         if index < LENGTH args then
           SOME ([n2w (LENGTH (EL index args));
                  n2w (LENGTH (EL index args) DIV 256)]:word8 list,args)
         else NONE)
    else NONE`;

val ffi_get_arg_def = Define `
  ffi_get_arg (conf:word8 list) (bytes:word8 list) args =
    if 2 <= LENGTH bytes then
      (let index = w2n (EL 1 bytes) * 256 + w2n (EL 0 bytes) in
       let arg = EL index args in
         if index < LENGTH args /\ LENGTH (EL index args) <= LENGTH bytes then
           SOME (MAP (n2w o ORD) arg ++ DROP (LENGTH arg) bytes,args)
         else NONE)
      else NONE`;

(* lengths *)

val ffi_get_arg_count_length = store_thm("ffi_get_arg_count_length",
  ``ffi_get_arg_count conf bytes args = SOME (bytes',args') ==>
    LENGTH bytes' = LENGTH bytes``,
  fs [ffi_get_arg_count_def] \\ rw [] \\ fs []);

val ffi_get_arg_length_length = store_thm("ffi_get_arg_length_length",
  ``ffi_get_arg_length conf bytes args = SOME (bytes',args') ==>
    LENGTH bytes' = LENGTH bytes``,
  fs [ffi_get_arg_length_def] \\ rw [] \\ fs []);

val ffi_get_arg_length = store_thm("ffi_get_arg_length",
  ``ffi_get_arg conf bytes args = SOME (bytes',args') ==>
    LENGTH bytes' = LENGTH bytes``,
  fs [ffi_get_arg_def] \\ rw [] \\ fs []);

(* FFI part for the commandline *)

val encode_def = Define `encode = encode_list Str`;

val encode_11 = prove(
  ``!x y. encode x = encode y <=> x = y``,
  rw [] \\ eq_tac \\ fs [encode_def] \\ rw []
  \\ drule encode_list_11 \\ fs []);

val decode_encode = new_specification("decode_encode",["decode"],
  prove(``?decode. !cls. decode (encode cls) = SOME cls``,
        qexists_tac `\f. some c. encode c = f` \\ fs [encode_11]));
val _ = export_rewrites ["decode_encode"];

val cl_ffi_part_def = Define`
  cl_ffi_part = (encode,decode,
    [("get_arg_count",ffi_get_arg_count);
     ("get_arg_length",ffi_get_arg_length);
     ("get_arg",ffi_get_arg)])`;

val _ = export_theory();
