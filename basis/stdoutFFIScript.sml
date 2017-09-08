open preamble
     cfHeapsBaseTheory

val _ = new_theory"stdoutFFI";

val ffi_putChar_def = Define`
  ffi_putChar (conf:word8 list) (bytes:word8 list) out =
    case(bytes, out) of
    | ([w], out) => SOME ([w], out ++ [CHR (w2n w)])
    | _ => NONE`

val ffi_putChar_length = Q.store_thm("ffi_putChar_length",
  `ffi_putChar conf bytes out = SOME (bytes',out') ⇒ LENGTH bytes' = LENGTH bytes`,
  EVAL_TAC \\ every_case_tac \\ rw[] \\ Cases_on`bytes` \\ fs[NULL_EQ]
  \\ Cases_on`t` \\ fs[]);

val ffi_writeStr_def = Define`
    ffi_writeStr (conf:word8 list) (bytes:word8 list) out =
      SOME (bytes, out ++ TAKE 65535 (MAP (CHR o w2n) conf))`

val ffi_write_length = Q.store_thm("ffi_writeStr_length",
  `ffi_write conf bytes out = SOME (bytes',out') ⇒ LENGTH bytes' = LENGTH bytes`,
  EVAL_TAC \\ every_case_tac \\ rw[] \\ Cases_on`bytes` \\ fs[NULL_EQ]
  \\ Cases_on`t` \\ fs[]);

val stdout_ffi_part_def = Define`
  stdout_ffi_part = (Str, destStr, [("putChar",ffi_putChar);("writeStr",ffi_writeStr)])`;

val _ = export_theory();
