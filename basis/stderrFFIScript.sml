open preamble
     cfHeapsBaseTheory

val _ = new_theory"stderrFFI";

val ffi_putChar_err_def = Define`
  ffi_putChar_err (conf:word8 list) (bytes:word8 list) out =
    case(bytes, out) of
    | ([w], out) => SOME ([w], out ++ [CHR (w2n w)])
    | _ => NONE`

val ffi_putChar_err_length = Q.store_thm("ffi_putChar_err_length",
  `ffi_putChar_err conf bytes out = SOME (bytes',out') ⇒ LENGTH bytes' = LENGTH bytes`,
  EVAL_TAC \\ every_case_tac \\ rw[] \\ Cases_on`bytes` \\ fs[NULL_EQ]
  \\ Cases_on`t` \\ fs[]);

val stderr_ffi_part_def = Define`
  stderr_ffi_part = (Str, destStr, [("putChar_err",ffi_putChar_err)])`;

val _ = export_theory();
