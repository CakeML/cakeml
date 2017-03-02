open preamble
     cfHeapsBaseTheory

val _ = new_theory"stdoutFFI";

val ffi_putChar_def = Define`
  ffi_putChar bytes out =
    case(bytes, out) of
    | ([w], out) => SOME ([w], out ++ [CHR (w2n w)])
    | _ => NONE`

val stdout_ffi_part_def = Define`
  stdout_ffi_part = (Str, destStr, [("putChar",ffi_putChar)])`;

val _ = export_theory();
