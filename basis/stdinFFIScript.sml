open preamble
     cfHeapsBaseTheory

val _ = new_theory"stdinFFI";

val ffi_getChar_def = Define`
  ffi_getChar bytes inp =
    case(bytes, inp) of
    | ([b;f], "") => SOME ([b; 1w], "")
    | ([b;f], h::t) => SOME ([n2w (ORD h); 0w], t)
    | _ => NONE`

val stdin_ffi_part_def = Define`
  stdin_ffi_part = (Str, destStr, [("getChar",ffi_getChar)])`;

val _ = export_theory();
