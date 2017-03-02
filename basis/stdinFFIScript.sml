open preamble
     cfHeapsBaseTheory

val _ = new_theory"stdinFFI";

val ffi_getChar_def = Define`
  ffi_getChar (bytes:word8 list) inp =
    case(bytes, inp) of
    | ([b;f], "") => SOME ([b; 1w], "")
    | ([b;f], h::t) => SOME ([n2w (ORD h); 0w], t)
    | _ => NONE`

val ffi_getChar_length = Q.store_thm("ffi_getChar_length",
  `ffi_getChar bytes inp = SOME (bytes',inp') ⇒ LENGTH bytes' = LENGTH bytes`,
  EVAL_TAC \\ every_case_tac \\ fs[]
  \\ Cases_on`bytes` \\ fs[NULL_EQ] \\ rw[] \\ rw[]
  \\ Cases_on`t` \\ fs[]);

val stdin_ffi_part_def = Define`
  stdin_ffi_part = (Str, destStr, [("getChar",ffi_getChar)])`;

val _ = export_theory();
