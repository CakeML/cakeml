open preamble
     cfHeapsBaseTheory

val _ = new_theory"clFFI";

(* Logical model of the commandline state: simply a list of char lists *)

(* a valid argument is non-empty, doesn't contain null, and is less than 256 long *)

val validArg_def = Define`
    validArg l <=>  (l <> []) /\ EVERY (\x. x <> #"\^@") l /\ LENGTH l < 256`;

val validArg_TOKENS = Q.store_thm("validArg_TOKENS",
  `!l. validArg l ==> TOKENS (\x. x = #"\^@") l = [l]`,
    Induct \\ rw[validArg_def, TOKENS_def]
    \\ pairarg_tac \\ fs[NULL_EQ] \\ rw[]
    >-(Cases_on `r` \\ imp_res_tac SPLITP_JOIN \\ fs[]
      \\ imp_res_tac SPLITP_NIL_IMP \\ fs[])
    >-(Cases_on `r` >-(imp_res_tac SPLITP_NIL_SND_EVERY \\ fs[])
      \\ imp_res_tac SPLITP_CONS_IMP \\ fs[] \\ full_simp_tac std_ss [EVERY_NOT_EXISTS])
    \\ Cases_on `r` >-(rw[TOKENS_def])
      \\ imp_res_tac SPLITP_CONS_IMP \\ fs[] \\ full_simp_tac std_ss [EVERY_NOT_EXISTS]
);

(* the sole FFI function over the commandline state, getArgs: *)

val ffi_getArgs_def = Define`
  ffi_getArgs (conf:word8 list) (bytes:word8 list) cls  =
    if LENGTH bytes = 256 /\ EVERY (\c. c = n2w 0) bytes then
      let cl = FLAT (MAP (\s. s ++ [CHR 0]) cls) in
        if (LENGTH cl < 257) then
          SOME(MAP (n2w o ORD) cl ++ DROP (LENGTH cl) bytes, cls)
        else
          SOME(MAP (n2w o ORD) (TAKE 256 cl), cls)
    else NONE`;

val ffi_getArgs_length = Q.store_thm("ffi_getArgs_length",
  `ffi_getArgs conf bytes cls = SOME (bytes',cls') ==> LENGTH bytes' = LENGTH bytes`,
  EVAL_TAC \\ rw[] \\ rw[]);

(* FFI part for the commandline *)

val encode_def = Define`encode = encode_list Str`;
val decode_def = Define`decode = decode_list destStr`;

val decode_encode = Q.store_thm("decode_encode[simp]",
  `decode (encode cls) = SOME cls`,
  EVAL_TAC \\ simp[OPT_MMAP_MAP_o]);

val cl_ffi_part_def = Define`
  cl_ffi_part = (encode,decode,[("getArgs",ffi_getArgs)])`;

val _ = export_theory();
