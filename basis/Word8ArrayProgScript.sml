(*
  Module about the built-in byte-array type.
*)
Theory Word8ArrayProg
Ancestors
  Word8Prog
Libs
  preamble ml_translatorLib ml_progLib basisFunctionsLib

val _ = translation_extends "Word8Prog";
val cakeml = append_prog o process_topdecs;

val _ = ml_prog_update (add_dec
  ``Dtabbrev unknown_loc [] "byte_array" (Atapp [] (Short "word8array"))`` I);

val _ = ml_prog_update (open_module "Word8Array");

val _ = append_decs
   ``[mk_binop "array" Aw8alloc;
      mk_binop "sub" Aw8sub;
      mk_unop "length" Aw8length;
      Dlet unknown_loc (Pvar "update") (Fun "x" (Fun "y" (Fun "z"
        (App Aw8update [Var (Short "x"); Var (Short "y"); Var (Short "z")]))));
      Dlet unknown_loc (Pvar "copy")
        (Fun "src" (Fun "srcoff" (Fun "len" (Fun "dst" (Fun "dstoff"
        (App CopyAw8Aw8 [Var (Short "src");Var (Short "srcoff");Var (Short "len");
                         Var (Short "dst");Var (Short "dstoff")]))))));
      Dlet unknown_loc (Pvar "copyVec")
        (Fun "src" (Fun "srcoff" (Fun "len" (Fun "dst" (Fun "dstoff"
        (App CopyStrAw8 [Var (Short "src");Var (Short "srcoff");Var (Short "len");
                         Var (Short "dst");Var (Short "dstoff")]))))));
      Dlet unknown_loc (Pvar "substring")
        (Fun "src" (Fun "srcoff" (Fun "len"
        (App CopyAw8Str [Var (Short "src");Var (Short "srcoff");Var (Short "len")]))))]``;

val _ = ml_prog_update open_local_block;

Quote cakeml:
  fun findi_aux f arr max n =
    if n = max
      then None
    else (if f (sub arr n)
        then Some (n, sub arr n)
      else findi_aux f arr max (n + 1))
End

val _ = ml_prog_update open_local_in_block;

Quote cakeml:
  fun findi f arr =
    findi_aux f arr (length arr) 0
End

val _ = ml_prog_update close_local_blocks;

val _ = ml_prog_update (close_module NONE);

