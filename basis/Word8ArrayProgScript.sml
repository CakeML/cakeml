(*
  Module about the built-in byte-array type.
*)
open preamble ml_translatorLib ml_progLib basisFunctionsLib
     Word8ProgTheory

val _ = new_theory "Word8ArrayProg";

val _ = translation_extends "Word8Prog";

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
        (App CopyAw8Str [Var (Short "src");Var (Short "srcoff");Var (Short "len")])))) ]``;

val _ = ml_prog_update (close_module NONE);

val _ = export_theory()
