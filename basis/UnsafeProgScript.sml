(*
  This module defines functions for accessing CakeML's unsafe
  array primitives, i.e. primitives that crash if the index is
  out of bounds. This is not part of the basis.

  This script defines four functions:
    Unsafe.sub -- unsafe version of Array.sub
    Unsafe.update -- unsafe version of Array.update
    Unsafe.w8sub -- unsafe version of Word8Array.sub
    Unsafe.w8update -- unsafe version of Word8Array.update
*)
Theory UnsafeProg
Ancestors
  basisProg
Libs
  preamble ml_translatorLib ml_progLib basisFunctionsLib

val _ = translation_extends"basisProg"

val () = ml_prog_update (open_module "Unsafe");

val () = append_decs
   ``[mk_binop «sub» Asub_unsafe;
      Dlet unknown_loc (Pvar «update»)
       (Fun «x» (Fun «y» (Fun «z»
         (App Aupdate_unsafe [Var (Short «x»); Var (Short «y»); Var (Short «z»)])))) ]``;

val () = append_decs
   ``[mk_binop «w8sub» Aw8sub_unsafe;
      Dlet unknown_loc (Pvar «w8update»)
       (Fun «x» (Fun «y» (Fun «z»
         (App Aw8update_unsafe [Var (Short «x»); Var (Short «y»); Var (Short «z»)])))) ]``;

val () = append_decs
   ``[mk_binop «w8xor_str» XorAw8Str_unsafe]``;

Definition vsub_def[simp]:
  vsub v n = sub_unsafe v n
End

val _ = (next_ml_names := ["vsub"]);
val _ = translate vsub_def;
val _ = update_precondition (fetch "-" "vsub_side_def");

val _ = ml_prog_update (close_module NONE);
