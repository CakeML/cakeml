(*
  This module defines functions for accessing CakeML's unsafe
  array primitives, i.e. primitives that crash if the index is
  out of bounds. This is not part of the basis.

  This script defines four functions:
    Unsafe.Array.sub
    Unsafe.Array.update
    Unsafe.Word8Array.sub
    Unsafe.Word8Array.update
*)
open preamble ml_translatorLib ml_progLib basisFunctionsLib
     basisProgTheory

val _ = new_theory"UnsafeProg"

val _ = translation_extends"basisProg"

val () = ml_prog_update (open_module "Unsafe");

val () = ml_prog_update (open_module "Array");

val () = append_decs
   ``[mk_binop "sub" Asub_unsafe;
      Dlet unknown_loc (Pvar "update")
       (Fun "x" (Fun "y" (Fun "z"
         (App Aupdate_unsafe [Var (Short "x"); Var (Short "y"); Var (Short "z")])))) ]``;

val _ = ml_prog_update (close_module NONE);

val () = ml_prog_update (open_module "Word8Array");

val () = append_decs
   ``[mk_binop "sub" Aw8sub_unsafe;
      Dlet unknown_loc (Pvar "update")
       (Fun "x" (Fun "y" (Fun "z"
         (App Aw8update_unsafe [Var (Short "x"); Var (Short "y"); Var (Short "z")])))) ]``;

val _ = ml_prog_update (close_module NONE);

val _ = ml_prog_update (close_module NONE);

val _ = export_theory ()
