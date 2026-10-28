(*
  This module defines functions for accessing CakeML's unsafe
  array primitives, i.e. primitives that crash if the index is
  out of bounds. This is not part of the basis.

  This script defines the following functions:
    Unsafe.sub -- unsafe version of Array.sub
    Unsafe.update -- unsafe version of Array.update
    Unsafe.w8sub -- unsafe version of Word8Array.sub
    Unsafe.w8update -- unsafe version of Word8Array.update
    Unsafe.w8subBit -- unsafe version of Word8Array.subBit
    Unsafe.w8updateBit -- unsafe version of Word8Array.updateBit
    Unsafe.strsub -- unsafe version of String.sub
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
      Dlet NoLocs (Pvar «update»)
       (Fun «x» (Fun «y» (Fun «z»
         (App Aupdate_unsafe [Var (Short «x»); Var (Short «y»); Var (Short «z»)])))) ]``;

val () = append_decs
   ``[mk_binop «w8sub» Aw8sub_unsafe;
      Dlet NoLocs (Pvar «w8update»)
       (Fun «x» (Fun «y» (Fun «z»
         (App Aw8update_unsafe [Var (Short «x»); Var (Short «y»); Var (Short «z»)])))) ]``;

val () = append_decs
   ``[mk_binop «w8subBit» Aw8subBit_unsafe;
      Dlet NoLocs (Pvar «w8updateBit»)
       (Fun «x» (Fun «y» (Fun «z»
         (App Aw8updateBit_unsafe [Var (Short «x»); Var (Short «y»); Var (Short «z»)])))) ]``;

val () = append_decs
   ``[mk_binop «w8xor_str» XorAw8Str_unsafe]``;

Definition vsub_def[simp]:
  vsub v n = sub_unsafe v n
End

val _ = (next_ml_names := ["vsub"]);
val _ = translate vsub_def;
val _ = update_precondition (fetch "-" "vsub_side_def");

Definition unsafe_strsub_def[simp]:
  unsafe_strsub s n = strsub_unsafe s n
End

val _ = (next_ml_names := ["strsub"]);
val _ = translate unsafe_strsub_def;
val _ = update_precondition (fetch "-" "unsafe_strsub_side_def");

val _ = ml_prog_update (open_module "Arith");

val () = append_decs
   ``[mk_binop «+» (UnsafeIndexArith Add);
      mk_binop «-» (UnsafeIndexArith Sub);
      mk_binop «*» (UnsafeIndexArith Mul);
      mk_binop «div» (UnsafeIndexArith Div);
      mk_binop «mod» (UnsafeIndexArith ast$Mod);
      mk_binop «<» (UnsafeIndexTest (Compare Lt));
      mk_binop «<=» (UnsafeIndexTest (Compare Leq));
      mk_binop «>» (UnsafeIndexTest (Compare Gt));
      mk_binop «>=» (UnsafeIndexTest (Compare Geq));
      mk_binop «=» (UnsafeIndexTest Equal)]``;

val () = append_decs
   ``[Dlet NoLocs (Pvar «addWitness»)
        (Fun «x» (Fun «y» (Fun «witness»
          (App (UnsafeIndexArith Add)
            [Var (Short «x»); Var (Short «y»); Var (Short «witness»)]))));
      Dlet NoLocs (Pvar «subWitness»)
        (Fun «x» (Fun «y» (Fun «witness»
          (App (UnsafeIndexArith Sub)
            [Var (Short «x»); Var (Short «y»); Var (Short «witness»)]))));
      Dlet NoLocs (Pvar «mulWitness»)
        (Fun «x» (Fun «y» (Fun «witness»
          (App (UnsafeIndexArith Mul)
            [Var (Short «x»); Var (Short «y»); Var (Short «witness»)]))));
      Dlet NoLocs (Pvar «divWitness»)
        (Fun «x» (Fun «y» (Fun «witness»
          (App (UnsafeIndexArith Div)
            [Var (Short «x»); Var (Short «y»); Var (Short «witness»)]))));
      Dlet NoLocs (Pvar «modWitness»)
        (Fun «x» (Fun «y» (Fun «witness»
          (App (UnsafeIndexArith ast$Mod)
            [Var (Short «x»); Var (Short «y»); Var (Short «witness»)]))));
      Dlet NoLocs (Pvar «ltWitness»)
        (Fun «x» (Fun «y» (Fun «witness»
          (App (UnsafeIndexTest (Compare Lt))
            [Var (Short «x»); Var (Short «y»); Var (Short «witness»)]))));
      Dlet NoLocs (Pvar «leWitness»)
        (Fun «x» (Fun «y» (Fun «witness»
          (App (UnsafeIndexTest (Compare Leq))
            [Var (Short «x»); Var (Short «y»); Var (Short «witness»)]))));
      Dlet NoLocs (Pvar «gtWitness»)
        (Fun «x» (Fun «y» (Fun «witness»
          (App (UnsafeIndexTest (Compare Gt))
            [Var (Short «x»); Var (Short «y»); Var (Short «witness»)]))));
      Dlet NoLocs (Pvar «geWitness»)
        (Fun «x» (Fun «y» (Fun «witness»
          (App (UnsafeIndexTest (Compare Geq))
            [Var (Short «x»); Var (Short «y»); Var (Short «witness»)]))));
      Dlet NoLocs (Pvar «eqWitness»)
        (Fun «x» (Fun «y» (Fun «witness»
          (App (UnsafeIndexTest Equal)
            [Var (Short «x»); Var (Short «y»); Var (Short «witness»)]))))]``;

val _ = ml_prog_update (close_module NONE);

val _ = ml_prog_update (close_module NONE);
