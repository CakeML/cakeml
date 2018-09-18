structure mlvectorSyntax :> mlvectorSyntax =
struct

open HolKernel boolLib mlvectorTheory;

val ERR = mk_HOL_ERR "mlvectorSyntax";

fun mk_vector_type ty = Type.mk_thy_type{Thy="regexp_compiler",Tyop="vector",Args=[ty]};

fun dest_vector_type ty =
  case total dest_thy_type ty
  of SOME {Thy="regexp_compiler", Tyop="vector", Args=[ty]} => ty
   | _ => raise ERR "dest_vector_type" ""

val is_vector_type = can dest_vector_type;

end
