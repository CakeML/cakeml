(*
  ML functions for manipulating HOL terms and types involving mlstrings.
*)
structure mlstringSyntax :> mlstringSyntax =
struct

open HolKernel boolLib mlstringTheory;

infix |->;

val ERR = Feedback.mk_HOL_ERR "mlstringSyntax";

val mlstring_ty = Type.mk_thy_type {Tyop = "mlstring", Thy = "mlstring", Args = []}

val monop = HolKernel.syntax_fns1 "mlstring"
val binop =
   HolKernel.syntax_fns
     {n = 2, dest = HolKernel.dest_binop, make = Lib.curry Term.mk_comb}
     "mlstring"

val (strlit_tm,mk_strlit,dest_strlit,is_strlit) = monop "strlit"
val (implode_tm,mk_implode,dest_implode,is_implode) = monop "implode"
val (explode_tm,mk_explode,dest_explode,is_explode) = monop "explode"
val (mlstring_case_tm,mk_mlstring_case,dest_mlstring_case,is_mlstring_case) = binop "mlstring_CASE"

fun is_mlstring_literal tm =
  stringSyntax.is_string_literal(dest_strlit tm)
  handle HOL_ERR _ => false

end
