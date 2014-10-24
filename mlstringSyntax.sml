structure mlstringSyntax :> mlstringSyntax =
struct

open HolKernel boolLib mlstringTheory;

infix |->;

val ERR = Feedback.mk_HOL_ERR "mlstringSyntax";

val mlstring_ty = Type.mk_thy_type {Tyop = "mlstring", Thy = "mlstring", Args = []}

val monop =
   HolKernel.syntax_fns "mlstring" 1 HolKernel.dest_monop (Lib.curry Term.mk_comb)

val (strlit_tm,mk_strlit,dest_strlit,is_strlit) = monop "strlit"
val (implode_tm,mk_implode,dest_implode,is_implode) = monop "implode"
val (explode_tm,mk_explode,dest_explode,is_explode) = monop "explode"

fun is_mlstring_literal tm =
  stringSyntax.is_string_literal(dest_strlit tm)
  handle HOL_ERR _ => false

end
