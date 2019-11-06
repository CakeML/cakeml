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
val binop = HolKernel.syntax_fns2 "mlstring"
val triop = HolKernel.syntax_fns3 "mlstring"
val cbinop =
   HolKernel.syntax_fns
     {n = 2, dest = HolKernel.dest_binop, make = Lib.curry Term.mk_comb}
     "mlstring"

val (implode_tm,mk_implode,dest_implode,is_implode) = monop "implode"
val (explode_tm,mk_explode,dest_explode,is_explode) = monop "explode"
val (strlen_tm,mk_strlen,dest_strlen,is_strlen) = monop "strlen"
val (strsub_tm,mk_strsub,dest_strsub,is_strsub) = binop "strsub"
val (strcat_tm,mk_strcat,dest_strcat,is_strcat) = binop "strcat"
val (concat_tm,mk_concat,dest_concat,is_concat) = monop "concat"
val (substring_tm,mk_substring,dest_substring,is_substring) = triop "substring"
val (mlstring_case_tm,mk_mlstring_case,dest_mlstring_case,is_mlstring_case) = cbinop "mlstring_CASE"

fun is_mlstring_literal tm =
  stringSyntax.is_string_literal(dest_implode tm)
  handle HOL_ERR _ => false

end
