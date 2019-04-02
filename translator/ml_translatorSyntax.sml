(*
  Library for manipulating the HOL terms and types defined in
  ml_translatorTheory.
*)
structure ml_translatorSyntax :> ml_translatorSyntax =
struct

open HolKernel boolLib ml_translatorTheory semanticPrimitivesSyntax;

val ERR = Feedback.mk_HOL_ERR "ml_translatorSyntax";

val monop = HolKernel.syntax_fns1 "ml_translator"

val (EqualityType,mk_EqualityType,dest_EqualityType,is_EqualityType) = monop "EqualityType";
val (CONTAINER,mk_CONTAINER,dest_CONTAINER,is_CONTAINER) = monop "CONTAINER";
val (PRECONDITION,mk_PRECONDITION,dest_PRECONDITION,is_PRECONDITION) = monop "PRECONDITION";

val (_, mk_Conv_args, _, _) = monop "Conv_args"
val (_, mk_trivial4, dest_trivial4, _) = HolKernel.syntax_fns4 "ml_translator" "trivial4";

val BOOL        = prim_mk_const{Thy="ml_translator",Name="BOOL"}
val WORD       = prim_mk_const{Thy="ml_translator",Name="WORD"}
val NUM         = prim_mk_const{Thy="ml_translator",Name="NUM"}
val INT         = prim_mk_const{Thy="ml_translator",Name="INT"}
val CHAR        = prim_mk_const{Thy="ml_translator",Name="CHAR"}
val STRING_TYPE = prim_mk_const{Thy="ml_translator",Name="STRING_TYPE"}
val UNIT_TYPE   = prim_mk_const{Thy="ml_translator",Name="UNIT_TYPE"}

val (LIST_TYPE,mk_LIST_TYPE,dest_LIST_TYPE,is_LIST_TYPE) = HolKernel.syntax_fns3 "ml_translator" "LIST_TYPE";

val TRUE  = prim_mk_const{Thy="ml_translator",Name="TRUE"}
val FALSE = prim_mk_const{Thy="ml_translator",Name="FALSE"}

val binop = HolKernel.syntax_fns2 "ml_translator"
val (TAG,mk_TAG,dest_TAG,is_TAG) = binop "TAG";
val (PreImp,mk_PreImp,dest_PreImp,is_PreImp) = binop "PreImp";

val And_tm = prim_mk_const{Thy="ml_translator",Name="And"}
fun mk_And (x, y) = list_mk_icomb (And_tm, [x, y])

val binop = HolKernel.syntax_fns2 "ml_prog"
val (lookup_cons,mk_lookup_cons,dest_lookup_cons,is_lookup_cons) = binop "lookup_cons";
val (lookup_var,mk_lookup_var,dest_lookup_var,is_lookup_var) = binop "lookup_var";

val (Eval,mk_Eval,dest_Eval,is_Eval) = HolKernel.syntax_fns3 "ml_translator" "Eval";

fun mk_Eq(t1,t2) = let
  val (Eq,mk_Eq4,_,_) = HolKernel.syntax_fns4 "ml_translator" "Eq";
  val v1 = mk_var("v1",type_of t2)
  val v2 = mk_var("v2",v_ty)
  in mk_Eq4(t1,t2,v1,v2) |> rator |> rator end

fun mk_Arrow(t1,t2) = let
  val (Arrow,mk_Arrow4,dest_Arrow4,is_Arrow) =
    HolKernel.syntax_fns4 "ml_translator" "Arrow";
  val a = t1 |> type_of |> dest_type |> snd |> hd
  val b = t2 |> type_of |> dest_type |> snd |> hd
  val v1 = mk_var("v1",mk_type("fun",[a,b]))
  val v2 = mk_var("v1",v_ty)
  in mk_Arrow4(t1,t2,v1,v2) |> rator |> rator end

fun dest_Arrow t = let
  val (Arrow,mk_Arrow4,dest_Arrow4,is_Arrow) =
    HolKernel.syntax_fns4 "ml_translator" "Arrow";
  val t1 = t |> rator |> rand
  val t2 = t |> rand
  val a = t1 |> type_of |> dest_type |> snd |> hd
  val b = t2 |> type_of |> dest_type |> snd |> hd
  val v1 = mk_var ("v1", mk_type ("fun",[a,b]))
  val v2 = mk_var ("v2", v_ty)
  val (t1', t2', _, _) = dest_Arrow4 (list_mk_comb (t, [v1, v2]))
  in (t1', t2') end

fun is_Arrow t = can dest_Arrow t

fun strip_Arrow t = let
  val (t1, t2) = dest_Arrow t
in
  if is_Arrow t2 then
    let val (t2_args, t2_ret) = strip_Arrow t2
    in (t1::t2_args, t2_ret) end
  else
    ([t1], t2)
end

val (write,mk_write,dest_write,is_write) = HolKernel.syntax_fns3 "ml_prog" "write";

end
