structure ml_translatorSyntax :> ml_translatorSyntax =
struct

open HolKernel boolLib ml_translatorTheory;

val ERR = Feedback.mk_HOL_ERR "ml_translatorSyntax";

val monop = HolKernel.syntax_fns1 "ml_translator"

val (EqualityType,mk_EqualityType,dest_EqualityType,is_EqualityType) = monop "EqualityType";
val (CONTAINER,mk_CONTAINER,dest_CONTAINER,is_CONTAINER) = monop "CONTAINER";
val (PRECONDITION,mk_PRECONDITION,dest_PRECONDITION,is_PRECONDITION) = monop "PRECONDITION";

val BOOL        = prim_mk_const{Thy="ml_translator",Name="BOOL"}
val WORD8       = prim_mk_const{Thy="ml_translator",Name="WORD8"}
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

fun mk_vector_type ty = mk_thy_type{Thy="ml_translator",Tyop="vector",Args=[ty]};

fun dest_vector_type ty =
  case total dest_thy_type ty
  of SOME {Thy="ml_translator", Tyop="vector", Args=[ty]} => ty
   | _ => raise ERR "dest_vector_type" ""

val is_vector_type = can dest_vector_type;

val (Eval,mk_Eval,dest_Eval,is_Eval) = HolKernel.syntax_fns3 "ml_translator" "Eval";
val (DeclAssum,mk_DeclAssum,dest_DeclAssum,is_DeclAssum) = HolKernel.syntax_fns4 "ml_translator" "DeclAssum";
val (Eq,mk_Eq,dest_Eq,is_Eq) = HolKernel.syntax_fns4 "ml_translator" "Eq";
val (Arrow,mk_Arrow,dest_Arrow,is_Arrow) = HolKernel.syntax_fns4 "ml_translator" "Arrow";

end
