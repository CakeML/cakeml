(*
  ML functions for manipulating the HOL terms and types defined in
  semanticPrimitivesTheory.
*)
structure semanticPrimitivesSyntax = struct
  local
  open HolKernel boolLib bossLib semanticPrimitivesTheory namespaceTheory;
  in
  (* types *)
  val abort_ty = mk_thy_type{Thy="semanticPrimitives",Tyop="abort",Args=[]};
  val eq_result_ty = mk_thy_type{Thy="semanticPrimitives",Tyop="eq_result",Args=[]};
  val error_result_ty = mk_thy_type{Thy="semanticPrimitives",Tyop="error_result",Args=[alpha]};
  val exp_or_val_ty = mk_thy_type{Thy="semanticPrimitives",Tyop="exp_or_val",Args=[]};
  val match_result_ty = mk_thy_type{Thy="semanticPrimitives",Tyop="match_result",Args=[alpha]};
  val result_ty = mk_thy_type{Thy="semanticPrimitives",Tyop="result",Args=[alpha,beta]};
  val sem_env_ty = mk_thy_type{Thy="semanticPrimitives",Tyop="sem_env",Args=[alpha]};
  val stamp_ty = mk_thy_type{Thy="semanticPrimitives",Tyop="stamp",Args=[]};
  val state_ty = mk_thy_type{Thy="semanticPrimitives",Tyop="state",Args=[alpha]};
  val store_v_ty = mk_thy_type{Thy="semanticPrimitives",Tyop="store_v",Args=[alpha]};
  val v_ty = mk_thy_type{Thy="semanticPrimitives",Tyop="v",Args=[]};
  (* constants *)
  val Eq_type_error = prim_mk_const{Thy="semanticPrimitives",Name="Eq_type_error"};
  val Match_type_error = prim_mk_const{Thy="semanticPrimitives",Name="Match_type_error"};
  val No_match = prim_mk_const{Thy="semanticPrimitives",Name="No_match"};
  val Rtimeout_error = prim_mk_const{Thy="semanticPrimitives",Name="Rtimeout_error"};
  val Rtype_error = prim_mk_const{Thy="semanticPrimitives",Name="Rtype_error"};
  val bind_exn_v = prim_mk_const{Thy="semanticPrimitives",Name="bind_exn_v"};
  val bind_stamp = prim_mk_const{Thy="semanticPrimitives",Name="bind_stamp"};
  val bool_type_num = prim_mk_const{Thy="semanticPrimitives",Name="bool_type_num"};
  val chr_exn_v = prim_mk_const{Thy="semanticPrimitives",Name="chr_exn_v"};
  val chr_stamp = prim_mk_const{Thy="semanticPrimitives",Name="chr_stamp"};
  val div_exn_v = prim_mk_const{Thy="semanticPrimitives",Name="div_exn_v"};
  val div_stamp = prim_mk_const{Thy="semanticPrimitives",Name="div_stamp"};
  val list_type_num = prim_mk_const{Thy="semanticPrimitives",Name="list_type_num"};
  val sub_exn_v = prim_mk_const{Thy="semanticPrimitives",Name="sub_exn_v"};
  val subscript_stamp = prim_mk_const{Thy="semanticPrimitives",Name="subscript_stamp"};
  fun mk_environment ty = mk_thy_type{Thy="semanticPrimitives",Tyop="sem_env",Args=[ty]};
  local val s = HolKernel.syntax_fns1 "semanticPrimitives" in
  (* single-argument functions *)
  val (Eq_val_tm,mk_Eq_val,dest_Eq_val,is_Eq_val) = s "Eq_val";
  val (ExnStamp_tm,mk_ExnStamp,dest_ExnStamp,is_ExnStamp) = s "ExnStamp";
  val (Exp_tm,mk_Exp,dest_Exp,is_Exp) = s "Exp";
  val (Litv_tm,mk_Litv,dest_Litv,is_Litv) = s "Litv";
  val (Loc_tm,mk_Loc,dest_Loc,is_Loc) = s "Loc";
  val (Match_tm,mk_Match,dest_Match,is_Match) = s "Match";
  val (Rabort_tm,mk_Rabort,dest_Rabort,is_Rabort) = s "Rabort";
  val (Refv_tm,mk_Refv,dest_Refv,is_Refv) = s "Refv";
  val (Rerr_tm,mk_Rerr,dest_Rerr,is_Rerr) = s "Rerr";
  val (Rraise_tm,mk_Rraise,dest_Rraise,is_Rraise) = s "Rraise";
  val (Rval_tm,mk_Rval,dest_Rval,is_Rval) = s "Rval";
  val (Val_tm,mk_Val,dest_Val,is_Val) = s "Val";
  val (Varray_tm,mk_Varray,dest_Varray,is_Varray) = s "Varray"
  val (Vectorv_tm,mk_Vectorv,dest_Vectorv,is_Vectorv) = s "Vectorv";
  val (W8array_tm,mk_W8array,dest_W8array,is_W8array) = s "W8array"
  end
  local val s = HolKernel.syntax_fns2 "semanticPrimitives" in
  (* two-argument functions *)
  val (Conv_tm,mk_Conv,dest_Conv,is_Conv) = s "Conv";
  val (TypeStamp_tm,mk_TypeStamp,dest_TypeStamp,is_TypeStamp) = s "TypeStamp";
  end
  local val s = HolKernel.syntax_fns3 "semanticPrimitives" in
  (* three-argument functions *)
  val (Closure_tm,mk_Closure,dest_Closure,is_Closure) = s "Closure";
  val (Recclosure_tm,mk_Recclosure,dest_Recclosure,is_Recclosure) = s "Recclosure";
  end
  end
end
