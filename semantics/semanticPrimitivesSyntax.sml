structure semanticPrimitivesSyntax = struct
  local
  open HolKernel boolLib bossLib semanticPrimitivesTheory namespaceTheory;
  in
  val v_ty = mk_thy_type{Thy="semanticPrimitives",Tyop="v",Args=[]};
  fun mk_environment ty = mk_thy_type{Thy="semanticPrimitives",Tyop="sem_env",Args=[ty]};
  local val s = HolKernel.syntax_fns1 "semanticPrimitives" in
  val (ExnStamp_tm,mk_ExnStamp,dest_ExnStamp,is_ExnStamp) = s "ExnStamp"
  val (Litv_tm,mk_Litv,dest_Litv,is_Litv) = s "Litv"
  val (Vectorv_tm,mk_Vectorv,dest_Vectorv,is_Vectorv) = s "Vectorv"
  val (Loc_tm,mk_Loc,dest_Loc,is_Loc) = s "Loc"
  val (Rraise_tm,mk_Rraise,dest_Rraise,is_Rraise) = s "Rraise"
  val (Rabort_tm,mk_Rabort,dest_Rabort,is_Rabort) = s "Rabort"
  val (Rval_tm,mk_Rval,dest_Rval,is_Rval) = s "Rval"
  val (Rerr_tm,mk_Rerr,dest_Rerr,is_Rerr) = s "Rerr"
  val (Refv_tm,mk_Refv,dest_Refv,is_Refv) = s "Refv"
  val (W8array_tm,mk_W8array,dest_W8array,is_W8array) = s "W8array"
  val (Varray_tm,mk_Varray,dest_Varray,is_Varray) = s "Varray"
  end
  local val s = HolKernel.syntax_fns2 "semanticPrimitives" in
  val (TypeStamp_tm,mk_TypeStamp,dest_TypeStamp,is_TypeStamp) = s "TypeStamp"
  val (Conv_tm,mk_Conv,dest_Conv,is_Conv) = s "Conv"
  end
  local val s = HolKernel.syntax_fns3 "semanticPrimitives" in
  val (Recclosure_tm,mk_Recclosure,dest_Recclosure,is_Recclosure) = s "Recclosure"
  val (Closure_tm,mk_Closure,dest_Closure,is_Closure) = s "Closure"
  end
  end
end
