structure semanticPrimitivesSyntax = struct
  local
  open HolKernel boolLib bossLib semanticPrimitivesTheory;
  in
  val v_ty = mk_thy_type{Thy="semanticPrimitives",Tyop="v",Args=[]};
  val tid_or_exn_ty = mk_thy_type{Thy="semanticPrimitives",Tyop="tid_or_exn",Args=[]};
  fun mk_environment ty = mk_thy_type{Thy="semanticPrimitives",Tyop="environment",Args=[ty]};
  local val s = HolKernel.syntax_fns1 "semanticPrimitives" in
  val (TypeId_tm,mk_TypeId,dest_TypeId,is_TypeId) = s "TypeId"
  val (TypeExn_tm,mk_TypeExn,dest_TypeExn,is_TypeExn) = s "TypeExn"
  end
  local val s = HolKernel.syntax_fns2 "semanticPrimitives" in
  val (Conv_tm,mk_Conv,dest_Conv,is_Conv) = s "Conv"
  end
  local val s = HolKernel.syntax_fns3 "semanticPrimitives" in
  val (Recclosure_tm,mk_Recclosure,dest_Recclosure,is_Recclosure) = s "Recclosure"
  val (Closure_tm,mk_Closure,dest_Closure,is_Closure) = s "Closure"
  end
  end
end
