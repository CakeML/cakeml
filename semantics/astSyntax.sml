structure astSyntax = struct
  local
  open HolKernel boolLib bossLib;
  open semanticPrimitivesSyntax astTheory;
  in
  fun id_ty tyM tyV = mk_thy_type{Thy="namespace",Tyop="id",Args=[tyM,tyV]};
  val str_id_ty = id_ty stringSyntax.string_ty stringSyntax.string_ty;
  val pat_ty = mk_thy_type{Thy="ast",Tyop="pat",Args=[]};
  val exp_ty = mk_thy_type{Thy="ast",Tyop="exp",Args=[]};
  val pat_exp_ty = pairSyntax.mk_prod(pat_ty,exp_ty);
  val dec_ty = mk_thy_type{Thy="ast",Tyop="dec",Args=[]};
  val decs_ty = listSyntax.mk_list_type dec_ty;
  val top_ty = mk_thy_type{Thy="ast",Tyop="top",Args=[]};
  val t_ty = mk_thy_type{Thy="ast",Tyop="t",Args=[]};
  val TC_int = prim_mk_const{Thy="ast",Name="TC_int"};
  val TC_char = prim_mk_const{Thy="ast",Name="TC_char"};
  val TC_string = prim_mk_const{Thy="ast",Name="TC_string"};
  val TC_ref = prim_mk_const{Thy="ast",Name="TC_ref"};
  val TC_word8 = prim_mk_const{Thy="ast",Name="TC_word8"};
  val TC_word64 = prim_mk_const{Thy="ast",Name="TC_word64"};
  val TC_word8array = prim_mk_const{Thy="ast",Name="TC_word8array"};
  val TC_fn = prim_mk_const{Thy="ast",Name="TC_fn"};
  val TC_tup = prim_mk_const{Thy="ast",Name="TC_tup"};
  val TC_exn = prim_mk_const{Thy="ast",Name="TC_exn"};
  val TC_vector = prim_mk_const{Thy="ast",Name="TC_vector"};
  val TC_array = prim_mk_const{Thy="ast",Name="TC_array"};
  local
    val s1 = HolKernel.syntax_fns1 "namespace"
    val s2 = HolKernel.syntax_fns2 "namespace" in
    val (Short_tm,mk_Short,dest_Short,is_Short) = s1 "Short"
    val mk_Short = (inst [``:'m`` |-> ``:tvarN``]) o mk_Short
    val (Long_tm,mk_Long,dest_Long,is_Long) = s2 "Long"
  end
  local val s = HolKernel.syntax_fns1 "ast" in
  val (Dtype_tm,mk_Dtype,dest_Dtype,is_Dtype) = s "Dtype"
  val (Dletrec_tm,mk_Dletrec,dest_Dletrec,is_Dletrec) = s "Dletrec"
  val (Tvar_tm,mk_Tvar,dest_Tvar,is_Tvar) = s "Tvar"
  val (Var_tm,mk_Var,dest_Var,is_Var) = s "Var"
  val (Pvar_tm,mk_Pvar,dest_Pvar,is_Pvar) = s "Pvar"
  val (Plit_tm,mk_Plit,dest_Plit,is_Plit) = s "Plit"
  val (Raise_tm,mk_Raise,dest_Raise,is_Raise) = s "Raise"
  val (TC_name_tm,mk_TC_name,dest_TC_name,is_TC_name) = s "TC_name"
  val (Tdec_tm,mk_Tdec,dest_Tdec,is_Tdec) = s "Tdec"
  val (Lit_tm,mk_Lit,dest_Lit,is_Lit) = s "Lit"
  end
  local val s = HolKernel.syntax_fns2 "ast" in
  val (Dexn_tm,mk_Dexn,dest_Dexn,is_Dexn) = s "Dexn"
  val (Dlet_tm,mk_Dlet,dest_Dlet,is_Dlet) = s "Dlet"
  val (Pcon_tm,mk_Pcon,dest_Pcon,is_Pcon) = s "Pcon"
  val (Tapp_tm,mk_Tapp,dest_Tapp,is_Tapp) = s "Tapp"
  val (Mat_tm,mk_Mat,dest_Mat,is_Mat) = s "Mat"
  val (Con_tm,mk_Con,dest_Con,is_Con) = s "Con"
  val (Fun_tm,mk_Fun,dest_Fun,is_Fun) = s "Fun"
  end
  local val s = HolKernel.syntax_fns3 "ast" in
  val (Dtabbrev_tm,mk_Dtabbrev,dest_Dtabbrev,is_Dtabbrev) = s "Dtabbrev"
  val (Tmod_tm,mk_Tmod,dest_Tmod,is_Tmod) = s "Tmod"
  end
  end
end
