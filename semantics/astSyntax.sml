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
  val ast_t_ty = mk_thy_type{Thy="ast",Tyop="ast_t",Args=[]};
  val Opapp = prim_mk_const{Thy="ast",Name="Opapp"};
  val And = prim_mk_const{Thy="ast",Name="And"};
  val Or = prim_mk_const{Thy="ast",Name="Or"};
  val Pany = prim_mk_const{Thy="ast",Name="Pany"};
  local
    val s1 = HolKernel.syntax_fns1 "namespace"
    val s2 = HolKernel.syntax_fns2 "namespace" in
    val (Short_tm,mk_Short,dest_Short,is_Short) = s1 "Short"
    val mk_Short = (inst [``:'m`` |-> ``:tvarN``]) o mk_Short
    val (Long_tm,mk_Long,dest_Long,is_Long) = s2 "Long"
  end
  local val s = HolKernel.syntax_fns1 "ast" in
  val (Atvar_tm,mk_Atvar,dest_Atvar,is_Atvar) = s "Atvar"
  val (Attup_tm,mk_Attup,dest_Attup,is_Attup) = s "Attup"
  val (Var_tm,mk_Var,dest_Var,is_Var) = s "Var"
  val (Pvar_tm,mk_Pvar,dest_Pvar,is_Pvar) = s "Pvar"
  val (Plit_tm,mk_Plit,dest_Plit,is_Plit) = s "Plit"
  val (Pref_tm,mk_Pref,dest_Pref,is_Pref) = s "Pref"
  val (Raise_tm,mk_Raise,dest_Raise,is_Raise) = s "Raise"
  val (Lit_tm,mk_Lit,dest_Lit,is_Lit) = s "Lit"
  end
  local val s = HolKernel.syntax_fns2 "ast" in
  val (Dtype_tm,mk_Dtype,dest_Dtype,is_Dtype) = s "Dtype"
  val (Dletrec_tm,mk_Dletrec,dest_Dletrec,is_Dletrec) = s "Dletrec"
  val (Pcon_tm,mk_Pcon,dest_Pcon,is_Pcon) = s "Pcon"
  val (Atapp_tm,mk_Atapp,dest_Atapp,is_Atapp) = s "Atapp"
  val (Atfun_tm,mk_Atfun,dest_Atfun,is_Atfun) = s "Atfun"
  val (Mat_tm,mk_Mat,dest_Mat,is_Mat) = s "Mat"
  val (Con_tm,mk_Con,dest_Con,is_Con) = s "Con"
  val (Fun_tm,mk_Fun,dest_Fun,is_Fun) = s "Fun"
  val (App_tm,mk_App,dest_App,is_App) = s "App"
  val (Handle_tm,mk_Handle,dest_Handle,is_Handle) = s "Handle"
  val (Letrec_tm,mk_Letrec,dest_Letrec,is_Letrec) = s "Letrec"
  val (Tannot_tm,mk_Tannot,dest_Tannot,is_Tannot) = s "Tannot"
  val (Lannot_tm,mk_Lannot,dest_Lannot,is_Lannot) = s "Lannot"
  val (Ptannot_tm,mk_Ptannot,dest_Ptannot,is_Ptannot) = s "Ptannot"
  val (Dmod_tm,mk_Dmod,dest_Dmod,is_Dmod) = s "Dmod"
  end
  local val s = HolKernel.syntax_fns3 "ast" in
  val (Dexn_tm,mk_Dexn,dest_Dexn,is_Dexn) = s "Dexn"
  val (Dlet_tm,mk_Dlet,dest_Dlet,is_Dlet) = s "Dlet"
  val (Let_tm,mk_Let,dest_Let,is_Let) = s "Let"
  val (Log_tm,mk_Log,dest_Log,is_Log) = s "Log"
  val (If_tm,mk_If,dest_If,is_If) = s "If"
  end
  local val s = HolKernel.syntax_fns4 "ast" in
  val (Dtabbrev_tm,mk_Dtabbrev,dest_Dtabbrev,is_Dtabbrev) = s "Dtabbrev"
  end
  end
end
