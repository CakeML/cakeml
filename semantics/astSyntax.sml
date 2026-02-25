(*
  ML functions for manipulating HOL terms and types defined as part of the
  CakeML semantics, in particular CakeML abstract syntax.
*)
structure astSyntax = struct
  local
  open HolKernel boolLib bossLib;
  open semanticPrimitivesSyntax astTheory;
  in
  fun id_ty tyM tyV = mk_thy_type{Thy="namespace",Tyop="id",Args=[tyM,tyV]};
  val ml_str_id_ty = id_ty mlstringSyntax.mlstring_ty mlstringSyntax.mlstring_ty;
  (* types *)
  val lit_ty = mk_thy_type{Thy="ast",Tyop="lit",Args=[]};
  val shift_ty = mk_thy_type{Thy="ast",Tyop="shift",Args=[]};
  val word_size_ty = mk_thy_type{Thy="ast",Tyop="word_size",Args=[]};
  val op_ty = mk_thy_type{Thy="ast",Tyop="op",Args=[]};
  val ast_t_ty = mk_thy_type{Thy="ast",Tyop="ast_t",Args=[]};
  val pat_ty = mk_thy_type{Thy="ast",Tyop="pat",Args=[]};
  val exp_ty = mk_thy_type{Thy="ast",Tyop="exp",Args=[]};
  val dec_ty = mk_thy_type{Thy="ast",Tyop="dec",Args=[]};
  val pat_exp_ty = pairSyntax.mk_prod(pat_ty,exp_ty);
  val decs_ty = listSyntax.mk_list_type dec_ty;
  (* constants *)
  val Aalloc = prim_mk_const{Thy="ast",Name="Aalloc"};
  val AallocEmpty = prim_mk_const{Thy="ast",Name="AallocEmpty"};
  val Add = prim_mk_const{Thy="ast",Name="Add"};
  val Alength = prim_mk_const{Thy="ast",Name="Alength"};
  val And = prim_mk_const{Thy="ast",Name="And"};
  val Andalso = prim_mk_const{Thy="ast",Name="Andalso"};
  val Asr = prim_mk_const{Thy="ast",Name="Asr"};
  val Asub = prim_mk_const{Thy="ast",Name="Asub"};
  val Aupdate = prim_mk_const{Thy="ast",Name="Aupdate"};
  val Aw8alloc = prim_mk_const{Thy="ast",Name="Aw8alloc"};
  val Aw8length = prim_mk_const{Thy="ast",Name="Aw8length"};
  val Aw8sub = prim_mk_const{Thy="ast",Name="Aw8sub"};
  val Aw8update = prim_mk_const{Thy="ast",Name="Aw8update"};
  val ConfigGC = prim_mk_const{Thy="ast",Name="ConfigGC"};
  val CopyAw8Aw8 = prim_mk_const{Thy="ast",Name="CopyAw8Aw8"};
  val CopyAw8Str = prim_mk_const{Thy="ast",Name="CopyAw8Str"};
  val CopyStrAw8 = prim_mk_const{Thy="ast",Name="CopyStrAw8"};
  val CopyStrStr = prim_mk_const{Thy="ast",Name="CopyStrStr"};
  val Equality = prim_mk_const{Thy="ast",Name="Equality"};
  val Geq = prim_mk_const{Thy="ast",Name="Geq"};
  val Gt = prim_mk_const{Thy="ast",Name="Gt"};
  val Implode = prim_mk_const{Thy="ast",Name="Implode"};
  val Leq = prim_mk_const{Thy="ast",Name="Leq"};
  val Lsl = prim_mk_const{Thy="ast",Name="Lsl"};
  val Lsr = prim_mk_const{Thy="ast",Name="Lsr"};
  val Lt = prim_mk_const{Thy="ast",Name="Lt"};
  val Opapp = prim_mk_const{Thy="ast",Name="Opapp"};
  val Opassign = prim_mk_const{Thy="ast",Name="Opassign"};
  val Opderef = prim_mk_const{Thy="ast",Name="Opderef"};
  val Opref = prim_mk_const{Thy="ast",Name="Opref"};
  val Or = prim_mk_const{Thy="ast",Name="Or"};
  val Orelse = prim_mk_const{Thy="ast",Name="Orelse"};
  val Pany = prim_mk_const{Thy="ast",Name="Pany"};
  val Ror = prim_mk_const{Thy="ast",Name="Ror"};
  val Strcat = prim_mk_const{Thy="ast",Name="Strcat"};
  val Strlen = prim_mk_const{Thy="ast",Name="Strlen"};
  val Strsub = prim_mk_const{Thy="ast",Name="Strsub"};
  val Sub = prim_mk_const{Thy="ast",Name="Sub"};
  val VfromList = prim_mk_const{Thy="ast",Name="VfromList"};
  val Vlength = prim_mk_const{Thy="ast",Name="Vlength"};
  val Vsub = prim_mk_const{Thy="ast",Name="Vsub"};
  val W64 = prim_mk_const{Thy="ast",Name="W64"};
  val W8 = prim_mk_const{Thy="ast",Name="W8"};
  val Xor = prim_mk_const{Thy="ast",Name="Xor"};
  local
    val s1 = HolKernel.syntax_fns1 "namespace"
    val s2 = HolKernel.syntax_fns2 "namespace"
  in
    val (Short_tm,mk_Short,dest_Short,is_Short) = s1 "Short"
    val mk_Short = (inst [``:'m`` |-> ``:tvarN``]) o mk_Short
    val (Long_tm,mk_Long,dest_Long,is_Long) = s2 "Long"
  end
  local val s = HolKernel.syntax_fns1 "ast" in
  (* single-argument functions *)
  val (Attup_tm,mk_Attup,dest_Attup,is_Attup) = s "Attup";
  val (Atvar_tm,mk_Atvar,dest_Atvar,is_Atvar) = s "Atvar";
  val (Char_tm,mk_Char,dest_Char,is_Char) = s "Char";
  val (FFI_tm,mk_FFI,dest_FFI,is_FFI) = s "FFI";
  val (IntLit_tm,mk_IntLit,dest_IntLit,is_IntLit) = s "IntLit";
  val (Lit_tm,mk_Lit,dest_Lit,is_Lit) = s "Lit";
  val (Plit_tm,mk_Plit,dest_Plit,is_Plit) = s "Plit";
  val (Pref_tm,mk_Pref,dest_Pref,is_Pref) = s "Pref";
  val (Pvar_tm,mk_Pvar,dest_Pvar,is_Pvar) = s "Pvar";
  val (Raise_tm,mk_Raise,dest_Raise,is_Raise) = s "Raise";
  val (StrLit_tm,mk_StrLit,dest_StrLit,is_StrLit) = s "StrLit";
  val (Var_tm,mk_Var,dest_Var,is_Var) = s "Var";
  val (Word64_tm,mk_Word64,dest_Word64,is_Word64) = s "Word64";
  val (Word8_tm,mk_Word8,dest_Word8,is_Word8) = s "Word8";
  end
  local val s = HolKernel.syntax_fns2 "ast" in
  (* two-argument functions *)
  val (App_tm,mk_App,dest_App,is_App) = s "App";
  val (Atapp_tm,mk_Atapp,dest_Atapp,is_Atapp) = s "Atapp";
  val (Atfun_tm,mk_Atfun,dest_Atfun,is_Atfun) = s "Atfun";
  val (Con_tm,mk_Con,dest_Con,is_Con) = s "Con";
  val (Dletrec_tm,mk_Dletrec,dest_Dletrec,is_Dletrec) = s "Dletrec";
  val (Dmod_tm,mk_Dmod,dest_Dmod,is_Dmod) = s "Dmod";
  val (Dlocal_tm,mk_Dlocal,dest_Dlocal,is_Dlocal) = s "Dlocal";
  val (Dtype_tm,mk_Dtype,dest_Dtype,is_Dtype) = s "Dtype";
  val (Fun_tm,mk_Fun,dest_Fun,is_Fun) = s "Fun";
  val (Handle_tm,mk_Handle,dest_Handle,is_Handle) = s "Handle";
  val (Lannot_tm,mk_Lannot,dest_Lannot,is_Lannot) = s "Lannot";
  val (Letrec_tm,mk_Letrec,dest_Letrec,is_Letrec) = s "Letrec";
  val (Mat_tm,mk_Mat,dest_Mat,is_Mat) = s "Mat";
  val (Pcon_tm,mk_Pcon,dest_Pcon,is_Pcon) = s "Pcon";
  val (Ptannot_tm,mk_Ptannot,dest_Ptannot,is_Ptannot) = s "Ptannot";
  val (Tannot_tm,mk_Tannot,dest_Tannot,is_Tannot) = s "Tannot";
  end
  local val s = HolKernel.syntax_fns3 "ast" in
  (* three-argument functions *)
  val (Dexn_tm,mk_Dexn,dest_Dexn,is_Dexn) = s "Dexn";
  val (Dlet_tm,mk_Dlet,dest_Dlet,is_Dlet) = s "Dlet";
  val (If_tm,mk_If,dest_If,is_If) = s "If";
  val (Let_tm,mk_Let,dest_Let,is_Let) = s "Let";
  val (Log_tm,mk_Log,dest_Log,is_Log) = s "Log";
  val (Shift_tm,mk_Shift,dest_Shift,is_Shift) = s "Shift";
  end
  local val s = HolKernel.syntax_fns4 "ast" in
  (* four-argument functions *)
  val (Dtabbrev_tm,mk_Dtabbrev,dest_Dtabbrev,is_Dtabbrev) = s "Dtabbrev";
  end
  end
end
