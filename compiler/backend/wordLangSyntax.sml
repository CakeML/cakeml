(*
  ML functions for dealing with the syntax of wordLang programs.
*)
structure wordLangSyntax = struct
  local
  open HolKernel boolLib bossLib;
  open wordLangTheory;
  in
  local val s = HolKernel.syntax_fns1 "wordLang" in
  val (Var_tm,mk_Var,dest_Var,is_Var) = s "Var"
  val (Const_tm,mk_Const,dest_Const,is_Const) = s "Const"
  val (Lookup_tm,mk_Lookup,dest_Lookup,is_Lookup) = s "Lookup"
  val (Load_tm,mk_Load,dest_Load,is_Load) = s "Load"
  val (Inst_tm,mk_Inst,dest_Inst,is_Inst) = s "Inst"
  end
  local val s = HolKernel.syntax_fns2 "wordLang" in
  val (Move_tm,mk_Move,dest_Move,is_Move) = s "Move"
  val (Get_tm,mk_Get,dest_Get,is_Get) = s "Get"
  val (Set_tm,mk_Set,dest_Set,is_Set) = s "Set"
  val (Seq_tm,mk_Seq,dest_Seq,is_Seq) = s "Seq"
  val (Return_tm,mk_Return,dest_Return,is_Return) = s "Return"
  end
  local val s = HolKernel.syntax_fns2 "wordLang" in
  val (Op_tm,mk_Op,dest_Op,is_Op) = s "Op"
  end
  local val s = HolKernel.syntax_fns3 "wordLang" in
  val (Shift_tm,mk_Shift,dest_Shift,is_Shift) = s "Shift"
  end
  end
end
