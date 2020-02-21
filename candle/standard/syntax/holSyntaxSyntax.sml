(*
  ML functions for constructing and picking apart terms arising from
  holSyntaxTheory.
*)
structure holSyntaxSyntax = struct
local
  open HolKernel holSyntaxTheory
in

  local
    val s = HolKernel.syntax_fns1 "holSyntax"
  in
    val (Tyvar_tm,mk_Tyvar,dest_Tyvar,is_Tyvar) = s "Tyvar"
    val (welltyped_tm,mk_welltyped,dest_welltyped,is_welltyped) = s "welltyped"
    val (typeof_tm,mk_typeof,dest_typeof,is_typeof) = s "typeof"
  end

  local
    val s = HolKernel.syntax_fns2 "holSyntax"
  in
    val (Tyapp_tm,mk_Tyapp,dest_Tyapp,is_Tyapp) = s "Tyapp"
    val (Var_tm,mk_Var,dest_Var,is_Var) = s "Var"
    val (Const_tm,mk_Const,dest_Const,is_Const) = s "Const"
    val (Comb_tm,mk_Comb,dest_Comb,is_Comb) = s "Comb"
    val (Abs_tm,mk_Abs,dest_Abs,is_Abs) = s "Abs"
    val (VFREE_IN_tm,mk_VFREE_IN,dest_VFREE_IN,is_VFREE_IN) = s "VFREE_IN"
    val (type_ok_tm,mk_type_ok,dest_type_ok,is_type_ok) = s "type_ok"
    val (term_ok_tm,mk_term_ok,dest_term_ok,is_term_ok) = s "term_ok"
    val (proves_tm,mk_proves,dest_proves,is_proves) = s "|-"
  end

  val type_ty = mk_thy_type{Thy="holSyntax",Tyop="type",Args=[]}
  val term_ty = mk_thy_type{Thy="holSyntax",Tyop="term",Args=[]}

end
end
