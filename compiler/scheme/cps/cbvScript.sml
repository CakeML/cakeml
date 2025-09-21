(*
  Call-by-value lambda calculus
*)
Theory cbv
Ancestors
  namespace string
Libs
  preamble

Datatype:
  cbvexp = EVar string | EAbs string cbvexp | EApp cbvexp cbvexp
End

Type cbvenv = ``:(string, string, 'a) namespace``

Datatype:
  cbvval = VCl string (cbvval cbvenv) cbvexp
End

Datatype:
  cbvctxt = CFn (cbvval cbvenv) cbvexp | CArg cbvval
End

Datatype:
  cbvstate = CExp (cbvval cbvenv) cbvexp | CVal cbvval
End

Definition strict_lookup_def:
  strict_lookup env x = THE (nsLookup env (Short x))
End

Definition cbv_continue_def:
  cbv_continue [] v = ([], CVal v) /\
  cbv_continue (CFn env e::ks) v = ((CArg v::ks), CExp env e) /\
  cbv_continue (CArg vfn::ks) v = case vfn of
  | VCl x env e => (ks, CExp (nsBind x v env) e)
End

Definition cbv_step_def:
  cbv_step (ks, CVal v) = cbv_continue ks v /\
  cbv_step (ks, CExp env (EVar x)) = (ks, CVal (strict_lookup env x)) /\
  cbv_step (ks, CExp env (EAbs x e)) = (ks, CVal (VCl x env e)) /\
  cbv_step (ks, CExp env (EApp e1 e2)) = (CFn env e2::ks, CExp env e1)
End
