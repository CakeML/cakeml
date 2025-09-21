(*
  Optimised CPS transform for call-by-value lambda calculus
*)
Theory optCps
Ancestors
  cbv namespaceProps
Libs
  preamble

Datatype:
  richcbvctxt = RCFn cbvexp | RCArg 'a
End

Datatype:
  valtag = TVar string | TAbs
End

Datatype:
  richcbvstate = RCExp cbvexp | RCVal bool valtag cbvval
End

Datatype:
  valtype = Trivial valtag | Computation
End

Definition count_rcarg_def:
  count_rcarg [] = 0 /\
  count_rcarg (RCFn _::ks) = count_rcarg ks /\
  count_rcarg (RCArg _::ks) = SUC (count_rcarg ks)
End

Definition opt_cps_def:
  cps_exp (EVar x) ks innerk = app_cont ks (EVar ("var" ++ x)) innerk /\
  cps_exp (EAbs x e) ks innerk = app_cont ks (EAbs ("var" ++ x) (EAbs "k" (cps_exp e [] (SOME "k")))) innerk /\
  cps_exp (EApp e1 e2) ks innerk = cps_exp e1 (RCFn e2::ks) innerk /\

  app_cont [] e innerk = (case innerk of
  | NONE => e
  | SOME k => EApp (EVar k) e) /\
  app_cont (RCFn e'::ks) e innerk = cps_exp e' (RCArg e::ks) innerk /\
  app_cont (RCArg e'::ks) e innerk = EApp (EApp e' e) (cont_lambda ks innerk) /\

  cont_lambda [] innerk = (case innerk of
  | NONE => EAbs "t" (EVar "t")
  | SOME k => EVar k) /\
  cont_lambda (RCFn e::ks) innerk = EAbs ("m" ++ toString (count_rcarg ks)) (cps_exp e (RCArg (EVar ("m" ++ toString (count_rcarg ks)))::ks) innerk) /\
  cont_lambda (RCArg e::ks) innerk = EAbs "n" (EApp (EApp (EVar "n") e) (cont_lambda ks innerk))
Termination
  cheat
End

Definition rich_cbv_continue_def:
  rich_cbv_continue [] env scopes comp tag v = (case scopes of
  | [] => ([], env, [], RCVal comp tag v)
  | (env', ks)::scopes' => (ks, env', scopes', RCVal T tag v)) /\
  rich_cbv_continue (RCFn e::ks) env scopes comp tag v = (if comp
    then ((RCArg (Computation, v)::ks), env, scopes, RCExp e)
    else ((RCArg (Trivial tag, v)::ks), env, scopes, RCExp e)) /\
  rich_cbv_continue (RCArg (vtype, vfn)::ks) env scopes comp tag v = (case vfn of
  | VCl x env' e => ([], nsBind x v env', (env, ks)::scopes, RCExp e))
End

Definition rich_cbv_step_def:
  rich_cbv_step (ks, env, scopes, RCVal comp tag v) = rich_cbv_continue ks env scopes comp tag v /\
  rich_cbv_step (ks, env, scopes, RCExp (EVar x)) = (ks, env, scopes, RCVal F (TVar x) (strict_lookup env x)) /\
  rich_cbv_step (ks, env, scopes, RCExp (EAbs x e)) = (ks, env, scopes, RCVal F TAbs (VCl x env e)) /\
  rich_cbv_step (ks, env, scopes, RCExp (EApp e1 e2)) = (RCFn e2::ks, env, scopes, RCExp e1)
End

Definition ctxt_with_env_def:
  ctxt_with_env env (RCFn e) = CFn env e /\
  ctxt_with_env env (RCArg (vtype, v)) = CArg v
End

Definition cat_ks_def:
  cat_ks ks env scopes = FLAT (MAP (\(env, ks). MAP (ctxt_with_env env) ks) ((env, ks)::scopes))
End

Definition forget_def:
  forget (ks, env, scopes, RCVal comp tag v) = (cat_ks ks env scopes, CVal v) /\
  forget (ks, env, scopes, RCExp e) = (cat_ks ks env scopes, CExp env e)
End

Theorem forget_rich:
  ! ks ks' env env' scopes scopes' e e' .
    rich_cbv_step (ks, env, scopes, e) = (ks', env', scopes', e')
    ==>
    cbv_step (forget (ks, env, scopes, e)) = forget (ks', env', scopes', e') \/
    forget (ks, env, scopes, e) = forget (ks', env', scopes', e')
Proof
  rpt strip_tac
  >> Cases_on `e`
  >~ [`RCExp e`] >>> HEADGOAL $ Cases_on `e`
  >~ [`RCVal comp tag v`]
  >>> HEADGOAL (
    Cases_on `ks`
    >~ [`k::ks'`]
    >>> HEADGOAL (
      Cases_on `k`
      >~ [`RCFn e`] >>> HEADGOAL $ Cases_on `comp`
      >~ [`RCArg tagv`]
      >>> HEADGOAL (
        PairCases_on `tagv`
        >> Cases_on `tagv1`
      )
    )
    >>> LASTGOAL (
      Cases_on `scopes`
      >~ [`scope::scopes'`]
      >>> HEADGOAL $ PairCases_on `scope`
    )
  )
  >> gvs[forget_def, rich_cbv_step_def, rich_cbv_continue_def, cbv_step_def, cbv_continue_def, cat_ks_def, ctxt_with_env_def]
QED
