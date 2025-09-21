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

Definition cont_closure_def:
  cont_closure [] cenv innerk = (case innerk of
  | NONE => VCl "t" cenv (EVar "t")
  | SOME k => strict_lookup cenv k) /\
  cont_closure (RCFn e::ks) cenv innerk = VCl ("m" ++ toString (count_rcarg ks)) cenv (cps_exp e (RCArg (EVar ("m" ++ toString (count_rcarg ks)))::ks) innerk) /\
  cont_closure (RCArg e::ks) cenv innerk = VCl "n" cenv (EApp (EApp (EVar "n") e) (cont_lambda ks innerk))
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
  >> gvs[forget_def, rich_cbv_step_def, rich_cbv_continue_def,
    cbv_step_def, cbv_continue_def, cat_ks_def, ctxt_with_env_def]
QED

Inductive vv_env_rel:
[~vv:]
  env_rel env cenv
  ==>
  vv_rel (VCl x env e) (VCl ("var" ++ x) cenv (EAbs "k" (cps_exp e [] (SOME "k"))))
[~env:]
  (! x . vv_rel (strict_lookup env x) (strict_lookup cenv ("var" ++ x)))
  ==>
  env_rel env cenv
End

Theorem vv_rel_cases = cj 1 vv_env_rel_cases;
Theorem env_rel_cases = cj 2 vv_env_rel_cases;

Inductive ve_rel:
[~TVar:]
  vv_rel v (strict_lookup cenv ("var" ++ x))
  ==>
  ve_rel (TVar x) v cenv (EVar ("var" ++ x))
[~TAbs:]
  env_rel env cenv
  ==>
  ve_rel TAbs (VCl x env e) cenv (EAbs ("var" ++ x) (EAbs "k" (cps_exp e [] (SOME "k"))))
End

Inductive m_val_rel:
[~Trivial:]
  ve_rel tag v cenv ce
  ==>
  m_val_rel (Trivial tag) v eks cenv ce
[~Computation:]
  vv_rel v (strict_lookup cenv ("m" ++ toString (count_rcarg eks)))
  ==>
  m_val_rel Computation v eks cenv (EVar ("m" ++ toString (count_rcarg eks)))
End

Inductive ks_rel:
[~Id:]
  ks_rel [] cenv []
[~RCFn:]
  ks_rel ks cenv eks
  ==>
  ks_rel (RCFn e::ks) cenv (RCFn e::eks)
[~RCArg:]
  ks_rel ks cenv eks /\
  m_val_rel vtype v eks cenv ce
  ==>
  ks_rel (RCArg (vtype, v)::ks) cenv (RCArg ce::eks)
End

Inductive scopes_rel:
[~NONE:]
  scopes_rel [] kenv NONE
[~SOME:]
  scopes_rel scopes kenv innerk /\
  ks_rel ks kenv eks /\
  strict_lookup cenv "k" = cont_closure eks kenv innerk
  ==>
  scopes_rel ((env, ks)::scopes) cenv (SOME "k")
End

Inductive opt_cps_rel:
[~RCExp:]
  ks_rel ks cenv eks /\
  env_rel env cenv /\
  scopes_rel scopes cenv innerk
  ==>
  opt_cps_rel ks env scopes (RCExp e) cenv (cps_exp e eks innerk)
[~RCVal_Trivial:]
  ks_rel ks cenv eks /\
  env_rel env cenv /\
  scopes_rel scopes cenv innerk /\
  ve_rel tag v cenv ce
  ==>
  opt_cps_rel ks env scopes (RCVal F tag v) cenv (app_cont eks ce innerk)
[~RCVal_Computation:]
  ks_rel ks kenv eks /\
  env_rel env kenv /\
  scopes_rel scopes kenv innerk /\
  ve_rel tag v cenv ce /\
  strict_lookup cenv "k" = cont_closure eks kenv innerk
  ==>
  opt_cps_rel ks env scopes (RCVal T tag v) cenv (EApp (EVar "k") ce)
End
