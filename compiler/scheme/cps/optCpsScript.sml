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
  valtag = Trivial | Computation
End

Datatype:
  richcbvstate = RCExp cbvexp | RCVal valtag cbvval
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
  cont_lambda (RCArg e::ks) innerk = EAbs "n" (EApp (EApp e (EVar "n")) (cont_lambda ks innerk))
Termination
  cheat
End

Definition cont_closure_def:
  cont_closure [] cenv innerk = (case innerk of
  | NONE => VCl "t" cenv (EVar "t")
  | SOME k => strict_lookup cenv k) /\
  cont_closure (RCFn e::ks) cenv innerk = VCl ("m" ++ toString (count_rcarg ks)) cenv (cps_exp e (RCArg (EVar ("m" ++ toString (count_rcarg ks)))::ks) innerk) /\
  cont_closure (RCArg e::ks) cenv innerk = VCl "n" cenv (EApp (EApp e (EVar "n")) (cont_lambda ks innerk))
End

Theorem cont_lambda_eval:
  ! eks cenv innerk . ? m . ! ks . cbv_steps m (ks, CExp cenv (cont_lambda eks innerk)) = (ks, CVal (cont_closure eks cenv innerk))
Proof
  rpt strip_tac
  >> Cases_on `eks` >>> HEADGOAL $ Cases_on `innerk`
  >~ [`ek::eks`] >>> HEADGOAL $ Cases_on `ek`
  >> simp[opt_cps_def, cont_closure_def]
  >> qrefine `1`
  >> simp[cbv_steps, cbv_step_def]
QED

Definition rich_cbv_continue_def:
  rich_cbv_continue [] env scopes tag v = (case scopes of
  | [] => ([], env, [], RCVal tag v)
  | (env', ks)::scopes' => (ks, env', scopes', RCVal Computation v)) /\
  rich_cbv_continue (RCFn e::ks) env scopes tag v = ((RCArg (tag, v)::ks), env, scopes, RCExp e) /\
  rich_cbv_continue (RCArg (vtype, vfn)::ks) env scopes tag v = (case vfn of
  | VCl x env' e => ([], nsBind x v env', (env, ks)::scopes, RCExp e))
End

Definition rich_cbv_step_def:
  rich_cbv_step (ks, env, scopes, RCVal tag v) = rich_cbv_continue ks env scopes tag v /\
  rich_cbv_step (ks, env, scopes, RCExp (EVar x)) = (ks, env, scopes, RCVal Trivial (strict_lookup env x)) /\
  rich_cbv_step (ks, env, scopes, RCExp (EAbs x e)) = (ks, env, scopes, RCVal Trivial (VCl x env e)) /\
  rich_cbv_step (ks, env, scopes, RCExp (EApp e1 e2)) = (RCFn e2::ks, env, scopes, RCExp e1)
End

Definition ctxt_with_env_def:
  ctxt_with_env env (RCFn e) = CFn env e /\
  ctxt_with_env env (RCArg (tag, v)) = CArg v
End

Definition cat_ks_def:
  cat_ks ks env scopes = FLAT (MAP (\(env, ks). MAP (ctxt_with_env env) ks) ((env, ks)::scopes))
End

Definition forget_def:
  forget (ks, env, scopes, RCVal tag v) = (cat_ks ks env scopes, CVal v) /\
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
  >~ [`RCVal tag v`]
  >>> HEADGOAL (
    Cases_on `ks`
    >~ [`k::ks'`]
    >>> HEADGOAL (
      Cases_on `k`
      >~ [`RCFn e`] >>> HEADGOAL $ Cases_on `tag`
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

Theorem env_rel_sync:
  ! v cv env cenv x .
    vv_rel v cv
    ==>
    env_rel env cenv ==> env_rel (nsBind x v env) (nsBind ("var" ++ x) cv cenv)
Proof
  rpt strip_tac
  >> gvs[env_rel_cases]
  >> qx_gen_tac `y`
  >> Cases_on `x = y`
  >> gvs[strict_lookup_def]
QED

Theorem env_rel_sync[allow_rebind] = SRULE [] env_rel_sync;

Theorem env_rel_indifference:
  ! var env cenv cv .
    (! x . var <> "var" ++ x)
    ==>
    env_rel env cenv ==> env_rel env (nsBind var cv cenv)
Proof
  simp[env_rel_cases, strict_lookup_def]
QED

Theorem env_rel_indifference[allow_rebind, simp] = SRULE [] env_rel_indifference;

Inductive ve_rel:
[~TVar:]
  vv_rel v (strict_lookup cenv ("var" ++ x))
  ==>
  ve_rel v cenv (EVar ("var" ++ x))
[~TAbs:]
  env_rel env cenv
  ==>
  ve_rel (VCl x env e) cenv (EAbs ("var" ++ x) (EAbs "k" (cps_exp e [] (SOME "k"))))
End

Theorem ve_rel_eval:
  ! v cenv ce .
    ve_rel v cenv ce
    ==>
    ? m cv .
      (! ks . cbv_steps m (ks, CExp cenv ce) = (ks, CVal cv)) /\
      vv_rel v cv
Proof
  rpt strip_tac
  >> gvs[Once ve_rel_cases]
  >> qexists `1`
  >> simp[cbv_steps, cbv_step_def]
  >> simp[Once vv_rel_cases]
QED

Theorem ve_rel_indifference:
  ! var cv v cenv ce .
    (! x . var <> "var" ++ x)
    ==>
    ve_rel v cenv ce ==> ve_rel v (nsBind var cv cenv) ce
Proof
  rpt strip_tac
  >> gvs[Once ve_rel_cases]
  >> simp[Once ve_rel_cases]
  >> simp[env_rel_indifference]
  >> gvs[strict_lookup_def]
QED

Inductive m_val_rel:
[~Trivial:]
  ve_rel v cenv ce
  ==>
  m_val_rel Trivial v eks cenv ce
[~Computation:]
  vv_rel v (strict_lookup cenv ("m" ++ toString (count_rcarg eks)))
  ==>
  m_val_rel Computation v eks cenv (EVar ("m" ++ toString (count_rcarg eks)))
End

Theorem m_val_rel_eval:
  ! tag v eks cenv ce .
    m_val_rel tag v eks cenv ce
    ==>
    ? m cv .
      (! ks . cbv_steps m (ks, CExp cenv ce) = (ks, CVal cv)) /\
      vv_rel v cv
Proof
  rpt strip_tac
  >> gvs[Once m_val_rel_cases] >- (
    irule ve_rel_eval
    >> first_assum $ irule_at Any
  )
  >> qexists `1`
  >> simp[cbv_steps, cbv_step_def]
  >> simp[Once vv_rel_cases]
QED

Inductive ks_rel:
[~Id:]
  ks_rel [] cenv []
[~RCFn:]
  ks_rel ks cenv eks
  ==>
  ks_rel (RCFn e::ks) cenv (RCFn e::eks)
[~RCArg:]
  ks_rel ks cenv eks /\
  m_val_rel tag v eks cenv ce
  ==>
  ks_rel (RCArg (tag, v)::ks) cenv (RCArg ce::eks)
End

Theorem ks_rel_indifference:
  ! var cv ks cenv eks .
    ks_rel ks cenv eks
    ==>
    (! i . i < count_rcarg eks ==> var <> "m" ++ toString i) /\
    (! x . var <> "var" ++ x)
    ==>
    ks_rel ks (nsBind var cv cenv) eks
Proof
  gen_tac >> gen_tac
  >> ho_match_mp_tac ks_rel_ind
  >> rpt strip_tac
  >> simp[Once ks_rel_cases]
  >> gvs[count_rcarg_def]
  >> gvs[Once m_val_rel_cases]
  >> simp[Once m_val_rel_cases]
  >> simp[ve_rel_indifference]
  >> gvs[strict_lookup_def]
QED

Theorem ks_rel_indifference[allow_rebind] = SRULE [Once $ GSYM AND_IMP_INTRO] $ SRULE [Once CONJ_COMM, AND_IMP_INTRO] ks_rel_indifference;

Inductive scopes_rel:
[~NONE:]
  scopes_rel [] kenv NONE
[~SOME:]
  scopes_rel scopes kenv innerk /\
  ks_rel ks kenv eks /\
  env_rel env kenv /\
  strict_lookup cenv "k" = cont_closure eks kenv innerk
  ==>
  scopes_rel ((env, ks)::scopes) cenv (SOME "k")
End

Theorem scopes_rel_indifference:
  ! var cv scopes cenv innerk .
    var <> "k"
    ==>
    scopes_rel scopes cenv innerk ==> scopes_rel scopes (nsBind var cv cenv) innerk
Proof
  rpt strip_tac
  >> gvs[Once scopes_rel_cases]
  >> simp[Once scopes_rel_cases]
  >> gvs[strict_lookup_def]
  >> irule_at (Pos last) EQ_REFL
  >> simp[]
QED

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
  ve_rel v cenv ce
  ==>
  opt_cps_rel ks env scopes (RCVal Trivial v) cenv (app_cont eks ce innerk)
[~RCVal_Computation:]
  ks_rel ks kenv eks /\
  env_rel env kenv /\
  scopes_rel scopes kenv innerk /\
  ve_rel v cenv ce /\
  strict_lookup cenv "k" = cont_closure eks kenv innerk
  ==>
  opt_cps_rel ks env scopes (RCVal Computation v) cenv (EApp (EVar "k") ce)
End

Theorem opt_step_preservation:
  ! ks ks' env env' scopes scopes' e e' cenv ce .
    rich_cbv_step (ks, env, scopes, e) = (ks', env', scopes', e') /\
    opt_cps_rel ks env scopes e cenv ce
    ==>
    ? n cenv' ce' .
      cbv_steps n ([], CExp cenv ce) = ([], CExp cenv' ce') /\
      opt_cps_rel ks' env' scopes' e' cenv' ce'
Proof
  rpt strip_tac
  >> Cases_on `e`
  >~ [`RCExp e`] >- (
    Cases_on `e`
    >> gvs[rich_cbv_step_def]
    >> gvs[Once opt_cps_rel_cases]
    >> simp[opt_cps_def]
    >> qexists `0`
    >> simp[cbv_steps]
    >> simp[Once opt_cps_rel_cases]
    >> irule_at (Pos hd) EQ_REFL
    >> simp[Once ve_rel_cases]
    >> simp[Once ks_rel_cases]
    >> gvs[Once env_rel_cases]
  )
  >~ [`RCVal tag v`]
  >> gvs[rich_cbv_step_def]
  >> Cases_on `tag` >- (
    (*Trivial term as value*)
    Cases_on `ks` >- (
      Cases_on `scopes`
      >> gvs[rich_cbv_continue_def]
      >- (
        gvs[Once opt_cps_rel_cases]
        >> gvs[Once ks_rel_cases]
        >> gvs[Once scopes_rel_cases]
        >> qexists `0`
        >> simp[cbv_steps]
        >> simp[Once opt_cps_rel_cases]
        >> simp[Once ks_rel_cases]
        >> simp[Once scopes_rel_cases]
        >> irule_at (Pos hd) EQ_REFL
        >> simp[]
      )
      >~ [`scope::scopes'`]
      >> PairCases_on `scope`
      >> gvs[Once opt_cps_rel_cases]
      >> gvs[Once ks_rel_cases]
      >> gvs[Once scopes_rel_cases]
      >> gvs[cont_closure_def]
      >> qexists `0`
      >> simp[cbv_steps]
      >> simp[Once opt_cps_rel_cases]
      >> irule_at (Pos last) EQ_REFL
      >> simp[opt_cps_def]
    )
    >~ [`k::ks'`]
    >> Cases_on `k`
    >~ [`RCFn e`] >- (
      gvs[rich_cbv_continue_def]
      >> gvs[Once opt_cps_rel_cases]
      >> gvs[Once ks_rel_cases]
      >> qexists `0`
      >> simp[cbv_steps]
      >> simp[Once opt_cps_rel_cases]
      >> simp[opt_cps_def]
      >> irule_at (Pos hd) EQ_REFL
      >> simp[Once ks_rel_cases]
      >> simp[m_val_rel_cases]
    )
    >~ [`RCArg tv`]
    >> PairCases_on `tv`
    >> Cases_on `tv1`
    >~ [`VCl x env e`]
    >> gvs[rich_cbv_continue_def]
    >> gvs[Once opt_cps_rel_cases]
    >> gvs[Once ks_rel_cases]
    >> simp[opt_cps_def]
    >> qrefine `n+2`
    >> simp[cbv_steps, cbv_step_def]
    >> drule_then assume_tac m_val_rel_eval
    >> gvs[]
    >> qrefine `n+m`
    >> simp[cbv_steps_ADD]
    >> qrefine `n+1`
    >> simp[cbv_steps, cbv_step_def, cbv_continue_def]
    >> gvs[Once vv_rel_cases]
    >> drule_then assume_tac ve_rel_eval
    >> gvs[]
    >> gvs[Once m_val_rel_cases]
    >> qrefine `n+m'`
    >> simp[cbv_steps_ADD]
    >> qrefine `n+1`
    >> simp[cbv_steps, cbv_step_def, cbv_continue_def]
    >> qrefine `n+2`
    >> simp[cbv_steps, cbv_step_def, cbv_continue_def]
    >> qspecl_then [`eks'`, `cenv`, `innerk`] assume_tac cont_lambda_eval
    >> gvs[]
    >> qrefine `n+m''`
    >> simp[cbv_steps_ADD]
    >> qrefine `n+1`
    >> simp[cbv_steps, cbv_step_def, cbv_continue_def]
    >> qexists `0`
    >> simp[cbv_steps]
    >> simp[Once opt_cps_rel_cases]
    >> irule_at (Pos hd) EQ_REFL
    >> simp[Once ks_rel_cases]
    >> simp[Once scopes_rel_cases]
    >> simp[strict_lookup_def]
    >> irule_at (Pos last) EQ_REFL
    >> irule_at (Pos hd) env_rel_indifference
    >> simp[env_rel_sync]
  )
  (*Computed term as value*)
  >> Cases_on `ks` >- (
    Cases_on `scopes`
    >> gvs[rich_cbv_continue_def]
    >- (
      gvs[Once opt_cps_rel_cases]
      >> gvs[Once ks_rel_cases]
      >> gvs[Once scopes_rel_cases]
      >> qexists `0`
      >> simp[cbv_steps]
      >> simp[Once opt_cps_rel_cases]
      >> simp[Once ks_rel_cases]
      >> simp[Once scopes_rel_cases]
      >> irule_at (Pos last) EQ_REFL
      >> simp[]
    )
    >~ [`scope::scopes'`]
    >> PairCases_on `scope`
    >> gvs[Once opt_cps_rel_cases]
    >> gvs[Once ks_rel_cases]
    >> gvs[Once scopes_rel_cases]
    >> gvs[cont_closure_def]
    >> qexists `0`
    >> simp[cbv_steps]
    >> simp[Once opt_cps_rel_cases]
    >> irule_at (Pos last) EQ_REFL
    >> simp[]
  )
  >~ [`k::ks'`]
  >> Cases_on `k`
  >~ [`RCFn e`] >- (
    gvs[rich_cbv_continue_def]
    >> gvs[Once opt_cps_rel_cases]
    >> gvs[Once ks_rel_cases]
    >> gvs[cont_closure_def]
    >> qrefine `n+3`
    >> simp[cbv_steps, cbv_step_def, cbv_continue_def]
    >> drule_then assume_tac ve_rel_eval
    >> gvs[]
    >> qrefine `n+m`
    >> simp[cbv_steps_ADD]
    >> qrefine `n+1`
    >> simp[cbv_steps, cbv_step_def, cbv_continue_def]
    >> qexists `0`
    >> simp[cbv_steps]
    >> simp[Once opt_cps_rel_cases]
    >> irule_at (Pos hd) EQ_REFL
    >> simp[Once ks_rel_cases]
    >> simp[m_val_rel_cases]
    >> simp[strict_lookup_def]
    >> simp[scopes_rel_indifference]
    >> simp[ks_rel_indifference]
  )
  >~ [`RCArg tv`]
  >> PairCases_on `tv`
  >> Cases_on `tv1`
  >~ [`VCl x env e`]
  >> gvs[rich_cbv_continue_def]
  >> gvs[Once opt_cps_rel_cases]
  >> gvs[Once ks_rel_cases]
  >> gvs[cont_closure_def]
  >> qrefine `n+3`
  >> simp[cbv_steps, cbv_step_def, cbv_continue_def]
  >> drule_then assume_tac ve_rel_eval
  >> gvs[]
  >> qrefine `n+m`
  >> simp[cbv_steps_ADD]
  >> qrefine `n+3`
  >> simp[cbv_steps, cbv_step_def, cbv_continue_def]
  >> gvs[Once m_val_rel_cases]
  >>> HEADGOAL (
    qspecl_then [`"n"`, `cv`] (assume_tac o SRULE []) ve_rel_indifference
    >> pop_assum $ rev_drule_then assume_tac
    >> drule_then assume_tac ve_rel_eval
    >> gvs[]
    >> qrefine `n+m'`
    >> simp[cbv_steps_ADD]
    >> qpat_x_assum `! _. cbv_steps _ _ = _` kall_tac
  )
  >>> LASTGOAL (
    qrefine `n+1`
    >> simp[cbv_steps, cbv_step_def]
    >> gvs[strict_lookup_def]
  )
  >> gvs[vv_rel_cases]
  >> qrefine `n+5`
  >> simp[cbv_steps, cbv_step_def, cbv_continue_def, strict_lookup_def]
  >> qmatch_goalsub_abbrev_tac `cbv_steps _ (_, CExp newenv _)`
  >> qspecl_then [`eks'`, `newenv`, `innerk`] assume_tac cont_lambda_eval
  >> gvs[]
  >> unabbrev_all_tac
  >> qrefine `n+m'`
  >> simp[cbv_steps_ADD]
  >> qrefine `n+1`
  >> simp[cbv_steps, cbv_step_def, cbv_continue_def]
  >> qexists `0`
  >> simp[cbv_steps]
  >> simp[Once opt_cps_rel_cases]
  >> irule_at (Pos hd) EQ_REFL
  >> simp[Once ks_rel_cases]
  >> simp[Once scopes_rel_cases]
  >> simp[strict_lookup_def]
  >> irule_at (Pos last) EQ_REFL
  >> irule_at (Pos hd) env_rel_indifference
  >> simp[]
  >> irule_at (Pos hd) env_rel_sync
  >> simp[vv_rel_cases]
  >> simp[scopes_rel_indifference]
  >> simp[ks_rel_indifference]
QED
