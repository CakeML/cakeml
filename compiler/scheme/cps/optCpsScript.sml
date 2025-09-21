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
