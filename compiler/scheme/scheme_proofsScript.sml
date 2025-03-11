(*
  Proofs for Scheme to CakeML compilation
*)
open preamble;
open scheme_astTheory;
open scheme_semanticsTheory;
open scheme_to_cakeTheory;
open astTheory;

open evaluateTheory;
open semanticPrimitivesTheory;
open namespaceTheory;

val _ = new_theory "scheme_proofs";

(*
Definition subset1_def:
  (subset1 (Apply fn args) ⇔ subset1 fn ∧ EVERY subset1 args) ∧
  (subset1 (Cond c t f) ⇔ subset1 c ∧ subset1 t ∧ subset1 f) ∧
  (subset1 (Exception _) ⇔ T) ∧
  (subset1 (Val v) ⇔ case v of
  | Prim _ => T
  | SNum _ => T
  | SBool _ => T
  | _ => F) ∧
  (subset1 _ ⇔ F)
Termination
  WF_REL_TAC ‘measure exp_size’
End
*)

Inductive subset1:
[~Prim:]
  vsubset1 (Prim p)
[~SNum:]
  vsubset1 (SNum n)
[~SBool:]
  vsubset1 (SBool b)
[~Apply:]
  subset1 fn ∧ EVERY subset1 args ⇒ subset1 (Apply fn args)
[~Cond:]
  subset1 c ∧ subset1 t ∧ subset1 f ⇒ subset1 (Cond c t f)
[~Val:]
  vsubset1 v ⇒ subset1 (Val v)
[~CondK:]
  subset1 t ∧ subset1 f ⇒ ksubset1 (CondK t f)
[~ApplyKNONE:]
  EVERY subset1 args ⇒ ksubset1 (ApplyK NONE args)
[~ApplyKSOME:]
  vsubset1 fv ∧ EVERY vsubset1 vs ∧ EVERY subset1 args
    ⇒ ksubset1 (ApplyK (SOME (fv, vs)) args)
[~Cont:]
  EVERY ksubset1 ks ⇒ kssubset1 ks
End

Theorem subset1_rewrite[simp] = LIST_CONJ[
  “vsubset1 (Prim p)” |> SCONV [Once subset1_cases],
  “vsubset1 (SNum n)” |> SCONV [Once subset1_cases],
  “vsubset1 (SBool b)” |> SCONV [Once subset1_cases],
  “vsubset1 (Wrong w)” |> SCONV [Once subset1_cases],
  “vsubset1 (SList l)” |> SCONV [Once subset1_cases],
  “vsubset1 (Proc r xs xp e)” |> SCONV [Once subset1_cases],
  “vsubset1 (Throw k)” |> SCONV [Once subset1_cases],

  “subset1 (Apply fn args)” |> SCONV [Once subset1_cases],
  “subset1 (Cond c t f)” |> SCONV [Once subset1_cases],
  “subset1 (Val v)” |> SCONV [Once subset1_cases],
  “subset1 (Print m)” |> SCONV [Once subset1_cases],
  “subset1 (Exception m)” |> SCONV [Once subset1_cases],
  “subset1 (Ident x)” |> SCONV [Once subset1_cases],
  “subset1 (Lambda xs xp e)” |> SCONV [Once subset1_cases],
  “subset1 (Begin e es)” |> SCONV [Once subset1_cases],
  “subset1 (Set x e)” |> SCONV [Once subset1_cases],
  “subset1 (Letrec bs e)” |> SCONV [Once subset1_cases],

  “ksubset1 (CondK t f)” |> SCONV [Once subset1_cases],
  “ksubset1 (ApplyK ps args)” |> SCONV [Once subset1_cases],
  “ksubset1 (SetK x)” |> SCONV [Once subset1_cases],
  “ksubset1 (BeginK es)” |> SCONV [Once subset1_cases],
  “kssubset1 ks” |> SCONV [Once subset1_cases]
];

Theorem eval_expand = LIST_CONJ[
  myEnv_def, myC_def, do_opapp_def, dec_clock_def,
  nsLookup_def, nsBind_def, do_con_check_def, build_conv_def
];

Inductive ml_subset:
[~Fun:]
  ml_subset e ⇒ ml_subset (Fun t e)
[~App:]
  EVERY ml_subset es ⇒ ml_subset (App op es)
[~Var:]
  ml_subset (Var (Short t))
[~Con:]
  EVERY ml_subset es ⇒ ml_subset (Con x es)
[~Lit:]
  ml_subset (Lit x')
[~Let:]
  ml_subset e1 ∧ ml_subset e2 ⇒ ml_subset (Let p e1 e2)
[~Mat:]
  ml_subset e ∧ EVERY ml_subset (MAP SND bs) ⇒ ml_subset (Mat e bs)
End

Definition rec_scheme_def:
  rec_scheme (Cond c t f) = rec_scheme c + rec_scheme t + rec_scheme f ∧
  rec_scheme (Apply fn es) = rec_scheme fn + SUM (MAP rec_scheme es) ∧
  rec_scheme (Val v) = 0
Termination
  WF_REL_TAC ‘measure exp_size’
End

Theorem ml_subset_rewrite[simp] = LIST_CONJ [
  “ml_subset (Fun t e)” |> SCONV [Once ml_subset_cases],
  “ml_subset (App op es)” |> SCONV [Once ml_subset_cases],
  “ml_subset (Var (Short t))” |> SCONV [Once ml_subset_cases],
  “ml_subset (Con x es)” |> SCONV [Once ml_subset_cases],
  “ml_subset (Lit x')” |> SCONV [Once ml_subset_cases],
  “ml_subset (Let p e1 e2)” |> SCONV [Once ml_subset_cases],
  “ml_subset (Mat e bs)” |> SCONV [Once ml_subset_cases]
];

Theorem small_ml:
  ∀ e n m ce . cps_transform n e = (m, ce) ∧ subset1 e
    ⇒ ml_subset ce
Proof
  ho_match_mp_tac rec_scheme_ind
  >> simp[cps_transform_def] >> rpt strip_tac
  >~ [‘vsubset1 v’] >- (
    Cases_on ‘v’ >> gvs[to_ml_vals_def]
    >> Cases_on ‘p’ >> simp[]
  )
  >> rpt strip_tac >> rpt (pairarg_tac >> gvs[step_def])
  >> rpt $ last_x_assum dxrule >> simp[] >> disch_then kall_tac
  >> cheat
QED

Theorem e_vals_subset1:
  ∀ n e . subset1 e ⇒  ∃ st ck v .
    evaluate <|clock := ck|> myEnv [SND $ cps_transform n e] = (st, Rval v)
Proof
  strip_tac >> Cases >> simp[]
  >~ [‘Val v’] >- (
    strip_tac >> simp[cps_transform_def, to_ml_vals_def, evaluate_def]
  )
  >> simp[cps_transform_def]
  >> rpt (pairarg_tac >> gvs[step_def])
  >> simp[evaluate_def]
QED

Theorem k_vals_subset1:
  ∀ ks . kssubset1 ks ⇒ ∃ (st : 'ffi state) ck v .
    evaluate <|clock := ck|> myEnv [scheme_cont ks] = (st, Rval v)
Proof
  Cases >> simp[] >- simp[scheme_cont_def, evaluate_def]
  >> Cases_on ‘h’ >> simp[] >> rpt strip_tac >> simp[]
  >> simp[scheme_cont_def, cps_transform_def]
  >> rpt (pairarg_tac >> gvs[step_def])
  >> simp[evaluate_def]
QED

Theorem clock_preserve_val:
  ∀ e ck (st:'ffi state) env v .
    evaluate <|clock := ck|> env [e] = (st, Rval v)
    ⇒ evaluate <|clock := ck + 1|> env [e] = (st, Rval v)
Proof
  Cases
  >> simp[Once evaluate_def]
  >> cheat
QED

Theorem myproof:
  ∀ e e' n k k' . kssubset1 (MAP SND k) ∧ subset1 e ⇒ step  ([], k, FEMPTY, e) = ([], k', FEMPTY, e') ⇒
      ∃ ck ck' t1 . evaluate (<| clock := ck |> : 'ffi state) myEnv [exp_with_cont (MAP SND k) e] =
        evaluate <| clock := ck' |> myEnv [exp_with_cont (MAP SND k') e']
Proof
  Cases >> simp[]
  >> rpt strip_tac
  >> simp[exp_with_cont_def, cps_transform_def]
  >~ [‘Cond c t f’] >- (
    gvs[step_def, scheme_cont_def, cps_transform_def]
    >> rpt (pairarg_tac >> gvs[step_def])
    >> simp[SimpLHS, evaluate_def]
    >> qexistsl_tac [‘ck+1’,‘ck’]
    >> dxrule_then assume_tac (SRULE [] k_vals_subset1)
    >> cheat
  ) >> cheat
QED

(*Theorem val_correct:
  ∀ n . ∃ k . SND (evaluate <| clock := k |> myEnv [scheme_program_to_cake (Val (SNum n))])
    = Rval [Conv (SOME $ TypeStamp "SNum" 0) [Litv $ IntLit n]]
Proof
  strip_tac
  >> qexists_tac ‘99’
  >> rw[scheme_program_to_cake_def, cps_transform_def, myEnv_def, myC_def,
    to_ml_vals_def,
    Once evaluate_def, do_opapp_def, dec_clock_def,
    nsLookup_def, nsBind_def, do_con_check_def, build_conv_def]
QED*)

val _ = export_theory();