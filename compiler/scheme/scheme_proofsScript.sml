(*
  Proofs for Scheme to CakeML compilation
*)
open preamble;
open scheme_astTheory;
open scheme_semanticsTheory;
open scheme_to_cakeTheory;
open astTheory;

open evaluateTheory;
open evaluatePropsTheory;
open semanticPrimitivesTheory;
open namespaceTheory;
open primTypesTheory;

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

(*
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
  ∀ ks ck . kssubset1 ks ⇒ ∃ v .
    evaluate <|clock := ck|> myEnv [scheme_cont ks]
      = (<|clock := ck|> : 'ffi state, Rval [v])
Proof
  Cases >> simp[] >- simp[scheme_cont_def, evaluate_def]
  >> Cases_on ‘h’ >> simp[] >> rpt strip_tac >> simp[]
  >> simp[scheme_cont_def, cps_transform_def]
  >> rpt (pairarg_tac >> gvs[step_def])
  >> simp[evaluate_def]
QED

Theorem cps_equiv:
  ∀ e n n' m m' ce ce' ck v v' c c' k k' t t'. subset1 e
    ∧ nsSub (λ id . $=) myEnv.c c ∧ nsSub (λ id . $=) myEnv.c c'
    ∧ nsSub (λ id . $=) myEnv.v v ∧ nsSub (λ id . $=) myEnv.v v'
    ∧ cps_transform n e = (n',ce) ∧ cps_transform m e = (m', ce')
    ∧ evaluate <|clock := ck+1|> <|v:=v;c:=c|> [App Opapp [ce;Fun t k]]
      = evaluate <|clock := ck+1|> <|v:=v';c:=c'|> [App Opapp [ce';Fun t' k']]
    ⇒ ∀ vl . evaluate <|clock := ck|> <|v:=nsBind t vl v;c:=c|> [k]
      = evaluate <|clock := ck|> <|v:=nsBind t vl v';c:=c'|> [k']
Proof
  ho_match_mp_tac rec_scheme_ind
  >> simp[cps_transform_def] >> rpt strip_tac
  >~ [‘vsubset1 v’] >- (
    Cases_on ‘v’ >> gvs[evaluate_def, to_ml_vals_def, do_opapp_def]
    >> gs[myEnv_def, nsSub_def]
    >> Cases_on ‘p’ >> simp[]
  )
  Induct_on ‘e’
  rpt strip_tac
QED
*)

(*
Example lambda calculus code of conditional expression,
before and after step in CEK machine

(\k0 -> (\k1 -> k1 $ SBool T)
  (\t0 -> match t0
          | SBool F => (\k2 -> k2 (SNum 1)) k0
          | _ => (\k2 -> k2 (SNum 2)) k0))
(\t -> t)

-->

(\k1 -> k1 $ SBool T)
(\t0 -> match t0
        | SBool F => (\k2 -> k2 (SNum 1)) (\t -> t)
        | _ => (\k2 -> k2 (SNum 2)) (\t -> t)))
*)

Definition e_or_v_to_exp_def:
  e_or_v_to_exp (Val v) var = App Opapp [Var (Short var); to_ml_vals v] ∧
  e_or_v_to_exp (Exp e) var = (let
    (n, ce) = cps_transform 0 e
  in
    App Opapp [ce; Var (Short var)])
End

Inductive cont_rel:
[~Id:]
  cont_rel []
    (Closure env t (Var (Short t)))
[~CondK:]
  cont_rel ks kv ∧
  nsLookup (env . v) (Short var) = SOME kv ∧
  (n', ct) = cps_transform n te ∧
  (m', cf) = cps_transform m fe
  ⇒
  (*Likely needs condition on se i.e. Scheme env*)
  cont_rel ((se, CondK te fe) :: ks)
    (Closure env t $ Mat (Var (Short t)) [
      (Pcon (SOME $ Short "SBool") [Pcon (SOME $ Short "False") []],
        App Opapp [cf; Var (Short var)]);
      (Pany, App Opapp [ct;  Var (Short var)])
    ])
End

(*
EVAL “case (SND $ evaluate_decs <|clock:=999;next_type_stamp:=0;next_exn_stamp:=0|>
<|v:=nsEmpty;c:=nsEmpty|> $ prim_types_program
++ (scheme_basis)) of
  | Rval env => evaluate <|clock:=999|> env $ [exp_with_cont [] (Lit $ LitBool T)]
  | _ => (st, v)”
*)

Definition scheme_env_def:
  scheme_env env
  ⇔
  (*not sure what to do with the state type variable,
  it doesn't work without a concrete type*)
  ∀ (st:num state) .
  evaluate st env [Con (SOME (Short "SBool")) [
    Con (SOME (Short "False")) []]]
  = (st, Rval [Conv (SOME (TypeStamp "SBool" 3)) [
    Conv (SOME (TypeStamp "False" 0)) []]]) ∧
  evaluate st env [Con (SOME (Short "SBool")) [
    Con (SOME (Short "True")) []]]
  = (st, Rval [Conv (SOME (TypeStamp "SBool" 3)) [
    Conv (SOME (TypeStamp "True" 0)) []]])
End

Theorem basis_scheme_env:
  ∃ st st' env .
    evaluate_decs st <|v:=nsEmpty;c:=nsEmpty|>
      (prim_types_program ++ scheme_basis) = (st', Rval env) ∧
    scheme_env env
Proof
  qexists ‘<|clock:=999;next_type_stamp:=0;next_exn_stamp:=0|>’
  >> simp[evaluate_decs_def, prim_types_program_def, scheme_basis_def,
  check_dup_ctors_def, build_tdefs_def, do_con_check_def,
  nsAppend_def, build_constrs_def, alist_to_ns_def,
  nsLookup_def, build_rec_env_def, extend_dec_env_def,
  nsSing_def, nsEmpty_def, nsBind_def, pat_bindings_def,
  evaluate_def, pmatch_def, combine_dec_result_def,
  every_exp_def, one_con_check_def, cons_list_def,
  scheme_env_def, build_conv_def]
QED

Theorem myproof:
  ∀ store store' env env' e e' k k' (st : 'ffi state) mlenv var kv mle .
  step  (store, k, env, e) = (store', k', env', e') ∧
  st.clock > 0 ∧
  cont_rel k kv ∧
  nsLookup mlenv.v (Short var) = SOME kv ∧
  scheme_env mlenv
  ⇒
  ∃ st' mlenv' var' kv' mle'.
    evaluate st mlenv [e_or_v_to_exp e var]
    =
    evaluate st' mlenv' [e_or_v_to_exp e' var'] ∧
    cont_rel k' kv' ∧
    nsLookup mlenv'.v (Short var') = SOME kv'
Proof
  Cases_on ‘e’
  >~ [‘Val v’] >- (
    Cases_on ‘k’
    >- (simp[step_def, return_def] >> metis_tac[])
    >> PairCases_on ‘h’
    >> Cases_on ‘∃ te fe . h1 = CondK te fe’
    >- (
      gvs[]
      >> cheat
    )
    >> cheat
  )
  >~ [‘Exp e’] >- (
    Cases_on ‘e’
    >> simp[step_def, e_or_v_to_exp_def]
    >~ [‘Cond c te fe’] >- (
      rpt strip_tac
      >> simp[cps_transform_def]
      >> rpt (pairarg_tac >> gvs[])
      >> simp[SimpLHS, Ntimes evaluate_def 6, do_opapp_def, nsOptBind_def]
      >> irule_at (Pos hd) EQ_REFL
      >> simp[nsLookup_def]
      >> simp[Once cont_rel_cases]
      >> metis_tac[]
    )
    >> cheat
  )
  >> cheat
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