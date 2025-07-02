(*
  Proof of semantic preservation from Scheme to CakeML
*)
open preamble;
open computeLib;
open scheme_astTheory;
open scheme_semanticsTheory;
open scheme_to_cakeTheory;
open scheme_semanticsPropsTheory;

open astTheory;
open evaluateTheory;
open evaluatePropsTheory;
open semanticPrimitivesTheory;
open namespaceTheory;
open primTypesTheory;
open namespacePropsTheory;
open integerTheory;

val _ = new_theory "scheme_to_cakeProof";

val _ = (max_print_depth := 30);

Definition closure_in_env_def:
  closure_in_env env dec env_cl =
    case dec of
      | Dlet _ (Pvar x) e => nsLookup env.v (Short x) = SOME (case evaluate
          (<|clock:=0;next_type_stamp:=0;next_exn_stamp:=0|> :num state)
          env_cl [e] of
        | (st', Rval [v]) => v)
      | Dletrec _ funs => EVERY
          (λ(f,_,_). nsLookup env.v (Short f) = SOME $ Recclosure env_cl funs f)
        funs
End

Theorem scheme_cons_env_def[allow_rebind, compute] = EVAL_RULE $ zDefine ‘
  scheme_cons_env = (case evaluate_decs
               (<|clock:=0;next_type_stamp:=0;next_exn_stamp:=0|> :num state)
               <|v:=nsEmpty;c:=nsEmpty|>
               (prim_types_program ++ [Dtype unknown_loc [(["'a"],"option",
                     [("None",[]); ("Some",[Atvar "'a"])])]] ++ [scheme_basis_types]) of
             | (st', Rval env) => env).c
’;

Theorem scheme_env_app_def[allow_rebind, compute] = EVAL_RULE $ zDefine ‘
  scheme_env_app env <=>
    env.c = scheme_cons_env ∧
    EVERY (λ dec. ∃ env_cl . env_cl.c = scheme_cons_env ∧ closure_in_env env dec env_cl) scheme_basis
’;

Theorem scheme_env_def[allow_rebind, compute] = RESTR_EVAL_RULE [``scheme_env_app``] $ zDefine ‘
  scheme_env env <=>
    env.c = scheme_cons_env ∧
    ∃ env_app .
      scheme_env_app env_app ∧
      closure_in_env env scheme_basis_app env_app
’;

Theorem scheme_env'_def[allow_rebind, compute] = EVAL_RULE $ zDefine ‘
  scheme_env' = case evaluate_decs (<|clock:=999;next_type_stamp:=0;next_exn_stamp:=0|> :num state)
                  <|v:=nsEmpty;c:=nsEmpty|>
                  (prim_types_program ++ [Dtype unknown_loc [(["'a"],"option", [("None",[]); ("Some",[Atvar "'a"])])]]
                    ++ [scheme_basis_types] ++ scheme_basis ++ [scheme_basis_app]) of
                | (st', Rval env) => env
’;

Theorem basis_scheme_env:
  scheme_env scheme_env'
Proof
  simp[scheme_env_def, PULL_EXISTS]
  >> qexists ‘case evaluate_decs (<|clock:=999;next_type_stamp:=0;next_exn_stamp:=0|> :num state)
                <|v:=nsEmpty;c:=nsEmpty|>
                (prim_types_program ++ [Dtype unknown_loc [(["'a"],"option", [("None",[]); ("Some",[Atvar "'a"])])]]
                  ++ [scheme_basis_types] ++ scheme_basis) of
              | (st', Rval env) => env’
  >> EVAL_TAC
  >> rpt strip_tac
  >> irule_at (Pos last) EQ_REFL
  >> simp[]
QED

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

Theorem scheme_conses_def[allow_rebind, compute] = EVAL_RULE $ zDefine‘
  scheme_conses = case scheme_cons_env of
    Bind cs _ => MAP FST cs
’;

Theorem scheme_runtime_funs_def[allow_rebind, compute] = EVAL_RULE $ zDefine‘
  scheme_runtime_funs = FOLDL (λ acc dec. acc ++ case dec of
    | Dlet _ (Pvar x) _ => [x]
    | Dletrec _ funs => MAP FST funs) [] $
    scheme_basis ++ [scheme_basis_app]
’;

Definition scheme_typestamp_def:
  scheme_typestamp con = SND $ THE $ nsLookup scheme_cons_env (Short con)
End

Theorem scheme_typestamp_def[allow_rebind, simp, compute] = SRULE [] $
  SIMP_CONV pure_ss [SimpRHS, scheme_typestamp_def, EVERY_DEF,
      scheme_conses_def, SND, THE_DEF, nsLookup_def, scheme_cons_env_def]
    “EVERY (λ x . scheme_typestamp x = scheme_typestamp x) scheme_conses”;

Definition muts_loc_def:
  muts_loc nl [] l = nl + l /\
  muts_loc nl (Refv _::refs) 0 = nl /\
  muts_loc nl (Refv _::refs) (SUC l) = muts_loc (SUC nl) refs l /\
  muts_loc nl (_::refs) l = muts_loc (SUC nl) refs l
End

Theorem muts_loc_props:
  ! nl refs l . muts_loc nl refs l >= nl + l /\ muts_loc (SUC nl) refs l = SUC (muts_loc nl refs l)
Proof
  ho_match_mp_tac muts_loc_ind
  >> simp[muts_loc_def]
QED

Theorem muts_loc_mono = cj 1 muts_loc_props;
Theorem muts_loc_SUC[simp] = cj 2 muts_loc_props;

Theorem muts_loc_FILTER:
  ! refs l .
    (muts_loc 0 refs l < LENGTH refs
     <=> l < LENGTH (FILTER (\ref. case ref of | Refv _ => T | _ => F) refs))
    /\
    EL (muts_loc 0 refs l) refs
     = EL l $ FILTER (\ref. case ref of | Refv _ => T | _ => F) refs
Proof
  Induct >> Induct
  >> simp[muts_loc_def]
  >> gen_tac >> Cases
  >> simp[muts_loc_def]
QED

Theorem muts_loc_alloc_same:
  ! refs l mlv .
    muts_loc 0 refs l = muts_loc 0 (refs ++ [Refv mlv]) l
Proof
  Induct >> Induct
  >> simp[muts_loc_def]
  >> gen_tac >> Cases
  >> simp[muts_loc_def]
QED

Theorem muts_loc_LUPDATE_same:
  ! refs l l' mlv mlv' .
    EL l' refs = Refv mlv
    ==>
    muts_loc 0 refs l = muts_loc 0 (LUPDATE (Refv mlv') l' refs) l
Proof
  Induct >> Induct
  >> simp[muts_loc_def, LUPDATE_def] >- (
    gen_tac >> Cases >> Cases
    >> simp[muts_loc_def, LUPDATE_def]
  )
  >> gen_tac >> gen_tac >> Cases
  >> simp[muts_loc_def, LUPDATE_def]
QED

Definition pairs_loc_def:
  pairs_loc nl [] l = nl + l /\
  pairs_loc nl (Varray _::refs) 0 = nl /\
  pairs_loc nl (Varray _::refs) (SUC l) = pairs_loc (SUC nl) refs l /\
  pairs_loc nl (_::refs) l = pairs_loc (SUC nl) refs l
End

Theorem pairs_loc_props:
  ! nl refs l . pairs_loc nl refs l >= nl + l /\ pairs_loc (SUC nl) refs l = SUC (pairs_loc nl refs l)
Proof
  ho_match_mp_tac pairs_loc_ind
  >> simp[pairs_loc_def]
QED

Theorem pairs_loc_mono = cj 1 pairs_loc_props;
Theorem pairs_loc_SUC[simp] = cj 2 pairs_loc_props;

Theorem pairs_loc_FILTER:
  ! refs l .
    (pairs_loc 0 refs l < LENGTH refs
     <=> l < LENGTH (FILTER (\ref. case ref of | Varray _ => T | _ => F) refs))
    /\
    EL (pairs_loc 0 refs l) refs
     = EL l $ FILTER (\ref. case ref of | Varray _ => T | _ => F) refs
Proof
  Induct >> Induct
  >> simp[pairs_loc_def]
  >> gen_tac >> Cases
  >> simp[pairs_loc_def]
QED

Theorem pairs_loc_alloc_diff:
  ! refs l mlv .
    pairs_loc 0 refs l < LENGTH refs ==> pairs_loc 0 refs l = pairs_loc 0 (refs ++ [Refv mlv]) l
Proof
  Induct >> Induct
  >> simp[pairs_loc_def]
  >> gen_tac >> Cases
  >> simp[pairs_loc_def]
QED

Theorem pairs_loc_LUPDATE_diff:
  ! refs l l' mlv mlv' .
    EL l' refs = Refv mlv
    ==>
    pairs_loc 0 refs l = pairs_loc 0 (LUPDATE (Refv mlv') l' refs) l
Proof
  Induct >> Induct
  >> simp[pairs_loc_def, LUPDATE_def]
  >> gen_tac >> Cases >> Cases
  >> simp[pairs_loc_def, LUPDATE_def]
QED

Inductive env_rel:
  FEVERY (λ (x, n).
    nsLookup env.v (Short ("var" ++ explode x)) = SOME (Loc T (muts_loc 0 refs n))) se
  ⇒
  env_rel refs se env
End

Theorem env_rel_alloc:
  ! refs mlv se env .
    env_rel refs se env ==> env_rel (refs ++ [Refv mlv]) se env
Proof
  simp[env_rel_cases]
  >> rpt strip_tac
  >> irule FEVERY_MONO
  >> pop_assum $ irule_at $ Pos last
  >> PairCases
  >> simp[muts_loc_alloc_same]
QED

Theorem env_rel_LUPDATE_same:
  ! refs l mlv'1 mlv'2 se env .
    EL l refs = Refv mlv'1
    ==>
    env_rel refs se env ==> env_rel (LUPDATE (Refv mlv'2) l refs) se env
Proof
  simp[env_rel_cases]
  >> rpt strip_tac
  >> irule FEVERY_MONO
  >> pop_assum $ irule_at $ Pos last
  >> PairCases
  >> rw[muts_loc_LUPDATE_same]
QED

Theorem vcons_list_def[allow_rebind] = SRULE [] $ Define ‘
  vcons_list [] = Conv (SOME (scheme_typestamp "[]")) [] ∧
  vcons_list (v::vs) = Conv (SOME (scheme_typestamp "::")) [v; vcons_list vs]
’;

Definition cps_app_ts_def:
  cps_app_ts (v::vs) = (let
    (t, ts) = cps_app_ts vs
  in
    ("t" ++ toString (SUC (LENGTH ts)), t::ts)) ∧

  cps_app_ts [] = ("t0", [])
End

Inductive val_cont_rels:
[~SBool_T:]
  ml_v_vals refs (SBool T) $
    Conv (SOME (scheme_typestamp "SBool")) [Conv (SOME (scheme_typestamp "True")) []]
[~SBool_F:]
  ml_v_vals refs (SBool F) $
    Conv (SOME (scheme_typestamp "SBool")) [Conv (SOME (scheme_typestamp "False")) []]
[~SNum:]
  ml_v_vals refs (SNum i) $
    Conv (SOME (scheme_typestamp "SNum")) [Litv (IntLit i)]
[~Prim_SAdd:]
  ml_v_vals refs (Prim SAdd) $
    Conv (SOME (scheme_typestamp "Prim")) [Conv (SOME (scheme_typestamp "SAdd")) []]
[~Prim_SMul:]
  ml_v_vals refs (Prim SMul) $
    Conv (SOME (scheme_typestamp "Prim")) [Conv (SOME (scheme_typestamp "SMul")) []]
[~Prim_SMinus:]
  ml_v_vals refs (Prim SMinus) $
    Conv (SOME (scheme_typestamp "Prim")) [Conv (SOME (scheme_typestamp "SMinus")) []]
[~Prim_SEqv:]
  ml_v_vals refs (Prim SEqv) $
    Conv (SOME (scheme_typestamp "Prim")) [Conv (SOME (scheme_typestamp "SEqv")) []]
[~Prim_CallCC:]
  ml_v_vals refs (Prim CallCC) $
    Conv (SOME (scheme_typestamp "Prim")) [Conv (SOME (scheme_typestamp "CallCC")) []]
[~Prim_Cons:]
  ml_v_vals refs (Prim Cons) $
    Conv (SOME (scheme_typestamp "Prim")) [Conv (SOME (scheme_typestamp "Cons")) []]
[~Prim_Car:]
  ml_v_vals refs (Prim Car) $
    Conv (SOME (scheme_typestamp "Prim")) [Conv (SOME (scheme_typestamp "Car")) []]
[~Prim_Cdr:]
  ml_v_vals refs (Prim Cdr) $
    Conv (SOME (scheme_typestamp "Prim")) [Conv (SOME (scheme_typestamp "Cdr")) []]
[~Prim_Wrong:]
  ml_v_vals refs (Wrong s) $
    Conv (SOME (scheme_typestamp "Wrong")) [Litv (StrLit s)]
[~Proc:]
  scheme_env env ∧
  env_rel refs se env ∧
  ce = cps_transform e ∧
  inner = proc_ml xs xp "k" ce
  ⇒
  ml_v_vals refs (Proc se xs xp e) $
    Conv (SOME (scheme_typestamp "Proc")) [
      Closure env "k" $ Fun "ts" inner
    ]
[~Throw:]
  cont_rel refs ks kv
  ⇒
  ml_v_vals refs (Throw ks) $
    Conv (SOME (scheme_typestamp "Throw")) [kv]
[~SList:]
  LIST_REL (ml_v_vals refs) vs mlvs
  ⇒
  ml_v_vals refs (SList vs) $
    Conv (SOME (scheme_typestamp "SList")) [vcons_list mlvs]
[~PairP:]
  pairs_loc 0 refs l < LENGTH refs
  ⇒
  ml_v_vals refs (PairP l) $
    Conv (SOME (scheme_typestamp "PairP")) [Loc T (pairs_loc 0 refs l)]
[~Nul:]
  ml_v_vals refs Null $
    Conv (SOME (scheme_typestamp "Null")) []

[~Id:]
  scheme_env env
  ⇒
  cont_rel refs []
    (Closure env "t" (Var (Short "t")))
[~CondK:]
  cont_rel refs ks kv ∧
  nsLookup env.v (Short "k") = SOME kv ∧
  ct = cps_transform te ∧
  cf = cps_transform fe ∧
  scheme_env env ∧
  env_rel refs se env
  ⇒
  cont_rel refs ((se, CondK te fe) :: ks)
    (Closure env "t" $ Mat (Var (Short "t")) [
      (Pcon (SOME $ Short "SBool") [Pcon (SOME $ Short "False") []],
        App Opapp [cf; Var (Short "k")]);
      (Pany, App Opapp [ct;  Var (Short "k")])
    ])
[~ApplyK_NONE:]
  cont_rel refs ks kv ∧
  nsLookup env.v (Short "k") = SOME kv ∧
  inner = cps_transform_app (Var (Short "t")) [] es (Var (Short "k")) ∧
  scheme_env env ∧
  env_rel refs se env
  ⇒
  cont_rel refs ((se, ApplyK NONE es) :: ks)
    (Closure env "t" $ inner)
[~ApplyK_SOME:]
  cont_rel refs ks kv ∧
  nsLookup env.v (Short "k") = SOME kv ∧
  (t, ts) = cps_app_ts vs ∧
  inner = cps_transform_app (Var (Short "t"))
    (MAP (Var o Short) (t::ts)) es (Var (Short "k")) ∧
  ml_v_vals refs fn mlfn ∧
  nsLookup env.v (Short "t") = SOME mlfn ∧
  LIST_REL (ml_v_vals refs) vs mlvs ∧
  LIST_REL (λ x mlv . nsLookup env.v (Short x) = SOME mlv) ts mlvs ∧
  scheme_env env ∧
  env_rel refs se env
  ⇒
  cont_rel refs ((se, ApplyK (SOME (fn, vs)) es) :: ks)
    (Closure env t $ inner)
[~BeginK:]
  cont_rel refs ks kv ∧
  nsLookup env.v (Short "k") = SOME kv ∧
  inner = cps_transform_seq (Var (Short "k")) es e ∧
  scheme_env env ∧
  env_rel refs se env
  ⇒
  cont_rel refs ((se, BeginK es e) :: ks)
    (Closure env "_" $ inner)
[~SetK:]
  cont_rel refs ks kv ∧
  nsLookup env.v (Short "k") = SOME kv ∧
  inner = refunc_set (Var (Short "t")) (Var (Short "k")) x ∧
  scheme_env env ∧
  env_rel refs se env
  ⇒
  cont_rel refs ((se, SetK x) :: ks)
    (Closure env "t" $ inner)
[~LetinitK:]
  cont_rel refs ks kv ∧
  nsLookup env.v (Short "k") = SOME kv ∧
  (t, ts) = cps_app_ts xvs ∧
  inner = cps_transform_letinit
    ((x,Var (Short t))::ZIP (MAP FST xvs, MAP (Var o Short) ts))
    bs e (Var (Short "k")) ∧
  LIST_REL (ml_v_vals refs) (MAP SND xvs) mlvs ∧
  LIST_REL (λ x mlv . nsLookup env.v (Short x) = SOME mlv) ts mlvs ∧
  scheme_env env ∧
  env_rel refs se env
  ⇒
  cont_rel refs ((se, LetinitK xvs x bs e) :: ks)
    (Closure env t $ inner)
End

Theorem val_cont_rels_ind[allow_rebind] = SRULE [] $ val_cont_rels_ind;
Theorem ml_v_vals_cases = SRULE [] $ cj 1 val_cont_rels_cases;
Theorem cont_rel_cases = cj 2 val_cont_rels_cases;

Theorem val_cont_rel_mono:
  ! refs mlv' .
    (! v mlv . ml_v_vals refs v mlv ==> ml_v_vals (refs ++ [Refv mlv']) v mlv) /\
    (! ks kv . cont_rel refs ks kv ==> cont_rel (refs ++ [Refv mlv']) ks kv)
Proof
  rpt gen_tac
  >> ho_match_mp_tac val_cont_rels_ind
  >> rpt strip_tac
  >> simp[Once ml_v_vals_cases, env_rel_alloc]
  >- (
    irule_at (Pos hd) EQ_REFL >> gvs[SF ETA_ss]
  )
  >- (
    simp[pairs_loc_alloc_diff]
    >> simp[GSYM pairs_loc_alloc_diff]
  )
  >> simp[Once cont_rel_cases, env_rel_alloc]
  >> irule_at (Pos hd) EQ_REFL
  >> first_assum $ irule_at (Pos last)
  >> gvs[SF ETA_ss]
QED

Theorem ml_v_vals_mono = SRULE [PULL_FORALL, AND_IMP_INTRO] $
  cj 1 val_cont_rel_mono;
Theorem cont_rel_mono = SRULE [PULL_FORALL, AND_IMP_INTRO] $
  cj 2 val_cont_rel_mono;

Theorem val_cont_rel_LUPDATE_same:
  ! refs l mlv'1 mlv'2 .
    EL l refs = Refv mlv'1
    ==>
    (! v mlv . ml_v_vals refs v mlv ==> ml_v_vals (LUPDATE (Refv mlv'2) l refs) v mlv) /\
    (! ks kv . cont_rel refs ks kv ==> cont_rel (LUPDATE (Refv mlv'2) l refs) ks kv)
Proof
  rpt gen_tac >> strip_tac
  >> ho_match_mp_tac val_cont_rels_ind
  >> rpt strip_tac
  >> simp[Once ml_v_vals_cases] >- simp[env_rel_LUPDATE_same]
  >- (
    irule_at (Pos hd) EQ_REFL >> gvs[SF ETA_ss]
  )
  >- (
    simp[pairs_loc_LUPDATE_diff]
    >> simp[GSYM pairs_loc_LUPDATE_diff]
  )
  >> simp[Once cont_rel_cases, env_rel_LUPDATE_same]
  >> irule_at (Pos hd) EQ_REFL
  >> first_assum $ irule_at (Pos last)
  >> gvs[SF ETA_ss]
QED

Theorem ml_v_vals_LUPDATE_same = SRULE [PULL_FORALL, AND_IMP_INTRO] $
  cj 1 val_cont_rel_LUPDATE_same;
Theorem cont_rel_LUPDATE_same = SRULE [PULL_FORALL, AND_IMP_INTRO] $
  cj 2 val_cont_rel_LUPDATE_same;

val (store_entry_rel_rules,store_entry_rel_ind,store_entry_rel_cases) =
(fn (x,y,z) => (SRULE [] x,SRULE [] y, SRULE [] z)) $ Hol_reln ‘
  (ml_v_vals refs v mlv
  ⇒
  store_entry_rel refs (SOME v) (Refv (Conv (SOME (scheme_typestamp "Some")) [mlv]))) ∧
  store_entry_rel refs NONE (Refv (Conv (SOME (scheme_typestamp "None")) []))
’;

Inductive pair_rel:
  ml_v_vals refs v mlv ∧
  ml_v_vals refs v' mlv'
  ⇒
  pair_rel refs (v, v') (Varray [mlv; mlv'])
End

Inductive muts_rel:
[~empty:]
  muts_rel refs' [] []
[~mut:]
  store_entry_rel refs' mut ref ∧
  muts_rel refs' muts refs
  ⇒
  muts_rel refs' (mut::muts) (ref::refs)
[~pair:]
  muts_rel refs' muts refs
  ⇒
  muts_rel refs' muts (Varray vs::refs)
End

Inductive pairs_rel:
[~empty:]
  pairs_rel refs' [] []
[~pair:]
  pair_rel refs' pair ref ∧
  pairs_rel refs' pairs refs
  ⇒
  pairs_rel refs' (pair::pairs) (ref::refs)
[~mut:]
  pairs_rel refs' pairs refs
  ⇒
  pairs_rel refs' pairs (Refv v::refs)
End

Definition store_rel_def[simp]:
  store_rel st refs <=> muts_rel refs st.muts refs ∧ pairs_rel refs st.pairs refs
End

Theorem muts_rel_FILTER:
  ! refs' muts refs .
    muts_rel refs' muts refs
    ==>
    LIST_REL (store_entry_rel refs') muts $
      FILTER (\ref. case ref of | Refv _ => T | _ => F) refs
Proof
  gen_tac >> ho_match_mp_tac muts_rel_ind
  >> simp[]
  >> rpt strip_tac
  >> CASE_TAC
  >> gvs[Once store_entry_rel_cases]
  >> simp[Once store_entry_rel_cases]
QED

Theorem muts_rel_LUPDATE_same:
  ! refs' muts refs .
    muts_rel refs' muts refs
    ==>
    ! mut ref l .
      store_entry_rel refs' mut ref
      ==>
      muts_rel refs' muts refs /\
      muts_rel refs' (LUPDATE mut l muts) (LUPDATE ref (muts_loc 0 refs l) refs)
Proof
  gen_tac
  >> ho_match_mp_tac muts_rel_ind
  >> simp[LUPDATE_def]
  >> simp[Once muts_rel_cases]
  >> rpt strip_tac >- (
    first_x_assum $ drule >> strip_tac
    >> simp[Once muts_rel_cases]
  )
  >- (
    gvs[Once store_entry_rel_cases]
    >> Cases_on `l`
    >> gvs[LUPDATE_def, muts_loc_def]
    >> first_x_assum $ drule >> strip_tac
    >> simp[Once muts_rel_cases]
    >> simp[store_entry_rel_cases]
  )
  >- (
    irule muts_rel_pair
    >> last_x_assum drule >> strip_tac
    >> simp[]
  )
  >> simp[muts_loc_def, LUPDATE_def, Once muts_rel_cases]
QED

Theorem muts_rel_LUPDATE_same[allow_rebind] = cj 2 muts_rel_LUPDATE_same;

Theorem muts_rel_mono:
  ! (refs'1:'a store_v list) (refs'2:'a store_v list) .
    (! mut ref . store_entry_rel refs'1 mut ref ==> store_entry_rel refs'2 mut ref)
    ==>
    ! muts refs .
      muts_rel refs'1 muts refs ==> muts_rel refs'2 muts refs
Proof
  rpt gen_tac >> strip_tac
  >> ho_match_mp_tac muts_rel_ind
  >> rpt strip_tac
  >> gvs[store_entry_rel_cases]
  >> simp[Once muts_rel_cases]
  >> simp[store_entry_rel_cases]
QED

Theorem muts_rel_loc:
  ! refs' muts refs l .
    l < LENGTH muts /\ muts_rel refs' muts refs 
    ==>
    muts_loc 0 refs l < LENGTH refs /\
    store_entry_rel refs' (EL l muts) (EL (muts_loc 0 refs l) refs)
Proof
  rpt strip_tac
  >> dxrule_then assume_tac muts_rel_FILTER
  >> gvs[LIST_REL_EL_EQN, muts_loc_FILTER]
QED

Theorem muts_rel_loc_alloc:
  ! mlv muts refs .
    muts_rel refs muts refs
    ==>
    muts_loc 0 refs (LENGTH muts) = LENGTH refs
Proof
  rpt strip_tac
  >> dxrule_then assume_tac muts_rel_FILTER
  >> dxrule_then assume_tac LIST_REL_LENGTH
  >> simp[muts_loc_FILTER]
QED

Theorem pairs_rel_FILTER:
  ! refs' pairs refs .
    pairs_rel refs' pairs refs
    ==>
    LIST_REL (pair_rel refs') pairs $
      FILTER (\ref. case ref of | Varray _ => T | _ => F) refs
Proof
  gen_tac >> ho_match_mp_tac pairs_rel_ind
  >> simp[]
  >> rpt strip_tac
  >> CASE_TAC
  >> gvs[Once pair_rel_cases]
  >> simp[Once pair_rel_cases]
QED

Theorem pairs_rel_LUPDATE_diff:
  ! refs' pairs refs .
    pairs_rel refs' pairs refs
    ==>
    ! mut ref l .
      store_entry_rel refs' mut ref
      ==>
      pairs_rel refs' pairs refs /\
      pairs_rel refs' pairs (LUPDATE ref (muts_loc 0 refs l) refs)
Proof
  gen_tac
  >> ho_match_mp_tac pairs_rel_ind
  >> simp[LUPDATE_def]
  >> simp[Once pairs_rel_cases]
  >> rpt strip_tac
  >> first_x_assum $ drule_then $ mp_tac o SRULE [Once $ GSYM PULL_FORALL]
  >> strip_tac
  >~ [`muts_loc 0 (Refv _::_) _`]
  >- (
    Cases_on `l`
    >> simp[LUPDATE_def, muts_loc_def]
    >> gvs[Once store_entry_rel_cases]
    >> simp[Once pairs_rel_cases]
    >> simp[Once pairs_rel_cases]
  )
  >> gvs[Once pair_rel_cases]
  >> simp[LUPDATE_def, muts_loc_def]
  >> simp[Once pairs_rel_cases]
  >> simp[Once pair_rel_cases]
QED

Theorem pairs_rel_LUPDATE_diff[allow_rebind] = cj 2 pairs_rel_LUPDATE_diff;

Theorem pairs_rel_mono:
  ! (refs'1:'a store_v list) (refs'2:'a store_v list) .
    (! pair ref . pair_rel refs'1 pair ref ==> pair_rel refs'2 pair ref)
    ==>
    ! pairs refs .
      pairs_rel refs'1 pairs refs ==> pairs_rel refs'2 pairs refs
Proof
  rpt gen_tac >> strip_tac
  >> ho_match_mp_tac pairs_rel_ind
  >> rpt strip_tac
  >> gvs[pair_rel_cases]
  >> simp[Once pairs_rel_cases]
  >> simp[pair_rel_cases]
QED

Theorem pairs_rel_loc:
  ! refs' pairs refs l .
    l < LENGTH pairs /\ pairs_rel refs' pairs refs 
    ==>
    pairs_loc 0 refs l < LENGTH refs /\
    pair_rel refs' (EL l pairs) (EL (pairs_loc 0 refs l) refs)
Proof
  rpt strip_tac
  >> dxrule_then assume_tac pairs_rel_FILTER
  >> gvs[LIST_REL_EL_EQN, pairs_loc_FILTER]
QED

(*
Inductive e_ce_rel:
[~Val:]
  ml_v_vals v mlv ∧
  nsLookup env.v (Short valv) = SOME (mlv) ∧
  nsLookup env.v (Short var) = SOME kv ∧
  valv ≠ var
  ⇒
  e_ce_rel (Val v) var env kv $ App Opapp [Var (Short var); Var (Short valv)]
[~Exp:]
  ce = cps_transform e ∧
  nsLookup env.v (Short var) = SOME kv ∧
  scheme_env env
  ⇒
  e_ce_rel (Exp e) var env kv $ App Opapp [ce; Var (Short var)]
[~Exception:]
  e_ce_rel (Exception s) var env kv $
    Con (SOME $ Short "Ex") [Lit $ StrLit $ explode s]
End
*)

Inductive cps_rel:
[~Val:]
  ml_v_vals refs v mlv ∧
  nsLookup env.v (Short t) = SOME (mlv) ∧
  nsLookup env.v (Short k) = SOME kv ∧
  t ≠ k
  ⇒
  cps_rel refs (Val v) k env kv $ App Opapp [Var (Short k); Var (Short t)]
[~Exp:]
  ce = cps_transform e ∧
  nsLookup env.v (Short k) = SOME kv ∧
  scheme_env env ∧
  env_rel refs senv env
  ⇒
  cps_rel refs (Exp senv e) var env kv $ App Opapp [ce; Var (Short k)]
[~Exception:]
  cps_rel refs (Exception s) var env kv $
    Con (SOME $ Short "Ex") [Lit $ StrLit $ explode s]
End

Theorem env_rel_FEMPTY[simp]:
  ∀ refs env . env_rel refs FEMPTY env
Proof
  simp[env_rel_cases, FEVERY_FEMPTY]
QED

Theorem env_rel_non_var[simp]:
  ! refs se env envv var v .
    (! x . var <> "var" ++ x)
    ==>
    env_rel refs se (env with v := nsBind var v envv) = env_rel refs se (env with v := envv)
Proof
  simp[env_rel_cases]
QED

Theorem scheme_env_sub:
  ∀ env envv var v .
    ¬ MEM var scheme_runtime_funs
    ⇒
   (scheme_env (env with v := nsBind var v envv) ⇔ scheme_env (env with v := envv))
Proof
  simp[scheme_runtime_funs_def, scheme_env_def]
QED

val scheme_env_tac = irule_at (Pat ‘scheme_env _’) $ iffRL scheme_env_sub >> simp[scheme_runtime_funs_def];

Theorem compile_in_rel:
  ∀ p st env .
    scheme_env env
    ⇒
    ∃ st' env' var mle ks kv .
      cps_rel st.refs (Exp FEMPTY p) var env' kv mle ∧
      cont_rel st.refs ks kv ∧
      evaluate st env [compile_scheme_prog p] = evaluate st' env' [mle]
Proof
  simp[Once cps_rel_cases, compile_scheme_prog_def]
  >> rpt strip_tac
  >> simp[Ntimes evaluate_def 2, nsOptBind_def]
  >> irule_at (Pos last) EQ_REFL
  >> simp[Once cont_rel_cases]
  >> scheme_env_tac
  >> metis_tac[]
QED

Theorem scheme_cons_lookup:
  ! env . scheme_env env ==> EVERY (\c . nsLookup env.c (Short c) = nsLookup scheme_cons_env (Short c)) scheme_conses
Proof
  rpt strip_tac
  >> gvs[scheme_env_def, scheme_cons_env_def, scheme_conses_def, nsLookup_def]
QED

Theorem scheme_app_cons_lookup:
  ! env . scheme_env_app env ==> EVERY (\c . nsLookup env.c (Short c) = nsLookup scheme_cons_env (Short c)) scheme_conses
Proof
  rpt strip_tac
  >> gvs[scheme_env_app_def, scheme_cons_env_def, scheme_conses_def, nsLookup_def]
QED

val _ = augment_srw_ss $ single $ rewrites $ BODY_CONJUNCTS $ SRULE [IMP_CONJ_THM] $ RESTR_EVAL_RULE [``scheme_env``] scheme_cons_lookup;
val _ = augment_srw_ss $ single $ rewrites $ BODY_CONJUNCTS $ SRULE [IMP_CONJ_THM] $ RESTR_EVAL_RULE [``scheme_env_app``] scheme_app_cons_lookup;

(*
open scheme_to_cakeProofTheory;
open scheme_parsingTheory;
*)

Theorem cps_app_ts_res:
  ∀ t ts vs .
    (t, ts) = cps_app_ts vs
    ⇒
    t = "t" ++ toString (LENGTH ts) ∧
    (∀ n:num . n ≥ LENGTH ts ⇒ ¬ MEM ("t" ++ toString n) ts) ∧
    LENGTH vs = LENGTH ts
Proof
  Induct_on ‘vs’
  >> simp[cps_app_ts_def]
  >> rpt (pairarg_tac >> gvs[])
QED

Theorem str_not_num:
  ∀ (n:num) str . ¬ EVERY isDigit str ⇒ toString n ≠ str
Proof
  simp[EVERY_isDigit_num_to_dec_string]
QED

Theorem cps_app_ts_distinct:
  ∀ t ts vs .
    (t, ts) = cps_app_ts vs
    ⇒
    ¬ MEM t ts ∧
    ALL_DISTINCT ts ∧
    t ≠ "t" ∧
    t ≠ "k" ∧
    ¬ MEM "t" ts ∧
    ¬ MEM "k" ts ∧
    ¬ MEM t scheme_runtime_funs ∧
    EVERY (λ t. ¬ MEM t scheme_runtime_funs) ts ∧
    (∀ x . t ≠ "var" ++ x) ∧
    EVERY (λ t. ∀ x . t ≠ "var" ++ x) ts
Proof
  Induct_on ‘vs’
  >> simp[cps_app_ts_def]
  >> rpt (pairarg_tac >> gvs[])
  >> gvs[scheme_runtime_funs_def]
  >> drule_then mp_tac $ GSYM cps_app_ts_res
  >> strip_tac
  >> qpat_x_assum ‘_ = t’ $ assume_tac o GSYM
  >> simp[]
  >> qpat_assum ‘∀ _ . _ ⇒ _’ $ irule_at (Pos hd) o SRULE []
  >> simp[]
  >> irule_at Any str_not_num
  >> simp[isDigit_def]
QED

Theorem cons_list_val:
  ∀ st env ts vs .
    scheme_env env ∧
    LIST_REL (λ x v . nsLookup env.v (Short x) = SOME v) ts vs
    ⇒
    evaluate (st:'ffi state) env [cons_list (MAP (Var o Short) ts)]
      = (st, Rval [vcons_list vs])
Proof
  rpt strip_tac
  >> pop_assum mp_tac
  >> qid_spec_tac ‘vs’
  >> qid_spec_tac ‘ts’
  >> ho_match_mp_tac LIST_REL_ind
  >> simp[evaluate_def, cons_list_def, vcons_list_def,
    do_con_check_def, build_conv_def]
  >> gvs[scheme_env_def]
QED

Theorem map_reverse(*[simp]*):
  ∀ xs f . MAP f (REVERSE xs) = REVERSE (MAP f xs)
Proof
  Induct >> simp[]
QED

Theorem LIST_REL_SNOC_ind:
  ∀R LIST_REL'.
    LIST_REL' [] [] ∧
    (∀h1 h2 t1 t2.
      R h1 h2 ∧ LIST_REL' t1 t2 ⇒ LIST_REL' (SNOC h1 t1) (SNOC h2 t2)) ⇒
    ∀a0 a1. LIST_REL R a0 a1 ⇒ LIST_REL' a0 a1
Proof
  strip_tac >> strip_tac >> strip_tac
  >> Induct_on ‘a0’ using SNOC_INDUCT
  >> Induct_on ‘a1’ using SNOC_INDUCT
  >- simp[]
  >- simp[EVERY2_LENGTH]
  >- simp[EVERY2_LENGTH]
  >> pop_assum kall_tac
  >> simp[LIST_REL_SNOC]
QED

Definition eval_eq_def:
  eval_eq st mlenv mle st' mlenv' mle' ck = ∀ start.
    evaluate (st with clock := ck + start) mlenv [mle]
    =
    evaluate (st' with clock := start) mlenv' [mle']
End

Theorem eval_eq_trivial:
  ∀ st mlenv mle .
    eval_eq st mlenv mle st mlenv mle 0
Proof
  simp[eval_eq_def]
QED

Theorem eval_eq_trans:
  ∀ st mlenv mle st' mlenv' mle' st'' mlenv'' mle'' ck ck' .
    eval_eq st mlenv mle st' mlenv' mle' ck ∧
    eval_eq st' mlenv' mle' st'' mlenv'' mle'' ck'
    ⇒
    eval_eq st mlenv mle st'' mlenv'' mle'' (ck + ck')
Proof
  simp[eval_eq_def]
QED

Definition val_eval_def:
  val_eval st env k t = evaluate st env [App Opapp [Var (Short k); Var (Short t)]]
End

Definition exp_eval_def:
  exp_eval st env e k = evaluate st env [App Opapp [cps_transform e; Var (Short k)]]
End

Definition ex_eval_def:
  ex_eval st env s = evaluate st env [Con (SOME $ Short "Ex") [Lit $ StrLit s]]
End

Theorem preservation_of_sadd_body:
  ∀ vs mlvs .
    LIST_REL ml_v_vals vs mlvs
    ⇒
  ∀ store st env n k kv .
    cont_rel k kv ∧
    LIST_REL store_entry_rel store st.refs ∧
    nsLookup env.v (Short "ts") = SOME (vcons_list mlvs) ∧
    nsLookup env.v (Short "n") = SOME (Litv (IntLit n)) ∧
    nsLookup env.v (Short "k") = SOME kv ∧
    nsLookup env.v (Short "sadd") = nsLookup scheme_env2.v (Short "sadd") ∧
    env.c = scheme_env1.c
    ⇒
    ∃ck st' mlenv' var' kv' mle'.
      (∀ start . evaluate (st with clock := ck + start) env
        [Mat (Var (Short "ts"))
           [(Pcon (SOME (Short "[]")) [],
             Let (SOME "t") (Con (SOME (Short "SNum")) [Var (Short "n")])
               (App Opapp [Var (Short "k"); Var (Short "t")]));
            (Pcon (SOME (Short "::")) [Pvar "t"; Pvar "ts'"],
             Mat (Var (Short "t"))
               [(Pcon (SOME (Short "SNum")) [Pvar "tn"],
                 App Opapp
                   [App Opapp
                      [App Opapp [Var (Short "sadd"); Var (Short "k")];
                       App (Opn Plus) [Var (Short "n"); Var (Short "tn")]];
                    Var (Short "ts'")]);
                (Pany,
                 Con (SOME (Short "Ex"))
                   [Lit (StrLit "Arith-op applied to non-number")])])]] =
      evaluate (st' with clock := start) mlenv' [mle']) ∧
      cont_rel k kv' ∧
      e_ce_rel (sadd vs n) var' mlenv' kv' mle' ∧
      env_rel FEMPTY mlenv' ∧
      LIST_REL store_entry_rel store st'.refs ∧
      st.ffi = st'.ffi
Proof
  ho_match_mp_tac LIST_REL_ind
  >> simp[vcons_list_def, sadd_def]
  >> rpt strip_tac >- (
    simp[Ntimes evaluate_def 2]
    >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
      same_type_def, same_ctor_def, evaluate_match_def,
      pat_bindings_def]
    >> simp[Ntimes evaluate_def 3, do_con_check_def, build_conv_def,
      nsOptBind_def]
    >> simp[GSYM eval_eq_def]
    >> irule_at (Pos hd) eval_eq_trivial
    >> last_assum $ irule_at (Pos hd)
    >> simp[Once e_ce_rel_cases, sadd_def, Once ml_v_vals_cases,
      env_rel_cases, FEVERY_FEMPTY]
  )
  >> gvs[Once ml_v_vals_cases]
  >> gvs[vcons_list_def]
  >~ [‘SNum m’] >- (
    simp[sadd_def]
    >> simp[evaluate_def, do_opapp_def, do_app_def,
      opn_lookup_def, can_pmatch_all_def, pmatch_def, nsLookup_def,
      same_type_def, same_ctor_def, evaluate_match_def,
      pat_bindings_def, do_con_check_def, build_conv_def, dec_clock_def]
    >> simp[Ntimes find_recfun_def 2, Ntimes build_rec_env_def 2]
    >> qrefine ‘ck+3’
    >> simp[Ntimes evaluate_def 2]
    >> ‘st.ffi = (st with <|refs := st.refs; ffi := st.ffi|>).ffi’ by simp[]
    >> first_assum $ once_asm_rewrite_tac o single
    >> pop_assum $ simp_tac pure_ss o single o Once o GSYM
    >> last_x_assum irule
    >> simp[]
    >> simp[Once INT_ADD_COMM]
  )
  >> simp[Ntimes evaluate_def 10, do_opapp_def, do_app_def,
    opn_lookup_def, can_pmatch_all_def, pmatch_def, nsLookup_def,
    same_type_def, same_ctor_def, evaluate_match_def,
    pat_bindings_def, do_con_check_def, build_conv_def, dec_clock_def]
  >> simp[Ntimes find_recfun_def 2, Ntimes build_rec_env_def 2]
  >> simp[sadd_def, Once e_ce_rel_cases]
  >> simp[GSYM eval_eq_def]
  >> irule_at (Pos hd) eval_eq_trivial
  >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
  >> simp[env_rel_cases, FEVERY_FEMPTY]
QED

Theorem preservation_of_smul_body:
  ∀ vs mlvs .
    LIST_REL ml_v_vals vs mlvs
    ⇒
  ∀ store st env n k kv .
    cont_rel k kv ∧
    LIST_REL store_entry_rel store st.refs ∧
    nsLookup env.v (Short "ts") = SOME (vcons_list mlvs) ∧
    nsLookup env.v (Short "n") = SOME (Litv (IntLit n)) ∧
    nsLookup env.v (Short "k") = SOME kv ∧
    nsLookup env.v (Short "smul") = nsLookup scheme_env3.v (Short "smul") ∧
    env.c = scheme_env1.c
    ⇒
    ∃ck st' mlenv' var' kv' mle'.
      (∀ start . evaluate (st with clock := ck + start) env
        [Mat (Var (Short "ts"))
           [(Pcon (SOME (Short "[]")) [],
             Let (SOME "t") (Con (SOME (Short "SNum")) [Var (Short "n")])
               (App Opapp [Var (Short "k"); Var (Short "t")]));
            (Pcon (SOME (Short "::")) [Pvar "t"; Pvar "ts'"],
             Mat (Var (Short "t"))
               [(Pcon (SOME (Short "SNum")) [Pvar "tn"],
                 App Opapp
                   [App Opapp
                      [App Opapp [Var (Short "smul"); Var (Short "k")];
                       App (Opn Times) [Var (Short "n"); Var (Short "tn")]];
                    Var (Short "ts'")]);
                (Pany,
                 Con (SOME (Short "Ex"))
                   [Lit (StrLit "Arith-op applied to non-number")])])]] =
      evaluate (st' with clock := start) mlenv' [mle']) ∧
      cont_rel k kv' ∧
      e_ce_rel (smul vs n) var' mlenv' kv' mle' ∧
      env_rel FEMPTY mlenv' ∧
      LIST_REL store_entry_rel store st'.refs ∧
      st.ffi = st'.ffi
Proof
  ho_match_mp_tac LIST_REL_ind
  >> simp[vcons_list_def, smul_def]
  >> rpt strip_tac >- (
    simp[Ntimes evaluate_def 2]
    >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
      same_type_def, same_ctor_def, evaluate_match_def,
      pat_bindings_def]
    >> simp[Ntimes evaluate_def 3, do_con_check_def, build_conv_def,
      nsOptBind_def]
    >> simp[GSYM eval_eq_def]
    >> irule_at (Pos hd) eval_eq_trivial
    >> last_assum $ irule_at (Pos hd)
    >> simp[Once e_ce_rel_cases, smul_def, Once ml_v_vals_cases,
      env_rel_cases, FEVERY_FEMPTY]
  )
  >> gvs[Once ml_v_vals_cases]
  >> gvs[vcons_list_def]
  >~ [‘SNum m’] >- (
    simp[smul_def]
    >> simp[evaluate_def, do_opapp_def, do_app_def,
      opn_lookup_def, can_pmatch_all_def, pmatch_def, nsLookup_def,
      same_type_def, same_ctor_def, evaluate_match_def,
      pat_bindings_def, do_con_check_def, build_conv_def, dec_clock_def]
    >> simp[Ntimes find_recfun_def 2, Ntimes build_rec_env_def 2]
    >> qrefine ‘ck+3’
    >> simp[Ntimes evaluate_def 2]
    >> ‘st.ffi = (st with <|refs := st.refs; ffi := st.ffi|>).ffi’ by simp[]
    >> first_assum $ once_asm_rewrite_tac o single
    >> pop_assum $ simp_tac pure_ss o single o Once o GSYM
    >> last_x_assum irule
    >> simp[]
    >> simp[scheme_env2_def, Once INT_MUL_COMM]
  )
  >> simp[Ntimes evaluate_def 10, do_opapp_def, do_app_def,
    opn_lookup_def, can_pmatch_all_def, pmatch_def, nsLookup_def,
    same_type_def, same_ctor_def, evaluate_match_def,
    pat_bindings_def, do_con_check_def, build_conv_def, dec_clock_def]
  >> simp[Ntimes find_recfun_def 2, Ntimes build_rec_env_def 2]
  >> simp[smul_def, Once e_ce_rel_cases]
  >> simp[GSYM eval_eq_def]
  >> irule_at (Pos hd) eval_eq_trivial
  >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
  >> simp[env_rel_cases, FEVERY_FEMPTY]
QED

Theorem preservation_of_sminus_body:
  ∀ vs mlvs .
    LIST_REL ml_v_vals vs mlvs
    ⇒
  ∀ store (st:'ffi state) env n k kv .
    cont_rel k kv ∧
    LIST_REL store_entry_rel store st.refs ∧
    nsLookup env.v (Short "ts") = SOME (vcons_list mlvs) ∧
    nsLookup env.v (Short "k") = SOME kv ∧
    nsLookup env.v (Short "sadd") = nsLookup scheme_env3.v (Short "sadd") ∧
    env.c = scheme_env1.c
    ⇒
    ∃ck st' mlenv' var' kv' mle'.
      (∀ start . evaluate (st with clock := ck + start) env
        [Mat (Var (Short "ts"))
           [(Pcon (SOME (Short "[]")) [],
             Con (SOME (Short "Ex")) [Lit (StrLit "Arity mismatch")]);
            (Pcon (SOME (Short "::")) [Pvar "t"; Pvar "ts'"],
             Mat (Var (Short "t"))
               [(Pcon (SOME (Short "SNum")) [Pvar "n"],
                  Mat (Var (Short "ts'")) [
                    (Pcon (SOME $ Short "[]") [],
                      Let (SOME "t") (Con (SOME $ Short "SNum") [
                          App (Opn Minus) [Lit $ IntLit 0; Var (Short "n")]]) $
                        App Opapp [Var (Short "k"); Var (Short "t")]);
                    (Pany, App Opapp [App Opapp [App Opapp [Var (Short "sadd");
                      Fun "t" $ Mat (Var (Short "t")) [
                        (Pcon (SOME $ Short "SNum") [Pvar "m"],
                          Let (SOME "t") (Con (SOME $ Short "SNum") [
                              App (Opn Minus) [Var (Short "n"); Var (Short "m")]]) $
                            App Opapp [Var (Short "k"); Var (Short "t")]);
                        (Pany,
                          App Opapp [Var (Short "k"); Var (Short "t")])
                      ]];
                      Lit $ IntLit 0]; Var (Short "ts'")])]);
                (Pany,
                 Con (SOME (Short "Ex"))
                   [Lit (StrLit "Arith-op applied to non-number")])])]] =
      evaluate (st' with clock := start) mlenv' [mle']) ∧
      cont_rel k kv' ∧
      e_ce_rel (sminus vs) var' mlenv' kv' mle' ∧
      env_rel FEMPTY mlenv' ∧
      LIST_REL store_entry_rel store st'.refs ∧
      st.ffi = st'.ffi
Proof
  Cases_on ‘vs’ >- (
    simp[vcons_list_def]
    >> rpt strip_tac
    >> simp[Ntimes evaluate_def 3]
    >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
      same_type_def, same_ctor_def, evaluate_match_def,
      pat_bindings_def]
    >> simp[GSYM eval_eq_def]
    >> irule_at (Pos hd) eval_eq_trivial
    >> last_assum $ irule_at (Pos hd)
    >> simp[sminus_def]
    >> simp[Once e_ce_rel_cases, env_rel_cases, FEVERY_FEMPTY]
  )
  >> Cases_on ‘mlvs’
  >> simp[vcons_list_def]
  >> strip_tac
  >> gvs[Once ml_v_vals_cases]
  >~ [‘SNum i’] >- (
    simp[Ntimes evaluate_def 3]
    >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
      same_type_def, same_ctor_def, evaluate_match_def,
      pat_bindings_def]
    >> rpt strip_tac
    >> simp[Ntimes evaluate_def 3]
    >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
      same_type_def, same_ctor_def, evaluate_match_def,
      pat_bindings_def]
    >> simp[Ntimes find_recfun_def 2, Ntimes build_rec_env_def 2]
    >> Cases_on ‘t=[]’ >- (
      gvs[vcons_list_def]
      >> simp[Ntimes evaluate_def 3]
      >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
        same_type_def, same_ctor_def, evaluate_match_def,
        pat_bindings_def]
      >> simp[Ntimes evaluate_def 6, do_app_def, do_con_check_def,
        build_conv_def, nsOptBind_def, opn_lookup_def]
      >> simp[GSYM eval_eq_def]
      >> irule_at (Pos hd) eval_eq_trivial
      >> simp[sminus_def, Once e_ce_rel_cases, Once ml_v_vals_cases,
        env_rel_cases, FEVERY_FEMPTY]
    )
    >> qrefine ‘ck+3’
    >> ‘∃ t' ts' . t'::ts'=t’ by (Cases_on ‘t’ >> gvs[])
    >> simp[sminus_def]
    >> first_assum $ simp_tac bool_ss o single o  GSYM
    >> simp[Ntimes evaluate_def 3]
    >> ‘∃ y ys . y::ys = t'’ by gvs[]
    >> pop_assum $ simp_tac bool_ss o single o (fn x => Ntimes x 2) o GSYM
    >> simp[vcons_list_def]
    >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
      same_type_def, same_ctor_def, evaluate_match_def,
      pat_bindings_def]
    >> pop_assum kall_tac
    >> pop_assum kall_tac
    >> simp[Ntimes evaluate_def 3]
    >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
      same_type_def, same_ctor_def, evaluate_match_def,
      pat_bindings_def]
    >> simp[Ntimes evaluate_def 7, do_opapp_def]
    >> simp[Ntimes find_recfun_def 2, Ntimes build_rec_env_def 2]
    >> simp[Ntimes evaluate_def 2, dec_clock_def]
    >> simp[sminus_def]
    >> ‘∃ n . 0i = n’ by simp[]
    >> pop_assum mp_tac >> strip_tac
    >> pop_assum $ simp o single
    >> ‘∃ kenv . (env with
                           v :=
                             nsBind "n" (Litv (IntLit i))
                               (nsBind "ts'" (vcons_list t')
                                  (nsBind "t"
                                     (Conv (SOME (TypeStamp "SNum" 4))
                                        [Litv (IntLit i)]) env.v)))
                  = kenv’ by simp[]
    >> pop_assum mp_tac >> strip_tac
    >> ‘nsLookup kenv.v (Short "n") = SOME (Litv (IntLit i))’ by gvs[]
    >> ‘nsLookup kenv.v (Short "k") = SOME kv’ by gvs[]
    >> ‘kenv.c = scheme_env1.c’ by gvs[]
    >> qpat_x_assum ‘_ = kenv’ $ simp o single
    >> rpt $ qpat_x_assum ‘nsLookup env.v _ = _’ kall_tac
    >> rpt $ pop_assum mp_tac
    >> strip_tac
    >> qid_spec_tac ‘i''’
    >> qid_spec_tac ‘n’
    >> qid_spec_tac ‘st’
    >> pop_assum mp_tac
    >> qid_spec_tac ‘t'’
    >> qid_spec_tac ‘t’
    >> ho_match_mp_tac LIST_REL_ind
    >> rpt strip_tac >- (
      simp[vcons_list_def, sadd_def]
      >> simp[Ntimes evaluate_def 3]
      >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
        same_type_def, same_ctor_def, evaluate_match_def,
        pat_bindings_def]
      >> simp[Ntimes evaluate_def 7, do_opapp_def, do_con_check_def,
        build_conv_def, nsOptBind_def]
      >> qrefine ‘ck+1’
      >> simp[Ntimes evaluate_def 3, dec_clock_def]
      >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
        same_type_def, same_ctor_def, evaluate_match_def,
        pat_bindings_def]
      >> simp[Ntimes evaluate_def 6, do_app_def, do_con_check_def,
        build_conv_def, nsOptBind_def, opn_lookup_def]
      >> simp[GSYM eval_eq_def]
      >> irule_at (Pos hd) eval_eq_trivial
      >> simp[env_rel_cases, FEVERY_FEMPTY]
      >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
      >> simp[Once e_ce_rel_cases, Once ml_v_vals_cases]
    )
    >> gvs[Once ml_v_vals_cases]
    >~ [‘SNum m’] >- (
      simp[sadd_def, vcons_list_def]
      >> simp[evaluate_def, do_opapp_def, do_app_def,
        opn_lookup_def, can_pmatch_all_def, pmatch_def, nsLookup_def,
        same_type_def, same_ctor_def, evaluate_match_def,
        pat_bindings_def, do_con_check_def, build_conv_def, dec_clock_def]
      >> simp[Ntimes find_recfun_def 2, Ntimes build_rec_env_def 2]
      >> qrefine ‘ck+3’
      >> simp[Ntimes evaluate_def 2]
      >> simp[Once INT_ADD_COMM]
      >> ‘st.ffi = (st with <|refs := st.refs; ffi := st.ffi|>).ffi’ by simp[]
      >> first_assum $ once_asm_rewrite_tac o single
      >> pop_assum $ simp_tac pure_ss o single o Once o GSYM
      >> last_x_assum irule
      >> simp[]
    )
    >> simp[sadd_def, vcons_list_def]
    >> simp[Ntimes evaluate_def 3]
    >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
      same_type_def, same_ctor_def, evaluate_match_def,
      pat_bindings_def]
    >> simp[Ntimes evaluate_def 3]
    >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
      same_type_def, same_ctor_def, evaluate_match_def,
      pat_bindings_def]
    >> simp[GSYM eval_eq_def]
    >> irule_at (Pos hd) eval_eq_trivial
    >> simp[env_rel_cases, FEVERY_FEMPTY]
    >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
    >> simp[Once e_ce_rel_cases]
  )
  >> simp[sminus_def]
  >> rpt strip_tac
  >> simp[Ntimes evaluate_def 3]
  >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
    same_type_def, same_ctor_def, evaluate_match_def,
    pat_bindings_def]
  >> simp[Ntimes evaluate_def 3]
  >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
    same_type_def, same_ctor_def, evaluate_match_def,
    pat_bindings_def]
  >> simp[GSYM eval_eq_def]
  >> irule_at (Pos hd) eval_eq_trivial
  >> simp[env_rel_cases, FEVERY_FEMPTY]
  >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
  >> simp[Once e_ce_rel_cases]
QED

Theorem preservation_of_proc:
∀ (st:'ffi state) inner n n' m m' env env' mlenv var kv n xs xp e e' ce k args vs mlvs store store' .
  valid_val store (Proc env xs xp e) ∧
  LIST_REL ml_v_vals vs mlvs ∧
  EVERY (valid_val store) vs ∧
  valid_cont store k ∧
  cont_rel k kv ∧
  ce = cps_transform e ∧
  inner = proc_ml xs xp "k" ce ∧
  (store', env',e') = parameterize store env xs xp e vs ∧
  EVERY (OPTION_ALL (valid_val store)) store ∧
  nsLookup mlenv.v (Short "k") = SOME kv ∧
  nsLookup mlenv.v (Short "ts") = SOME (vcons_list mlvs) ∧
  env_rel env mlenv ∧
  scheme_env mlenv ∧
  can_lookup env store ∧
  LIST_REL store_entry_rel store st.refs
  ⇒
  ∃ck st' mlenv' var' kv' mle'.
    (∀ start . evaluate (st with clock := ck + start) mlenv [inner]
      = evaluate (st' with clock := start) mlenv' [mle']) ∧
    cont_rel k kv' ∧
    e_ce_rel e' var' mlenv' kv' mle' ∧
    env_rel env' mlenv' ∧
    LIST_REL store_entry_rel store' st'.refs ∧
    st.ffi = st'.ffi
Proof
  Induct_on ‘xs’
  >> rpt strip_tac
  >- (
    qpat_assum ‘cont_rel _ _’ $ irule_at (Pat ‘cont_rel _ _’)
    >> Cases_on ‘xp’
    >> gvs[proc_ml_def] >- (
      Cases_on ‘vs’
      >> gvs[parameterize_def] >- (
        simp[Ntimes evaluate_def 3]
        >> simp[can_pmatch_all_def, evaluate_match_def, vcons_list_def,
          pmatch_def]
        >> qpat_assum ‘scheme_env mlenv’ $ simp o single
          o SRULE [scheme_env_def]
        >> simp[same_type_def, same_ctor_def, pat_bindings_def]
        >> simp[GSYM eval_eq_def]
        >> irule_at (Pos hd) eval_eq_trivial
        >> simp[Once e_ce_rel_cases]
      )
      >> simp[Ntimes evaluate_def 3]
      >> simp[can_pmatch_all_def, evaluate_match_def, vcons_list_def,
        pmatch_def]
      >> qpat_assum ‘scheme_env mlenv’ $ simp o single
        o SRULE [scheme_env_def]
      >> simp[same_type_def, same_ctor_def, pat_bindings_def]
      >> simp[GSYM eval_eq_def]
      >> irule_at (Pos hd) eval_eq_trivial
      >> simp[Once e_ce_rel_cases]
      >> simp[env_rel_cases, FEVERY_FEMPTY]
    )
    >> gvs[parameterize_def]
    >> simp[Ntimes evaluate_def 3]
    >> simp[can_pmatch_all_def, evaluate_match_def, vcons_list_def,
      pmatch_def, do_con_check_def, build_conv_def]
    >> qpat_assum ‘scheme_env mlenv’ $ simp o single
      o SRULE [scheme_env_def]
    >> simp[same_type_def, same_ctor_def, pat_bindings_def]
    >> simp[Ntimes evaluate_def 2, do_app_def, store_alloc_def]
    >> simp[can_pmatch_all_def, evaluate_match_def, vcons_list_def,
      pmatch_def, do_con_check_def, build_conv_def, nsOptBind_def]
    >> qpat_assum ‘scheme_env mlenv’ $ simp o single
      o SRULE [scheme_env_def]
    >> simp[GSYM eval_eq_def]
    >> irule_at (Pos hd) eval_eq_trivial
    >> simp[]
    >> rpt (pairarg_tac >> gvs[])
    >> gvs[fresh_loc_def, store_entry_rel_cases]
    >> simp[Once ml_v_vals_cases]
    >> simp[Once e_ce_rel_cases]
    >> irule_at Any EQ_REFL
    >> simp[]
    >> gvs[scheme_env_def, env_rel_cases]
    >> Cases_on ‘x ∈ FDOM env’ >- (
      simp[FEVERY_DEF]
      >> strip_tac
      >> Cases_on ‘x = x'’
      >> gvs[] >- (
        drule $ cj 1 $ iffLR EVERY2_EVERY
        >> simp[]
      )
      >> strip_tac
      >> gvs[FEVERY_DEF]
      >> simp[FAPPLY_FUPDATE_THM]
    )
    >> irule $ cj 2 FEVERY_STRENGTHEN_THM
    >> simp[]
    >> drule_then assume_tac $ cj 1 $ iffLR EVERY2_EVERY
    >> simp[FEVERY_DEF]
    >> rpt strip_tac
    >> ‘x ≠ x'’ by (strip_tac >> gvs[])
    >> gvs[FEVERY_DEF]
  )
  >> gvs[proc_ml_def]
  >> rpt (pairarg_tac >> gvs[])
  >> Cases_on ‘vs’
  >> gvs[parameterize_def] >- (
    qpat_assum ‘cont_rel _ _’ $ irule_at (Pat ‘cont_rel _ _’)
    >> simp[Ntimes evaluate_def 3]
    >> simp[can_pmatch_all_def, evaluate_match_def, vcons_list_def,
      pmatch_def]
    >> qpat_assum ‘scheme_env mlenv’ $ simp o single
      o SRULE [scheme_env_def]
    >> simp[same_type_def, same_ctor_def, pat_bindings_def]
    >> simp[GSYM eval_eq_def]
    >> irule_at (Pos hd) eval_eq_trivial
    >> simp[Once e_ce_rel_cases]
    >> simp[env_rel_cases, FEVERY_FEMPTY]
  )
  >> simp[Ntimes evaluate_def 3]
  >> simp[can_pmatch_all_def, evaluate_match_def, vcons_list_def,
    pmatch_def]
  >> qpat_assum ‘scheme_env mlenv’ $ simp o single
    o SRULE [scheme_env_def]
  >> simp[same_type_def, same_ctor_def, pat_bindings_def]
  >> simp[Ntimes evaluate_def 4, do_app_def, store_alloc_def]
  >> simp[can_pmatch_all_def, evaluate_match_def, vcons_list_def,
    pmatch_def, do_con_check_def, build_conv_def, nsOptBind_def]
  >> qpat_assum ‘scheme_env mlenv’ $ simp o single
    o SRULE [scheme_env_def]
  >> simp[same_type_def, same_ctor_def, pat_bindings_def]
  >> ‘st.ffi = (st with <|refs :=
                  st.refs ++ [Refv (Conv (SOME (TypeStamp "Some" 2)) [y])];
                ffi := st.ffi|>).ffi’ by simp[]
  >> first_assum $ once_asm_rewrite_tac o single
  >> pop_assum $ simp_tac pure_ss o single o Once o GSYM
  >> last_x_assum irule
  >> simp[]
  >> rpt (pairarg_tac >> gvs[])
  >> rpt $ irule_at Any EQ_REFL
  >> simp[]
  >> qpat_assum ‘scheme_env mlenv’ $ simp
    o curry ((::) o swap) [scheme_env_def]
    o SRULE [scheme_env_def]
  >> gvs[fresh_loc_def]
  >> simp[SNOC_APPEND, store_entry_rel_cases]
  >> irule_at (Pos hd) EVERY_MONOTONIC
  >> qpat_assum ‘EVERY _ store’ $ irule_at (Pos $ el 2)
  >> strip_tac >- (
    rpt strip_tac
    >> irule OPTION_ALL_MONO
    >> pop_assum $ irule_at (Pos last)
    >> rpt strip_tac
    >> irule valid_val_larger_store
    >> pop_assum $ irule_at (Pos last)
    >> simp[]
  )
  >> irule_at (Pos hd) valid_val_larger_store
  >> qpat_assum ‘valid_store _ h'’ $ irule_at (Pos $ el 2)
  >> simp[]
  >> irule_at (Pos hd) EVERY_MONOTONIC
  >> qpat_assum ‘EVERY _ t’ $ irule_at (Pos $ el 2)
  >> strip_tac >- (
    rpt strip_tac
    >> irule valid_val_larger_store
    >> pop_assum $ irule_at (Pos last)
    >> simp[]
  )
  >> irule_at (Pos $ el 3) valid_cont_larger_store
  >> qpat_assum ‘valid_cont _ k'’ $ irule_at (Pos $ el 2)
  >> simp[Once valid_val_cases]
  >> conj_asm1_tac >- (
    gvs[can_lookup_cases]
    >> irule $ cj 2 FEVERY_STRENGTHEN_THM
    >> irule_at (Pos last) FEVERY_MONO
    >> qpat_assum ‘FEVERY _ env’ $ irule_at (Pos $ el 2)
    >> simp[]
    >> PairCases
    >> simp[]
  )
  >> simp[]
  >> gvs[env_rel_cases]
  >> strip_tac >- (
    Cases_on ‘h ∈ FDOM env’ >- (
      simp[FEVERY_DEF]
      >> strip_tac
      >> Cases_on ‘x = h’
      >> gvs[] >- (
        drule $ cj 1 $ iffLR EVERY2_EVERY
        >> simp[]
      )
      >> strip_tac
      >> gvs[FEVERY_DEF]
      >> simp[FAPPLY_FUPDATE_THM]
    )
    >> irule $ cj 2 FEVERY_STRENGTHEN_THM
    >> simp[]
    >> drule_then assume_tac $ cj 1 $ iffLR EVERY2_EVERY
    >> simp[FEVERY_DEF]
    >> rpt strip_tac
    >> ‘x ≠ h’ by (strip_tac >> gvs[])
    >> gvs[FEVERY_DEF]
  )
  >> Cases_on ‘xp’
  >> simp[]
  >> irule static_scope_mono
  >> gvs[Once valid_val_cases]
  >> qpat_assum ‘static_scope _ _’ $ irule_at (Pos last)
  >> simp[Ntimes INSERT_SING_UNION 2]
  >> simp[SUBSET_DEF]
QED

Theorem preservation_of_letrec:
  ∀ xs inner (st:'ffi state) mlenv store env store' env' .
    (store', env') = letrec_preinit store env xs ∧
    env_rel env mlenv ∧
    LIST_REL store_entry_rel store st.refs ∧
    scheme_env mlenv
    ⇒
    ∃ ck st' mlenv' var' .
      (∀ start . evaluate (st with clock:=ck+start) mlenv [letpreinit_ml xs inner]
        = evaluate (st' with clock:=start) mlenv' [inner]) ∧
      env_rel env' mlenv' ∧
      LIST_REL store_entry_rel store' st'.refs ∧
      (∀ x v . (∀ x' . x ≠ "var" ++ x') ∧ nsLookup mlenv.v (Short x) = SOME v
      ⇒
      nsLookup mlenv'.v (Short x) = SOME v) ∧
      scheme_env mlenv' ∧
      st.ffi = st'.ffi
Proof
  Induct
  >> simp[letrec_preinit_def, letpreinit_ml_def]
  >> rpt strip_tac >- (
    simp[GSYM eval_eq_def]
    >> irule_at (Pos hd) eval_eq_trivial
    >> simp[]
  )
  >> rpt (pairarg_tac >> gvs[])
  >> simp[Ntimes evaluate_def 3, do_con_check_def, build_conv_def,
    do_app_def, store_alloc_def, nsOptBind_def]
  >> qpat_assum ‘scheme_env _’ $ simp o single
    o SRULE [scheme_env_def]
  >> qsuff_tac ‘∀ mlenv' .
          (∀x v.
             (∀x'. x ≠ STRING #"v" (STRING #"a" (STRING #"r" x'))) ∧
             nsLookup (mlenv with
               v :=
                 nsBind (STRING #"v" (STRING #"a" (STRING #"r" (explode h))))
                   (Loc T (LENGTH st.refs)) mlenv.v).v (Short x) = SOME v ⇒
             nsLookup mlenv'.v (Short x) = SOME v)
          ⇔
          (∀x v.
             (∀x'. x ≠ STRING #"v" (STRING #"a" (STRING #"r" x'))) ∧
             nsLookup mlenv.v (Short x) = SOME v ⇒
             nsLookup mlenv'.v (Short x) = SOME v)
        ’ >- (
    strip_tac
    >> pop_assum $ simp_tac pure_ss o single o GSYM
    >> ‘st.ffi = (st with <|refs :=
                    st.refs ++ [Refv (Conv (SOME (TypeStamp "None" 2)) [])];
                  ffi := st.ffi|>).ffi’ by simp[]
    >> first_assum $ once_asm_rewrite_tac o single
    >> pop_assum $ simp_tac pure_ss o single o Once o GSYM
    >> last_x_assum $ irule
    >> simp[]
    >> strip_tac >- gvs[scheme_env_def]
    >> irule_at (Pos hd) EQ_REFL
    >> gvs[env_rel_cases, fresh_loc_def, store_entry_rel_cases]
    >> Cases_on ‘h ∈ FDOM env’ >- (
      simp[FEVERY_DEF]
      >> strip_tac
      >> Cases_on ‘x = h’
      >> gvs[] >- (
        drule $ cj 1 $ iffLR EVERY2_EVERY
        >> simp[]
      )
      >> strip_tac
      >> gvs[FEVERY_DEF]
      >> simp[FAPPLY_FUPDATE_THM]
    )
    >> irule $ cj 2 FEVERY_STRENGTHEN_THM
    >> simp[]
    >> drule_then assume_tac $ cj 1 $ iffLR EVERY2_EVERY
    >> simp[FEVERY_DEF]
    >> rpt strip_tac
    >> ‘x ≠ h’ by (strip_tac >> gvs[])
    >> gvs[FEVERY_DEF]
  )
  >> strip_tac
  >> iff_tac
  >> rpt strip_tac
  >> qpat_assum ‘∀ _ _ . _ ∧ _ ⇒ _’ irule
  >> simp[]
  >> qpat_assum ‘∀ _ . _ ≠ _’ $ qspec_then ‘explode h’ assume_tac
  >> simp[]
  >> Cases_on ‘mlenv’
  >> gvs[]
QED

Theorem preservation_of_letinit:
  ∀ (st:'ffi state) mlenv mlvs store env e k kv var xvs ts .
    EVERY (FDOM env) (MAP FST xvs) ∧
    EVERY (valid_val store) (MAP SND xvs) ∧
    LIST_REL ml_v_vals (MAP SND xvs) mlvs ∧
    LIST_REL (λx mlv. nsLookup mlenv.v (Short x) = SOME mlv) ts mlvs ∧
    cont_rel k kv ∧ nsLookup mlenv.v (Short var) = SOME kv ∧
    scheme_env mlenv ∧
    env_rel env mlenv ∧
    can_lookup env store ∧
    LIST_REL store_entry_rel store st.refs
    ⇒
    ∃ck st' mlenv' var' kv' mle'.
      (∀start.
         evaluate (st with clock := ck + start) mlenv
           [letinit_ml
              (ZIP (MAP FST xvs,MAP (Var ∘ Short) ts))
              (App Opapp [cps_transform e; Var (Short var)])] =
         evaluate (st' with clock := start) mlenv' [mle']) ∧
      cont_rel k kv' ∧ e_ce_rel (Exp e) var' mlenv' kv' mle' ∧
      env_rel env mlenv' ∧
      LIST_REL store_entry_rel (letinit store env xvs) st'.refs ∧
      st.ffi = st'.ffi
Proof
  Induct_on ‘xvs’
  >> rpt strip_tac
  >> gvs[letinit_ml_def, letinit_def] >- (
    simp[GSYM eval_eq_def]
    >> irule_at (Pos hd) eval_eq_trivial
    >> simp[Once e_ce_rel_cases]
  )
  >> PairCases_on ‘h’
  >> simp[letinit_def]
  >> gvs[]
  >> simp[Ntimes evaluate_def 6, do_con_check_def, build_conv_def,
    nsOptBind_def]
  >> qpat_assum ‘scheme_env _’ $ simp o single
    o SRULE [scheme_env_def]
  >> qpat_assum ‘env_rel env _’ $ drule_then assume_tac
    o SRULE [env_rel_cases, FEVERY_DEF, SPECIFICATION]
  >> simp[do_app_def, store_assign_def, store_v_same_type_def]
  >> qpat_assum ‘can_lookup env _’ $ drule_then assume_tac
    o SRULE [can_lookup_cases, FEVERY_DEF, SPECIFICATION]
  >> drule_then assume_tac EVERY2_LENGTH
  >> drule_all_then assume_tac $ cj 2 $ iffLR LIST_REL_EL_EQN
  >> gvs[store_entry_rel_cases]
  >> (‘st.ffi = (st with <|refs := LUPDATE (Refv (Conv (SOME (TypeStamp "Some" 2)) [y]))
                      (env ' h0) st.refs; ffi := st.ffi|>).ffi’ by simp[]
  >> first_assum $ once_asm_rewrite_tac o single
  >> pop_assum $ simp_tac pure_ss o single o Once o GSYM
  >> last_x_assum $ irule
  >> first_assum $ irule_at (Pos last)
  >> simp[]
  >> irule_at (Pos hd) EVERY_MONOTONIC
  >> last_assum $ irule_at (Pos $ el 2)
  >> strip_tac >- (
    rpt strip_tac
    >> irule valid_val_larger_store
    >> pop_assum $ irule_at (Pos last)
    >> simp[LENGTH_LUPDATE]
  )
  >> gvs[can_lookup_cases]
  >> irule EVERY2_LUPDATE_same
  >> simp[store_entry_rel_cases])
QED

Theorem state_ffi_trivial[simp]:
  ! st:'ffi state . st with ffi := st.ffi = st
Proof
  simp[state_component_equality]
QED

Theorem state_refs_trivial[simp]:
  ! st:'ffi state . st with refs := st.refs = st
Proof
  simp[state_component_equality]
QED

fun dup n x = if n = 0 then [] else x::dup (n-1) x;

fun reduce_to_cps ck (thms:thm list) = EVERY (dup ck $ qrefine ‘ck+1’)
    >> simp([GSYM exp_eval_def, GSYM val_eval_def, GSYM ex_eval_def, do_opapp_def, evaluate_def,
            do_con_check_def, build_conv_def, dec_clock_def, nsOptBind_def,
            do_app_def, can_pmatch_all_def, pmatch_def, store_lookup_def,
            same_type_def, same_ctor_def, pat_bindings_def, store_assign_def, store_v_same_type_def]
         @ thms)
    >> simp([exp_eval_def, val_eval_def, ex_eval_def] @ thms);

Theorem application_preservation:
  ∀ sst sst' env env' fn vs e' ks ks' (st : 'ffi state) t mlfn ts mlvs mlenv k kv mle .
    application sst ks fn vs = (sst',ks',e') ∧
    cont_rel st.refs ks kv ∧
    store_rel sst st.refs ∧
    nsLookup mlenv.v (Short k) = SOME kv ∧
    ml_v_vals st.refs fn mlfn ∧
    nsLookup mlenv.v (Short t) = SOME mlfn ∧
    LIST_REL (ml_v_vals st.refs) vs mlvs ∧
    LIST_REL (λx mlv. nsLookup mlenv.v (Short x) = SOME mlv) ts mlvs ∧
    scheme_env mlenv ∧
    env_rel st.refs env mlenv
    ⇒
    ∃ ck st' mlenv' k' kv' mle' .
      (∀ start . evaluate (st with clock := start + ck) mlenv
        [App Opapp
          [App Opapp
            [App Opapp [Var (Short "app"); Var (Short k)];
            Var (Short t)];
          cons_list (MAP (Var o Short) ts)]]
      =
      evaluate (st' with clock := start) mlenv' [mle']) ∧
      cont_rel st'.refs ks' kv' ∧
      cps_rel st'.refs e' k' mlenv' kv' mle'∧
      store_rel sst' st'.refs ∧
      st.ffi = st'.ffi
Proof
  rpt strip_tac
  >> drule_all_then assume_tac cons_list_val
  >> drule $ cj 2 $ iffLR scheme_env_def
  >> strip_tac
  >> gvs[Once ml_v_vals_cases]
  >> qrefine ‘ck+3’
  >> simp[evaluate_def]
  >> simp[do_opapp_def, dec_clock_def]
  >> simp[Ntimes find_recfun_def 2, Ntimes build_rec_env_def 2]
  >> simp[Ntimes evaluate_def 3]
  >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
    same_type_def, same_ctor_def, evaluate_match_def,
    pat_bindings_def]
  >~ [`Prim SAdd`] >- (
    drule $ cj 2 $ iffLR scheme_env_app_def
    >> strip_tac
    >> gvs[application_def]
    >> qrefine ‘ck+2’
    >> simp[evaluate_def]
    >> simp[do_opapp_def, dec_clock_def]
    >> simp[Ntimes find_recfun_def 2, Ntimes build_rec_env_def 2]
    >> simp[Ntimes evaluate_def 2]
    >> `? n . 0:int = n` by simp[]
    >> pop_assum $ simp_tac std_ss o single
    >> rpt $ pop_assum mp_tac
    >> qid_spec_tac `n`
    >> qid_spec_tac `vs`
    >> qid_spec_tac `ts`
    >> Induct_on `mlvs`
    >> rpt strip_tac >- (
      fs[cons_list_def, vcons_list_def, sadd_def]
      >> rpt strip_tac
      >> reduce_to_cps 0 [can_pmatch_all_def, pmatch_def, nsLookup_def,
        same_type_def, same_ctor_def, evaluate_match_def,
        pat_bindings_def]
      >> simp[GSYM eval_eq_def]
      >> irule_at (Pos hd) eval_eq_trivial
      >> simp[Once cps_rel_cases, Once ml_v_vals_cases]
    )
    >> Cases_on `vs`
    >> fs[]
    >> Cases_on `ts`
    >> fs[cons_list_def, vcons_list_def]
    >> simp[Ntimes evaluate_def 2]
    >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
      same_type_def, same_ctor_def, evaluate_match_def,
      pat_bindings_def]
    >> fs[Once ml_v_vals_cases]
    >~ [`SNum i`]
    >> simp[Ntimes evaluate_def 2]
    >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
      same_type_def, same_ctor_def, evaluate_match_def,
      pat_bindings_def]
    >- (
      qrefine ‘ck+3’
      >> simp[evaluate_def]
      >> simp[do_opapp_def, do_app_def, dec_clock_def, opn_lookup_def]
      >> simp[Ntimes find_recfun_def 2, Ntimes build_rec_env_def 2]
      >> simp[Ntimes evaluate_def 2]
      >> simp[sadd_def]
      >> simp[Once INT_ADD_COMM]
      >> last_x_assum irule
      >> simp[]
      >> last_assum $ irule_at $ Pos last
      >> irule cons_list_val
      >> simp[]
    )
    >> simp[sadd_def]
    >> simp[GSYM eval_eq_def]
    >> irule_at (Pos hd) eval_eq_trivial
    >> simp[Once cps_rel_cases]
    >> first_assum $ irule_at $ Pos hd
  )
  >~ [`Prim SMul`] >- cheat
  >~ [`Prim SMinus`] >- cheat
  >~ [`Prim SEqv`] >- cheat
  >~ [`Prim CallCC`] >- cheat
  >~ [`Prim Cons`] >- cheat
  >~ [`Prim Car`] >- cheat
  >~ [`Prim Cdr`] >- cheat
  >~ [`Proc se xs xp e`] >- (
    pop_assum kall_tac
    >> pop_assum kall_tac
    >> rename1 `Closure proc_env _ _`
    >> qrefine ‘ck+1’
    >> simp[evaluate_def]
    >> simp[do_opapp_def, dec_clock_def]
    >> simp[Once evaluate_def]
    >> gvs[application_def]
    >> rpt (pairarg_tac >> gvs[])
    >> qpat_x_assum `! _._` kall_tac
    >> qpat_x_assum `scheme_env mlenv` kall_tac
    >> qpat_x_assum `env_rel _ _ mlenv` kall_tac
    >> qpat_x_assum `scheme_env_app _` kall_tac
    >> rpt $ qpat_x_assum `nsLookup mlenv.v _ = _` kall_tac
    >> qpat_x_assum `LIST_REL _ ts _` kall_tac
    >> qpat_abbrev_tac `proc_env' = proc_env with v:= _`
    >> `scheme_env proc_env'` by (unabbrev_all_tac >> rpt scheme_env_tac)
    >> `env_rel st.refs se proc_env'` by simp[Abbr `proc_env'`]
    >> `nsLookup proc_env'.v (Short "ts") = SOME (vcons_list mlvs)` by simp[Abbr `proc_env'`]
    >> `nsLookup proc_env'.v (Short "k") = SOME kv` by simp[Abbr `proc_env'`]
    >> qpat_x_assum `Abbrev _` kall_tac
    >> qpat_x_assum `scheme_env proc_env` kall_tac
    >> qpat_x_assum `env_rel _ _ proc_env` kall_tac
    >> rpt $ pop_assum mp_tac
    >> qid_spec_tac `se`
    >> qid_spec_tac `proc_env'`
    >> qid_spec_tac `sst`
    >> qid_spec_tac `st`
    >> qid_spec_tac `vs`
    >> qid_spec_tac `mlvs`
    >> Induct_on ‘xs’
    >> rpt strip_tac
    >> gvs[]
    >- (
      qpat_assum ‘cont_rel _ _ _’ $ irule_at (Pat ‘cont_rel _ _ _’)
      >> Cases_on ‘xp’
      >~ [`proc_ml _ (SOME _) _`] >- cheat
      >> gvs[proc_ml_def]
      >> Cases_on ‘vs’
      >> gvs[parameterize_def]
      >> reduce_to_cps 0 [can_pmatch_all_def, vcons_list_def, pmatch_def]
      >> simp[GSYM eval_eq_def]
      >> irule_at (Pos hd) eval_eq_trivial
      >> simp[Once cps_rel_cases]
    )
    >> Cases_on ‘xp’
    >~ [`proc_ml _ (SOME _) _`] >- cheat
    >> simp[proc_ml_def]
    >> Cases_on ‘vs’
    >> gvs[parameterize_def] >- (
      qpat_assum ‘cont_rel _ _ _’ $ irule_at (Pat ‘cont_rel _ _ _’)
      >> reduce_to_cps 0 [can_pmatch_all_def, vcons_list_def, pmatch_def]
      >> simp[GSYM eval_eq_def]
      >> irule_at (Pos hd) eval_eq_trivial
      >> simp[Once cps_rel_cases]
    )
    >> rpt (pairarg_tac >> gvs[])
    >> reduce_to_cps 0 [can_pmatch_all_def, vcons_list_def, pmatch_def, store_alloc_def]
val _ = (max_print_depth := 50);
    >> qpat_abbrev_tac `new_st = st with refs := new_refs`
    >> `st.ffi = new_st.ffi` by (unabbrev_all_tac >> simp[])
    >> pop_assum $ simp o single
    >> last_x_assum irule
    >> unabbrev_all_tac
    >> simp[]
    >> irule_at Any EQ_REFL
    >> rpt scheme_env_tac
    >> first_assum $ irule_at $ Pat `parameterize _ _ _ _ _ _ = _`
    >> gvs[fresh_loc_def]
    >> simp[cont_rel_mono]
    >> strip_tac >- (
      irule LIST_REL_mono
      >> last_assum $ irule_at $ Pos last
      >> rpt strip_tac
      >> simp[ml_v_vals_mono]
    )
    >> strip_tac >- (
      irule env_rel_alloc
      >> gvs[env_rel_cases]
      >> rename1 `explode x`
      >> Cases_on ‘x ∈ FDOM env’ >- (
        simp[FEVERY_DEF]
        >> strip_tac
        >> rename1 `x' = x`
        >> Cases_on ‘x' = x’
        >> gvs[] >- (
          drule $ cj 1 $ iffLR EVERY2_EVERY
          >> simp[GSYM muts_loc_alloc_same]
          >> simp[muts_loc_FILTER]
        )
        >> strip_tac
        >> gvs[FEVERY_DEF]
        >> simp[FAPPLY_FUPDATE_THM]
      )
      >> irule $ cj 2 FEVERY_STRENGTHEN_THM
      >> simp[]
      >> drule_then assume_tac $ cj 1 $ iffLR EVERY2_EVERY
      >> simp[FEVERY_DEF]
      >> rpt strip_tac
      >> ‘x ≠ h’ by (strip_tac >> gvs[])
      >> gvs[FEVERY_DEF]
    )

    >> qpat_assum ‘scheme_env mlenv’ $ simp
      o curry ((::) o swap) [scheme_env_def]
      o SRULE [scheme_env_def]
    >> gvs[fresh_loc_def]
    >> simp[SNOC_APPEND, store_entry_rel_cases]
    >> irule_at (Pos hd) EVERY_MONOTONIC
    >> qpat_assum ‘EVERY _ store’ $ irule_at (Pos $ el 2)
    >> strip_tac >- (
      rpt strip_tac
      >> irule OPTION_ALL_MONO
      >> pop_assum $ irule_at (Pos last)
      >> rpt strip_tac
      >> irule valid_val_larger_store
      >> pop_assum $ irule_at (Pos last)
      >> simp[]
    )
    >> irule_at (Pos hd) valid_val_larger_store
    >> qpat_assum ‘valid_store _ h'’ $ irule_at (Pos $ el 2)
    >> simp[]
    >> irule_at (Pos hd) EVERY_MONOTONIC
    >> qpat_assum ‘EVERY _ t’ $ irule_at (Pos $ el 2)
    >> strip_tac >- (
      rpt strip_tac
      >> irule valid_val_larger_store
      >> pop_assum $ irule_at (Pos last)
      >> simp[]
    )
    >> irule_at (Pos $ el 3) valid_cont_larger_store
    >> qpat_assum ‘valid_cont _ k'’ $ irule_at (Pos $ el 2)
    >> simp[Once valid_val_cases]
    >> conj_asm1_tac >- (
      gvs[can_lookup_cases]
      >> irule $ cj 2 FEVERY_STRENGTHEN_THM
      >> irule_at (Pos last) FEVERY_MONO
      >> qpat_assum ‘FEVERY _ env’ $ irule_at (Pos $ el 2)
      >> simp[]
      >> PairCases
      >> simp[]
    )
    >> simp[]
    >> gvs[env_rel_cases]
    >> strip_tac >- (
      Cases_on ‘h ∈ FDOM env’ >- (
        simp[FEVERY_DEF]
        >> strip_tac
        >> Cases_on ‘x = h’
        >> gvs[] >- (
          drule $ cj 1 $ iffLR EVERY2_EVERY
          >> simp[]
        )
        >> strip_tac
        >> gvs[FEVERY_DEF]
        >> simp[FAPPLY_FUPDATE_THM]
      )
      >> irule $ cj 2 FEVERY_STRENGTHEN_THM
      >> simp[]
      >> drule_then assume_tac $ cj 1 $ iffLR EVERY2_EVERY
      >> simp[FEVERY_DEF]
      >> rpt strip_tac
      >> ‘x ≠ h’ by (strip_tac >> gvs[])
      >> gvs[FEVERY_DEF]
    )
    >> Cases_on ‘xp’
    >> simp[]
    >> irule static_scope_mono
    >> gvs[Once valid_val_cases]
    >> qpat_assum ‘static_scope _ _’ $ irule_at (Pos last)
    >> simp[Ntimes INSERT_SING_UNION 2]
    >> simp[SUBSET_DEF]
  )
  >> reduce_to_cps 0 []
  >> simp[GSYM eval_eq_def]
  >> irule_at (Pos hd) eval_eq_trivial
  >> simp[Once cps_rel_cases]
  >> first_assum $ irule_at $ Pos hd
QED

Theorem step_preservation:
  ∀ sst sst' env env' e e' ks ks' (st : 'ffi state) mlenv k kv mle .
    step (sst, ks, e) = (sst', ks', e') ∧
    valid_state sst ks e ∧
    cont_rel st.refs ks kv ∧
    cps_rel st.refs e k mlenv kv mle ∧
    store_rel sst st.refs
    ⇒
    ∃ ck st' mlenv' k' kv' mle' .
      (∀ start . evaluate (st with clock := start + ck) mlenv [mle]
      =
      evaluate (st' with clock := start) mlenv' [mle']) ∧
      cont_rel st.refs ks' kv' ∧
      cps_rel st.refs e' k' mlenv' kv' mle' ∧
      store_rel sst' st'.refs ∧
      (¬ terminating_state (sst', ks', e') ⇒ 0 < ck) ∧
      st.ffi = st'.ffi
Proof
  Cases_on ‘e’
  >> simp[terminating_state_def]
  >~ [‘Exception s’] >- (
    simp[step_def, Once cps_rel_cases]
    >> rpt strip_tac
    >> simp[GSYM eval_eq_def]
    >> irule_at (Pos hd) eval_eq_trivial
    >> simp[Once cps_rel_cases, Once cont_rel_cases]
    >> irule_at (Pos hd) basis_scheme_env
  )
  >~ [‘Exp env e’] >- (
    Cases_on ‘e’
    >> simp[step_def, Once cps_rel_cases]
    >~ [‘Letrec bs e’] >- (
      cheat
      (*
      Cases_on ‘bs’
      >> rpt strip_tac
      >> gvs[cps_transform_def] >- (
        qrefine ‘ck+1’
        >> simp[SimpLHS, Ntimes evaluate_def 4, do_opapp_def,
          nsOptBind_def, dec_clock_def, letpreinit_ml_def, letinit_ml_def]
        >> simp[GSYM eval_eq_def]
        >> irule_at (Pos hd) eval_eq_trivial
        >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
        >> simp[Once e_ce_rel_cases]
        >> gvs[scheme_env_def, env_rel_cases]
      )
      >> PairCases_on ‘h’
      >> simp[cps_transform_def]
      >> rpt (pairarg_tac >> gvs[])
      >> qrefine ‘ck+1’
      >> simp[SimpLHS, Ntimes evaluate_def 4, do_opapp_def,
        nsOptBind_def, dec_clock_def]
      >> qpat_x_assum ‘letrec_preinit _ _ _ = _’ $ assume_tac o GSYM
      >> drule preservation_of_letrec
      >> ‘env_rel env (mlenv with v := nsBind "k" kv mlenv.v)’
        by gvs[env_rel_cases]
      >> strip_tac
      >> pop_assum $ drule_then drule
      >> ‘scheme_env (mlenv with v := nsBind "k" kv mlenv.v)’
        by gvs[scheme_env_def]
      >> strip_tac
      >> pop_assum $ drule
      >> strip_tac
      >> pop_assum $ qspec_then
        ‘Let (SOME "k'")
           (Fun "t0"
              (cps_transform_letinit [(h0,Var (Short "t0"))] t e
                 (Var (Short "k"))))
           (App Opapp [cps_transform h1; Var (Short "k'")])’ mp_tac
      >> rpt strip_tac
      >> gvs[GSYM eval_eq_def]
      >> irule_at (Pos hd) eval_eq_trans
      >> first_assum $ irule_at (Pos hd)
      >> simp[eval_eq_def]
      >> simp[Ntimes evaluate_def 2, nsOptBind_def]
      >> simp[GSYM eval_eq_def]
      >> irule_at (Pos hd) eval_eq_trivial
      >> simp[Once cont_rel_cases]
      >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pat ‘cont_rel _ _’)
      >> simp[cps_app_ts_def]
      >> simp[Once e_ce_rel_cases]
      >> gvs[scheme_env_def, env_rel_cases]
      *)
    )
    >~ [‘Letrecstar bs e’] >- (
      cheat
      (*
      simp[Once cps_transform_def]
      >> rpt strip_tac
      >> rpt (pairarg_tac >> gvs[])
      >> qrefine ‘ck+1’
      >> simp[Ntimes evaluate_def 4, do_opapp_def, dec_clock_def]
      >> pop_assum $ assume_tac o GSYM
      >> drule preservation_of_letrec
      >> ‘env_rel env (mlenv with v := nsBind "k" kv mlenv.v)’
        by gvs[env_rel_cases]
      >> strip_tac
      >> pop_assum $ drule_then drule
      >> ‘scheme_env (mlenv with v := nsBind "k" kv mlenv.v)’
        by gvs[scheme_env_def]
      >> strip_tac
      >> pop_assum $ drule
      >> strip_tac
      >> pop_assum $ qspec_then
        ‘App Opapp
          [cps_transform (Begin (MAP (UNCURRY Set) bs) e);
           Var (Short "k")]’ mp_tac
      >> rpt strip_tac
      >> gvs[GSYM eval_eq_def]
      >> first_assum $ irule_at (Pos hd)
      >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
      >> simp[Once e_ce_rel_cases]
      *)
    )
    >~ [‘Begin es e’] >>> HEADGOAL $ Cases_on ‘es’
    >> simp[cps_transform_def]
    >~ [‘Lit l’] >>> HEADGOAL (
      Cases_on ‘l’
      >~ [`LitBool b`] >>> HEADGOAL $ Cases_on ‘b’ (*for Bool cases*)
      >~ [`LitPrim p`] >>> HEADGOAL $ Cases_on `p`
      >> simp[lit_to_val_def, lit_to_ml_val_def]
    )
    >> rpt strip_tac
    >~ [‘Ident x’] >>> HEADGOAL (
      gvs[Once valid_state_cases]
      >> gvs[Once static_scope_def]
      >> gvs[Once $ GSYM SPECIFICATION]
      >> qpat_assum ‘env_rel _ _ _’ $ drule_then assume_tac
        o SRULE [env_rel_cases, FEVERY_DEF]
      >> qpat_assum ‘can_lookup _ _’ $ drule_then assume_tac
        o SRULE [can_lookup_cases, FEVERY_DEF]
      >> drule_all muts_rel_loc >> strip_tac
      >> gvs[store_entry_rel_cases]
    )
    >> reduce_to_cps 1 []
    >> simp[GSYM eval_eq_def]
    >> irule_at (Pos hd) eval_eq_trivial
    >> TRY $ qpat_assum ‘cont_rel _ _ _’ $ irule_at (Pos hd)
    >> simp[Once cps_rel_cases]
    >> simp[Once ml_v_vals_cases, Once cont_rel_cases]
    >> rpt scheme_env_tac
  )
  >~ [‘Val v’] >- (
    Cases_on ‘ks’
    >- (
      simp[step_def, return_def]
      >> rw[]
      >> simp[GSYM eval_eq_def]
      >> irule_at (Pos hd) eval_eq_trivial
      >> simp[]
      >> rpt $ first_assum $ irule_at Any
    )
    >> PairCases_on ‘h’
    >> Cases_on ‘∃ te fe . h1 = CondK te fe’ >- (
      gvs[]
      >> simp[step_def, return_def]
      >> simp[Once cps_rel_cases, Once cont_rel_cases]
      >> simp[Once ml_v_vals_cases]
      >> rpt strip_tac
      >> gvs[]
      >> simp[Once evaluate_def]
      >> reduce_to_cps 1 []
      >> simp[GSYM eval_eq_def]
      >> irule_at (Pos hd) eval_eq_trivial
      >> qpat_assum ‘cont_rel _ _ _’ $ irule_at (Pos hd)
      >> simp[Once cps_rel_cases]
      >> scheme_env_tac
    )
    >> Cases_on ‘∃ es e . h1 = BeginK es e’ >- (
      gvs[]
      >> Cases_on ‘es’
      >> rpt strip_tac
      >> gvs[Once cont_rel_cases, Once cps_rel_cases]
      >> gvs[cps_transform_def, step_def, return_def]
      >> simp[Once evaluate_def]
      >> reduce_to_cps 1 []
      >> simp[GSYM eval_eq_def]
      >> irule_at (Pos hd) eval_eq_trivial
      >> simp[Once cps_rel_cases]
      >> simp[Once cont_rel_cases]
      >> rpt scheme_env_tac
    )
    >> Cases_on ‘∃ x . h1 = SetK x’ >- (
      gvs[]
      >> simp[step_def, return_def, Once cps_rel_cases, refunc_set_def,
        Once cont_rel_cases, cps_transform_def, cps_app_ts_def]
      >> rpt strip_tac
      >> gvs[Once valid_state_cases, Once valid_cont_cases]
      >> qpat_assum ‘env_rel _ _ _’ $ drule_then assume_tac
        o SRULE [env_rel_cases, FEVERY_DEF, SPECIFICATION]
      >> qpat_assum ‘can_lookup _ _’ $ drule_then assume_tac
        o SRULE [can_lookup_cases, FEVERY_DEF, SPECIFICATION]
      >> drule_all muts_rel_loc >> strip_tac
      >> gvs[store_entry_rel_cases]
      >> simp[Once evaluate_def]
      >> reduce_to_cps 1 []
      >> simp[GSYM eval_eq_def]
      >> irule_at (Pos hd) eval_eq_trivial
      >> simp[]
      >> qpat_assum ‘cont_rel _ _ _’ $ irule_at (Pos hd)
      >> simp[Once cps_rel_cases, Once ml_v_vals_cases]
      >> (strip_tac >- (
        irule muts_rel_LUPDATE_same
        >> irule_at (Pos hd) muts_rel_mono
        >> qpat_assum `muts_rel _ _ _` $ irule_at Any
        >> rpt strip_tac
        >> gvs[store_entry_rel_cases, ml_v_vals_LUPDATE_same]
      )
      >> irule pairs_rel_LUPDATE_diff
      >> irule_at (Pos hd) pairs_rel_mono
      >> qpat_assum `pairs_rel _ _ _` $ irule_at Any
      >> rpt strip_tac
      >> simp[store_entry_rel_cases]
      >> irule_at Any EQ_REFL
      >> irule_at Any ml_v_vals_LUPDATE_same
      >> rpt $ first_assum $ irule_at $ Pos hd
      >> rpt strip_tac
      >> gvs[Once pair_rel_cases]
      >> simp[Once pair_rel_cases, ml_v_vals_LUPDATE_same])
    )
    >> Cases_on ‘∃ xvs x bs e . h1 = LetinitK xvs x bs e’ >- (
      gvs[]
      >> Cases_on ‘bs’
      >> rpt strip_tac
      >> gvs[Once cont_rel_cases, Once e_ce_rel_cases]
      >> gvs[cps_transform_def, step_def, return_def]
      >> qrefine ‘ck+1’
      >> simp[SimpLHS, Ntimes evaluate_def 4, do_opapp_def,
        nsOptBind_def, dec_clock_def] >- (
        gvs[Once valid_state_cases]
        >> qpat_x_assum ‘valid_cont _ _’ $ mp_tac
          o SRULE [Once valid_val_cases]
        >> strip_tac
        >> ‘∃ xvs' . (x,v)::xvs = xvs'’ by simp[]
        >> first_assum $ simp_tac bool_ss o single
        >> ‘x::(MAP FST xvs) = MAP FST xvs'’ by gvs[]
        >> simp_tac bool_ss [Once $ cj 3 $ GSYM ZIP_def]
        >> first_assum $ simp_tac bool_ss o single
        >> ‘Var (Short t')::MAP (Var o Short) ts = MAP (Var o Short) (t'::ts)’ by gvs[]
        >> first_assum $ simp_tac bool_ss o single
        >> irule preservation_of_letinit
        >> drule cps_app_ts_distinct
        >> strip_tac
        >> gvs[]
        >> last_assum $ irule_at (Pos last)
        >> irule_at (Pos $ el 5) EQ_REFL
        >> irule_at Any EQ_REFL
        >> simp[]
        >> irule_at (Pos last) EVERY2_MEM_MONO
        >> qpat_assum ‘LIST_REL _ ts mlvs’ $ irule_at (Pat ‘LIST_REL _ ts mlvs’)
        >> strip_tac >- (
          PairCases
          >> simp[]
          >> rpt strip_tac
          >> qpat_assum ‘LIST_REL _ ts mlvs’ $ assume_tac
          >> dxrule_then assume_tac EVERY2_LENGTH
          >> drule_at_then (Pos $ el 2) assume_tac $ cj 1 MEM_ZIP_MEM_MAP
          >> gvs[]
          >> Cases_on ‘x'0 = t'’
          >> gvs[]
        )
        >> gvs[scheme_env_def, env_rel_cases]
      )
      >> PairCases_on ‘h’
      >> gvs[]
      >> simp[cps_transform_def]
      >> simp[Ntimes evaluate_def 2, nsOptBind_def]
      >> simp[GSYM eval_eq_def]
      >> irule_at (Pos hd) eval_eq_trivial
      >> simp[Once e_ce_rel_cases, Once cont_rel_cases]
      >> simp_tac bool_ss [Once $ GSYM ZIP_def]
      >> ‘Var (Short t'')::MAP (Var o Short) ts = MAP (Var o Short) (t''::ts)’ by gvs[]
      >> first_assum $ simp_tac bool_ss o single
      >> irule_at (Pos hd) EQ_REFL
      >> simp[cps_app_ts_def]
      >> rpt (pairarg_tac >> gvs[])
      >> qpat_assum ‘LIST_REL _ ts mlvs’ $ assume_tac
      >> dxrule_then assume_tac EVERY2_LENGTH
      >> qpat_assum ‘LIST_REL ml_v_vals _ mlvs’ $ assume_tac
      >> dxrule_then assume_tac EVERY2_LENGTH
      >> gvs[]
      >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
      >> qpat_assum ‘LIST_REL ml_v_vals _ _’ $ irule_at (Pos $ el 2)
      >> drule $ GSYM cps_app_ts_distinct
      >> strip_tac
      >> simp[]
      >> irule_at (Pos hd) EVERY2_MEM_MONO
      >> qpat_assum ‘LIST_REL _ ts mlvs’ $ irule_at (Pat ‘LIST_REL _ ts mlvs’)
      >> strip_tac >- (
        PairCases
        >> simp[]
        >> rpt strip_tac
        >> drule_at_then (Pos $ el 2) assume_tac $ cj 1 MEM_ZIP_MEM_MAP
        >> gvs[]
        >> Cases_on ‘x'0 = t''’
        >> gvs[]
      )
      >> gvs[scheme_env_def, env_rel_cases]
    )
    >> Cases_on ‘∃ e es . h1 = ApplyK NONE (e::es)’ >- (
      gvs[]
      >> simp[step_def, return_def, Once cps_rel_cases,
        Once cont_rel_cases, cps_transform_def, cps_app_ts_def]
      >> rpt strip_tac
      >> simp[evaluate_def]
      >> reduce_to_cps 1 []
      >> simp[GSYM eval_eq_def]
      >> irule_at (Pos hd) eval_eq_trivial
      >> simp[Once cps_rel_cases, Once cont_rel_cases]
      >> simp[cps_app_ts_def]
      >> rpt scheme_env_tac
    )
    >> Cases_on ‘∃ fn vs e es . h1 = ApplyK (SOME (fn, vs)) (e::es)’ >- (
      gvs[]
      >> simp[step_def, return_def, Once cps_rel_cases,
        Once cont_rel_cases, cps_transform_def, cps_app_ts_def]
      >> rpt strip_tac
      >> simp[evaluate_def]
      >> reduce_to_cps 1 []
      >> simp[GSYM eval_eq_def]
      >> irule_at (Pos hd) eval_eq_trivial
      >> simp[Once cps_rel_cases, Once cont_rel_cases]
      >> simp[PULL_EXISTS]
      >> irule_at (Pos hd) EQ_REFL
      >> qpat_assum ‘cont_rel _ _ _’ $ irule_at (Pos hd)
      >> simp[cps_app_ts_def]
      >> rpt (pairarg_tac >> gvs[])
      >> qpat_assum ‘ml_v_vals _ _ _’ $ irule_at Any
      >> qpat_assum ‘LIST_REL (ml_v_vals _) _ _’ $ irule_at Any
      >> drule $ GSYM cps_app_ts_distinct
      >> strip_tac
      >> simp[]
      >> irule_at (Pos hd) EVERY2_MEM_MONO
      >> qpat_assum ‘LIST_REL _ ts _’ $ irule_at Any
      >> qpat_x_assum ‘LIST_REL _ ts _’ $ assume_tac
      >> drule_then assume_tac EVERY2_LENGTH
      >> strip_tac >- (
        PairCases >> simp[]
        >> strip_tac
        >> drule_at_then (Pos last) assume_tac MEM_ZIP_MEM_MAP
        >> gvs[]
        >> qsuff_tac ‘x0 ≠ t'’
        >> strip_tac
        >> gvs[]
      )
      >> rpt scheme_env_tac
    )
    >> Cases_on ‘h1 = ApplyK NONE []’ >- (
      gvs[]
      >> simp[step_def, return_def, Once cps_rel_cases, Once cont_rel_cases]
      >> simp[Once ml_v_vals_cases]
      >> rpt strip_tac
      >> gvs[]
      >> simp[Once evaluate_def]
      >> reduce_to_cps 1 []
      >> cheat

      >> gvs[application_def, sadd_def, smul_def, sminus_def,
        seqv_def, cps_transform_def, cons_list_def]
      >> qrefine ‘ck+2’
      >> simp[SimpLHS, evaluate_def, do_con_check_def,
        build_conv_def, do_opapp_def, dec_clock_def]
      >> qpat_assum ‘scheme_env env''’ $ simp o single
        o SRULE [scheme_env_def]
      >> simp[Ntimes find_recfun_def 2, Ntimes build_rec_env_def 2]
      >> qrefine ‘ck+1’
      >> simp[Ntimes evaluate_def 3, dec_clock_def]
      >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
        same_type_def, same_ctor_def, evaluate_match_def,
        pat_bindings_def]
      >~ [‘Litv (IntLit i)’] >- (
        qrefine ‘ck+1’
        >> simp[Once evaluate_def]
        >> simp[GSYM eval_eq_def]
        >> irule_at (Pos hd) eval_eq_trivial
        >> simp[Once cps_rel_cases]
        >> last_assum $ irule_at (Pos hd)
        >> simp[env_rel_cases, FEVERY_FEMPTY]
      )
      >~ [‘SOME (Conv (SOME (TypeStamp "SBool" _)) [
        Conv (Some (TypeStamp "True" _)) []
      ])’] >- (
        qrefine ‘ck+1’
        >> simp[Once evaluate_def]
        >> simp[GSYM eval_eq_def]
        >> irule_at (Pos hd) eval_eq_trivial
        >> simp[Once cps_rel_cases]
        >> last_assum $ irule_at (Pos hd)
        >> simp[env_rel_cases, FEVERY_FEMPTY]
      )
      >~ [‘SOME (Conv (SOME (TypeStamp "SBool" _)) [
        Conv (Some (TypeStamp "False" _)) []
      ])’] >- (
        qrefine ‘ck+1’
        >> simp[Once evaluate_def]
        >> simp[GSYM eval_eq_def]
        >> irule_at (Pos hd) eval_eq_trivial
        >> simp[Once cps_rel_cases]
        >> last_assum $ irule_at (Pos hd)
        >> simp[env_rel_cases, FEVERY_FEMPTY]
      )
      >~ [‘SOME (Conv (SOME (TypeStamp "SList" _)) [_])’] >- (
        qrefine ‘ck+1’
        >> simp[Once evaluate_def]
        >> simp[GSYM eval_eq_def]
        >> irule_at (Pos hd) eval_eq_trivial
        >> simp[Once cps_rel_cases]
        >> last_assum $ irule_at (Pos hd)
        >> simp[env_rel_cases, FEVERY_FEMPTY]
      )
      >~ [‘SOME (Conv (SOME (TypeStamp "Wrong" _)) [_])’] >- (
        qrefine ‘ck+1’
        >> simp[Once evaluate_def]
        >> simp[GSYM eval_eq_def]
        >> irule_at (Pos hd) eval_eq_trivial
        >> simp[Once cps_rel_cases]
        >> last_assum $ irule_at (Pos hd)
        >> simp[env_rel_cases, FEVERY_FEMPTY]
      )
      >> qrefine ‘ck+2’
      >> simp[evaluate_def]
      >> simp[do_opapp_def,
      Once find_recfun_def, Once build_rec_env_def]
      >> simp[Ntimes evaluate_def 4, dec_clock_def]
      >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
        same_type_def, same_ctor_def, evaluate_match_def,
        pat_bindings_def]
      >~ [‘"SAdd"’] >- (
        qrefine ‘ck+1’
        >> simp[Ntimes evaluate_def 3, nsOptBind_def,
          do_con_check_def, build_conv_def]
        >> simp[GSYM eval_eq_def]
        >> irule_at (Pos hd) eval_eq_trivial
        >> last_assum $ irule_at (Pos hd)
        >> simp[Once cps_rel_cases, Once ml_v_vals_cases]
        >> simp[env_rel_cases, FEVERY_FEMPTY]
      )
      >~ [‘"SMul"’] >- (
        qrefine ‘ck+1’
        >> simp[Ntimes evaluate_def 3, nsOptBind_def,
          do_con_check_def, build_conv_def]
        >> simp[GSYM eval_eq_def]
        >> irule_at (Pos hd) eval_eq_trivial
        >> last_assum $ irule_at (Pos hd)
        >> simp[Once cps_rel_cases, Once ml_v_vals_cases]
        >> simp[env_rel_cases, FEVERY_FEMPTY]
      )
      >~ [‘Proc _ _ _ _’] >- (
        rpt (pairarg_tac >> gvs[])
        >> irule preservation_of_proc
        >> simp[]
        >> qpat_assum ‘scheme_env env'³'’ $ simp
          o curry ((::) o swap) [scheme_env_def]
          o SRULE [scheme_env_def]
        >> first_assum $ irule_at Any o GSYM
        >> simp[vcons_list_def]
        >> last_x_assum $ mp_tac o SRULE [Once valid_state_cases]
        >> strip_tac
        >> simp[]
        >> qpat_x_assum ‘valid_cont _ _’ $ mp_tac o SRULE [Once valid_val_cases]
        >> strip_tac
        >> simp[]
        >> qpat_x_assum ‘valid_val _ (Proc _ _ _ _)’ $ mp_tac o SRULE [Once valid_val_cases]
        >> strip_tac
        >> gvs[env_rel_cases]
      )
      >> simp[GSYM eval_eq_def]
      >> irule_at (Pos hd) eval_eq_trivial
      >> simp[Once cps_rel_cases]
      >> simp[env_rel_cases, FEVERY_FEMPTY]
      >> last_assum $ irule_at Any
    )
    >> Cases_on ‘∃ fn vs . h1 = ApplyK (SOME (fn, vs)) []’ >- (
      gvs[]
      >> simp[step_def, return_def, Once cps_rel_cases]
      >> rpt strip_tac
      >> gvs[Once cont_rel_cases, Excl "MAP"]
      >> simp[Once evaluate_def]
      >> reduce_to_cps 1 [Excl "MAP"]
      >> gvs[cps_transform_def, Excl "MAP"]
      >> simp_tac std_ss [Once $ GSYM MAP_REVERSE]

      gvs[]
      >> simp[step_def, return_def, Once e_ce_rel_cases,
        Once cont_rel_cases]
      >> rpt strip_tac
      >> gvs[cps_transform_def, cons_list_def]
      >> qrefine ‘ck+1’
      >> simp[evaluate_def, do_con_check_def,
        build_conv_def, do_opapp_def, dec_clock_def]
      >> drule $ cps_app_ts_distinct
      >> strip_tac
      >> ‘scheme_env (env'' with v:= nsBind t' mlv env''.v)’ by gvs[scheme_env_def]
      >> qsuff_tac ‘LIST_REL (λx v'. nsLookup (env'' with v:= nsBind t' mlv
      env''.v).v (Short x) = SOME v') (REVERSE (t'::ts)) (REVERSE (mlv::mlvs))’ >- (
        strip_tac
        >> drule_all_then assume_tac cons_list_val
        >> gvs[Once ml_v_vals_cases]
        >> gvs[application_def]
        >> qpat_assum ‘scheme_env env''’ $ simp o single o SRULE [scheme_env_def]
        >> simp[Ntimes find_recfun_def 2, Ntimes build_rec_env_def 2]
        >~ [‘Prim SAdd’] >- (
          qrefine ‘ck+3’
          >> simp[Ntimes evaluate_def 3]
          >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
            same_type_def, same_ctor_def, evaluate_match_def,
            pat_bindings_def]
          >> simp[Ntimes find_recfun_def 2, Ntimes build_rec_env_def 2]
          >> simp[Ntimes evaluate_def 3]
          >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
            same_type_def, same_ctor_def, evaluate_match_def,
            pat_bindings_def]
          >> simp[Ntimes evaluate_def 7, do_opapp_def]
          >> simp[Ntimes find_recfun_def 2, Ntimes build_rec_env_def 2]
          >> qrefine ‘ck+2’
          >> simp[Ntimes evaluate_def 2, dec_clock_def]
          >> irule preservation_of_sadd_body
          >> simp[]
          >> irule_at (Pos hd) EQ_REFL
          >> irule $ cj 1 $ iffLR LIST_REL_APPEND
          >> simp[]
        )
        >~ [‘Prim SMul’] >- (
          qrefine ‘ck+3’
          >> simp[Ntimes evaluate_def 3]
          >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
            same_type_def, same_ctor_def, evaluate_match_def,
            pat_bindings_def]
          >> simp[Ntimes find_recfun_def 2, Ntimes build_rec_env_def 2]
          >> simp[Ntimes evaluate_def 3]
          >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
            same_type_def, same_ctor_def, evaluate_match_def,
            pat_bindings_def]
          >> simp[Ntimes evaluate_def 7, do_opapp_def]
          >> simp[Ntimes find_recfun_def 2, Ntimes build_rec_env_def 2]
          >> qrefine ‘ck+2’
          >> simp[Ntimes evaluate_def 2, dec_clock_def]
          >> irule preservation_of_smul_body
          >> simp[]
          >> simp[scheme_env2_def]
          >> irule_at (Pos hd) EQ_REFL
          >> irule $ cj 1 $ iffLR LIST_REL_APPEND
          >> simp[]
        )
        >~ [‘Prim SMinus’] >- (
          qrefine ‘ck+4’
          >> simp[Ntimes evaluate_def 3]
          >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
            same_type_def, same_ctor_def, evaluate_match_def,
            pat_bindings_def]
          >> simp[Ntimes evaluate_def 5, do_opapp_def, dec_clock_def]
          >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
            same_type_def, same_ctor_def, evaluate_match_def,
            pat_bindings_def]
          >> irule preservation_of_sminus_body
          >> simp[]
          >> simp[scheme_env3_def, scheme_env2_def]
          >> irule_at (Pos hd) EQ_REFL
          >> irule $ cj 1 $ iffLR LIST_REL_APPEND
          >> simp[]
        )
        >~ [‘Proc _ _ _ _’] >- (
          qrefine ‘ck+3’
          >> simp[Ntimes evaluate_def 3]
          >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
            same_type_def, same_ctor_def, evaluate_match_def,
            pat_bindings_def]
          >> qrefine ‘ck+1’
          >> simp[Ntimes evaluate_def 5, do_opapp_def, dec_clock_def]
          >> rpt (pairarg_tac >> gvs[])
          >> irule preservation_of_proc
          >> simp[]
          >> qpat_assum ‘scheme_env env'³'’ $ simp
            o curry ((::) o swap) [scheme_env_def]
            o SRULE [scheme_env_def]
          >> first_assum $ irule_at Any o GSYM
          >> rpt $ irule_at Any EQ_REFL
          >> simp[]
          >> last_x_assum $ mp_tac o SRULE [Once valid_state_cases]
          >> strip_tac
          >> simp[]
          >> qpat_x_assum ‘valid_cont _ _’ $ mp_tac o SRULE [Once valid_val_cases]
          >> strip_tac
          >> simp[]
          >> qpat_x_assum ‘valid_val _ (Proc _ _ _ _)’ $ mp_tac o SRULE [Once valid_val_cases]
          >> strip_tac
          >> gvs[env_rel_cases]
        )
        >~ [‘Prim SEqv’] >- (
          qrefine ‘ck+4’
          >> simp[Ntimes evaluate_def 3]
          >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
            same_type_def, same_ctor_def, evaluate_match_def,
            pat_bindings_def]
          >> simp[Ntimes evaluate_def 5, do_opapp_def, dec_clock_def]
          >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
            same_type_def, same_ctor_def, evaluate_match_def,
            pat_bindings_def]
          >> Cases_on ‘vs’ using SNOC_CASES
          >> gvs[vcons_list_def, seqv_def] >- (
            simp[Ntimes evaluate_def 8]
            >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
              same_type_def, same_ctor_def, evaluate_match_def,
              pat_bindings_def]
            >> simp[GSYM eval_eq_def]
            >> irule_at (Pos hd) eval_eq_trivial
            >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
            >> simp[Once e_ce_rel_cases, env_rel_cases, FEVERY_FEMPTY]
          )
          >> Cases_on ‘mlvs’ using SNOC_CASES
          >> gvs[vcons_list_def, LIST_REL_SNOC, REVERSE_SNOC]
          >> simp[Ntimes evaluate_def 5]
          >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
            same_type_def, same_ctor_def, evaluate_match_def,
            pat_bindings_def]
          >> Cases_on ‘l’ using SNOC_CASES
          >> gvs[vcons_list_def, seqv_def] >- (
            simp[Ntimes evaluate_def 8]
            >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
              same_type_def, same_ctor_def, evaluate_match_def,
              pat_bindings_def]
            >> Cases_on ‘∃ n . x = SNum n’ >- (
              gvs[Once ml_v_vals_cases]
              >> simp[Ntimes evaluate_def 8]
              >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
                same_type_def, same_ctor_def, evaluate_match_def,
                pat_bindings_def, do_con_check_def, build_conv_def]
              >> Cases_on ‘∃ m . v = SNum m’ >- (
                gvs[Once ml_v_vals_cases]
                >> simp[Ntimes evaluate_def 11, nsOptBind_def, do_app_def]
                >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
                  same_type_def, same_ctor_def, evaluate_match_def,
                  pat_bindings_def, do_con_check_def, build_conv_def,
                  do_eq_def, lit_same_type_def]
                >> simp[GSYM eval_eq_def]
                >> irule_at (Pos hd) eval_eq_trivial
                >> simp[env_rel_cases, FEVERY_FEMPTY]
                >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
                >> Cases_on ‘i=i'’
                >> simp[Once e_ce_rel_cases, Once ml_v_vals_cases,
                  Boolv_def, bool_type_num_def]
              )
              >> Cases_on ‘v’
              >> gvs[Once ml_v_vals_cases]
              >> simp[Ntimes evaluate_def 8, nsOptBind_def]
              >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
                same_type_def, same_ctor_def, evaluate_match_def,
                pat_bindings_def, do_con_check_def, build_conv_def]
              >> simp[GSYM eval_eq_def]
              >> irule_at (Pos hd) eval_eq_trivial
              >> simp[env_rel_cases, FEVERY_FEMPTY]
              >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
              >> simp[Once e_ce_rel_cases, Once ml_v_vals_cases,
                Boolv_def, bool_type_num_def]
            )
            >> Cases_on ‘∃ b . x = SBool b’ >- (
              gvs[Once ml_v_vals_cases]
              >> simp[Ntimes evaluate_def 8]
              >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
                same_type_def, same_ctor_def, evaluate_match_def,
                pat_bindings_def, do_con_check_def, build_conv_def]
              >> (Cases_on ‘∃ b' . v = SBool b'’ >- (
                gvs[Once ml_v_vals_cases]
                >> simp[Ntimes evaluate_def 11, nsOptBind_def, do_app_def]
                >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
                  same_type_def, same_ctor_def, evaluate_match_def,
                  pat_bindings_def, do_con_check_def, build_conv_def,
                  do_eq_def, lit_same_type_def, ctor_same_type_def]
                >> simp[GSYM eval_eq_def]
                >> irule_at (Pos hd) eval_eq_trivial
                >> simp[env_rel_cases, FEVERY_FEMPTY]
                >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
                >> simp[Once e_ce_rel_cases, Once ml_v_vals_cases,
                  Boolv_def, bool_type_num_def]
              ))
              >> Cases_on ‘v’ >> gvs[]
              >> gvs[Once ml_v_vals_cases]
              >> simp[Ntimes evaluate_def 8, nsOptBind_def]
              >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
                same_type_def, same_ctor_def, evaluate_match_def,
                pat_bindings_def, do_con_check_def, build_conv_def]
              >> simp[GSYM eval_eq_def]
              >> irule_at (Pos hd) eval_eq_trivial
              >> simp[env_rel_cases, FEVERY_FEMPTY]
              >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
              >> simp[Once e_ce_rel_cases, Once ml_v_vals_cases,
                Boolv_def, bool_type_num_def]
            )
            >> Cases_on ‘x’ >> gvs[]
            >> gvs[Once ml_v_vals_cases]
            >> simp[Ntimes evaluate_def 9, nsOptBind_def]
            >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
              same_type_def, same_ctor_def, evaluate_match_def,
              pat_bindings_def, do_con_check_def, build_conv_def]
            >> simp[GSYM eval_eq_def]
            >> irule_at (Pos hd) eval_eq_trivial
            >> simp[env_rel_cases, FEVERY_FEMPTY]
            >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
            >> simp[Once e_ce_rel_cases, Once ml_v_vals_cases]
          )
          >> Cases_on ‘l'’ using SNOC_CASES
          >> gvs[vcons_list_def, LIST_REL_SNOC, REVERSE_SNOC]
          >> Cases_on ‘l''’ using SNOC_CASES
          >> Cases_on ‘l’ using SNOC_CASES
          >> gvs[vcons_list_def, seqv_def, LIST_REL_SNOC, REVERSE_SNOC]
          >> simp[Ntimes evaluate_def 8]
          >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
            same_type_def, same_ctor_def, evaluate_match_def,
            pat_bindings_def]
          >> simp[GSYM eval_eq_def]
          >> irule_at (Pos hd) eval_eq_trivial
          >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
          >> simp[Once e_ce_rel_cases, env_rel_cases, FEVERY_FEMPTY]
        )
        >~ [‘Prim CallCC’] >- (
          qrefine ‘ck+4’
          >> simp[Ntimes evaluate_def 5]
          >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
            same_type_def, same_ctor_def, evaluate_match_def,
            pat_bindings_def]
          >> simp[Ntimes find_recfun_def 2, Ntimes build_rec_env_def 2]
          >> simp[Ntimes evaluate_def 4, do_opapp_def]
          >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
            same_type_def, same_ctor_def, evaluate_match_def,
            pat_bindings_def]
          >> simp[Ntimes find_recfun_def 2, Ntimes build_rec_env_def 2]
          >> simp[Ntimes evaluate_def 1, do_opapp_def, dec_clock_def]
          >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
            same_type_def, same_ctor_def, evaluate_match_def,
            pat_bindings_def]
          >> simp[Ntimes find_recfun_def 2, Ntimes build_rec_env_def 2]
          >> Cases_on ‘vs’ using SNOC_CASES
          >> gvs[vcons_list_def] >- (
            simp[Ntimes evaluate_def 8]
            >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
              same_type_def, same_ctor_def, evaluate_match_def,
              pat_bindings_def]
            >> simp[Ntimes evaluate_def 5, do_con_check_def, build_conv_def,
              nsOptBind_def]
            >> simp[GSYM eval_eq_def]
            >> irule_at (Pos hd) eval_eq_trivial
            >> simp[env_rel_cases, FEVERY_FEMPTY]
            >> simp[Once cont_rel_cases]
            >> gvs[cps_transform_def, cps_app_ts_def]
            >> irule_at (Pos hd) EQ_REFL
            >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
            >> qpat_assum ‘ml_v_vals _ _’ $ irule_at Any
            >> simp[Once e_ce_rel_cases]
            >> simp[Once ml_v_vals_cases]
            >> simp[cons_list_def]
            >> simp[scheme_env_def, env_rel_cases, FEVERY_FEMPTY]
          )
          >> Cases_on ‘mlvs’ using SNOC_CASES
          >> gvs[vcons_list_def, LIST_REL_SNOC, REVERSE_SNOC]
          >> Cases_on ‘l’ using SNOC_CASES
          >> Cases_on ‘l'’ using SNOC_CASES
          >> gvs[vcons_list_def, LIST_REL_SNOC, REVERSE_SNOC]
          >> simp[Ntimes evaluate_def 8]
          >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
            same_type_def, same_ctor_def, evaluate_match_def,
            pat_bindings_def]
          >> simp[GSYM eval_eq_def]
          >> irule_at (Pos hd) eval_eq_trivial
          >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
          >> simp[Once e_ce_rel_cases, env_rel_cases, FEVERY_FEMPTY]
        )
        >~ [‘Throw _’] >- (
          qrefine ‘ck+4’
          >> simp[Ntimes evaluate_def 5]
          >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
            same_type_def, same_ctor_def, evaluate_match_def,
            pat_bindings_def]
          >> simp[Ntimes find_recfun_def 2, Ntimes build_rec_env_def 2]
          >> simp[Ntimes evaluate_def 5, do_opapp_def, dec_clock_def]
          >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
            same_type_def, same_ctor_def, evaluate_match_def,
            pat_bindings_def]
          >> simp[Ntimes find_recfun_def 2, Ntimes build_rec_env_def 2]
          >> Cases_on ‘vs’ using SNOC_CASES
          >> gvs[vcons_list_def] >- (
            simp[Ntimes evaluate_def 8]
            >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
              same_type_def, same_ctor_def, evaluate_match_def,
              pat_bindings_def]
            >> simp[GSYM eval_eq_def]
            >> irule_at (Pos hd) eval_eq_trivial
            >> simp[env_rel_cases, FEVERY_FEMPTY]
            >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
            >> simp[Once e_ce_rel_cases]
          )
          >> Cases_on ‘mlvs’ using SNOC_CASES
          >> gvs[vcons_list_def, LIST_REL_SNOC, REVERSE_SNOC]
          >> Cases_on ‘l’ using SNOC_CASES
          >> Cases_on ‘l'’ using SNOC_CASES
          >> gvs[vcons_list_def, LIST_REL_SNOC, REVERSE_SNOC]
          >> simp[Ntimes evaluate_def 8]
          >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
            same_type_def, same_ctor_def, evaluate_match_def,
            pat_bindings_def]
          >> simp[GSYM eval_eq_def]
          >> irule_at (Pos hd) eval_eq_trivial
          >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
          >> simp[Once e_ce_rel_cases, env_rel_cases, FEVERY_FEMPTY]
        )
        >> qrefine ‘ck+3’
        >> simp[Ntimes evaluate_def 5]
        >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
          same_type_def, same_ctor_def, evaluate_match_def,
          pat_bindings_def]
        >> simp[Once evaluate_def, do_opapp_def, dec_clock_def,
          do_con_check_def, build_conv_def]
        >> simp[GSYM eval_eq_def]
        >> irule_at (Pos hd) eval_eq_trivial
        >> simp[env_rel_cases, FEVERY_FEMPTY]
        >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
        >> simp[Once e_ce_rel_cases]
      )
      >> simp[]
      >> irule_at (Pos hd) EVERY2_MEM_MONO
      >> qpat_assum ‘LIST_REL _ ts _’ $ irule_at Any
      >> qpat_x_assum ‘LIST_REL _ ts _’ $ assume_tac
      >> drule_then assume_tac EVERY2_LENGTH
      >> PairCases >> simp[]
      >> strip_tac
      >> drule_at_then (Pos last) assume_tac MEM_ZIP_MEM_MAP
      >> gvs[]
      >> qsuff_tac ‘x0 ≠ t'’
      >> strip_tac
      >> gvs[]
    )
    >> Cases_on ‘h1’ >> gvs[]
    >> Cases_on ‘l’ >> gvs[]
    >> Cases_on ‘o'’ >> gvs[]
    >> PairCases_on ‘x’ >> gvs[]
  )
QED

Theorem steps_preservation:
  ∀ n store store' env env' e e' k k' (st : 'ffi state) mlenv var kv mle .
  FUNPOW step n (store, k, env, e) = (store', k', env', e') ∧
  valid_state store k env e ∧
  cont_rel k kv ∧
  e_ce_rel e var mlenv kv mle ∧
  env_rel env mlenv ∧
  LIST_REL store_entry_rel store st.refs
  ⇒
  ∃ ck st' mlenv' var' kv' mle' .
    (∀ start . evaluate (st with clock := start + ck) mlenv [mle]
    =
    evaluate (st' with clock := start) mlenv' [mle']) ∧
    cont_rel k' kv' ∧
    e_ce_rel e' var' mlenv' kv' mle' ∧
    env_rel env' mlenv' ∧
    LIST_REL store_entry_rel store' st'.refs ∧
    (¬ terminating_state (store', k', env', e') ⇒ n ≤ ck) ∧
    st.ffi = st'.ffi
Proof
  Induct >- (
    simp[terminating_state_def]
    >> rpt strip_tac
    >> rpt $ pop_assum $ irule_at Any
    >> qexists ‘0’
    >> simp[]
  )
  >> simp[FUNPOW]
  >> rpt strip_tac
  >> drule valid_state_progress
  >> rpt strip_tac
  >> gvs[]
  >> last_x_assum $ drule_then assume_tac
  >> pop_assum $ drule_then assume_tac
  >> drule_all step_preservation
  >> rpt strip_tac
  >> qpat_x_assum ‘∀ _ _ _ _ _ . _ ⇒ _’ drule_all
  >> rpt strip_tac
  >> qexists ‘ck + ck'’
  >> gvs[SF SFY_ss]
  >> rpt $ first_assum $ irule_at Any
  >> simp[]
  >> strip_tac
  >> gvs[]
  >> drule_all_then assume_tac terminating_direction_n
  >> gvs[]
QED

Theorem value_terminating:
  ∀ n e v mle mlv store store' ks env (st:'ffi state) mlenv var kv .
    FUNPOW step n (store, ks, env, e) = (store', [], FEMPTY, Val v) ∧
    valid_state store ks env e ∧
    e_ce_rel e var mlenv kv mle ∧
    cont_rel ks kv ∧
    env_rel env mlenv ∧
    LIST_REL store_entry_rel store st.refs
    ⇒
    ∃ ck st' mlv . evaluate (st with clock:=ck) mlenv [mle]
      = (st', Rval [mlv]) ∧
    ml_v_vals v mlv ∧
    st.ffi = st'.ffi
Proof
  rpt strip_tac
  >> drule_all steps_preservation
  >> rpt strip_tac
  >> first_x_assum $ qspec_then ‘1’ $ assume_tac
  >> qexists ‘1 + ck’
  >> irule_at (Pos hd) EQ_TRANS
  >> pop_assum $ irule_at (Pos hd)
  >> qpat_x_assum ‘_ (Val v) _ _ _ _’ mp_tac
  >> simp[Once e_ce_rel_cases]
  >> rpt strip_tac
  >> gvs[]
  >> qpat_x_assum ‘cont_rel [] _’ mp_tac
  >> simp[Once cont_rel_cases]
  >> rpt strip_tac
  >> gvs[]
  >> simp[evaluate_def, do_opapp_def, dec_clock_def]
QED

Theorem evaluate_timeout_smaller_clock:
  ∀ ck ck' st' (st:'ffi state) env e .
    evaluate (st with clock := ck) env [e] = (st', Rerr (Rabort Rtimeout_error)) ∧
    ck' ≤ ck
    ⇒
    ∃ st'' . evaluate (st with clock := ck') env [e] = (st'', Rerr (Rabort Rtimeout_error))
Proof
  rpt strip_tac
  >> ‘∃ i . ck = ck' + i’ by (qexists ‘ck - ck'’ >> simp[])
  >> qpat_x_assum ‘_ ≤ _’ kall_tac
  >> gvs[]
  >> spose_not_then assume_tac
  >> Cases_on ‘evaluate (st with clock := ck') env [e]’
  >> gvs[]
  >> drule_all_then assume_tac evaluate_add_to_clock
  >> gvs[]
QED

Theorem cps_val:
  ∀ st env e . ∃ mle .
    evaluate st env [cps_transform e] = (st, Rval [Closure env "k" mle])
Proof
  Cases_on ‘e’
  >> simp[cps_transform_def, evaluate_def]
QED

Theorem diverges:
  ∀ e v mle mlv store store' ks env (st:'ffi state) mlenv var kv .
    (∀ n . ¬ terminating_state (FUNPOW step n (store, ks, env, e))) ∧
    valid_state store ks env e ∧
    e_ce_rel e var mlenv kv mle ∧
    cont_rel ks kv ∧
    env_rel env mlenv ∧
    LIST_REL store_entry_rel store st.refs
    ⇒
    ∀ ck . ∃ st' . evaluate (st with clock:=ck) mlenv [mle]
      = (st', Rerr (Rabort Rtimeout_error)) ∧
      st.ffi = st'.ffi
Proof
  rpt strip_tac
  >> last_x_assum $ qspec_then ‘ck’ assume_tac
  >> Cases_on ‘FUNPOW step ck (store,ks,env,e)’
  >> PairCases_on ‘r’
  >> drule_all steps_preservation
  >> rpt strip_tac
  >> gvs[]
  >> qpat_x_assum ‘∀ _._=_’ $ qspec_then ‘0’ assume_tac
  >> qpat_x_assum ‘e_ce_rel _ _ _ _ mle'’ $ assume_tac o SRULE [Once e_ce_rel_cases]
  >> gvs[terminating_state_def]
  >> qpat_x_assum ‘cont_rel _ kv'’ $ assume_tac o SRULE [Once cont_rel_cases]
  >> qspecl_then [‘st' with clock:=0’,‘mlenv'’,‘e'’] mp_tac cps_val
  >> strip_tac
  >> gvs[evaluate_def, do_opapp_def]
  >> drule_all evaluate_timeout_smaller_clock
  >> strip_tac
  >> simp[]
  >> rpt $ last_assum $ irule_at Any
  >> qpat_assum ‘st.ffi = _’ $ simp o single o GSYM o Once
  >> irule io_events_mono_antisym
  >> drule_then assume_tac $ cj 1 evaluate_io_events_mono_imp
  >> gvs[]
  >> rev_drule_then assume_tac (
    cj 4 $ SRULE [PULL_FORALL] $ cj 6 $
    SRULE [is_clock_io_mono_def, pair_CASE_eq_forall] $
      cj 1 is_clock_io_mono_evaluate
  )
  >> gvs[]
  >> pop_assum $ drule_then assume_tac
  >> gvs[]
QED

val _ = export_theory();
