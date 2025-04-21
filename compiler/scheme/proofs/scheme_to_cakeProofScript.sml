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

Theorem scheme_env1_def[allow_rebind, compute] = EVAL_RULE $ zDefine ‘
  scheme_env1 = case evaluate_decs
      (<|clock:=999;next_type_stamp:=0;next_exn_stamp:=0|> :num state)
      <|v:=nsEmpty;c:=nsEmpty|>
      (prim_types_program ++ [Dtype unknown_loc [(["'a"],"option",
            [("None",[]); ("Some",[Atvar "'a"])])]] ++ [scheme_basis1]) of
    | (st', Rval env) => env
    | _ => <|v:=nsEmpty;c:=nsEmpty|>
’;

Definition cconses_def[simp]:
  cconses = ["SNum"; "SBool"; "True"; "False";
    "Prim";"SAdd";"SMul";"SMinus";"SEqv";"CallCC";
    "[]"; "::"; "Some"; "None"; "Ex"; "Proc"; "Throw";"SList";"Wrong"]
End

Theorem scheme_env1_rw[simp] = SRULE [nsLookup_def] $ SIMP_CONV pure_ss [
  SimpRHS, scheme_env1_def,
  EVERY_DEF, cconses_def, MAP
] “
  EVERY (λ x . nsLookup scheme_env1.c x = nsLookup scheme_env1.c x) $
    MAP Short cconses
”;

Theorem scheme_env2_def[allow_rebind, compute] = SRULE [] $
  RESTR_EVAL_RULE [“scheme_env1”] $ zDefine ‘
    scheme_env2 = case evaluate_decs
        (<|clock:=999;next_type_stamp:=0;next_exn_stamp:=0|> :num state)
        scheme_env1
        [scheme_basis2] of
      | (st', Rval env) => <|c:=scheme_env1.c;v:=nsAppend env.v scheme_env1.v|>
      | _ => <|v:=nsEmpty;c:=nsEmpty|>
’;

Theorem scheme_env2_rw[simp] = SRULE [GSYM CONJ_ASSOC] $
CONJ (SRULE [Once scheme_env2_def] $ SCONV [] “
  EVERY (λ x . nsLookup scheme_env2.c x = nsLookup scheme_env1.c x) $
    MAP Short cconses
”) $ SRULE [GSYM scheme_env1_def] $ EVAL “nsLookup scheme_env2.v (Short "sadd")”;

Theorem scheme_env3_def[allow_rebind, compute] = SRULE [] $
  RESTR_EVAL_RULE [“scheme_env2”] $ zDefine ‘
    scheme_env3 = case evaluate_decs
        (<|clock:=999;next_type_stamp:=0;next_exn_stamp:=0|> :num state)
        scheme_env2
        [scheme_basis3] of
      | (st', Rval env) => <|c:=scheme_env2.c;v:=nsAppend env.v scheme_env2.v|>
      | _ => <|v:=nsEmpty;c:=nsEmpty|>
’;

Theorem scheme_env3_rw[simp] = SRULE [GSYM CONJ_ASSOC] $
CONJ (SRULE [Once scheme_env3_def] $ SCONV [] “
  EVERY (λ x . nsLookup scheme_env3.c x = nsLookup scheme_env1.c x) $
    MAP Short cconses
”) $ LIST_CONJ $ map
  (SRULE [
    GSYM $ EVAL “scheme_env1”,
    GSYM $ EVAL “scheme_env2”
  ] o EVAL) [
  “nsLookup scheme_env3.v (Short "sadd")”,
  “nsLookup scheme_env3.v (Short "smul")”
];

Theorem scheme_env4_def[allow_rebind, compute] = SRULE [] $
  RESTR_EVAL_RULE [“scheme_env3”] $ zDefine ‘
    scheme_env4 = case evaluate_decs
        (<|clock:=999;next_type_stamp:=0;next_exn_stamp:=0|> :num state)
        scheme_env3
        [scheme_basis4] of
      | (st', Rval env) => <|c:=scheme_env3.c;v:=nsAppend env.v scheme_env3.v|>
      | _ => <|v:=nsEmpty;c:=nsEmpty|>
’;

Theorem scheme_env4_rw[simp] = SRULE [GSYM CONJ_ASSOC] $
CONJ (SRULE [Once scheme_env4_def] $ SCONV [] “
  EVERY (λ x . nsLookup scheme_env4.c x = nsLookup scheme_env1.c x) $
    MAP Short cconses
”) $ LIST_CONJ $ map
  (SRULE [
    GSYM $ EVAL “scheme_env1”,
    GSYM $ EVAL “scheme_env2”,
    GSYM $ EVAL “scheme_env3”
  ] o EVAL) [
  “nsLookup scheme_env4.v (Short "sadd")”,
  “nsLookup scheme_env4.v (Short "smul")”,
  “nsLookup scheme_env4.v (Short "sminus")”
];

Theorem scheme_env5_def[allow_rebind, compute] = SRULE [] $
  RESTR_EVAL_RULE [“scheme_env4”] $ zDefine ‘
    scheme_env5 = case evaluate_decs
        (<|clock:=999;next_type_stamp:=0;next_exn_stamp:=0|> :num state)
        scheme_env4
        [scheme_basis5] of
      | (st', Rval env) => <|c:=scheme_env4.c;v:=nsAppend env.v scheme_env4.v|>
      | _ => <|v:=nsEmpty;c:=nsEmpty|>
’;

Theorem scheme_env5_rw[simp] = SRULE [GSYM CONJ_ASSOC] $
CONJ (SRULE [Once scheme_env5_def] $ SCONV [] “
  EVERY (λ x . nsLookup scheme_env5.c x = nsLookup scheme_env1.c x) $
    MAP Short cconses
”) $ LIST_CONJ $ map
  (SRULE [
    GSYM $ EVAL “scheme_env1”,
    GSYM $ EVAL “scheme_env2”,
    GSYM $ EVAL “scheme_env3”,
    GSYM $ EVAL “scheme_env4”
  ] o EVAL) [
  “nsLookup scheme_env5.v (Short "sadd")”,
  “nsLookup scheme_env5.v (Short "smul")”,
  “nsLookup scheme_env5.v (Short "sminus")”,
  “nsLookup scheme_env5.v (Short "seqv")”
];

Theorem scheme_env6_def[allow_rebind, compute] = SRULE [] $
  RESTR_EVAL_RULE [“scheme_env5”] $ zDefine ‘
    scheme_env6 = case evaluate_decs
        (<|clock:=999;next_type_stamp:=0;next_exn_stamp:=0|> :num state)
        scheme_env5
        [scheme_basis6] of
      | (st', Rval env) => <|c:=scheme_env5.c;v:=nsAppend env.v scheme_env5.v|>
      | _ => <|v:=nsEmpty;c:=nsEmpty|>
’;

Theorem scheme_env6_rw[simp] = SRULE [GSYM CONJ_ASSOC] $
CONJ (SRULE [Once scheme_env6_def] $ SCONV [] “
  EVERY (λ x . nsLookup scheme_env6.c x = nsLookup scheme_env1.c x) $
    MAP Short cconses
”) $ LIST_CONJ $ map
  (SRULE [
    GSYM $ EVAL “scheme_env1”,
    GSYM $ EVAL “scheme_env2”,
    GSYM $ EVAL “scheme_env3”,
    GSYM $ EVAL “scheme_env4”,
    GSYM $ EVAL “scheme_env5”
  ] o EVAL) [
  “nsLookup scheme_env6.v (Short "sadd")”,
  “nsLookup scheme_env6.v (Short "smul")”,
  “nsLookup scheme_env6.v (Short "sminus")”,
  “nsLookup scheme_env6.v (Short "seqv")”,
  “nsLookup scheme_env6.v (Short "throw")”
];

Theorem scheme_env7_def[allow_rebind, compute] = SRULE [] $
  RESTR_EVAL_RULE [“scheme_env6”] $ zDefine ‘
    scheme_env7 = case evaluate_decs
        (<|clock:=999;next_type_stamp:=0;next_exn_stamp:=0|> :num state)
        scheme_env6
        [scheme_basis7] of
      | (st', Rval env) => <|c:=scheme_env6.c;v:=nsAppend env.v scheme_env6.v|>
      | _ => <|v:=nsEmpty;c:=nsEmpty|>
’;

Theorem scheme_env7_rw[simp] = SRULE [GSYM CONJ_ASSOC] $
CONJ (SRULE [Once scheme_env7_def] $ SCONV [] “
  EVERY (λ x . nsLookup scheme_env7.c x = nsLookup scheme_env1.c x) $
    MAP Short cconses
”) $ LIST_CONJ $ map
  (SRULE [
    GSYM $ EVAL “scheme_env1”,
    GSYM $ EVAL “scheme_env2”,
    GSYM $ EVAL “scheme_env3”,
    GSYM $ EVAL “scheme_env4”,
    GSYM $ EVAL “scheme_env5”,
    GSYM $ EVAL “scheme_env6”
  ] o EVAL) [
  “nsLookup scheme_env7.v (Short "sadd")”,
  “nsLookup scheme_env7.v (Short "smul")”,
  “nsLookup scheme_env7.v (Short "sminus")”,
  “nsLookup scheme_env7.v (Short "seqv")”,
  “nsLookup scheme_env7.v (Short "throw")”,
  “nsLookup scheme_env7.v (Short "callcc")”,
  “nsLookup scheme_env7.v (Short "app")”
];

Theorem scheme_env'_def[allow_rebind, compute] = EVAL_RULE $ zDefine ‘
  scheme_env' = case evaluate_decs (<|clock:=999;next_type_stamp:=0;next_exn_stamp:=0|> :num state) <|v:=nsEmpty;c:=nsEmpty|> (prim_types_program ++ [Dtype unknown_loc [(["'a"],"option",
            [("None",[]); ("Some",[Atvar "'a"])])]] ++ scheme_basis) of
    | (st', Rval env) => env
    | _ => <|v:=nsEmpty;c:=nsEmpty|>
’;

Definition vconses_def[simp]:
  vconses = ["sadd"; "smul"; "sminus"; "seqv"; "throw"; "callcc"; "app"]
End

Theorem scheme_env_def[allow_rebind, compute] = SRULE [GSYM CONJ_ASSOC] $ zDefine ‘
  scheme_env env
  ⇔
  EVERY (λ x . nsLookup env.c x = nsLookup scheme_env7.c x) $
    MAP Short cconses ∧
  EVERY (λ x . nsLookup env.v x = nsLookup scheme_env7.v x) $
    MAP Short vconses
’

Theorem basis_scheme_env:
    scheme_env scheme_env'
Proof
  EVAL_TAC
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

Definition scheme_typestamp_def:
  scheme_typestamp con = SND $ THE $ nsLookup scheme_env1.c (Short con)
End

Theorem scheme_typestamp_def[allow_rebind, simp] = SRULE [] $
  SIMP_CONV pure_ss [SimpRHS, scheme_typestamp_def, EVERY_DEF, cconses_def]
  “EVERY (λ x . scheme_typestamp x = scheme_typestamp x) cconses”;

Inductive env_rel:
  FEVERY (λ (x, n).
    nsLookup env.v (Short ("var" ++ explode x)) = SOME (Loc T n)) se
  ⇒
  env_rel se env
End

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
  ml_v_vals' (SBool T) $
    Conv (SOME (scheme_typestamp "SBool")) [Conv (SOME (scheme_typestamp "True")) []]
[~SBool_F:]
  ml_v_vals' (SBool F) $
    Conv (SOME (scheme_typestamp "SBool")) [Conv (SOME (scheme_typestamp "False")) []]
[~SNum:]
  ml_v_vals' (SNum i) $
    Conv (SOME (scheme_typestamp "SNum")) [Litv (IntLit i)]
[~Prim_SAdd:]
  ml_v_vals' (Prim SAdd) $
    Conv (SOME (scheme_typestamp "Prim")) [Conv (SOME (scheme_typestamp "SAdd")) []]
[~Prim_SMul:]
  ml_v_vals' (Prim SMul) $
    Conv (SOME (scheme_typestamp "Prim")) [Conv (SOME (scheme_typestamp "SMul")) []]
[~Prim_SMinus:]
  ml_v_vals' (Prim SMinus) $
    Conv (SOME (scheme_typestamp "Prim")) [Conv (SOME (scheme_typestamp "SMinus")) []]
[~Prim_SEqv:]
  ml_v_vals' (Prim SEqv) $
    Conv (SOME (scheme_typestamp "Prim")) [Conv (SOME (scheme_typestamp "SEqv")) []]
[~Prim_CallCC:]
  ml_v_vals' (Prim CallCC) $
    Conv (SOME (scheme_typestamp "Prim")) [Conv (SOME (scheme_typestamp "CallCC")) []]
[~Prim_Wrong:]
  ml_v_vals' (Wrong s) $
    Conv (SOME (scheme_typestamp "Wrong")) [Litv (StrLit s)]
[~Proc:]
  scheme_env env ∧
  env_rel se env ∧
  ce = cps_transform e ∧
  inner = proc_ml xs xp "k" ce
  ⇒
  ml_v_vals' (Proc se xs xp e) $
    Conv (SOME (scheme_typestamp "Proc")) [
      Closure env "k" $ Fun "xs" inner
    ]
[~Throw:]
  cont_rel ks kv
  ⇒
  ml_v_vals' (Throw ks) $
    Conv (SOME (scheme_typestamp "Throw")) [kv]
[~SList:]
  LIST_REL ml_v_vals' vs mlvs
  ⇒
  ml_v_vals' (SList vs) $
    Conv (SOME (scheme_typestamp "SList")) [vcons_list mlvs]

[~Id:]
  scheme_env env
  ⇒
  cont_rel []
    (Closure env "t" (Var (Short "t")))
[~CondK:]
  cont_rel ks kv ∧
  nsLookup env.v (Short "k") = SOME kv ∧
  ct = cps_transform te ∧
  cf = cps_transform fe ∧
  scheme_env env ∧
  env_rel se env
  ⇒
  cont_rel ((se, CondK te fe) :: ks)
    (Closure env "t" $ Mat (Var (Short "t")) [
      (Pcon (SOME $ Short "SBool") [Pcon (SOME $ Short "False") []],
        App Opapp [cf; Var (Short "k")]);
      (Pany, App Opapp [ct;  Var (Short "k")])
    ])
[~ApplyK_NONE:]
  cont_rel ks kv ∧
  nsLookup env.v (Short "k") = SOME kv ∧
  inner = cps_transform_app (Var (Short "t")) [] es (Var (Short "k")) ∧
  scheme_env env ∧
  env_rel se env
  ⇒
  cont_rel ((se, ApplyK NONE es) :: ks)
    (Closure env "t" $ inner)
[~ApplyK_SOME:]
  cont_rel ks kv ∧
  nsLookup env.v (Short "k") = SOME kv ∧
  (t, ts) = cps_app_ts vs ∧
  inner = cps_transform_app (Var (Short "t"))
    (Var (Short t) :: MAP (Var o Short) ts) es (Var (Short "k")) ∧
  ml_v_vals' fn mlfn ∧
  nsLookup env.v (Short "t") = SOME mlfn ∧
  LIST_REL ml_v_vals' vs mlvs ∧
  LIST_REL (λ x mlv . nsLookup env.v (Short x) = SOME mlv) ts mlvs ∧
  scheme_env env ∧
  env_rel se env
  ⇒
  cont_rel ((se, ApplyK (SOME (fn, vs)) es) :: ks)
    (Closure env t $ inner)
[~BeginK:]
  cont_rel ks kv ∧
  nsLookup env.v (Short "k") = SOME kv ∧
  inner = cps_transform_seq (Var (Short "k")) es e ∧
  scheme_env env ∧
  env_rel se env
  ⇒
  cont_rel ((se, BeginK es e) :: ks)
    (Closure env "_" $ inner)
[~SetK:]
  cont_rel ks kv ∧
  nsLookup env.v (Short "k") = SOME kv ∧
  inner = refunc_set (Var (Short "t")) (Var (Short "k")) x ∧
  scheme_env env ∧
  env_rel se env
  ⇒
  cont_rel ((se, SetK x) :: ks)
    (Closure env "t" $ inner)
End

Theorem val_cont_rels_ind[allow_rebind] = SRULE [] $ val_cont_rels_ind;
Theorem ml_v_vals'_cases = SRULE [] $ cj 1 val_cont_rels_cases;
Theorem cont_rel_cases = cj 2 val_cont_rels_cases;

val (store_entry_rel_rules,store_entry_rel_ind,store_entry_rel_cases) =
(fn (x,y,z) => (SRULE [] x,SRULE [] y, SRULE [] z)) $ Hol_reln ‘
  (ml_v_vals' v mlv
  ⇒
  store_entry_rel (SOME v) (Refv (Conv (SOME (scheme_typestamp "Some")) [mlv]))) ∧
  store_entry_rel NONE (Refv (Conv (SOME (scheme_typestamp "None")) []))
’;

Inductive e_ce_rel:
[~Val:]
  ml_v_vals' v mlv ∧
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

Theorem compile_in_rel:
  ∀ p st env .
    scheme_env env
    ⇒
    ∃ st' env' var mle k kv .
      e_ce_rel (Exp p) var env' kv mle ∧
      cont_rel k kv ∧
      evaluate st env [compile_scheme_prog p] = evaluate st' env' [mle]
Proof
  simp[Once e_ce_rel_cases, compile_scheme_prog_def]
  >> rpt strip_tac
  >> rpt (pairarg_tac >> gvs[])
  >> simp[Ntimes evaluate_def 2, nsOptBind_def]
  >> irule_at (Pos last) EQ_REFL
  >> simp[]
  >> simp[Once cont_rel_cases]
  >> gvs[scheme_env_def]
  >> metis_tac[]
QED

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
    ¬ MEM t vconses ∧
    EVERY (λ t. ¬ MEM t vconses) ts ∧
    (∀ x . t ≠ "var" ++ x) ∧
    EVERY (λ t. ∀ x . t ≠ "var" ++ x) ts
Proof
  Induct_on ‘vs’
  >> simp[cps_app_ts_def]
  >> rpt (pairarg_tac >> gvs[])
  >> drule_then mp_tac $ GSYM cps_app_ts_res
  >> strip_tac
  >> qpat_x_assum ‘_ = t’ $ assume_tac o GSYM
  >> simp[]
  >> qpat_assum ‘∀ _ . _ ⇒ _’ $ irule_at (Pos hd) o SRULE []
  >> irule_at (Pos last) str_not_num
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

Theorem map_reverse[simp]:
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

Theorem preservation_of_sadd_body:
  ∀ vs mlvs .
    LIST_REL ml_v_vals' vs mlvs
    ⇒
  ∀ store st env n k kv i .
    cont_rel k kv ∧
    LIST_REL store_entry_rel store st.refs ∧
    nsLookup env.v (Short "xs") = SOME (vcons_list mlvs) ∧
    nsLookup env.v (Short "n") = SOME (Litv (IntLit n)) ∧
    nsLookup env.v (Short "k") = SOME kv ∧
    nsLookup env.v (Short "sadd") = nsLookup scheme_env2.v (Short "sadd") ∧
    env.c = scheme_env1.c ∧
    i > 0
    ⇒
    ∃ck st' mlenv' var' kv' mle'.
      evaluate (st with clock := ck) env
        [Mat (Var (Short "xs"))
           [(Pcon (SOME (Short "[]")) [],
             Let (SOME "v") (Con (SOME (Short "SNum")) [Var (Short "n")])
               (App Opapp [Var (Short "k"); Var (Short "v")]));
            (Pcon (SOME (Short "::")) [Pvar "x"; Pvar "xs'"],
             Mat (Var (Short "x"))
               [(Pcon (SOME (Short "SNum")) [Pvar "xn"],
                 App Opapp
                   [App Opapp
                      [App Opapp [Var (Short "sadd"); Var (Short "k")];
                       App (Opn Plus) [Var (Short "n"); Var (Short "xn")]];
                    Var (Short "xs'")]);
                (Pany,
                 Con (SOME (Short "Ex"))
                   [Lit (StrLit "Arith-op applied to non-number")])])]] =
      evaluate st' mlenv' [mle'] ∧
      cont_rel k kv' ∧
      e_ce_rel (sadd vs n) var' mlenv' kv' mle' ∧
      env_rel FEMPTY mlenv' ∧
      LIST_REL store_entry_rel store st'.refs ∧
      st'.clock ≤ ck + i ∧
      st'.clock < ck + i
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
    >> irule_at (Pos hd) EQ_REFL
    >> last_assum $ irule_at (Pos hd)
    >> simp[Once e_ce_rel_cases, sadd_def, Once ml_v_vals'_cases,
      env_rel_cases, FEVERY_FEMPTY]
  )
  >> gvs[Once ml_v_vals'_cases]
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
  >> irule_at (Pos hd) EQ_REFL
  >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
  >> simp[env_rel_cases, FEVERY_FEMPTY]
QED

Theorem preservation_of_smul_body:
  ∀ vs mlvs .
    LIST_REL ml_v_vals' vs mlvs
    ⇒
  ∀ store st env n k kv i .
    cont_rel k kv ∧
    LIST_REL store_entry_rel store st.refs ∧
    nsLookup env.v (Short "xs") = SOME (vcons_list mlvs) ∧
    nsLookup env.v (Short "n") = SOME (Litv (IntLit n)) ∧
    nsLookup env.v (Short "k") = SOME kv ∧
    nsLookup env.v (Short "smul") = nsLookup scheme_env3.v (Short "smul") ∧
    env.c = scheme_env1.c ∧
    i > 0
    ⇒
    ∃ck st' mlenv' var' kv' mle'.
      evaluate (st with clock := ck) env
        [Mat (Var (Short "xs"))
           [(Pcon (SOME (Short "[]")) [],
             Let (SOME "v") (Con (SOME (Short "SNum")) [Var (Short "n")])
               (App Opapp [Var (Short "k"); Var (Short "v")]));
            (Pcon (SOME (Short "::")) [Pvar "x"; Pvar "xs'"],
             Mat (Var (Short "x"))
               [(Pcon (SOME (Short "SNum")) [Pvar "xn"],
                 App Opapp
                   [App Opapp
                      [App Opapp [Var (Short "smul"); Var (Short "k")];
                       App (Opn Times) [Var (Short "n"); Var (Short "xn")]];
                    Var (Short "xs'")]);
                (Pany,
                 Con (SOME (Short "Ex"))
                   [Lit (StrLit "Arith-op applied to non-number")])])]] =
      evaluate st' mlenv' [mle'] ∧
      cont_rel k kv' ∧
      e_ce_rel (smul vs n) var' mlenv' kv' mle' ∧
      env_rel FEMPTY mlenv' ∧
      LIST_REL store_entry_rel store st'.refs ∧
      st'.clock ≤ ck + i ∧
      st'.clock < ck + i
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
    >> irule_at (Pos hd) EQ_REFL
    >> last_assum $ irule_at (Pos hd)
    >> simp[Once e_ce_rel_cases, smul_def, Once ml_v_vals'_cases,
      env_rel_cases, FEVERY_FEMPTY]
  )
  >> gvs[Once ml_v_vals'_cases]
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
  >> irule_at (Pos hd) EQ_REFL
  >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
  >> simp[env_rel_cases, FEVERY_FEMPTY]
QED

Theorem preservation_of_sminus_body:
  ∀ vs mlvs .
    LIST_REL ml_v_vals' vs mlvs
    ⇒
  ∀ store (st:'ffi state) env n k kv i .
    cont_rel k kv ∧
    LIST_REL store_entry_rel store st.refs ∧
    nsLookup env.v (Short "xs") = SOME (vcons_list mlvs) ∧
    nsLookup env.v (Short "k") = SOME kv ∧
    nsLookup env.v (Short "sadd") = nsLookup scheme_env3.v (Short "sadd") ∧
    env.c = scheme_env1.c ∧
    i > 0
    ⇒
    ∃ck st' mlenv' var' kv' mle'.
      evaluate (st with clock := ck) env
        [Mat (Var (Short "xs"))
           [(Pcon (SOME (Short "[]")) [],
             Con (SOME (Short "Ex")) [Lit (StrLit "Arity mismatch")]);
            (Pcon (SOME (Short "::")) [Pvar "x"; Pvar "xs'"],
             Mat (Var (Short "x"))
               [(Pcon (SOME (Short "SNum")) [Pvar "n"],
                 App Opapp
                   [App Opapp
                      [App Opapp
                         [Var (Short "sadd");
                          Fun "t"
                            (Mat (Var (Short "t"))
                               [(Pcon (SOME (Short "SNum")) [Pvar "m"],
                                 Let (SOME "v")
                                   (Con (SOME (Short "SNum"))
                                      [App (Opn Minus)
                                         [Var (Short "n");
                                          Var (Short "m")]])
                                   (App Opapp
                                      [Var (Short "k"); Var (Short "v")]));
                                (Pany,
                                 App Opapp
                                   [Var (Short "k"); Var (Short "t")])])];
                       Lit (IntLit 0)]; Var (Short "xs'")]);
                (Pany,
                 Con (SOME (Short "Ex"))
                   [Lit (StrLit "Arith-op applied to non-number")])])]] =
      evaluate st' mlenv' [mle'] ∧
      cont_rel k kv' ∧
      e_ce_rel (sminus vs) var' mlenv' kv' mle' ∧
      env_rel FEMPTY mlenv'
      ∧ LIST_REL store_entry_rel store st'.refs ∧
      st'.clock ≤ ck + i ∧ st'.clock < ck + i
Proof
  Cases_on ‘vs’ >- (
    simp[vcons_list_def]
    >> rpt strip_tac
    >> simp[Ntimes evaluate_def 3]
    >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
      same_type_def, same_ctor_def, evaluate_match_def,
      pat_bindings_def]
    >> irule_at (Pos hd) EQ_REFL
    >> last_assum $ irule_at (Pos hd)
    >> simp[sminus_def]
    >> simp[Once e_ce_rel_cases, env_rel_cases, FEVERY_FEMPTY]
  )
  >> Cases_on ‘mlvs’
  >> simp[vcons_list_def]
  >> strip_tac
  >> gvs[Once ml_v_vals'_cases]
  >~ [‘SNum i’] >- (
    simp[Ntimes evaluate_def 3]
    >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
      same_type_def, same_ctor_def, evaluate_match_def,
      pat_bindings_def]
    >> rpt strip_tac
    >> qrefine ‘ck+3’
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
    >> simp[Ntimes evaluate_def 2, dec_clock_def]
    >> ‘∃ i'' . i' + 3 = i''’ by simp[]
    >> pop_assum mp_tac >> strip_tac
    >> ‘i'' > 0’ by simp[]
    >> qpat_x_assum ‘i' > 0’ kall_tac
    >> qpat_x_assum ‘i' + 3 = i''’ $ simp o single
    >> simp[sminus_def]
    >> ‘∃ n . 0i = n’ by simp[]
    >> pop_assum mp_tac >> strip_tac
    >> pop_assum $ simp o single
    >> ‘∃ kenv . (env with
                           v :=
                             nsBind "n" (Litv (IntLit i))
                               (nsBind "xs'" (vcons_list t')
                                  (nsBind "x"
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
      >> irule_at (Pos hd) EQ_REFL
      >> simp[env_rel_cases, FEVERY_FEMPTY]
      >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
      >> simp[Once e_ce_rel_cases, Once ml_v_vals'_cases]
    )
    >> gvs[Once ml_v_vals'_cases]
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
    >> irule_at (Pos hd) EQ_REFL
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
  >> irule_at (Pos hd) EQ_REFL
  >> simp[env_rel_cases, FEVERY_FEMPTY]
  >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
  >> simp[Once e_ce_rel_cases]
QED

Theorem preservation_of_proc:
∀ (st:'ffi state) inner n n' m m' env env' mlenv var kv n xs xp e e' ce k args vs mlvs store store' i .
  valid_val store (Proc env xs xp e) ∧
  LIST_REL ml_v_vals' vs mlvs ∧
  EVERY (valid_val store) vs ∧
  valid_cont store k ∧
  cont_rel k kv ∧
  ce = cps_transform e ∧
  inner = proc_ml xs xp "k" ce ∧
  (store', env',e') = parameterize store env xs xp e vs ∧
  EVERY (OPTION_ALL (valid_val store)) store ∧
  nsLookup mlenv.v (Short "k") = SOME kv ∧
  nsLookup mlenv.v (Short "xs") = SOME (vcons_list mlvs) ∧
  env_rel env mlenv ∧
  scheme_env mlenv ∧
  can_lookup env store ∧
  LIST_REL store_entry_rel store st.refs ∧
  i > 0
  ⇒
  ∃ck st' mlenv' var' kv' mle'.
    evaluate (st with clock := ck) mlenv [inner]
      = evaluate st' mlenv' [mle'] ∧
    cont_rel k kv' ∧
    e_ce_rel e' var' mlenv' kv' mle' ∧
    env_rel env' mlenv' ∧
    LIST_REL store_entry_rel store' st'.refs ∧
    st'.clock ≤ ck + i ∧
    st'.clock < ck + i
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
        >> irule_at (Pos hd) EQ_REFL
        >> simp[Once e_ce_rel_cases]
      )
      >> simp[Ntimes evaluate_def 3]
      >> simp[can_pmatch_all_def, evaluate_match_def, vcons_list_def,
        pmatch_def]
      >> qpat_assum ‘scheme_env mlenv’ $ simp o single
        o SRULE [scheme_env_def]
      >> simp[same_type_def, same_ctor_def, pat_bindings_def]
      >> irule_at (Pos hd) EQ_REFL
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
    >> irule_at (Pos hd) EQ_REFL
    >> simp[]
    >> rpt (pairarg_tac >> gvs[])
    >> gvs[fresh_loc_def, store_entry_rel_cases]
    >> simp[Once ml_v_vals'_cases]
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
    >> irule_at (Pos hd) EQ_REFL
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
    (store', env') = letrec_init store env xs ∧
    env_rel env mlenv ∧
    LIST_REL store_entry_rel store st.refs ∧
    scheme_env mlenv
    ⇒
    ∃ ck st' mlenv' var' .
      evaluate (st with clock:=ck) mlenv [letinit_ml xs inner]
        = evaluate st' mlenv' [inner] ∧
      env_rel env' mlenv' ∧
      LIST_REL store_entry_rel store' st'.refs ∧
      st'.clock ≤ ck ∧
      (∀ x v . (∀ x' . x ≠ "var" ++ x') ∧ nsLookup mlenv.v (Short x) = SOME v
      ⇒
      nsLookup mlenv'.v (Short x) = SOME v) ∧
      scheme_env mlenv'
Proof
  Induct
  >> simp[letrec_init_def, letinit_ml_def]
  >> rpt strip_tac >- (
    irule_at (Pos hd) EQ_REFL >> simp[]
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

Theorem step_preservation:
  ∀ store store' env env' e e' k k' (st : 'ffi state) mlenv var kv mle .
  step (store, k, env, e) = (store', k', env', e') ∧
  valid_state store k env e ∧
  cont_rel k kv ∧
  e_ce_rel e var mlenv kv mle ∧
  env_rel env mlenv ∧
  LIST_REL store_entry_rel store st.refs
  ⇒
  ∃ ck st' mlenv' var' kv' mle' .
    evaluate (st with clock:=ck) mlenv [mle]
    =
    evaluate st' mlenv' [mle'] ∧
    cont_rel k' kv' ∧
    e_ce_rel e' var' mlenv' kv' mle' ∧
    env_rel env' mlenv' ∧
    LIST_REL store_entry_rel store' st'.refs ∧
    st'.clock ≤ ck ∧
    (k ≠ [] ∧ (∀ s . e ≠ Exception s) ⇒ st'.clock < ck)
Proof
  Cases_on ‘e’
  >~ [‘Exception s’] >- (
    simp[step_def, Once e_ce_rel_cases]
    >> rpt strip_tac
    >> irule_at (Pos hd) EQ_REFL
    >> simp[Once e_ce_rel_cases, Once cont_rel_cases]
    >> qexists ‘scheme_env7’
    >> simp[scheme_env_def]
  )
  >~ [‘Exp e’] >- (
    Cases_on ‘e’
    >> simp[step_def, Once e_ce_rel_cases]
    >~ [‘Lit l’] >- (
      simp[cps_transform_def]
      >> rpt strip_tac
      >> Cases_on ‘l’
      >> simp[lit_to_val_def, to_ml_vals_def]
      >> TRY CASE_TAC (*for Prim cases*)
      >> TRY (Cases_on ‘b’) (*for Bool cases*)
      >> gvs[lit_to_val_def, to_ml_vals_def]
      >> qrefine ‘ck+1’
      >> simp[SimpLHS, Ntimes evaluate_def 7, do_opapp_def,
        do_con_check_def, build_conv_def, nsOptBind_def, dec_clock_def]
      >> qpat_assum ‘scheme_env mlenv’ $ simp o single
        o SRULE [scheme_env_def]
      >> irule_at (Pos hd) EQ_REFL
      >> simp[Once e_ce_rel_cases, Once ml_v_vals'_cases]
      >> gvs[env_rel_cases]
    )
    >~ [‘Cond c te fe’] >- (
      simp[cps_transform_def]
      >> rpt strip_tac
      >> qrefine ‘ck+1’
      >> simp[SimpLHS, Ntimes evaluate_def 6, do_opapp_def,
        nsOptBind_def, dec_clock_def]
      >> irule_at (Pos hd) EQ_REFL
      >> simp[Once e_ce_rel_cases, Once cont_rel_cases]
      >> gvs[scheme_env_def, env_rel_cases]
    )
    >~ [‘Apply fn es’] >- (
      simp[cps_transform_def]
      >> rpt strip_tac
      >> qrefine ‘ck+1’
      >> simp[SimpLHS, Ntimes evaluate_def 6, do_opapp_def,
        nsOptBind_def, dec_clock_def]
      >> irule_at (Pos hd) EQ_REFL
      >> simp[Once e_ce_rel_cases, Once cont_rel_cases]
      >> gvs[scheme_env_def, env_rel_cases]
    )
    >~ [‘Begin es e’] >- (
      Cases_on ‘es’
      >> rpt strip_tac
      >> gvs[cps_transform_def] >- (
        qrefine ‘ck+1’
        >> simp[SimpLHS, Ntimes evaluate_def 4, do_opapp_def,
          nsOptBind_def, dec_clock_def]
        >> irule_at (Pos hd) EQ_REFL
        >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
        >> simp[Once e_ce_rel_cases]
        >> gvs[scheme_env_def, env_rel_cases]
      )
      >> qrefine ‘ck+1’
      >> simp[SimpLHS, Ntimes evaluate_def 6, do_opapp_def,
        nsOptBind_def, dec_clock_def]
      >> irule_at (Pos hd) EQ_REFL
      >> simp[Once e_ce_rel_cases, Once cont_rel_cases]
      >> gvs[scheme_env_def, env_rel_cases]
    )
    >~ [‘Lambda xs xp e’] >- (
      simp[cps_transform_def]
      >> rpt strip_tac
      >> qrefine ‘ck+1’
      >> simp[Ntimes evaluate_def 7, do_opapp_def,
        nsOptBind_def, dec_clock_def, do_con_check_def,
        build_conv_def]
      >> qpat_assum ‘scheme_env mlenv’ $ simp o single
        o SRULE [scheme_env_def]
      >> irule_at (Pos hd) EQ_REFL
      >> last_assum $ irule_at (Pos hd)
      >> simp[Once e_ce_rel_cases, Once ml_v_vals'_cases]
      >> gvs[scheme_env_def, env_rel_cases]
    )
    >~ [‘Ident x’] >- (
      simp[cps_transform_def]
      >> rpt strip_tac
      >> gvs[Once valid_state_cases]
      >> gvs[Once static_scope_def]
      >> gvs[Once $ GSYM SPECIFICATION]
      >> qpat_assum ‘env_rel _ _’ $ drule_then assume_tac
        o SRULE [env_rel_cases, FEVERY_DEF]
      >> qpat_assum ‘can_lookup _ _’ $ drule_then assume_tac
        o SRULE [can_lookup_cases, FEVERY_DEF]
      >> qpat_assum ‘LIST_REL _ _ _’ $ mp_tac
        o SRULE [LIST_REL_EL_EQN, store_entry_rel_cases]
      >> strip_tac
      >> pop_assum $ drule_then assume_tac
      >> qrefine ‘ck+1’
      >> simp[SimpLHS, Ntimes evaluate_def 7, do_opapp_def,
        nsOptBind_def, dec_clock_def]
      >> simp[can_pmatch_all_def, pmatch_def, evaluate_match_def,
        do_app_def, store_lookup_def]
      >> Cases_on ‘EL (env ' x) store’
      >> gvs[]
      >> simp[can_pmatch_all_def, pmatch_def, evaluate_match_def,
        do_app_def, store_lookup_def]
      >> qpat_assum ‘scheme_env mlenv’ $ simp o single
        o SRULE [scheme_env_def]
      >> simp[same_type_def, same_ctor_def, pat_bindings_def]
      >> irule_at (Pos hd) EQ_REFL
      >> simp[]
      >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
      >> simp[Once e_ce_rel_cases]
      >> gvs[env_rel_cases]
    )
    >~ [‘Set x e’] >- (
      simp[cps_transform_def]
      >> rpt strip_tac
      >> qrefine ‘ck+1’
      >> simp[SimpLHS, Ntimes evaluate_def 6, do_opapp_def,
        nsOptBind_def, dec_clock_def]
      >> irule_at (Pos hd) EQ_REFL
      >> simp[Once e_ce_rel_cases, Once cont_rel_cases]
      >> gvs[scheme_env_def, env_rel_cases]
    )
    >~ [‘Letrec bs e’] >- (
      simp[Once cps_transform_def]
      >> cheat(*
      >> rpt strip_tac
      >> rpt (pairarg_tac >> gvs[])
      >> qrefine ‘ck+1’
      >> simp[Ntimes evaluate_def 4, do_opapp_def, dec_clock_def]
      >> pop_assum $ assume_tac o GSYM
      >> drule preservation_of_letrec
      >> qsuff_tac ‘env_rel env
        (mlenv with v := nsBind (STRING #"k" (toString m')) kv mlenv.v)’ >- (
        rpt strip_tac
        >> pop_assum $ drule_then drule
        >> qsuff_tac ‘scheme_env
          (mlenv with v := nsBind (STRING #"k" (toString m')) kv mlenv.v)’ >- (
          rpt strip_tac
          >> pop_assum $ drule
          >> rpt strip_tac
          >> pop_assum $ qspec_then
            ‘(App Opapp [ce'; Var (Short (STRING #"k" (toString m')))])’ mp_tac
          >> rpt strip_tac
          >> qpat_assum ‘evaluate _ _ _ = _’ $ irule_at (Pos hd)
          >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
          >> simp[Once e_ce_rel_cases]
          >> qpat_assum ‘cps_transform _ _ = _’ $ irule_at (Pos hd) o GSYM
        )
        >> gvs[scheme_env_def]
      )
      >> gvs[env_rel_cases]*)
    )
  )
  >~ [‘Val v’] >- (
    Cases_on ‘k’
    >- (
      simp[step_def, return_def]
      >> rw[]
      >> irule_at (Pos hd) EQ_REFL
      >> simp[env_rel_cases, FEVERY_FEMPTY]
      >> metis_tac[]
    )
    >> PairCases_on ‘h’
    >> Cases_on ‘∃ te fe . h1 = CondK te fe’ >- (
      gvs[]
      >> simp[step_def, return_def]
      >> simp[Once e_ce_rel_cases, Once cont_rel_cases]
      >> simp[Once ml_v_vals'_cases]
      >> rpt strip_tac
      >> gvs[]
      >> qrefine ‘ck+1’
      >> simp[SimpLHS, Ntimes evaluate_def 6, do_con_check_def,
        build_conv_def, scheme_env_def, do_opapp_def,
      can_pmatch_all_def, pmatch_def, dec_clock_def]
      >> qpat_assum ‘scheme_env env''’ $ simp o curry ((::) o swap) [
          same_type_def, same_ctor_def, do_opapp_def,
          evaluate_match_def, pmatch_def, pat_bindings_def]
        o SRULE [scheme_env_def]
      >> irule_at (Pos hd) EQ_REFL
      >> gvs[]
      >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
      >> simp[Once e_ce_rel_cases]
      >> gvs[scheme_env_def, env_rel_cases]
    )
    >> Cases_on ‘∃ es e . h1 = BeginK es e’ >- (
      gvs[]
      >> Cases_on ‘es’
      >> rpt strip_tac
      >> gvs[Once cont_rel_cases, Once e_ce_rel_cases]
      >> gvs[cps_transform_def, step_def, return_def]
      >> qrefine ‘ck+1’
      >> simp[SimpLHS, Ntimes evaluate_def 4, do_opapp_def,
        nsOptBind_def, dec_clock_def] >- (
        irule_at (Pos hd) EQ_REFL
        >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
        >> simp[Once e_ce_rel_cases]
        >> gvs[scheme_env_def, env_rel_cases]
      )
      >> simp[SimpLHS, Ntimes evaluate_def 2, nsOptBind_def]
      >> irule_at (Pos hd) EQ_REFL
      >> simp[Once e_ce_rel_cases, Once cont_rel_cases]
      >> gvs[scheme_env_def, env_rel_cases]
    )
    >> Cases_on ‘∃ x . h1 = SetK x’ >- (
      gvs[]
      >> simp[step_def, return_def, Once e_ce_rel_cases, refunc_set_def,
        Once cont_rel_cases, cps_transform_def, cps_app_ts_def]
      >> rpt strip_tac
      >> simp[]
      >> gvs[Once valid_state_cases]
      >> qpat_x_assum ‘valid_cont _ _’ $ mp_tac
        o SRULE [Once valid_val_cases]
      >> strip_tac
      >> qpat_assum ‘env_rel h0 _’ $ drule_then assume_tac
        o SRULE [env_rel_cases, FEVERY_DEF, SPECIFICATION]
      >> qpat_assum ‘can_lookup h0 _’ $ drule_then assume_tac
        o SRULE [can_lookup_cases, FEVERY_DEF, SPECIFICATION]
      >> drule_then assume_tac EVERY2_LENGTH
      >> drule_all_then assume_tac $ cj 2 $ iffLR LIST_REL_EL_EQN
      >> gvs[store_entry_rel_cases]
      >> qrefine ‘ck+1’
      >> simp[Ntimes evaluate_def 13, do_con_check_def, nsOptBind_def,
        build_conv_def, scheme_env_def, do_opapp_def, dec_clock_def,
        do_app_def, store_assign_def, store_v_same_type_def]
      >> qpat_assum ‘scheme_env _’ $ simp o single
        o SRULE [scheme_env_def]
      >> irule_at (Pos hd) EQ_REFL
      >> simp[]
      >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
      >> simp[Once e_ce_rel_cases, Once ml_v_vals'_cases]
      >> gvs[env_rel_cases]
      >> irule EVERY2_LUPDATE_same
      >> simp[store_entry_rel_cases]
    )
    >> Cases_on ‘∃ e es . h1 = ApplyK NONE (e::es)’ >- (
      gvs[]
      >> simp[step_def, return_def, Once e_ce_rel_cases,
        Once cont_rel_cases, cps_transform_def, cps_app_ts_def]
      >> rpt strip_tac
      >> qrefine ‘ck+1’
      >> simp[Ntimes evaluate_def 6, do_opapp_def,
        nsOptBind_def, dec_clock_def]
      >> irule_at (Pos hd) EQ_REFL
      >> simp[Once e_ce_rel_cases, Once cont_rel_cases]
      >> simp[cps_app_ts_def]
      >> gvs[scheme_env_def, env_rel_cases]
    )
    >> Cases_on ‘∃ fn vs e es . h1 = ApplyK (SOME (fn, vs)) (e::es)’ >- (
      gvs[]
      >> simp[step_def, return_def, Once e_ce_rel_cases,
        Once cont_rel_cases, cps_transform_def, cps_app_ts_def]
      >> rpt strip_tac
      >> qrefine ‘ck+1’
      >> simp[Ntimes evaluate_def 6, do_opapp_def,
        nsOptBind_def, dec_clock_def]
      >> irule_at (Pos hd) EQ_REFL
      >> simp[Once e_ce_rel_cases, Once cont_rel_cases]
      >> simp[PULL_EXISTS]
      >> irule_at (Pos hd) EQ_REFL
      >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
      >> simp[cps_app_ts_def]
      >> rpt (pairarg_tac >> gvs[])
      >> qpat_assum ‘ml_v_vals' _ _’ $ irule_at Any
      >> qpat_assum ‘LIST_REL ml_v_vals' _ _’ $ irule_at Any
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
      >> gvs[scheme_env_def, env_rel_cases]
    )
    >> Cases_on ‘h1 = ApplyK NONE []’ >- (
      gvs[]
      >> simp[step_def, return_def, Once e_ce_rel_cases, Once cont_rel_cases]
      >> simp[Once ml_v_vals'_cases]
      >> rpt strip_tac
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
        >> irule_at (Pos hd) EQ_REFL
        >> simp[Once e_ce_rel_cases]
        >> last_assum $ irule_at (Pos hd)
        >> simp[env_rel_cases, FEVERY_FEMPTY]
      )
      >~ [‘SOME (Conv (SOME (TypeStamp "SBool" _)) [
        Conv (Some (TypeStamp "True" _)) []
      ])’] >- (
        qrefine ‘ck+1’
        >> simp[Once evaluate_def]
        >> irule_at (Pos hd) EQ_REFL
        >> simp[Once e_ce_rel_cases]
        >> last_assum $ irule_at (Pos hd)
        >> simp[env_rel_cases, FEVERY_FEMPTY]
      )
      >~ [‘SOME (Conv (SOME (TypeStamp "SBool" _)) [
        Conv (Some (TypeStamp "False" _)) []
      ])’] >- (
        qrefine ‘ck+1’
        >> simp[Once evaluate_def]
        >> irule_at (Pos hd) EQ_REFL
        >> simp[Once e_ce_rel_cases]
        >> last_assum $ irule_at (Pos hd)
        >> simp[env_rel_cases, FEVERY_FEMPTY]
      )
      >~ [‘SOME (Conv (SOME (TypeStamp "SList" _)) [_])’] >- (
        qrefine ‘ck+1’
        >> simp[Once evaluate_def]
        >> irule_at (Pos hd) EQ_REFL
        >> simp[Once e_ce_rel_cases]
        >> last_assum $ irule_at (Pos hd)
        >> simp[env_rel_cases, FEVERY_FEMPTY]
      )
      >~ [‘SOME (Conv (SOME (TypeStamp "Wrong" _)) [_])’] >- (
        qrefine ‘ck+1’
        >> simp[Once evaluate_def]
        >> irule_at (Pos hd) EQ_REFL
        >> simp[Once e_ce_rel_cases]
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
        >> irule_at (Pos hd) EQ_REFL
        >> last_assum $ irule_at (Pos hd)
        >> simp[Once e_ce_rel_cases, Once ml_v_vals'_cases]
        >> simp[env_rel_cases, FEVERY_FEMPTY]
      )
      >~ [‘"SMul"’] >- (
        qrefine ‘ck+1’
        >> simp[Ntimes evaluate_def 3, nsOptBind_def,
          do_con_check_def, build_conv_def]
        >> irule_at (Pos hd) EQ_REFL
        >> last_assum $ irule_at (Pos hd)
        >> simp[Once e_ce_rel_cases, Once ml_v_vals'_cases]
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
      >> irule_at (Pos hd) EQ_REFL
      >> simp[Once e_ce_rel_cases]
      >> simp[env_rel_cases, FEVERY_FEMPTY]
      >> last_assum $ irule_at Any
    )
    >> Cases_on ‘∃ fn vs . h1 = ApplyK (SOME (fn, vs)) []’ >- (
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
        >> gvs[Once ml_v_vals'_cases]
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
            >> irule_at (Pos hd) EQ_REFL
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
              gvs[Once ml_v_vals'_cases]
              >> simp[Ntimes evaluate_def 8]
              >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
                same_type_def, same_ctor_def, evaluate_match_def,
                pat_bindings_def, do_con_check_def, build_conv_def]
              >> Cases_on ‘∃ m . v = SNum m’ >- (
                gvs[Once ml_v_vals'_cases]
                >> simp[Ntimes evaluate_def 11, nsOptBind_def, do_app_def]
                >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
                  same_type_def, same_ctor_def, evaluate_match_def,
                  pat_bindings_def, do_con_check_def, build_conv_def,
                  do_eq_def, lit_same_type_def]
                >> irule_at (Pos hd) EQ_REFL
                >> simp[env_rel_cases, FEVERY_FEMPTY]
                >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
                >> Cases_on ‘i=i'’
                >> simp[Once e_ce_rel_cases, Once ml_v_vals'_cases,
                  Boolv_def, bool_type_num_def]
              )
              >> Cases_on ‘v’
              >> gvs[Once ml_v_vals'_cases]
              >> simp[Ntimes evaluate_def 8, nsOptBind_def]
              >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
                same_type_def, same_ctor_def, evaluate_match_def,
                pat_bindings_def, do_con_check_def, build_conv_def]
              >> irule_at (Pos hd) EQ_REFL
              >> simp[env_rel_cases, FEVERY_FEMPTY]
              >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
              >> simp[Once e_ce_rel_cases, Once ml_v_vals'_cases,
                Boolv_def, bool_type_num_def]
            )
            >> Cases_on ‘∃ b . x = SBool b’ >- (
              gvs[Once ml_v_vals'_cases]
              >> simp[Ntimes evaluate_def 8]
              >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
                same_type_def, same_ctor_def, evaluate_match_def,
                pat_bindings_def, do_con_check_def, build_conv_def]
              >> (Cases_on ‘∃ b' . v = SBool b'’ >- (
                gvs[Once ml_v_vals'_cases]
                >> simp[Ntimes evaluate_def 11, nsOptBind_def, do_app_def]
                >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
                  same_type_def, same_ctor_def, evaluate_match_def,
                  pat_bindings_def, do_con_check_def, build_conv_def,
                  do_eq_def, lit_same_type_def, ctor_same_type_def]
                >> irule_at (Pos hd) EQ_REFL
                >> simp[env_rel_cases, FEVERY_FEMPTY]
                >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
                >> simp[Once e_ce_rel_cases, Once ml_v_vals'_cases,
                  Boolv_def, bool_type_num_def]
              ))
              >> Cases_on ‘v’ >> gvs[]
              >> gvs[Once ml_v_vals'_cases]
              >> simp[Ntimes evaluate_def 8, nsOptBind_def]
              >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
                same_type_def, same_ctor_def, evaluate_match_def,
                pat_bindings_def, do_con_check_def, build_conv_def]
              >> irule_at (Pos hd) EQ_REFL
              >> simp[env_rel_cases, FEVERY_FEMPTY]
              >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
              >> simp[Once e_ce_rel_cases, Once ml_v_vals'_cases,
                Boolv_def, bool_type_num_def]
            )
            >> Cases_on ‘x’ >> gvs[]
            >> gvs[Once ml_v_vals'_cases]
            >> simp[Ntimes evaluate_def 9, nsOptBind_def]
            >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
              same_type_def, same_ctor_def, evaluate_match_def,
              pat_bindings_def, do_con_check_def, build_conv_def]
            >> irule_at (Pos hd) EQ_REFL
            >> simp[env_rel_cases, FEVERY_FEMPTY]
            >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
            >> simp[Once e_ce_rel_cases, Once ml_v_vals'_cases]
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
          >> irule_at (Pos hd) EQ_REFL
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
            >> irule_at (Pos hd) EQ_REFL
            >> simp[env_rel_cases, FEVERY_FEMPTY]
            >> simp[Once cont_rel_cases]
            >> gvs[cps_transform_def, cps_app_ts_def]
            >> irule_at (Pos hd) EQ_REFL
            >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
            >> qpat_assum ‘ml_v_vals' _ _’ $ irule_at Any
            >> simp[Once e_ce_rel_cases]
            >> simp[Once ml_v_vals'_cases]
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
          >> irule_at (Pos hd) EQ_REFL
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
            >> irule_at (Pos hd) EQ_REFL
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
          >> irule_at (Pos hd) EQ_REFL
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
        >> irule_at (Pos hd) EQ_REFL
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

(*
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
    evaluate (st with clock:=ck) mlenv [mle]
    =
    evaluate st' mlenv' [mle'] ∧
    cont_rel k' kv' ∧
    e_ce_rel e' var' mlenv' kv' mle' ∧
    env_rel env' mlenv' ∧
    LIST_REL store_entry_rel store' st'.refs ∧
    st'.clock ≤ ck ∧
    (n > 0 ∧ k ≠ [] ∧ (∀ s . e ≠ Exception s) ⇒ st'.clock < ck)
Proof
  Induct >- (
    simp[]
    >> rpt strip_tac
    >> irule_at (Pos hd) EQ_REFL
    >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
    >> qpat_assum ‘e_ce_rel _ _ _ _ _’ $ irule_at (Pos hd)
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
  >> qpat_assum ‘∀ _ _ _ _ _ . _ ⇒ _’ drule_all
  >> rpt strip_tac
  >> simp[]
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
    ml_v_vals' v mlv
Proof
  Induct_on ‘n’
  >> simp[FUNPOW]
  >> rpt strip_tac >- (
    gvs[Once e_ce_rel_cases, Once cont_rel_cases]
    >> qrefine ‘ck+1’
    >> simp[evaluate_def, do_opapp_def]
  )
  >> drule valid_state_progress
  >> strip_tac
  >> gvs[]
  >> drule_all step_preservation
  >> strip_tac
  >> last_x_assum $ drule_all
  >> strip_tac
QED
*)

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