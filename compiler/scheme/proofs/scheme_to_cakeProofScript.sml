(*
  Proof of semantic preservation from Scheme to CakeML
*)
Theory scheme_to_cakeProof
Ancestors
  scheme_to_cake_env scheme_ast scheme_semantics scheme_to_cake
  scheme_semanticsProps ast evaluate evaluateProps ml_prog
  semanticPrimitives namespace primTypes namespaceProps integer
Libs
  preamble computeLib

val _ = (max_print_depth := 30);

Type state = ``:'a semanticPrimitives$state``;

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

Definition scheme_cons_env_def[nocompute]:
  scheme_cons_env = nsAppend scheme_to_cake_env_env_0.c init_env.c
End

Theorem scheme_cons_env_simp =
  scheme_cons_env_def
  |> SRULE [Once scheme_init_env_defs, init_env_def]
  |> SRULE [scheme_to_cake_env_env_def, empty_env_def]
  |> SRULE [Ntimes write_cons_def 22]
  |> SRULE [nsBind_def, nsEmpty_def, nsAppend_def];

Theorem scheme_env_app_def[allow_rebind, compute] = EVAL_RULE $ zDefine ‘
  scheme_env_app env <=>
    env.c = scheme_cons_env ∧
    EVERY (λ dec. ∃ env_cl . env_cl.c = scheme_cons_env ∧ closure_in_env env dec env_cl)
      (TAKE 2 scheme_basis ++ DROP 3 scheme_basis ++ [scheme_basis_list]) /\
    (? env_sminus . env_sminus.c = scheme_cons_env /\ closure_in_env env (EL 2 scheme_basis) env_sminus /\
      (? env_sadd . env_sadd.c = scheme_cons_env /\ closure_in_env env_sminus (EL 0 scheme_basis) env_sadd))
’;

Theorem scheme_env_def[allow_rebind, compute] = RESTR_EVAL_RULE [``scheme_env_app``] $ zDefine ‘
  scheme_env env <=>
    env.c = scheme_cons_env ∧
    (∃ env_app .
      scheme_env_app env_app ∧
      closure_in_env env scheme_basis_app env_app) /\
    ? env_list .
      env_list.c = scheme_cons_env /\
      closure_in_env env scheme_basis_list env_list
’;

val scheme_init_conjs = BODY_CONJUNCTS scheme_init_env_defs;
val scheme_init_env_defs_but_0 = LIST_CONJ $ List.take (scheme_init_conjs, length scheme_init_conjs - 1);

Theorem basis_scheme_env:
  scheme_env scheme_to_cake_env
Proof
  simp[scheme_env_def, scheme_to_cake_env_def]
  >> rpt conj_tac >- (
    simp[merge_env_def]
    >> simp[Once scheme_init_env_defs]
    >> simp[Once scheme_init_env_defs]
    >> simp[Once scheme_init_env_defs]
    >> simp[Once scheme_init_env_defs]
    >> simp[Once scheme_init_env_defs]
    >> simp[Once scheme_init_env_defs]
    >> simp[Once scheme_init_env_defs]
    >> simp[Once scheme_init_env_defs]
    >> simp[Once scheme_init_env_defs]
    >> simp[Once scheme_init_env_defs]
    >> simp[Once scheme_init_env_defs]
    >> simp[Once scheme_init_env_defs]
    >> simp[scheme_cons_env_def]
  )
  >- (
    qexists `merge_env scheme_to_cake_env_env_11 init_env`
    >> simp[cj 11 scheme_init_env_defs]
    >> simp[scheme_init_v_defs]
    >> simp[merge_env_def]
    >> simp[scheme_env_app_def]
    >> simp[cj 12 scheme_init_env_defs]
    >> simp[cj 13 scheme_init_env_defs]
    >> simp[cj 2 scheme_init_env_defs]
    >> simp[cj 3 scheme_init_env_defs]
    >> simp[cj 4 scheme_init_env_defs]
    >> simp[cj 5 scheme_init_env_defs]
    >> simp[cj 6 scheme_init_env_defs]
    >> simp[cj 7 scheme_init_env_defs]
    >> simp[cj 8 scheme_init_env_defs]
    >> simp[cj 9 scheme_init_env_defs]
    >> simp[cj 10 scheme_init_env_defs]
    >> simp[scheme_cons_env_def]
    >> simp[scheme_init_v_defs, merge_env_def]
    >> simp[scheme_init_env_defs_but_0]
    >> simp[scheme_init_v_defs]
    >> simp[merge_env_def]
  )
  >> simp[cj 11 scheme_init_env_defs]
  >> simp[merge_env_def]
  >> simp[cj 12 scheme_init_env_defs]
  >> simp[scheme_cons_env_def]
  >> simp[scheme_init_v_defs, merge_env_def]
  >> simp[scheme_init_env_defs_but_0]
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

Theorem scheme_conses_def[allow_rebind, compute] = EVAL_RULE $ SRULE [scheme_cons_env_simp] $ zDefine‘
  scheme_conses = case scheme_cons_env of
    Bind cs _ => MAP FST cs
’;

Theorem scheme_runtime_funs_def[allow_rebind, compute] = EVAL_RULE $ SRULE [scheme_cons_env_simp] $ zDefine‘
  scheme_runtime_funs = FOLDL (λ acc dec. acc ++ case dec of
    | Dlet _ (Pvar x) _ => [x]
    | Dletrec _ funs => MAP FST funs) [] $
    scheme_basis ++ [scheme_basis_list; scheme_basis_app]
’;

Definition scheme_typestamp_def:
  scheme_typestamp con = SND $ THE $ nsLookup scheme_cons_env (Short con)
End

Theorem scheme_typestamp_def[allow_rebind, simp, compute] = SRULE [] $
  SIMP_CONV pure_ss [SimpRHS, scheme_typestamp_def, EVERY_DEF,
      scheme_conses_def, SND, THE_DEF, nsLookup_def, scheme_cons_env_simp]
    “EVERY (λ x . scheme_typestamp x = scheme_typestamp x) scheme_conses”;

Inductive env_rel:
  FEVERY (λ (x, l).
    nsLookup env.v (Short ("var" ++ explode x)) = SOME (Loc T l)) se
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

val (bool_val_rel_rules,bool_val_rel_ind,bool_val_rel_cases) =
(fn (x,y,z) => (SRULE [] x,SRULE [] y, SRULE [] z)) $ Hol_reln ‘
  bool_val_rel T (Conv (SOME (scheme_typestamp "True")) []) ∧
  bool_val_rel F (Conv (SOME (scheme_typestamp "False")) [])
’;

val (prim_val_rel_rules,prim_val_rel_ind,prim_val_rel_cases) =
(fn (x,y,z) => (SRULE [] x,SRULE [] y, SRULE [] z)) $ Hol_reln ‘
  prim_val_rel SAdd (Conv (SOME (scheme_typestamp "SAdd")) []) ∧
  prim_val_rel SMul (Conv (SOME (scheme_typestamp "SMul")) []) ∧
  prim_val_rel SMinus (Conv (SOME (scheme_typestamp "SMinus")) []) ∧
  prim_val_rel SEqv (Conv (SOME (scheme_typestamp "SEqv")) []) ∧
  prim_val_rel CallCC (Conv (SOME (scheme_typestamp "CallCC")) []) ∧
  prim_val_rel Cons (Conv (SOME (scheme_typestamp "Cons")) []) ∧
  prim_val_rel Car (Conv (SOME (scheme_typestamp "Car")) []) ∧
  prim_val_rel Cdr (Conv (SOME (scheme_typestamp "Cdr")) []) ∧
  prim_val_rel IsNull (Conv (SOME (scheme_typestamp "IsNull")) []) ∧
  prim_val_rel IsPair (Conv (SOME (scheme_typestamp "IsPair")) [])
’;

Inductive val_cont_rels:
[~SBool:]
  bool_val_rel b mlb
  ==>
  ml_v_vals (SBool b) $ Conv (SOME (scheme_typestamp "SBool")) [mlb]
[~SNum:]
  ml_v_vals (SNum i) $
    Conv (SOME (scheme_typestamp "SNum")) [Litv (IntLit i)]
[~Prim:]
  prim_val_rel prim mlprim
  ==>
  ml_v_vals (Prim prim) $ Conv (SOME (scheme_typestamp "Prim")) [mlprim]
[~Wrong:]
  ml_v_vals (Wrong s) $
    Conv (SOME (scheme_typestamp "Wrong")) [Litv (StrLit s)]
[~Proc:]
  scheme_env env ∧
  env_rel se env ∧
  ce = cps_transform e ∧
  inner = proc_ml xs xp "k" ce
  ⇒
  ml_v_vals (Proc se xs xp e) $
    Conv (SOME (scheme_typestamp "Proc")) [
      Closure env "k" $ Fun "ts" inner
    ]
[~Throw:]
  cont_rel ks kv
  ⇒
  ml_v_vals (Throw ks) $
    Conv (SOME (scheme_typestamp "Throw")) [kv]
[~PairP:]
  ml_v_vals (PairP l) $
    Conv (SOME (scheme_typestamp "PairP")) [Loc T l]
[~Null:]
  ml_v_vals Null $
    Conv (SOME (scheme_typestamp "Null")) []

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
    (MAP (Var o Short) (t::ts)) es (Var (Short "k")) ∧
  ml_v_vals fn mlfn ∧
  nsLookup env.v (Short "t") = SOME mlfn ∧
  LIST_REL ml_v_vals vs mlvs ∧
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
[~LetinitK:]
  cont_rel ks kv ∧
  nsLookup env.v (Short "k") = SOME kv ∧
  (t, ts) = cps_app_ts xvs ∧
  inner = cps_transform_letinit
    ((x,Var (Short t))::ZIP (MAP FST xvs, MAP (Var o Short) ts))
    bs e (Var (Short "k")) ∧
  LIST_REL ml_v_vals (MAP SND xvs) mlvs ∧
  LIST_REL (λ x mlv . nsLookup env.v (Short x) = SOME mlv) ts mlvs ∧
  scheme_env env ∧
  env_rel se env
  ⇒
  cont_rel ((se, LetinitK xvs x bs e) :: ks)
    (Closure env t $ inner)
End

Theorem val_cont_rels_ind[allow_rebind] = SRULE [] $ val_cont_rels_ind;
Theorem ml_v_vals_cases = SRULE [] $ cj 1 val_cont_rels_cases;
Theorem cont_rel_cases = cj 2 val_cont_rels_cases;

val (store_entry_rel_rules,store_entry_rel_ind,store_entry_rel_cases) =
(fn (x,y,z) => (SRULE [] x,SRULE [] y, SRULE [] z)) $ Hol_reln ‘
  store_entry_rel (Mut NONE) (Refv (Conv (SOME (scheme_typestamp "None")) [])) ∧
  (ml_v_vals v mlv
  ⇒
  store_entry_rel (Mut (SOME v)) (Refv (Conv (SOME (scheme_typestamp "Some")) [mlv]))) ∧
  (ml_v_vals v1 mlv1 ∧
  ml_v_vals v2 mlv2
  ⇒
  store_entry_rel (Pair (v1, v2)) (Varray [mlv1; mlv2]))
’;

Inductive cps_rel:
[~Val:]
  ml_v_vals v mlv ∧
  nsLookup env.v (Short t) = SOME (mlv) ∧
  nsLookup env.v (Short k) = SOME kv ∧
  t ≠ k
  ⇒
  cps_rel (Val v) k env kv $ App Opapp [Var (Short k); Var (Short t)]
[~Exp:]
  ce = cps_transform e ∧
  nsLookup env.v (Short k) = SOME kv ∧
  scheme_env env ∧
  env_rel senv env
  ⇒
  cps_rel (Exp senv e) var env kv $ App Opapp [ce; Var (Short k)]
[~Exception:]
  cps_rel (Exception s) var env kv $
    Con (SOME $ Short "Ex") [Lit $ StrLit $ explode s]
End

Theorem env_rel_FEMPTY[simp]:
  ∀ env . env_rel FEMPTY env
Proof
  simp[env_rel_cases, FEVERY_FEMPTY]
QED

Theorem env_rel_non_var[simp]:
  ! se env envv var v .
    (! x . var <> "var" ++ x)
    ==>
    env_rel se (env with v := nsBind var v envv) = env_rel se (env with v := envv)
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
      cps_rel (Exp FEMPTY p) var env' kv mle ∧
      cont_rel ks kv ∧
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
  >> gvs[scheme_env_def, scheme_cons_env_simp, scheme_conses_def, nsLookup_def]
QED

Theorem scheme_app_cons_lookup:
  ! env . scheme_env_app env ==> EVERY (\c . nsLookup env.c (Short c) = nsLookup scheme_cons_env (Short c)) scheme_conses
Proof
  rpt strip_tac
  >> gvs[scheme_env_app_def, scheme_cons_env_simp, scheme_conses_def, nsLookup_def]
QED

Theorem scheme_env_cons_lookup:
  EVERY (\c . nsLookup scheme_cons_env (Short c) = nsLookup scheme_cons_env (Short c)) scheme_conses
Proof
  simp[]
QED

val _ = augment_srw_ss $ single $ rewrites $ BODY_CONJUNCTS $ SRULE [IMP_CONJ_THM, scheme_cons_env_simp, nsLookup_def] $ RESTR_EVAL_RULE [``scheme_env``] scheme_cons_lookup;
val _ = augment_srw_ss $ single $ rewrites $ BODY_CONJUNCTS $ SRULE [IMP_CONJ_THM, scheme_cons_env_simp, nsLookup_def] $ RESTR_EVAL_RULE [``scheme_env_app``] scheme_app_cons_lookup;
val _ = augment_srw_ss $ single $ rewrites $ BODY_CONJUNCTS $ EVAL_RULE $ SIMP_RULE pure_ss [SimpRHS, scheme_cons_env_simp, nsLookup_def] $ scheme_env_cons_lookup;

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

Definition letpreinit_mlenv_def:
  letpreinit_mlenv mlenv xs l
  =
  (mlenv with v := nsAppend (Bind (REVERSE $ MAP (\ p. ("var" ++ (explode $ FST p), Loc T $ l + SND p)) $ ZIP (xs, GENLIST I $ LENGTH xs)) []) mlenv.v)
End

Theorem letpreinit_ml_eval:
  ! xs (st:'ffi state) mlenv e .
    scheme_env mlenv
    ==>
    evaluate st mlenv [letpreinit_ml xs e]
    =
    evaluate
      (st with refs := st.refs ++ (GENLIST (K $ Refv $ Conv (SOME $ scheme_typestamp "None") []) $ LENGTH xs))
      (letpreinit_mlenv mlenv xs $ LENGTH st.refs)
      [e]
Proof
  Induct
  >> simp[letpreinit_mlenv_def, letpreinit_ml_def, GSYM nsEmpty_def]
  >> rpt strip_tac
  >> gvs[letpreinit_mlenv_def]
  >> simp[evaluate_def, do_con_check_def, build_conv_def,
    do_app_def, store_alloc_def, nsOptBind_def]
  >> simp_tac bool_ss [SIMP_RULE bool_ss [Once CONS_APPEND] GENLIST_CONS, APPEND_ASSOC]
  >> simp[]
  >> Cases_on `mlenv.v`
  >> simp_tac bool_ss [nsAppend_def, GSYM APPEND_ASSOC]
  >> simp_tac bool_ss [GSYM nsAppend_def]
  >> simp[GSYM nsBind_def]
  >> pop_assum $ simp o single o GSYM
  >> `! l . GENLIST SUC l = MAP SUC $ GENLIST I l` by simp[MAP_GENLIST]
  >> pop_assum $ simp o single
  >> simp[cj 2 ZIP_MAP, MAP_MAP_o, o_DEF]
  >> qpat_abbrev_tac `st' = st with refs := _`
  >> qpat_abbrev_tac `mlenv' = mlenv with v := _`
  >> last_x_assum $ qspec_then `st'` $
    qspec_then `mlenv'` $ qspec_then `e` $ assume_tac
  >> `scheme_env mlenv'` by (unabbrev_all_tac >> rpt scheme_env_tac)
  >> unabbrev_all_tac
  >> simp[]
  >> `! n . SUC n = n + 1` by simp[]
  >> simp[]
QED

Theorem letpreinit_ml_eval[allow_rebind] = SRULE [] letpreinit_ml_eval;

Theorem letpreinit_env_rel:
  ! mlenv xs env l .
    env_rel env mlenv
    ==>
    env_rel (letrec_preinit_env env xs l) (letpreinit_mlenv mlenv xs l)
Proof
  simp[letrec_preinit_env_def, letpreinit_mlenv_def, env_rel_cases]
  >> gen_tac
  >> `? mlenvv . mlenv.v = mlenvv` by simp[]
  >> pop_assum $ simp o single
  >> qid_spec_tac `mlenvv`
  >> Induct_on `xs`
  >> simp[GSYM nsEmpty_def, FUPDATE_LIST]
  >> rpt strip_tac
  >> simp[GENLIST_CONS]
  >> simp[GSYM FUPDATE_LIST]
  >> Cases_on `mlenvv`
  >> simp_tac bool_ss [nsAppend_def, GSYM APPEND_ASSOC]
  >> simp[GSYM nsAppend_def, GSYM nsBind_def]
  >> `! l . GENLIST SUC l = MAP SUC $ GENLIST I l` by simp[MAP_GENLIST]
  >> pop_assum $ simp o single
  >> simp[cj 2 ZIP_MAP, MAP_MAP_o, o_DEF]
  >> `! x y . x + SUC y = SUC x + y` by simp[]
  >> pop_assum $ simp_tac bool_ss o single
  >> last_x_assum irule
  >> gvs[FEVERY_DEF, SPECIFICATION]
  >> rename1 `_ |+ (x,l)`
  >> qx_gen_tac `x'`
  >> Cases_on `x' = x`
  >> simp[FAPPLY_FUPDATE_THM]
QED

Theorem allocate_list_ml:
  ! store store' (st:'ffi state) env env_list vs mlvs tail ts ck .
    env.c = scheme_cons_env /\
    env_list.c = scheme_cons_env /\
    closure_in_env env scheme_basis_list env_list /\
    nsLookup env.v (Short ts) = SOME (vcons_list mlvs) /\
    allocate_list store vs = (store', tail) /\
    LIST_REL ml_v_vals vs mlvs /\
    LIST_REL store_entry_rel store st.refs /\
    ¬ MEM ts scheme_runtime_funs
    ==>
    ? ck st' mltail .
      (! start . evaluate (st with clock := ck + start) env [App Opapp [
        Var (Short "allocate_list");
        Var (Short ts)
      ]]
      = (st' with clock := start, Rval [mltail])) /\
      LIST_REL store_entry_rel store' st'.refs /\
      ml_v_vals tail mltail /\
      st.ffi = st'.ffi
Proof
  Induct_on `vs`
  >> rpt strip_tac
  >> qpat_x_assum `closure_in_env _ _ _` $ assume_tac o EVAL_RULE
  >> gvs[allocate_list_def, vcons_list_def, scheme_cons_env_simp]
  >> qrefine `ck+1`
  >> simp[evaluate_def, dec_clock_def]
  >> simp[do_opapp_def]
  >> simp[Ntimes find_recfun_def 2, Ntimes build_rec_env_def 2]
  >> simp[Ntimes evaluate_def 2, can_pmatch_all_def, pmatch_def, nsLookup_def,
    same_type_def, same_ctor_def, evaluate_match_def, pat_bindings_def]
  >- (
    simp[evaluate_def, do_con_check_def, build_conv_def, nsLookup_def]
    >> qexists `0`
    >> simp[Once ml_v_vals_cases]
    >> first_assum $ irule_at $ Pat `LIST_REL _ _ _`
    >> simp[]
  )
  >> gvs[fresh_loc_def]
  >> rpt (pairarg_tac >> gvs[])
  >> simp[Ntimes evaluate_def 3, do_con_check_def, build_conv_def, nsLookup_def]
  >> qpat_abbrev_tac `newenv = env_list with v := _`
  >> last_x_assum $ drule_at_then (Pat `allocate_list _ _`) assume_tac
  >> rpt (pop_assum $ drule_at_then (Pat `LIST_REL _ _ _`) assume_tac)
  >> `closure_in_env newenv scheme_basis_list env_list`
    by (EVAL_TAC >> unabbrev_all_tac >> simp[])
  >> first_x_assum $ dxrule_at_then (Pat `closure_in_env _ _`) assume_tac
  >> pop_assum $ qspec_then `"ts'"` assume_tac
  >> unabbrev_all_tac
  >> gvs[scheme_runtime_funs_def]
  >> qexists `ck`
  >> simp[]
  >> simp[Once evaluate_def, do_app_def, store_alloc_def, SNOC_APPEND]
  >> qpat_abbrev_tac `newst = _ with refs := _`
  >> qexists `newst`
  >> unabbrev_all_tac
  >> simp[store_entry_rel_cases]
  >> simp[Once ml_v_vals_cases]
  >> irule $ GSYM LIST_REL_LENGTH
  >> first_assum $ irule_at $ Pos hd
QED

fun dup n x = if n = 0 then [] else x::dup (n-1) x;

fun reduce_to_cps ck (thms:thm list) = EVERY (dup ck $ qrefine ‘ck+1’)
    >> simp([GSYM exp_eval_def, GSYM val_eval_def, GSYM ex_eval_def, do_opapp_def, evaluate_def,
            do_con_check_def, build_conv_def, dec_clock_def, nsOptBind_def,
            do_app_def, can_pmatch_all_def, pmatch_def, store_lookup_def,
            same_type_def, same_ctor_def, pat_bindings_def, store_assign_def, store_v_same_type_def]
         @ thms)
    >> simp([exp_eval_def, val_eval_def, ex_eval_def] @ thms);

Theorem letinit_preservation:
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
      cont_rel k kv' ∧ cps_rel (Exp env e) var' mlenv' kv' mle' ∧
      LIST_REL store_entry_rel (letinit store env xvs) st'.refs ∧
      st.ffi = st'.ffi
Proof
  Induct_on ‘xvs’
  >> rpt strip_tac
  >> gvs[letinit_ml_def, letinit_def] >- (
    simp[GSYM eval_eq_def]
    >> irule_at (Pos hd) eval_eq_trivial
    >> simp[Once cps_rel_cases]
  )
  >> PairCases_on ‘h’
  >> simp[letinit_def]
  >> gvs[]
  >> qpat_assum ‘env_rel env _’ $ drule_then assume_tac
    o SRULE [env_rel_cases, FEVERY_DEF, SPECIFICATION]
  >> qpat_assum ‘can_lookup env _’ $ drule
    o SRULE [can_lookup_cases, FEVERY_DEF, SPECIFICATION]
  >> strip_tac
  >> drule_then assume_tac EVERY2_LENGTH
  >> drule_all_then assume_tac $ cj 2 $ iffLR LIST_REL_EL_EQN
  >> gvs[store_entry_rel_cases]
  >> (reduce_to_cps 0 []
  >> qpat_abbrev_tac `newst = st with refs := _`
  >> `st.ffi = newst.ffi` by (unabbrev_all_tac >> simp[])
  >> pop_assum $ simp o single
  >> last_x_assum irule
  >> unabbrev_all_tac
  >> first_assum $ irule_at $ Pos last
  >> simp[]
  >> irule_at (Pos hd) EVERY_MONOTONIC
  >> last_assum $ irule_at $ Pat `EVERY _ _`
  >> strip_tac >- (
    rpt strip_tac
    >> irule valid_val_LUPDATE_same
    >> simp[]
  )
  >> gvs[can_lookup_LUPDATE_same]
  >> irule EVERY2_LUPDATE_same
  >> simp[store_entry_rel_cases])
QED

Theorem application_preservation:
  ∀ store store' env env' fn vs e' ks ks' (st : 'ffi state) t mlfn ts mlvs mlenv k kv mle .
    application store ks fn vs = (store',ks',e') ∧
    valid_val store fn ∧
    EVERY (valid_val store) vs ∧
    valid_cont store ks ∧
    cont_rel ks kv ∧
    LIST_REL store_entry_rel store st.refs ∧
    nsLookup mlenv.v (Short k) = SOME kv ∧
    ml_v_vals fn mlfn ∧
    nsLookup mlenv.v (Short t) = SOME mlfn ∧
    LIST_REL ml_v_vals vs mlvs ∧
    LIST_REL (λx mlv. nsLookup mlenv.v (Short x) = SOME mlv) ts mlvs ∧
    scheme_env mlenv ∧
    env_rel env mlenv
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
      cont_rel ks' kv' ∧
      cps_rel e' k' mlenv' kv' mle'∧
      LIST_REL store_entry_rel store' st'.refs ∧
      st.ffi = st'.ffi
Proof
  rpt strip_tac
  >> drule_all_then assume_tac cons_list_val
  >> drule $ cj 2 $ iffLR scheme_env_def
  >> strip_tac
  >> gvs[Once ml_v_vals_cases, prim_val_rel_cases]
  >> qrefine ‘ck+3’
  >> simp[Ntimes evaluate_def 10, do_opapp_def, dec_clock_def,
       Ntimes find_recfun_def 2, Ntimes build_rec_env_def 2]
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
  >~ [`Prim SMul`] >- (
    drule $ cj 3 $ iffLR scheme_env_app_def
    >> strip_tac
    >> gvs[application_def]
    >> qrefine ‘ck+2’
    >> simp[evaluate_def]
    >> simp[do_opapp_def, dec_clock_def]
    >> simp[Ntimes find_recfun_def 2, Ntimes build_rec_env_def 2]
    >> simp[Ntimes evaluate_def 2]
    >> `? n . 1:int = n` by simp[]
    >> pop_assum $ simp_tac std_ss o single
    >> rpt $ pop_assum mp_tac
    >> qid_spec_tac `n`
    >> qid_spec_tac `vs`
    >> qid_spec_tac `ts`
    >> Induct_on `mlvs`
    >> rpt strip_tac >- (
      fs[cons_list_def, vcons_list_def, smul_def]
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
      >> simp[smul_def]
      >> simp[Once INT_MUL_COMM]
      >> last_x_assum irule
      >> simp[]
      >> last_assum $ irule_at $ Pos last
      >> irule cons_list_val
      >> simp[]
    )
    >> simp[smul_def]
    >> simp[GSYM eval_eq_def]
    >> irule_at (Pos hd) eval_eq_trivial
    >> simp[Once cps_rel_cases]
    >> first_assum $ irule_at $ Pos hd
  )
  >~ [`Prim SMinus`] >- (
    drule $ cj 12 $ iffLR scheme_env_app_def
    >> strip_tac
    >> gvs[application_def]
    >> qrefine ‘ck+1’
    >> simp[evaluate_def]
    >> simp[do_opapp_def, dec_clock_def]
    >> simp[Once evaluate_def]
    >> Cases_on `mlvs`
    >> gvs[vcons_list_def] >>> LASTGOAL (
      rename1 `vcons_list mlvs`
      >> rename1 `LIST_REL ml_v_vals vs mlvs`
      >> gvs[Once ml_v_vals_cases] >~ [`SNum i`] >>> HEADGOAL (
        Cases_on `mlvs = []`
        >> gvs[vcons_list_def] >>> LASTGOAL (
          ‘∃ mlv' mlvs' . mlv'::mlvs'=mlvs’ by (Cases_on ‘mlvs’ >> gvs[])
          >> ‘∃ v' vs' . v'::vs' = vs’ by gvs[]
          >> first_assum $ simp_tac bool_ss o single o GSYM
          >> simp[sminus_def]
          >> pop_assum $ simp_tac bool_ss o single
          >> simp[Ntimes evaluate_def 2, can_pmatch_all_def, pmatch_def, nsLookup_def,
            same_type_def, same_ctor_def, evaluate_match_def,
            pat_bindings_def, opn_lookup_def]
          >> simp[Ntimes evaluate_def 2, can_pmatch_all_def, pmatch_def, nsLookup_def,
            same_type_def, same_ctor_def, evaluate_match_def,
            pat_bindings_def, opn_lookup_def]
          >> simp[Ntimes evaluate_def 3]
          >> pop_assum $ simp_tac bool_ss o single o (fn x => Ntimes x 2) o GSYM
          >> simp[evaluate_match_def, can_pmatch_all_def, pmatch_def, nsLookup_def,
            same_type_def, same_ctor_def, evaluate_match_def,
            pat_bindings_def, opn_lookup_def, vcons_list_def]
          >> pop_assum kall_tac
          >> qrefine `ck+3`
          >> simp[Ntimes evaluate_def 3, can_pmatch_all_def, pmatch_def, nsLookup_def,
            same_type_def, same_ctor_def, evaluate_match_def,
            pat_bindings_def]
          >> simp[Ntimes evaluate_def 7, do_opapp_def]
          >> simp[Ntimes find_recfun_def 2, Ntimes build_rec_env_def 2]
          >> simp[Ntimes evaluate_def 2, dec_clock_def]
          >> ‘∃ n . 0i = n’ by simp[]
          >> pop_assum $ simp o single
          >> qpat_abbrev_tac `env_sminus' = env_sminus with v := _`
          >> ‘nsLookup env_sminus'.v (Short "n") = SOME (Litv (IntLit i))’ by (unabbrev_all_tac >> gvs[])
          >> ‘nsLookup env_sminus'.v (Short "k") = SOME kv’ by (unabbrev_all_tac >> gvs[])
          >> ‘env_sminus'.c = env_sminus.c’ by (unabbrev_all_tac >> gvs[])
          >> qpat_x_assum ‘Abbrev _’ kall_tac
          >> qpat_x_assum ‘! _ . _’ kall_tac
          >> gvs[]
          >> qpat_x_assum `LIST_REL (\ _ _ . nsLookup _ _ = _) _ _` kall_tac
          >> rpt $ pop_assum mp_tac
          >> qid_spec_tac ‘n’
          >> qid_spec_tac ‘mlvs’
          >> qid_spec_tac ‘vs’
          >> Induct_on `mlvs`
          >> Cases_on `vs`
          >> rpt strip_tac
          >> gvs[vcons_list_def] >- (
            simp[sadd_def]
            >> reduce_to_cps 0 [can_pmatch_all_def, pmatch_def, nsLookup_def,
              same_type_def, same_ctor_def, evaluate_match_def,
              pat_bindings_def]
            >> simp[Once evaluate_def]
            >> reduce_to_cps 1 [can_pmatch_all_def, pmatch_def, nsLookup_def,
              same_type_def, same_ctor_def, evaluate_match_def,
              pat_bindings_def, opn_lookup_def]
            >> simp[GSYM eval_eq_def]
            >> irule_at (Pos hd) eval_eq_trivial
            >> simp[Once cps_rel_cases, Once ml_v_vals_cases]
          )
          >> gvs[Once ml_v_vals_cases]
          >~ [‘sadd (SNum m::_) _’] >- (
            simp[sadd_def, vcons_list_def]
            >> simp[evaluate_def, do_opapp_def, do_app_def,
              opn_lookup_def, can_pmatch_all_def, pmatch_def, nsLookup_def,
              same_type_def, same_ctor_def, evaluate_match_def,
              pat_bindings_def, do_con_check_def, build_conv_def, dec_clock_def]
            >> simp[Ntimes find_recfun_def 2, Ntimes build_rec_env_def 2]
            >> qrefine ‘ck+3’
            >> simp[Ntimes evaluate_def 2]
            >> simp[Once INT_ADD_COMM]
            >> last_x_assum irule
          )
        )
      )
    )
    >> reduce_to_cps 0 [can_pmatch_all_def, pmatch_def, nsLookup_def,
      same_type_def, same_ctor_def, evaluate_match_def,
      pat_bindings_def, opn_lookup_def]
    >> simp[sminus_def, sadd_def]
    >> simp[GSYM eval_eq_def]
    >> irule_at (Pos hd) eval_eq_trivial
    >> simp[Once cps_rel_cases, Once ml_v_vals_cases]
    >> first_assum $ irule_at $ Pos hd
  )
  >~ [`Prim SEqv`] >- (
    drule $ cj 4 $ iffLR scheme_env_app_def
    >> strip_tac
    >> gvs[application_def]
    >> qrefine ‘ck+1’
    >> simp[evaluate_def]
    >> simp[do_opapp_def, dec_clock_def]
    >> simp[Once evaluate_def]
    >> Cases_on `mlvs`
    >> Cases_on `vs`
    >> gvs[vcons_list_def, seqv_def] >>> LASTGOAL (
      rename1 `vcons_list mlvs`
      >> rename1 `LIST_REL ml_v_vals vs mlvs`
      >> simp[Ntimes evaluate_def 2, can_pmatch_all_def, pmatch_def, nsLookup_def,
        same_type_def, same_ctor_def, evaluate_match_def,
        pat_bindings_def, opn_lookup_def]
      >> Cases_on `mlvs`
      >> Cases_on `vs`
      >> gvs[vcons_list_def, seqv_def] >>> LASTGOAL (
        rename1 `vcons_list mlvs`
        >> rename1 `LIST_REL ml_v_vals vs mlvs`
        >> simp[Ntimes evaluate_def 2, can_pmatch_all_def, pmatch_def, nsLookup_def,
          same_type_def, same_ctor_def, evaluate_match_def,
          pat_bindings_def, opn_lookup_def]
        >> Cases_on `mlvs`
        >> Cases_on `vs`
        >> gvs[vcons_list_def, seqv_def] >- (
          reduce_to_cps 0 [can_pmatch_all_def, pmatch_def, nsLookup_def,
            same_type_def, same_ctor_def, evaluate_match_def,
            pat_bindings_def, opn_lookup_def]
          >> gvs[Once ml_v_vals_cases]
          >~ [`SNum n`] >- (
            gvs[Once ml_v_vals_cases]
            >> reduce_to_cps 0 [can_pmatch_all_def, pmatch_def, nsLookup_def,
              do_eq_def, Boolv_def, bool_type_num_def, ctor_same_type_def, lit_same_type_def]
            >> simp[GSYM eval_eq_def]
            >> irule_at (Pos hd) eval_eq_trivial
            >> simp[Once cps_rel_cases, Once ml_v_vals_cases, bool_val_rel_cases]
            >> IF_CASES_TAC
            >> simp[]
          )
          >~ [`bool_val_rel b _`] >- (
            gvs[Once ml_v_vals_cases]
            >> reduce_to_cps 0 [can_pmatch_all_def, pmatch_def, nsLookup_def,
              do_eq_def, Boolv_def, bool_type_num_def, ctor_same_type_def]
            >> gvs[bool_val_rel_cases]
            >> reduce_to_cps 0 [can_pmatch_all_def, pmatch_def, nsLookup_def,
              do_eq_def, Boolv_def, bool_type_num_def, ctor_same_type_def]
            >> simp[GSYM eval_eq_def]
            >> irule_at (Pos hd) eval_eq_trivial
            >> simp[Once cps_rel_cases, Once ml_v_vals_cases, bool_val_rel_cases]
          )
          >> reduce_to_cps 0 [can_pmatch_all_def, pmatch_def, nsLookup_def,
            do_eq_def, Boolv_def, bool_type_num_def, ctor_same_type_def]
          >> simp[GSYM eval_eq_def]
          >> irule_at (Pos hd) eval_eq_trivial
          >> simp[Once cps_rel_cases, Once ml_v_vals_cases, bool_val_rel_cases]
          (*At some point I will need to find a way to evaluate a match
          expression without expanding all val cases, based on non-equality,
          because these rewrites take far too long*)
        )
      )
    )
    >> reduce_to_cps 0 [can_pmatch_all_def, vcons_list_def, pmatch_def, nsLookup_def]
    >> simp[GSYM eval_eq_def]
    >> irule_at (Pos hd) eval_eq_trivial
    >> simp[Once cps_rel_cases]
    >> first_assum $ irule_at $ Pos hd
  )
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
    >> last_x_assum kall_tac
    >> last_x_assum kall_tac
    >> last_x_assum kall_tac
    >> qpat_x_assum `! _._` kall_tac
    >> qpat_x_assum `scheme_env mlenv` kall_tac
    >> qpat_x_assum `env_rel _ mlenv` kall_tac
    >> qpat_x_assum `scheme_env_app _` kall_tac
    >> rpt $ qpat_x_assum `nsLookup mlenv.v _ = _` kall_tac
    >> qpat_x_assum `LIST_REL _ ts _` kall_tac
    >> qpat_abbrev_tac `proc_env' = proc_env with v:= _`
    >> `scheme_env proc_env'` by (unabbrev_all_tac >> rpt scheme_env_tac)
    >> `env_rel se proc_env'` by simp[Abbr `proc_env'`]
    >> `nsLookup proc_env'.v (Short "ts") = SOME (vcons_list mlvs)` by simp[Abbr `proc_env'`]
    >> `nsLookup proc_env'.v (Short "k") = SOME kv` by simp[Abbr `proc_env'`]
    >> qpat_x_assum `Abbrev _` kall_tac
    >> qpat_x_assum `scheme_env proc_env` kall_tac
    >> qpat_x_assum `env_rel _ proc_env` kall_tac
    >> rpt $ pop_assum mp_tac
    >> qid_spec_tac `se`
    >> qid_spec_tac `proc_env'`
    >> qid_spec_tac `store`
    >> qid_spec_tac `st`
    >> qid_spec_tac `vs`
    >> qid_spec_tac `mlvs`
    >> Induct_on ‘xs’
    >> rpt strip_tac
    >> gvs[]
    >- (
      Cases_on ‘xp’
      >> gvs[proc_ml_def] >- (
        Cases_on ‘vs’
        >> gvs[parameterize_def]
        >> reduce_to_cps 0 [can_pmatch_all_def, vcons_list_def, pmatch_def]
        >> simp[GSYM eval_eq_def]
        >> irule_at (Pos hd) eval_eq_trivial
        >> first_assum $ irule_at $ Pat ‘cont_rel _ _’
        >> simp[Once cps_rel_cases]
      )
      >> gvs[parameterize_def, fresh_loc_def]
      >> rpt (pairarg_tac >> gvs[])
      >> simp[Ntimes evaluate_def 3, nsOptBind_def, dec_clock_def,
        do_con_check_def, build_conv_def, do_opapp_def]

      >> drule_at_then (Pat `allocate_list _ _ = _`) assume_tac allocate_list_ml
      >> rpt $ pop_assum $ drule_at_then (Pat `LIST_REL _ _ _`) assume_tac
      >> drule_then assume_tac $ cj 1 $ iffLR scheme_env_def
      >> drule $ cj 3 $ iffLR scheme_env_def
      >> strip_tac
      >> `closure_in_env proc_env' scheme_basis_list env_list` by (EVAL_TAC >> simp[])
      >> first_x_assum $ drule_at_then (Pat `closure_in_env _ _ _`) assume_tac
      >> pop_assum $ qspec_then `"ts"` assume_tac
      >> gvs[scheme_cons_env_simp, scheme_runtime_funs_def]
      >> qrefine `ck + ck'`
      >> simp[do_app_def, store_alloc_def]
      >> simp[GSYM eval_eq_def]
      >> irule_at (Pos hd) eval_eq_trivial
      >> simp[SNOC_APPEND]
      >> first_assum $ irule_at $ Pos hd
      >> simp[Once cps_rel_cases]
      >> rpt scheme_env_tac
      >> simp[store_entry_rel_cases]
      >> gvs[env_rel_cases]
      >> rename1 `explode x`
      >> Cases_on ‘x ∈ FDOM se’ >- (
        simp[FEVERY_DEF, SNOC_APPEND]
        >> strip_tac
        >> rename1 `x' = x`
        >> Cases_on ‘x' = x’
        >> gvs[] >- (
          irule $ GSYM LIST_REL_LENGTH
          >> first_assum $ irule_at $ Pos hd
        )
        >> strip_tac
        >> gvs[FEVERY_DEF]
        >> simp[FAPPLY_FUPDATE_THM]
      )
      >> irule $ cj 2 FEVERY_STRENGTHEN_THM
      >> simp[]
      >> irule_at (Pos hd) $ GSYM LIST_REL_LENGTH
      >> first_assum $ irule_at $ Pos hd
      >> simp[FEVERY_DEF]
      >> rpt strip_tac
      >> ‘x ≠ x'’ by (strip_tac >> gvs[])
      >> gvs[FEVERY_DEF]
    )
    >> simp[proc_ml_def]
    >> Cases_on ‘vs’
    >> gvs[parameterize_def] >- (
      first_assum $ irule_at (Pat ‘cont_rel _ _’)
      >> reduce_to_cps 0 [can_pmatch_all_def, vcons_list_def, pmatch_def]
      >> simp[GSYM eval_eq_def]
      >> irule_at (Pos hd) eval_eq_trivial
      >> simp[Once cps_rel_cases]
    )
    >> reduce_to_cps 0 [can_pmatch_all_def, vcons_list_def, pmatch_def, store_alloc_def]
    >> qpat_abbrev_tac `new_st = st with refs := new_refs`
    >> `st.ffi = new_st.ffi` by (unabbrev_all_tac >> simp[])
    >> pop_assum $ simp o single
    >> last_x_assum irule
    >> unabbrev_all_tac
    >> simp[]
    >> irule_at Any EQ_REFL
    >> rpt scheme_env_tac
    >> gvs[fresh_loc_def]
    >> first_assum $ irule_at $ Pat `parameterize _ _ _ _ _ _ = _`
    >> simp[SNOC_APPEND]
    >> simp[Once store_entry_rel_cases]
    >> rename1 `env_rel env proc_env'`
    >> gvs[env_rel_cases]
    >> rename1 `explode x`
    >> Cases_on ‘x ∈ FDOM env’ >- (
      simp[FEVERY_DEF, SNOC_APPEND]
      >> strip_tac
      >> rename1 `x' = x`
      >> Cases_on ‘x' = x’
      >> gvs[] >- (
        irule $ GSYM LIST_REL_LENGTH
        >> first_assum $ irule_at $ Pos hd
      )
      >> strip_tac
      >> gvs[FEVERY_DEF]
      >> simp[FAPPLY_FUPDATE_THM]
    )
    >> irule $ cj 2 FEVERY_STRENGTHEN_THM
    >> simp[]
    >> rev_drule_then assume_tac $ LIST_REL_LENGTH
    >> simp[FEVERY_DEF]
    >> rpt strip_tac
    >> ‘x ≠ x'’ by (strip_tac >> gvs[])
    >> gvs[FEVERY_DEF]
  )
  >~ [`Prim CallCC`] >- (
    gvs[application_def]
    >> qrefine ‘ck+1’
    >> simp[evaluate_def]
    >> simp[do_opapp_def, dec_clock_def]
    >> simp[Ntimes find_recfun_def 2, Ntimes build_rec_env_def 2]
    >> simp[Once evaluate_def]
    >> Cases_on `mlvs`
    >> Cases_on `vs`
    >> gvs[vcons_list_def] >>> LASTGOAL (
      rename1 `vcons_list mlvs`
      >> rename1 `LIST_REL ml_v_vals vs mlvs`
      >> simp[Ntimes evaluate_def 2, can_pmatch_all_def, pmatch_def, nsLookup_def,
        same_type_def, same_ctor_def, evaluate_match_def,
        pat_bindings_def, opn_lookup_def]
      >> Cases_on `mlvs`
      >> Cases_on `vs`
      >> gvs[vcons_list_def] >- (
        reduce_to_cps 0 [can_pmatch_all_def, vcons_list_def, pmatch_def, nsLookup_def]
        >> simp[GSYM eval_eq_def]
        >> irule_at (Pos hd) eval_eq_trivial
        >> simp[Once cps_rel_cases, Once ml_v_vals_cases]
        >> simp[Once cont_rel_cases]
        >> simp[cps_transform_def, cps_app_ts_def, cons_list_def]
        >> drule_then assume_tac $ cj 1 $ iffLR scheme_env_app_def
        >> gvs[scheme_env_def, scheme_env_app_def]
      )
    )
    >> reduce_to_cps 0 [can_pmatch_all_def, vcons_list_def, pmatch_def, nsLookup_def]
    >> simp[GSYM eval_eq_def]
    >> irule_at (Pos hd) eval_eq_trivial
    >> simp[Once cps_rel_cases]
    >> first_assum $ irule_at $ Pos hd
  )
  >~ [`Throw ks`] >- (
    drule $ cj 10 $ iffLR scheme_env_app_def
    >> strip_tac
    >> gvs[application_def]
    >> qrefine ‘ck+1’
    >> simp[evaluate_def]
    >> simp[do_opapp_def, dec_clock_def]
    >> simp[Ntimes find_recfun_def 2, Ntimes build_rec_env_def 2]
    >> simp[Once evaluate_def]
    >> Cases_on `mlvs`
    >> Cases_on `vs`
    >> gvs[vcons_list_def] >>> LASTGOAL (
      rename1 `vcons_list mlvs`
      >> rename1 `LIST_REL ml_v_vals vs mlvs`
      >> simp[Ntimes evaluate_def 2, can_pmatch_all_def, pmatch_def, nsLookup_def,
        same_type_def, same_ctor_def, evaluate_match_def,
        pat_bindings_def, opn_lookup_def]
      >> Cases_on `mlvs`
      >> Cases_on `vs`
      >> gvs[vcons_list_def]
    )
    >> reduce_to_cps 0 [can_pmatch_all_def, vcons_list_def, pmatch_def, nsLookup_def]
    >> simp[GSYM eval_eq_def]
    >> irule_at (Pos hd) eval_eq_trivial
    >> simp[Once cps_rel_cases]
    >> first_assum $ irule_at $ Pos hd
  )
  >~ [`Prim Cons`] >- (
    drule $ cj 5 $ iffLR scheme_env_app_def
    >> strip_tac
    >> gvs[application_def]
    >> qrefine ‘ck+1’
    >> simp[evaluate_def]
    >> simp[do_opapp_def, dec_clock_def]
    >> simp[Once evaluate_def]
    >> Cases_on `mlvs`
    >> Cases_on `vs`
    >> gvs[vcons_list_def] >>> LASTGOAL (
      rename1 `vcons_list mlvs`
      >> rename1 `LIST_REL ml_v_vals vs mlvs`
      >> simp[Ntimes evaluate_def 2, can_pmatch_all_def, pmatch_def, nsLookup_def,
        same_type_def, same_ctor_def, evaluate_match_def,
        pat_bindings_def, opn_lookup_def]
      >> Cases_on `mlvs`
      >> Cases_on `vs`
      >> gvs[vcons_list_def] >>> LASTGOAL (
        rename1 `vcons_list mlvs`
        >> rename1 `LIST_REL ml_v_vals vs mlvs`
        >> simp[Ntimes evaluate_def 2, can_pmatch_all_def, pmatch_def, nsLookup_def,
          same_type_def, same_ctor_def, evaluate_match_def,
          pat_bindings_def, opn_lookup_def]
        >> Cases_on `mlvs`
        >> Cases_on `vs`
        >> gvs[vcons_list_def] >- (
          reduce_to_cps 0 [can_pmatch_all_def, vcons_list_def, pmatch_def, store_alloc_def, nsLookup_def]
          >> gvs[fresh_loc_def]
          >> simp[GSYM eval_eq_def]
          >> irule_at (Pos hd) eval_eq_trivial
          >> simp[Once cps_rel_cases, SNOC, SNOC_APPEND]
          >> simp[Once ml_v_vals_cases]
          >> simp[Once store_entry_rel_cases]
          >> irule $ GSYM LIST_REL_LENGTH
          >> first_assum $ irule_at $ Pos hd
        )
      )
    )
    >> reduce_to_cps 0 [can_pmatch_all_def, vcons_list_def, pmatch_def, nsLookup_def]
    >> gvs[application_def]
    >> simp[GSYM eval_eq_def]
    >> irule_at (Pos hd) eval_eq_trivial
    >> simp[Once cps_rel_cases]
    >> first_assum $ irule_at $ Pos hd
  )
  >~ [`Prim Car`] >- (
    drule $ cj 6 $ iffLR scheme_env_app_def
    >> strip_tac
    >> gvs[application_def]
    >> qrefine ‘ck+1’
    >> simp[evaluate_def]
    >> simp[do_opapp_def, dec_clock_def]
    >> simp[Once evaluate_def]
    >> Cases_on `mlvs`
    >> Cases_on `vs`
    >> gvs[vcons_list_def] >>> LASTGOAL (
      rename1 `vcons_list mlvs`
      >> rename1 `LIST_REL ml_v_vals vs mlvs`
      >> simp[Ntimes evaluate_def 2, can_pmatch_all_def, pmatch_def, nsLookup_def,
        same_type_def, same_ctor_def, evaluate_match_def,
        pat_bindings_def, opn_lookup_def]
      >> Cases_on `mlvs`
      >> Cases_on `vs`
      >> gvs[vcons_list_def] >>> HEADGOAL (
        rename1 `ml_v_vals v mlv`
        >> Cases_on `? l . v = PairP l`
        >> gvs[Once ml_v_vals_cases]
        >> rfs[Once valid_val_cases] >>> HEADGOAL (
          drule $ iffLR LIST_REL_EL_EQN
          >> strip_tac
          >> pop_assum $ drule_then assume_tac
          >> gvs[Once store_entry_rel_cases]
        )
      )
    )
    >> reduce_to_cps 0 [can_pmatch_all_def, vcons_list_def, pmatch_def, nsLookup_def]
    >> simp[GSYM eval_eq_def]
    >> irule_at (Pos hd) eval_eq_trivial
    >> simp[Once cps_rel_cases]
    >> first_assum $ irule_at $ Pos hd
  )
  >~ [`Prim Cdr`] >- (
    drule $ cj 7 $ iffLR scheme_env_app_def
    >> strip_tac
    >> gvs[application_def]
    >> qrefine ‘ck+1’
    >> simp[evaluate_def]
    >> simp[do_opapp_def, dec_clock_def]
    >> simp[Once evaluate_def]
    >> Cases_on `mlvs`
    >> Cases_on `vs`
    >> gvs[vcons_list_def] >>> LASTGOAL (
      rename1 `vcons_list mlvs`
      >> rename1 `LIST_REL ml_v_vals vs mlvs`
      >> simp[Ntimes evaluate_def 2, can_pmatch_all_def, pmatch_def, nsLookup_def,
        same_type_def, same_ctor_def, evaluate_match_def,
        pat_bindings_def, opn_lookup_def]
      >> Cases_on `mlvs`
      >> Cases_on `vs`
      >> gvs[vcons_list_def] >>> HEADGOAL (
        rename1 `ml_v_vals v mlv`
        >> Cases_on `? l . v = PairP l`
        >> gvs[Once ml_v_vals_cases]
        >> rfs[Once valid_val_cases] >>> HEADGOAL (
          drule $ iffLR LIST_REL_EL_EQN
          >> strip_tac
          >> pop_assum $ drule_then assume_tac
          >> gvs[Once store_entry_rel_cases]
        )
      )
    )
    >> reduce_to_cps 0 [can_pmatch_all_def, vcons_list_def, pmatch_def, nsLookup_def]
    >> simp[GSYM eval_eq_def]
    >> irule_at (Pos hd) eval_eq_trivial
    >> simp[Once cps_rel_cases]
    >> first_assum $ irule_at $ Pos hd
  )
  >~ [`Prim IsNull`] >- (
    drule $ cj 8 $ iffLR scheme_env_app_def
    >> strip_tac
    >> gvs[application_def]
    >> qrefine ‘ck+1’
    >> simp[evaluate_def]
    >> simp[do_opapp_def, dec_clock_def]
    >> simp[Once evaluate_def]
    >> Cases_on `mlvs`
    >> Cases_on `vs`
    >> gvs[vcons_list_def] >>> LASTGOAL (
      rename1 `vcons_list mlvs`
      >> rename1 `LIST_REL ml_v_vals vs mlvs`
      >> simp[Ntimes evaluate_def 2, can_pmatch_all_def, pmatch_def, nsLookup_def,
        same_type_def, same_ctor_def, evaluate_match_def,
        pat_bindings_def, opn_lookup_def]
      >> Cases_on `mlvs`
      >> Cases_on `vs`
      >> gvs[vcons_list_def] >>> HEADGOAL (gvs[Once ml_v_vals_cases])
    )
    >> reduce_to_cps 0 [can_pmatch_all_def, vcons_list_def, pmatch_def, nsLookup_def]
    >> simp[GSYM eval_eq_def]
    >> irule_at (Pos hd) eval_eq_trivial
    >> simp[Once cps_rel_cases]
    >> simp[Once ml_v_vals_cases, bool_val_rel_cases]
    >> first_assum $ irule_at $ Pos hd
  )
  >~ [`Prim IsPair`] >- (
    drule $ cj 9 $ iffLR scheme_env_app_def
    >> strip_tac
    >> gvs[application_def]
    >> qrefine ‘ck+1’
    >> simp[evaluate_def]
    >> simp[do_opapp_def, dec_clock_def]
    >> simp[Once evaluate_def]
    >> Cases_on `mlvs`
    >> Cases_on `vs`
    >> gvs[vcons_list_def] >>> LASTGOAL (
      rename1 `vcons_list mlvs`
      >> rename1 `LIST_REL ml_v_vals vs mlvs`
      >> simp[Ntimes evaluate_def 2, can_pmatch_all_def, pmatch_def, nsLookup_def,
        same_type_def, same_ctor_def, evaluate_match_def,
        pat_bindings_def, opn_lookup_def]
      >> Cases_on `mlvs`
      >> Cases_on `vs`
      >> gvs[vcons_list_def] >>> HEADGOAL (gvs[Once ml_v_vals_cases])
    )
    >> reduce_to_cps 0 [can_pmatch_all_def, vcons_list_def, pmatch_def, nsLookup_def]
    >> simp[GSYM eval_eq_def]
    >> irule_at (Pos hd) eval_eq_trivial
    >> simp[Once cps_rel_cases]
    >> simp[Once ml_v_vals_cases, bool_val_rel_cases]
    >> first_assum $ irule_at $ Pos hd
  )
  >> reduce_to_cps 0 []
  >> gvs[application_def]
  >> simp[GSYM eval_eq_def]
  >> irule_at (Pos hd) eval_eq_trivial
  >> simp[Once cps_rel_cases]
  >> first_assum $ irule_at $ Pos hd
QED

Theorem step_preservation:
  ∀ store store' e e' ks ks' (st : 'ffi state) mlenv k kv mle .
    step (store, ks, e) = (store', ks', e') ∧
    valid_state store ks e ∧
    cont_rel ks kv ∧
    cps_rel e k mlenv kv mle ∧
    LIST_REL store_entry_rel store st.refs
    ⇒
    ∃ ck st' mlenv' k' kv' mle' .
      (∀ start . evaluate (st with clock := start + ck) mlenv [mle]
      =
      evaluate (st' with clock := start) mlenv' [mle']) ∧
      cont_rel ks' kv' ∧
      cps_rel e' k' mlenv' kv' mle' ∧
      LIST_REL store_entry_rel store' st'.refs ∧
      (¬ terminating_state (store', ks', e') ⇒ 0 < ck) ∧
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
      Cases_on ‘bs’
      >> rpt strip_tac
      >> gvs[cps_transform_def, Excl "MAP"] >- (
        reduce_to_cps 1 [letpreinit_ml_def, letinit_ml_def]
        >> simp[GSYM eval_eq_def]
        >> irule_at (Pos hd) eval_eq_trivial
        >> first_assum $ irule_at $ Pos hd
        >> simp[Once cps_rel_cases]
        >> rpt scheme_env_tac
      )
      >> PairCases_on ‘h’
      >> gvs[]
      >> simp[cps_transform_def]
      >> rpt (pairarg_tac >> gvs[])
      >> reduce_to_cps 1 [store_alloc_def]
      >> qpat_abbrev_tac `mlenv' = mlenv with v := _`
      >> `scheme_env mlenv'` by (unabbrev_all_tac >> rpt scheme_env_tac)
      >> simp[letpreinit_ml_eval]
      >> gvs[letrec_preinit_APPEND]
      >> unabbrev_all_tac
      >> reduce_to_cps 0 []
      >> simp[GSYM eval_eq_def]
      >> irule_at (Pos hd) eval_eq_trivial
      >> simp[Once cps_rel_cases]
      >> simp[Once cont_rel_cases]
      >> first_assum $ irule_at $ Pos hd
      >> drule_then assume_tac LIST_REL_LENGTH
      >> simp[cps_app_ts_def, letpreinit_env_rel]
      >> simp[letrec_preinit_env_def, letpreinit_mlenv_def]
      >> rpt scheme_env_tac
      >> strip_tac >- (
        simp[nsLookup_nsAppend_some, id_to_mods_def,
          nsLookup_def, ALOOKUP_NONE, MEM_MAP]
        >> disj2_tac
        >> PairCases
        >> simp[]
      )
      >> strip_tac >- (
        gvs[scheme_env_def]
        >> simp[nsLookup_nsAppend_some, id_to_mods_def,
          nsLookup_def, ALOOKUP_NONE, MEM_MAP]
        >> first_assum $ irule_at $ Pos hd
        >> qexists `env_list`
        >> simp[]
        >> rpt strip_tac
        >> disj2_tac
        >> PairCases
        >> simp[]
      )
      >> irule LIST_REL_APPEND_suff
      >> simp[LIST_REL_EL_EQN, Once store_entry_rel_cases]
    )
    >~ [‘Letrecstar bs e’] >- (
      simp[cps_transform_def]
      >> rpt strip_tac
      >> rpt (pairarg_tac >> gvs[])
      >> reduce_to_cps 1 [store_alloc_def]
      >> qpat_abbrev_tac `mlenv' = mlenv with v := _`
      >> `scheme_env mlenv'` by (unabbrev_all_tac >> rpt scheme_env_tac)
      >> simp[letpreinit_ml_eval]
      >> gvs[letrec_preinit_APPEND]
      >> unabbrev_all_tac
      >> simp[GSYM eval_eq_def]
      >> irule_at (Pos hd) eval_eq_trivial
      >> simp[Once cps_rel_cases]
      >> first_assum $ irule_at $ Pos hd
      >> simp[cps_transform_def]
      >> drule_then assume_tac LIST_REL_LENGTH
      >> simp[letpreinit_env_rel]
      >> simp[letrec_preinit_env_def, letpreinit_mlenv_def]
      >> strip_tac >- (
        simp[nsLookup_nsAppend_some, id_to_mods_def,
          nsLookup_def, ALOOKUP_NONE, MEM_MAP]
        >> disj2_tac
        >> PairCases
        >> simp[]
      )
      >> strip_tac >- (
        gvs[scheme_env_def]
        >> simp[nsLookup_nsAppend_some, id_to_mods_def,
          nsLookup_def, ALOOKUP_NONE, MEM_MAP]
        >> first_assum $ irule_at $ Pos hd
        >> qexists `env_list`
        >> simp[]
        >> rpt strip_tac
        >> disj2_tac
        >> PairCases
        >> simp[]
      )
      >> irule LIST_REL_APPEND_suff
      >> simp[LIST_REL_EL_EQN, Once store_entry_rel_cases]
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
      >> qpat_assum ‘env_rel _ _’ $ drule_then assume_tac
        o SRULE [env_rel_cases, FEVERY_DEF]
      >> qpat_assum ‘can_lookup _ _’ $ drule
        o SRULE [can_lookup_cases, FEVERY_DEF]
      >> strip_tac
      >> drule $ iffLR LIST_REL_EL_EQN
      >> strip_tac
      >> pop_assum $ drule_then assume_tac
      >> gvs[store_entry_rel_cases]
    )
    >> reduce_to_cps 1 []
    >> simp[GSYM eval_eq_def]
    >> irule_at (Pos hd) eval_eq_trivial
    >> TRY $ qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
    >> simp[Once cps_rel_cases]
    >> simp[Once ml_v_vals_cases, Once cont_rel_cases,
      bool_val_rel_cases, prim_val_rel_cases]
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
      >> simp[Once ml_v_vals_cases, bool_val_rel_cases]
      >> rpt strip_tac
      >> gvs[]
      >> simp[Once evaluate_def]
      >> reduce_to_cps 1 []
      >> simp[GSYM eval_eq_def]
      >> irule_at (Pos hd) eval_eq_trivial
      >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
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
      >> qpat_assum ‘env_rel _ _’ $ drule_then assume_tac
        o SRULE [env_rel_cases, FEVERY_DEF, SPECIFICATION]
      >> qpat_assum ‘can_lookup _ _’ $ drule
        o SRULE [can_lookup_cases, FEVERY_DEF, SPECIFICATION]
      >> strip_tac
      >> drule $ iffLR LIST_REL_EL_EQN
      >> strip_tac
      >> pop_assum $ drule_then assume_tac
      >> gvs[store_entry_rel_cases]
      >> simp[Once evaluate_def]
      >> reduce_to_cps 1 []
      >> simp[GSYM eval_eq_def]
      >> irule_at (Pos hd) eval_eq_trivial
      >> simp[]
      >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
      >> simp[Once cps_rel_cases, Once ml_v_vals_cases]
      >> irule EVERY2_LUPDATE_same
      >> simp[Once store_entry_rel_cases]
    )
    >> Cases_on ‘∃ xvs x bs e . h1 = LetinitK xvs x bs e’ >- (
      gvs[]
      >> Cases_on ‘bs’
      >> rpt strip_tac
      >> gvs[Once cont_rel_cases, Once cps_rel_cases]
      >> gvs[cps_transform_def, step_def, return_def]
      >> simp[Once evaluate_def]
      >> reduce_to_cps 1 [] >- (
        gvs[Once valid_state_cases]
        >> gvs[Once valid_cont_cases]
        >> ‘∃ xvs' . (x,v)::xvs = xvs'’ by simp[]
        >> first_assum $ simp_tac bool_ss o single
        >> ‘x::(MAP FST xvs) = MAP FST xvs'’ by gvs[]
        >> simp_tac bool_ss [Once $ cj 3 $ GSYM ZIP_def]
        >> first_assum $ simp_tac bool_ss o single
        >> drule cps_app_ts_distinct >> strip_tac
        >> ‘! x xs . Var (Short x)::MAP (Var o Short) xs = MAP (Var o Short) (x::xs)’ by gvs[]
        >> first_assum $ simp_tac bool_ss o single
        >> irule letinit_preservation
        >> drule cps_app_ts_distinct
        >> strip_tac
        >> gvs[]
        >> last_assum $ irule_at $ Pos last
        >> last_assum $ irule_at $ Pos last
        >> irule_at (Pos last) EQ_REFL
        >> irule_at Any EQ_REFL
        >> rpt scheme_env_tac
        >> irule_at (Pos last) EVERY2_MEM_MONO
        >> first_assum $ irule_at $ Pat ‘LIST_REL _ _ _’
        >> PairCases
        >> simp[]
        >> rpt strip_tac
        >> qpat_assum ‘LIST_REL _ ts mlvs’ $ assume_tac
        >> dxrule_then assume_tac EVERY2_LENGTH
        >> drule_at_then (Pos $ el 2) assume_tac $ cj 1 MEM_ZIP_MEM_MAP
        >> gvs[]
        >> qmatch_goalsub_abbrev_tac `nsLookup (nsBind x1 _ _) (Short x2) = SOME _`
        >> Cases_on ‘x1 = x2’
        >> gvs[]
      )
      >> PairCases_on ‘h’
      >> gvs[]
      >> simp[cps_transform_def]
      >> reduce_to_cps 0 []
      >> simp[GSYM eval_eq_def]
      >> irule_at (Pos hd) eval_eq_trivial
      >> simp[Once cps_rel_cases, Once cont_rel_cases]
      >> simp_tac bool_ss [Once $ GSYM ZIP_def]
      >> ‘! x xs . Var (Short x)::MAP (Var o Short) xs = MAP (Var o Short) (x::xs)’ by gvs[]
      >> first_assum $ simp_tac bool_ss o single
      >> irule_at (Pos hd) EQ_REFL
      >> simp[cps_app_ts_def]
      >> rpt (pairarg_tac >> gvs[])
      >> qpat_assum ‘LIST_REL _ ts mlvs’ $ assume_tac
      >> dxrule_then assume_tac EVERY2_LENGTH
      >> qpat_assum ‘LIST_REL ml_v_vals _ mlvs’ $ assume_tac
      >> dxrule_then assume_tac EVERY2_LENGTH
      >> gvs[]
      >> first_assum $ irule_at $ Pos hd
      >> first_assum $ irule_at (Pos $ el 2)
      >> drule $ GSYM cps_app_ts_distinct
      >> strip_tac
      >> simp[]
      >> irule_at (Pos hd) EVERY2_MEM_MONO
      >> first_assum $ irule_at (Pat ‘LIST_REL _ ts mlvs’)
      >> strip_tac >- (
        PairCases
        >> simp[]
        >> rpt strip_tac
        >> drule_at_then (Pos $ el 2) assume_tac $ cj 1 MEM_ZIP_MEM_MAP
        >> gvs[]
        >> qmatch_goalsub_abbrev_tac `nsLookup (nsBind x1 _ _) (Short x2) = SOME _`
        >> Cases_on ‘x1 = x2’
        >> gvs[]
      )
      >> rpt scheme_env_tac
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
      >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
      >> simp[cps_app_ts_def]
      >> rpt (pairarg_tac >> gvs[])
      >> qpat_assum ‘ml_v_vals _ _’ $ irule_at Any
      >> qpat_assum ‘LIST_REL ml_v_vals _ _’ $ irule_at Any
      >> drule $ GSYM cps_app_ts_distinct
      >> strip_tac
      >> simp[]
      >> irule_at (Pos hd) EVERY2_MEM_MONO
      >> first_assum $ irule_at $ Pat ‘LIST_REL _ _ _’
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
      >> simp[step_def, return_def]
      >> rpt strip_tac
      >> gvs[Once cps_rel_cases, Once cont_rel_cases]
      >> simp[Once evaluate_def]
      >> reduce_to_cps 1 []
      >> simp[cps_transform_def]
      >> simp_tac bool_ss [Once ADD_COMM]
      >> `cons_list [] = cons_list $ MAP (Var o Short) []` by simp[]
      >> pop_assum $ simp_tac bool_ss o single
      >> irule application_preservation
      >> simp[]
      >> rpt scheme_env_tac
      >> rpt $ first_assum $ irule_at $ Pos hd
      >> gvs[Once valid_state_cases]
      >> gvs[Once valid_cont_cases]
    )
    >> Cases_on ‘∃ fn vs . h1 = ApplyK (SOME (fn, vs)) []’ >- (
      gvs[]
      >> simp[step_def, return_def, Once cps_rel_cases]
      >> rpt strip_tac
      >> gvs[Once cont_rel_cases, Excl "MAP"]
      >> simp[Once evaluate_def]
      >> reduce_to_cps 1 [Excl "MAP"]
      >> gvs[cps_transform_def, Excl "MAP"]
      >> simp_tac bool_ss [GSYM MAP_REVERSE, Excl "MAP"]
      >> simp_tac bool_ss [Once ADD_COMM]
      >> irule application_preservation
      >> simp[]
      >> drule cps_app_ts_distinct >> strip_tac
      >> rpt scheme_env_tac
      >> first_assum $ irule_at $ Pat `application _ _ _ _ = _`
      >> first_assum $ irule_at $ Pos hd
      >> gvs[Once valid_state_cases]
      >> gvs[Once valid_cont_cases]
      >> qrefine `SNOC front lst`
      >> simp[SNOC_APPEND]
      >> rpt $ irule_at Any EVERY2_REVERSE
      >> first_assum $ irule_at $ Pos hd
      >> irule EVERY2_MEM_MONO
      >> first_assum $ irule_at $ Pat ‘LIST_REL _ _ _’
      >> qpat_x_assum ‘LIST_REL _ ts _’ $ assume_tac
      >> drule_then assume_tac EVERY2_LENGTH
      >> PairCases >> simp[]
      >> strip_tac
      >> drule_at_then (Pos last) assume_tac MEM_ZIP_MEM_MAP
      >> gvs[]
      >> qsuff_tac ‘x0 ≠ t''’
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
  ∀ n store store' e e' k k' (st : 'ffi state) mlenv var kv mle .
  FUNPOW step n (store, k, e) = (store', k', e') ∧
  valid_state store k e ∧
  cont_rel k kv ∧
  cps_rel e var mlenv kv mle ∧
  LIST_REL store_entry_rel store st.refs
  ⇒
  ∃ ck st' mlenv' var' kv' mle' .
    (∀ start . evaluate (st with clock := start + ck) mlenv [mle]
    =
    evaluate (st' with clock := start) mlenv' [mle']) ∧
    cont_rel k' kv' ∧
    cps_rel e' var' mlenv' kv' mle' ∧
    LIST_REL store_entry_rel store' st'.refs ∧
    (¬ terminating_state (store', k', e') ⇒ n ≤ ck) ∧
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
  >> first_x_assum drule_all
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
  ∀ n e v mle mlv store store' ks (st:'ffi state) mlenv var kv .
    FUNPOW step n (store, ks, e) = (store', [], Val v) ∧
    valid_state store ks e ∧
    cps_rel e var mlenv kv mle ∧
    cont_rel ks kv ∧
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
  >> qpat_x_assum ‘cps_rel (Val v) _ _ _ _’ $ mp_tac
    o SRULE [Once cps_rel_cases]
  >> rpt strip_tac
  >> gvs[]
  >> qpat_x_assum ‘cont_rel [] _’ $ mp_tac
    o SRULE [Once cont_rel_cases]
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
  ∀ e v mle mlv store store' ks (st:'ffi state) mlenv var kv .
    (∀ n . ¬ terminating_state (FUNPOW step n (store, ks, e))) ∧
    valid_state store ks e ∧
    cps_rel e var mlenv kv mle ∧
    cont_rel ks kv ∧
    LIST_REL store_entry_rel store st.refs
    ⇒
    ∀ ck . ∃ st' . evaluate (st with clock:=ck) mlenv [mle]
      = (st', Rerr (Rabort Rtimeout_error)) ∧
      st.ffi = st'.ffi
Proof
  rpt strip_tac
  >> last_x_assum $ qspec_then ‘ck’ assume_tac
  >> Cases_on ‘FUNPOW step ck (store,ks,e)’
  >> PairCases_on ‘r’
  >> drule_all steps_preservation
  >> rpt strip_tac
  >> gvs[]
  >> first_x_assum $ qspec_then ‘0’ assume_tac
  >> qpat_x_assum ‘cps_rel _ _ _ _ mle'’ $ assume_tac o SRULE [Once cps_rel_cases]
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

