(*
  Proofs for Scheme to CakeML compilation
*)
open preamble;
open computeLib;
open scheme_astTheory;
open scheme_semanticsTheory;
open scheme_to_cakeTheory;
open astTheory;

open evaluateTheory;
open evaluatePropsTheory;
open semanticPrimitivesTheory;
open namespaceTheory;
open primTypesTheory;
open namespacePropsTheory;
open integerTheory;

val _ = new_theory "scheme_proofs";

val _ = (max_print_depth := 50);

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
    "[]"; "::"; "Some"; "None"; "Ex"; "Proc"; "Throw";"SList"]
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

val (ml_v_vals'_rules,ml_v_vals'_ind,ml_v_vals'_cases) =
(fn (x,y,z) => (SRULE [] x,SRULE [] y, SRULE [] z)) $ Hol_reln ‘
  (ml_v_vals' (SBool T) $
    Conv (SOME (scheme_typestamp "SBool")) [Conv (SOME (scheme_typestamp "True")) []]) ∧
  (ml_v_vals' (SBool F) $
    Conv (SOME (scheme_typestamp "SBool")) [Conv (SOME (scheme_typestamp "False")) []]) ∧
  (ml_v_vals' (SNum n') $
    Conv (SOME (scheme_typestamp "SNum")) [Litv (IntLit n')]) ∧
  (ml_v_vals' (Prim SAdd) $
    Conv (SOME (scheme_typestamp "Prim")) [Conv (SOME (scheme_typestamp "SAdd")) []]) ∧
  (ml_v_vals' (Prim SMul) $
    Conv (SOME (scheme_typestamp "Prim")) [Conv (SOME (scheme_typestamp "SMul")) []]) ∧
  (ml_v_vals' (Prim SMinus) $
    Conv (SOME (scheme_typestamp "Prim")) [Conv (SOME (scheme_typestamp "SMinus")) []]) ∧
  (ml_v_vals' (Prim SEqv) $
    Conv (SOME (scheme_typestamp "Prim")) [Conv (SOME (scheme_typestamp "SEqv")) []]) ∧
  (ml_v_vals' (Prim CallCC) $
    Conv (SOME (scheme_typestamp "Prim")) [Conv (SOME (scheme_typestamp "CallCC")) []]) ∧

  (scheme_env env ∧
  env_rel se env ∧
  (m, ce) = cps_transform n e ∧
  args = "xs" ++ toString m ∧
  k = "k" ++ toString (m+1) ∧
  (l, inner) = proc_ml (m+2) xs xp k args ce
  ⇒
  ml_v_vals' (Proc se xs xp e) $
    Conv (SOME (scheme_typestamp "Proc")) [
      Closure env k $ Fun args inner
    ]) ∧
  (LIST_REL ml_v_vals' vs mlvs
  ⇒
  ml_v_vals' (SList vs) $
    Conv (SOME (scheme_typestamp "SList")) [vcons_list mlvs])
’;

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
  (m, ce) = cps_transform n e ∧
  nsLookup env.v (Short var) = SOME kv ∧
  scheme_env env
  ⇒
  e_ce_rel (Exp e) var env kv $ App Opapp [ce; Var (Short var)]
[~Exception:]
  e_ce_rel (Exception s) var env kv $
    Con (SOME $ Short "Ex") [Lit $ StrLit $ explode s]
End

Definition cps_app_ts_def:
  cps_app_ts n (e::es) = (let
    (m, ce) = cps_transform n e;
    t = "t" ++ toString m
  in
    t :: cps_app_ts (m+1) es) ∧

  cps_app_ts n [] = []
End

Inductive cont_rel:
[~Id:]
  scheme_env env ∧
  ¬ MEM t vconses
  ⇒
  cont_rel []
    (Closure env t (Var (Short t)))
[~CondK:]
  cont_rel ks kv ∧
  nsLookup env.v (Short var) = SOME kv ∧
  (n', ct) = cps_transform n te ∧
  (m', cf) = cps_transform m fe ∧
  scheme_env env ∧
  env_rel se env ∧
  ¬ MEM var vconses ∧
  ¬ MEM t vconses ∧
  (∀ x . t ≠ "var" ++ x) ∧
  var ≠ t
  ⇒
  (*Likely needs condition on se i.e. Scheme env*)
  cont_rel ((se, CondK te fe) :: ks)
    (Closure env t $ Mat (Var (Short t)) [
      (Pcon (SOME $ Short "SBool") [Pcon (SOME $ Short "False") []],
        App Opapp [cf; Var (Short var)]);
      (Pany, App Opapp [ct;  Var (Short var)])
    ])
[~ApplyK_NONE:]
  cont_rel ks kv ∧
  nsLookup env.v (Short var) = SOME kv ∧
  (m, ce) = cps_transform_app n (Var (Short t)) [] es (Var (Short var)) ∧
  scheme_env env ∧
  env_rel se env ∧
  ¬ MEM var vconses ∧
  ¬ MEM t vconses ∧
  ts = cps_app_ts n es ∧
  ¬ MEM var ts ∧
  ¬ MEM t ts ∧
  (∀ x . t ≠ "var" ++ x) ∧
  var ≠ t
  ⇒
  (*Likely needs condition on se i.e. Scheme env*)
  cont_rel ((se, ApplyK NONE es) :: ks)
    (Closure env t $ ce)
[~ApplyK_SOME:]
  cont_rel ks kv ∧
  nsLookup env.v (Short var) = SOME kv ∧
  (m, ce) = cps_transform_app n (Var (Short fnt))
    (Var (Short t) :: MAP (Var o Short) ts) es (Var (Short var)) ∧
  ml_v_vals' fn mlfn ∧
  nsLookup env.v (Short fnt) = SOME mlfn ∧
  LIST_REL ml_v_vals' vs mlvs ∧
  LIST_REL (λ x mlv . nsLookup env.v (Short x) = SOME mlv) ts mlvs ∧
  scheme_env env ∧
  env_rel se env ∧
  ALL_DISTINCT ts ∧
  ¬ MEM var vconses ∧
  ¬ MEM fnt vconses ∧
  ¬ MEM t vconses ∧
  EVERY (λ x . ¬ MEM x vconses) ts ∧
  ¬ MEM var ts ∧
  ¬ MEM fnt ts ∧
  ¬ MEM t ts ∧
  ts' = cps_app_ts n es ∧
  EVERY (λ x . ¬ MEM x ts') ts ∧
  ¬ MEM var ts' ∧
  ¬ MEM fnt ts' ∧
  ¬ MEM t ts' ∧
  (∀ x . t ≠ "var" ++ x) ∧
  var ≠ fnt ∧
  var ≠ t ∧
  fnt ≠ t
  ⇒
  (*Likely needs condition on se i.e. Scheme env*)
  cont_rel ((se, ApplyK (SOME (fn, vs)) es) :: ks)
    (Closure env t $ ce)
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
  >> irule_at (Pos hd) EQ_REFL
  >> irule_at Any EQ_REFL
  >> pop_assum $ irule_at (Pos hd) o GSYM
  >> simp[nsLookup_def, Once cont_rel_cases]
  >> gvs[scheme_env_def]
  >> metis_tac[]
QED

(*
open scheme_proofsTheory;
open scheme_parsingTheory;
*)

Theorem app = SRULE [Ntimes evaluate_def 45, do_opapp_def, nsOptBind_def, dec_clock_def,
  do_con_check_def, build_conv_def] $
  RESTR_EVAL_CONV [“evaluate”, “scheme_env7”]
    “evaluate <|clock:=999;refs:=[]|> scheme_env7 [
      compile_scheme_prog $ OUTR $ parse_to_ast
      "((lambda (x y) (lambda (z) y)) 1 2)"
    ]”;

Theorem stuck = SRULE [Ntimes evaluate_def 45, do_opapp_def, nsOptBind_def, dec_clock_def,
  do_con_check_def, build_conv_def, Ntimes find_recfun_def 2,
  Ntimes build_rec_env_def 2, can_pmatch_all_def, pmatch_def, evaluate_match_def,
  same_type_def, same_ctor_def, pat_bindings_def] app;

Theorem stuck_again = SRULE [Ntimes evaluate_def 12, do_opapp_def, nsOptBind_def, dec_clock_def,
  do_con_check_def, build_conv_def, Ntimes find_recfun_def 2,
  Ntimes build_rec_env_def 2, can_pmatch_all_def, pmatch_def, evaluate_match_def,
  same_type_def, same_ctor_def, pat_bindings_def, do_app_def, store_alloc_def,
  Once LET_DEF] stuck;

Theorem more = SRULE [Ntimes evaluate_def 6, do_opapp_def, nsOptBind_def, dec_clock_def,
  do_con_check_def, build_conv_def, Ntimes find_recfun_def 2,
  Ntimes build_rec_env_def 2, can_pmatch_all_def, pmatch_def, evaluate_match_def,
  same_type_def, same_ctor_def, pat_bindings_def, do_app_def, store_alloc_def,
  Once LET_DEF] stuck_again;

SRULE [evaluate_def, do_opapp_def, nsOptBind_def, dec_clock_def,
  do_con_check_def, build_conv_def, Ntimes find_recfun_def 2,
  Ntimes build_rec_env_def 2, can_pmatch_all_def, pmatch_def, evaluate_match_def,
  same_type_def, same_ctor_def, pat_bindings_def, do_app_def, store_alloc_def,
  Once LET_DEF] more;

Theorem str_not_num:
  ∀ (n:num) str . ¬ EVERY isDigit str ⇒ toString n ≠ str
Proof
  simp[EVERY_isDigit_num_to_dec_string]
QED

Theorem k_in_ts:
  ∀ es (n:num) m . ¬ MEM (STRING #"k" (toString n)) (cps_app_ts m es)
Proof
  Induct
  >> simp[cps_app_ts_def]
  >> rpt strip_tac
  >> rpt (pairarg_tac >> gvs[])
QED

Theorem mono_proc_ml_on_n:
  ∀ xs xp n k args ce m ce' .
    (m, ce') = proc_ml n xs xp k args ce ⇒ m ≥ n
Proof
  Induct >> Cases
  >> simp[proc_ml_def]
  >> rpt strip_tac
  >> rpt (pairarg_tac >> gvs[])
  >> last_x_assum $ dxrule o GSYM
  >> simp[]
QED

Theorem mono_cps_on_n:
  (∀ n e m ce . (m, ce) = cps_transform n e ⇒ m ≥ n) ∧
  (∀ n fn ts es k m ce . (m, ce) = cps_transform_app n fn ts es k ⇒ m ≥ n) ∧
  (∀ n k es e m ce . (m, ce) = cps_transform_seq n k es e ⇒ m ≥ n) ∧
  (∀ n k bs ce' m ce . (m, ce) = cps_transform_letreinit n k bs ce' ⇒ m ≥ n)
Proof
  ho_match_mp_tac $ cps_transform_ind
  >> simp[cps_transform_def]
  >> rpt strip_tac
  >> rpt (pairarg_tac >> gvs[])
  >> dxrule $ GSYM mono_proc_ml_on_n
  >> simp[]
QED

Theorem t_in_ts:
  ∀ es n m . m > n ⇒ ¬ MEM (STRING #"t" (toString n)) (cps_app_ts m es)
Proof
  Induct >> rpt strip_tac
  >> gvs[cps_app_ts_def]
  >> rpt (pairarg_tac >> gvs[])
  >> dxrule $ GSYM $ cj 1 mono_cps_on_n
  >> simp[]
  >> last_x_assum $ qspecl_then [‘n’, ‘m'+1’] mp_tac
  >> simp[]
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

Theorem preservation_of_proc:
∀ (st:'ffi state) inner n n' m m' env env' mlenv var kv n xs xp e e' ce k args vs mlvs store store' i .
  valid_val store (Proc env xs xp e) ∧
  LIST_REL ml_v_vals' vs mlvs ∧
  EVERY (valid_val store) vs ∧
  valid_cont store k ∧
  cont_rel k kv ∧
  (n', ce) = cps_transform n e ∧
  (m', inner) = proc_ml m xs xp var args ce ∧
  (store', env',e') = parameterize store env xs xp e vs ∧
  EVERY (OPTION_ALL (valid_val store)) store ∧
  nsLookup mlenv.v (Short var) = SOME kv ∧
  nsLookup mlenv.v (Short args) = SOME (vcons_list mlvs) ∧
  env_rel env mlenv ∧
  scheme_env mlenv ∧
  can_lookup env store ∧
  ¬ MEM args vconses ∧
  ¬ MEM var vconses ∧
  var ≠ args ∧
  (∀ s . var ≠ "var" ++ s) ∧
  (∀ s . args ≠ "var" ++ s) ∧
  (∀ s . var ≠ "x" ++ s) ∧
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
        >> qpat_assum ‘_ = cps_transform _ _’ $ irule_at (Pos hd)
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
    >> simp[Once ml_v_vals'_cases, vcons_list_def]
    >> simp[Once e_ce_rel_cases]
    >> irule_at (Pos hd) EQ_REFL
    >> qpat_assum ‘_ = cps_transform _ _’ $ irule_at (Pos hd)
    >> qpat_assum ‘scheme_env mlenv’ $ simp
      o curry ((::) o swap) [scheme_env_def]
      o SRULE [scheme_env_def]
    >> irule_at (Pos $ el 2) EQ_REFL
    >> simp[]
    >> gvs[env_rel_cases]
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
  >> qsuff_tac ‘STRING #"s" (toString (m + 1)) ≠ toString m’ >- (
    simp[]
    >> strip_tac
    >> simp[Ntimes evaluate_def 4, do_app_def, store_alloc_def]
    >> simp[can_pmatch_all_def, evaluate_match_def, vcons_list_def,
      pmatch_def, do_con_check_def, build_conv_def, nsOptBind_def]
    >> qpat_assum ‘scheme_env mlenv’ $ simp o single
      o SRULE [scheme_env_def]
    >> simp[same_type_def, same_ctor_def, pat_bindings_def]
    >> last_x_assum irule
    >> qpat_assum ‘scheme_env mlenv’ $ simp
      o curry ((::) o swap) [scheme_env_def]
      o SRULE [scheme_env_def]
    >> gvs[fresh_loc_def]
    >> qpat_assum ‘LIST_REL _ t ys’ $ irule_at (Pos last)
    >> irule_at (Pat ‘parameterize _ _ _ _ _ _ = parameterize _ _ _ _ _ _’) EQ_REFL
    >> simp[SNOC_APPEND, store_entry_rel_cases]
    >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pat ‘cont_rel _ _’)
    >> qpat_assum ‘_ = cps_transform _ _’ $ irule_at (Pat ‘_ = cps_transform _ _’)
    >> qpat_assum ‘proc_ml _ _ _ _ _ _ = _’ $
      irule_at (Pat ‘_ = proc_ml _ _ _ _ _ _’) o GSYM
    >> simp[]
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
  >> irule $ GSYM str_not_num
  >> simp[isDigit_def]
QED

Theorem myproof:
  ∀ store store' env env' e e' k k' (st : 'ffi state) mlenv var kv mle .
  step  (store, k, env, e) = (store', k', env', e') ∧
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
    (k ≠ [] ⇒ st'.clock < ck)
Proof
  Cases_on ‘e’
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
      >> rpt (pairarg_tac >> gvs[])
      >> qrefine ‘ck+1’
      >> simp[SimpLHS, Ntimes evaluate_def 6, do_opapp_def,
        nsOptBind_def, dec_clock_def]
      >> irule_at (Pos hd) EQ_REFL
      >> simp[Once e_ce_rel_cases]
      >> irule_at Any EQ_REFL
      >> simp[Once cont_rel_cases]
      >> gvs[scheme_env_def, env_rel_cases]
      >> irule_at Any str_not_num
      >> simp[isDigit_def]
      >> metis_tac[]
    )
    >~ [‘Apply fn es’] >- (
      simp[cps_transform_def]
      >> rpt strip_tac
      >> rpt (pairarg_tac >> gvs[])
      >> qrefine ‘ck+1’
      >> simp[SimpLHS, Ntimes evaluate_def 6, do_opapp_def,
        nsOptBind_def, dec_clock_def]
      >> irule_at (Pos hd) EQ_REFL
      >> simp[Once e_ce_rel_cases]
      >> irule_at Any EQ_REFL
      >> qpat_assum ‘cps_transform _ _ = _’ $
        irule_at (Pos $ hd o tl) o GSYM
      >> simp[Once cont_rel_cases]
      >> pop_assum $ irule_at (Pos $ el 3) o GSYM
      >> last_assum $ irule_at (Pos hd)
      >> gvs[scheme_env_def, env_rel_cases]
      >> irule_at (Pos hd) str_not_num
      >> simp[isDigit_def, k_in_ts, t_in_ts]
    )
    >~ [‘Lambda xs xp e’] >- (
      simp[cps_transform_def]
      >> rpt strip_tac
      >> rpt (pairarg_tac >> gvs[])
      >> qrefine ‘ck+1’
      >> simp[Ntimes evaluate_def 7, do_opapp_def,
        nsOptBind_def, dec_clock_def, do_con_check_def,
        build_conv_def]
      >> qpat_assum ‘scheme_env mlenv’ $ simp o single
        o SRULE [scheme_env_def]
      >> irule_at (Pos hd) EQ_REFL
      >> last_assum $ irule_at (Pos hd)
      >> simp[Once e_ce_rel_cases, Once ml_v_vals'_cases]
      >> gvs[env_rel_cases]
      >> pop_assum $ irule_at (Pos last) o GSYM
      >> pop_assum $ irule_at Any o GSYM
      >> gvs[scheme_env_def]
    )
    >~ [‘Ident x’] >- (
      simp[cps_transform_def]
      >> rpt strip_tac
      >> gvs[Once valid_state_cases]
      >> gvs[Once static_scope_cases]
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
      >> gvs[env_rel_cases, FEVERY_DEF]
    )
    >> cheat
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
      >> irule_at (Pos hd) EQ_REFL
      >> gvs[scheme_env_def, env_rel_cases]
      >> metis_tac[]
    )
    >> Cases_on ‘∃ e es . h1 = ApplyK NONE (e::es)’ >- (
      gvs[]
      >> simp[step_def, return_def, Once e_ce_rel_cases,
        Once cont_rel_cases, cps_transform_def, cps_app_ts_def]
      >> rpt strip_tac
      >> rpt (pairarg_tac >> gvs[])
      >> qrefine ‘ck+1’
      >> simp[Ntimes evaluate_def 6, do_opapp_def,
        nsOptBind_def, dec_clock_def]
      >> irule_at (Pos hd) EQ_REFL
      >> simp[Once e_ce_rel_cases]
      >> irule_at Any EQ_REFL
      >> qpat_assum ‘cps_transform _ _ = (_,_)’ $
        irule_at (Pos $ el 2) o GSYM
      >> simp[Once cont_rel_cases]
      >> pop_assum $ irule_at (Pos $ el 3) o GSYM
      >> qpat_assum ‘scheme_env env'’ $ simp
        o curry ((::) o swap) [scheme_env_def] o SRULE [scheme_env_def]
      >> irule_at Any str_not_num
      >> simp[isDigit_def, t_in_ts]
      >> gvs[env_rel_cases]
    )
    >> Cases_on ‘∃ e es . h1 = ApplyK (SOME (fn, vs)) (e::es)’ >- (
      gvs[]
      >> simp[step_def, return_def, Once e_ce_rel_cases,
        Once cont_rel_cases, cps_transform_def, cps_app_ts_def]
      >> rpt strip_tac
      >> rpt (pairarg_tac >> gvs[])
      >> qrefine ‘ck+1’
      >> simp[Ntimes evaluate_def 6, do_opapp_def,
        nsOptBind_def, dec_clock_def]
      >> irule_at (Pos hd) EQ_REFL
      >> simp[Once e_ce_rel_cases]
      >> irule_at Any EQ_REFL
      >> qpat_assum ‘cps_transform _ _ = (_,_)’ $ irule_at
        (Pos $ hd o tl) o GSYM
      >> simp[Once cont_rel_cases]
      >> SIMP_TAC std_ss [MAP_o]
      >> pop_assum $ irule_at (Pos $ el 3) o GSYM
        o SIMP_RULE std_ss [Ntimes (GSYM MAP) 2, MAP_o]
      >> irule_at Any EQ_REFL
      >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
      >> qpat_assum ‘scheme_env env'’ $ simp
        o curry ((::) o swap) [scheme_env_def] o SRULE [scheme_env_def]
      >> irule_at Any str_not_num
      >> simp[isDigit_def, t_in_ts]
      >> qpat_assum ‘LIST_REL _ vs _’ $ irule_at (Pos hd)
      >> gvs[EVERY_CONJ]
      >> qpat_assum ‘EVERY (λ x . x ≠ _) _’ $ simp o single
        o SRULE [EVERY_MEM]
      >> gvs[env_rel_cases]
      >> irule EVERY2_MEM_MONO
      >> qpat_assum ‘LIST_REL _ _ _’ $ irule_at (Pos last)
      >> qpat_assum ‘LIST_REL _ _ _’ $ assume_tac o cj 1
        o SRULE [EVERY2_EVERY]
      >> PairCases >> simp[]
      >> strip_tac
      >> drule $ SRULE [Once CONJ_COMM] MEM_ZIP_MEM_MAP
      >> simp[]
      >> strip_tac
      >> qpat_assum ‘LIST_REL _ ts mlvs’ $ assume_tac o cj 1
        o SRULE [EVERY2_EVERY]
      >> qsuff_tac ‘x0 ≠ t'’
      >> strip_tac
      >> gvs[]
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
        >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pat ‘cont_rel _ _’)
        >> qpat_assum ‘_ = proc_ml _ _ _ _ _ _’ $ irule_at Any
        >> simp[]
        >> simp[vcons_list_def]
        >> qpat_assum ‘_ = cps_transform _ _’ $ irule_at (Pos hd)
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
    >> Cases_on ‘h1 = ApplyK (SOME (fn, vs)) []’ >- (
      gvs[]
      >> simp[step_def, return_def, Once e_ce_rel_cases,
        Once cont_rel_cases]
      >> rpt strip_tac
      >> gvs[cps_transform_def, cons_list_def]
      >> qrefine ‘ck+1’
      >> simp[evaluate_def, do_con_check_def,
        build_conv_def, do_opapp_def, dec_clock_def]
      >> qsuff_tac ‘scheme_env env'' ∧ ¬ MEM t' vconses ⇒ scheme_env (env'' with v:= nsBind t'
        mlv env''.v)’
      >- (
        simp[] >> strip_tac
        >> qsuff_tac ‘LIST_REL (λx v'. nsLookup (env'' with v:= nsBind t' mlv
        env''.v).v (Short x) = SOME v') (REVERSE (t'::ts)) (REVERSE (mlv::mlvs))’ >- (
          strip_tac
          >> drule_all_then assume_tac cons_list_val
          >> gvs[Once ml_v_vals'_cases]
          >> gvs[application_def]
          >~ [‘"SAdd"’] >- (
            qpat_assum ‘scheme_env env''’ $ simp o single o SRULE [scheme_env_def]
            >> simp[Ntimes find_recfun_def 2, Ntimes build_rec_env_def 2]
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
            >> qrefine ‘ck+2’
            >> simp[Ntimes evaluate_def 2, dec_clock_def]
            >> Cases_on ‘∃ (n:int) . n = 0’ >~ [‘¬∃n.n=0’] >- gvs[]
            >> pop_assum mp_tac
            >> strip_tac
            >> pop_assum $ simp o single o GSYM
            >> qid_spec_tac ‘n’
            >> pop_assum kall_tac
            >> rpt $ qpat_x_assum ‘LIST_REL _ ts _’ kall_tac
            >> qpat_assum ‘LIST_REL _ vs mlvs’ mp_tac
            >> qid_spec_tac ‘mlvs’
            >> qid_spec_tac ‘vs’
            >> ho_match_mp_tac LIST_REL_SNOC_ind
            >> rpt strip_tac >- (
              gvs[Once ml_v_vals'_cases, vcons_list_def]
              >> qrefine ‘ck+1’
              >> simp[Ntimes evaluate_def 2]
              >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
                same_type_def, same_ctor_def, evaluate_match_def,
                pat_bindings_def]
              >~ [‘SNum m’] >- (
                qrefine ‘ck+3’
                >> simp[evaluate_def, do_app_def, do_opapp_def, dec_clock_def]
                >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
                  same_type_def, same_ctor_def, evaluate_match_def,
                  pat_bindings_def]
                >> simp[Ntimes find_recfun_def 2, Ntimes build_rec_env_def 2]
                >> simp[Ntimes evaluate_def 4]
                >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
                  same_type_def, same_ctor_def, evaluate_match_def,
                  pat_bindings_def]
                >> simp[Ntimes find_recfun_def 2, Ntimes build_rec_env_def 2]
                >> simp[Ntimes evaluate_def 3, do_con_check_def,
                build_conv_def, nsOptBind_def]
                >> simp[sadd_def]
                >> irule_at (Pos hd) EQ_REFL
                >> simp[]
                >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
                >> simp[Once e_ce_rel_cases, opn_lookup_def,
                  env_rel_cases, FEVERY_FEMPTY, Once ml_v_vals'_cases]
                >> simp[INT_ADD_COMM]
              )
              >> simp[Ntimes evaluate_def 3, do_app_def, do_opapp_def, dec_clock_def]
              >> simp[can_pmatch_all_def, pmatch_def, nsLookup_def,
                same_type_def, same_ctor_def, evaluate_match_def,
                pat_bindings_def, do_con_check_def, build_conv_def]
              >> irule_at (Pos hd) EQ_REFL
              >> last_assum $ irule_at (Pos hd)
              >> simp[Once e_ce_rel_cases, sadd_def,
                env_rel_cases, FEVERY_FEMPTY]
            )
            >> qpat_assum ‘ml_v_vals' h1 h2’ $ assume_tac o SRULE [Once ml_v_vals'_cases]
            >> gvs[REVERSE_SNOC, vcons_list_def]
            >~ [‘SNum m’] >- (
              simp[evaluate_def, do_opapp_def, do_app_def,
                opn_lookup_def, can_pmatch_all_def, pmatch_def, nsLookup_def,
                same_type_def, same_ctor_def, evaluate_match_def,
                pat_bindings_def, do_con_check_def, build_conv_def, dec_clock_def]
              >> simp[Ntimes find_recfun_def 2, Ntimes build_rec_env_def 2]
              >> qrefine ‘ck+3’
              >> simp[Ntimes evaluate_def 2]
              >> simp[sadd_def]
              >> ‘∀ ck . st with <|clock:=ck;refs:=st.refs;ffi:=st.ffi|> = st with clock:=ck’
                by (simp[state_component_equality])
              >> simp[]
              >> pop_assum kall_tac
              >> pop_assum $ qspec_then ‘n + m’ mp_tac
              >> strip_tac
              >> qpat_assum ‘evaluate _ _ _ = evaluate _ _ _’ $ irule_at (Pos hd)
              >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
              >> simp[Once INT_ADD_COMM]
              >> qpat_assum ‘e_ce_rel _ _ _ _ _’ $ irule_at (Pos hd)
            )
            >> gvs[]
            >> simp[Ntimes evaluate_def 10, do_opapp_def, do_app_def,
              opn_lookup_def, can_pmatch_all_def, pmatch_def, nsLookup_def,
              same_type_def, same_ctor_def, evaluate_match_def,
              pat_bindings_def, do_con_check_def, build_conv_def, dec_clock_def]
            >> simp[Ntimes find_recfun_def 2, Ntimes build_rec_env_def 2]
            >> simp[sadd_def, Once e_ce_rel_cases]
            >> irule_at (Pos hd) EQ_REFL
            >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pos hd)
            >> simp[env_rel_cases, FEVERY_FEMPTY]
          )
          >~ [‘"Proc"’] >- (
            qpat_assum ‘scheme_env env''’ $ simp o single o SRULE [scheme_env_def]
            >> simp[Ntimes find_recfun_def 2, Ntimes build_rec_env_def 2]
            >> qrefine ‘ck+3’
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
            >> qpat_assum ‘cont_rel _ _’ $ irule_at (Pat ‘cont_rel _ _’)
            >> qpat_assum ‘_ = proc_ml _ _ _ _ _ _’ $ irule_at Any
            >> simp[]
            >> irule_at (Pos hd) EQ_REFL
            >> qpat_assum ‘_ = cps_transform _ _’ $ irule_at (Pos hd)
            >> irule_at (Pos last) $ cj 1 $ iffLR LIST_REL_APPEND
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
          >> cheat
        )
        >> simp[]
        >> qsuff_tac ‘EVERY (λ(x,y). t' ≠ x) (ZIP (ts,mlvs))’ >- (
          strip_tac
          >> qpat_x_assum ‘LIST_REL _ ts mlvs’ assume_tac
          >> drule_then assume_tac EVERY2_LENGTH
          >> rev_drule_all $ iffRL EVERY2_EVERY
          >> qpat_x_assum ‘LIST_REL _ _ _’ mp_tac
          >> simp[AND_IMP_INTRO, GSYM LIST_REL_CONJ]
          >> ho_match_mp_tac EVERY2_mono
          >> simp[]
        )
        >> simp[EVERY_MEM] >> PairCases >> simp[]
        >> qpat_x_assum ‘LIST_REL _ ts mlvs’ assume_tac
        >> strip_tac >> drule_at_then Any assume_tac MEM_ZIP_MEM_MAP
        >> drule_then assume_tac EVERY2_LENGTH >> gvs[]
        >> strip_tac >> gvs[]
      )
      >> gvs[scheme_env_def]
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