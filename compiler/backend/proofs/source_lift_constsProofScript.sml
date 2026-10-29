(*
  Correctness for the source_lift_consts pass.
*)
Theory source_lift_constsProof
Ancestors
  source_lift_consts ast finite_map mlstring evaluate semanticPrimitives semantics
  namespaceProps semanticPrimitivesProps evaluateProps source_evalProof
Libs
  preamble

Theorem delete_all_lookup[local]:
  FLOOKUP (delete_all xs fm) x =
    if MEM x xs then NONE else FLOOKUP fm x
Proof
  Induct_on ‘xs’
  >> simp [delete_all_def,DOMSUB_FLOOKUP_THM] >> qx_gen_tac ‘h’
  >> Cases_on ‘h = x’ >> simp []
QED

Theorem bind_all_lookup[local]:
  FLOOKUP (bind_all xs fm) x =
    if MEM x xs then SOME () else FLOOKUP fm x
Proof
  qid_spec_tac ‘fm’
  >> Induct_on ‘xs’ >> simp [bind_all_def,FLOOKUP_UPDATE] >> qx_genl_tac [‘h’,‘fm’]
  >> Cases_on ‘h = x’ >> simp []
QED

Theorem maps_disjoint_domains[local]:
  maps_disjoint fvs bound ⇔ DISJOINT (FDOM fvs) (FDOM bound)
Proof
  simp [maps_disjoint_def,str_empty_def,DISJOINT_DEF]
  >> metis_tac [FDOM_EQ_EMPTY,FDOM_DRESTRICT]
QED

Theorem rename_var_empty[local]:
  rename_var FEMPTY id = id
Proof
  Cases_on ‘id’ >> simp [rename_var_def]
QED

Theorem rename_var_shadow[local]:
  rename_var (fdomsub ren x) (Short x) = Short x
Proof
  simp [rename_var_def,DOMSUB_FLOOKUP]
QED

Theorem rename_var_bind[local]:
  rename_var (ren |+ (x,y)) (Short x) = Short y
Proof
  simp [rename_var_def,FLOOKUP_UPDATE]
QED

Theorem bump_make_name[local]:
  bump x n ≤ m ⇒ make_name m ≠ x
Proof
  rw [bump_def,make_name_def]
  >> CCONTR_TAC >> gvs [] >> last_x_assum mp_tac >> EVAL_TAC >> simp [ADD1]
QED

Theorem bump_le[local]:
  n ≤ bump x n
Proof
  rw [bump_def]
QED

Theorem bump_mono[local]:
  n ≤ m ⇒ bump x n ≤ bump x m
Proof
  rw [bump_def,MAX_DEF] >> decide_tac
QED

Theorem bump_le_imp[local]:
  bump x n ≤ m ⇒ n ≤ m ∧ bump x 0 ≤ m
Proof
  metis_tac [bump_le,bump_mono,LESS_EQ_TRANS,ZERO_LESS_EQ]
QED

Theorem bump_all_le[local]:
  n ≤ bump_all xs n
Proof
  qid_spec_tac ‘n’
  >> Induct_on ‘xs’ >> simp [bump_all_def] >> metis_tac [bump_le,LESS_EQ_TRANS]
QED

Theorem annotate_exp_evaluate[local]:
  ∀e t tree limit captures.
    annotate_exp t e = (tree,limit,captures) ⇒
    ∀(s:'ffi semanticPrimitives$state) env.
      evaluate s env [tree_exp tree] = evaluate s env [e]
Proof
  Induct_on ‘e’
  >> simp [Once annotate_exp_def] >> rw [] >> rpt (pairarg_tac >> gvs [])
  >> simp [tree_exp_def,cj 15 evaluate_def,cj 16 evaluate_def] >> metis_tac []
QED

Theorem annotate_exp_reannotate[local]:
  ∀e t tree limit captures.
    annotate_exp t e = (tree,limit,captures) ⇒
    annotate_exp t (tree_exp tree) = (tree,limit,captures)
Proof
  Induct_on ‘e’
  >> simp [Once annotate_exp_def] >> rw [] >> rpt (pairarg_tac >> gvs [])
  >> simp [tree_exp_def,Once annotate_exp_def]
QED

Theorem annotate_LENGTH[local]:
  (∀t es trees n fvs.
     annotate_exps t es = (trees,n,fvs) ⇒ LENGTH trees = LENGTH es) ∧
  (∀t pes trees n fvs.
     annotate_pes t pes = (trees,n,fvs) ⇒ LENGTH trees = LENGTH pes) ∧
  (∀t funs trees n fvs.
     annotate_funs t funs = (trees,n,fvs) ⇒ LENGTH trees = LENGTH funs)
Proof
  rpt conj_tac >> gen_tac >> Induct >> simp [FORALL_PROD,Once annotate_exp_def]
  >> rw [] >> rpt (pairarg_tac >> gvs [NULL_EQ,AllCaseEqs()])
QED

Theorem make_name_injective[local]:
  make_name n = make_name m ⇔ n = m
Proof
  eq_tac
  >- (
    disch_then (mp_tac o AP_TERM “strlen”)
    >> simp [make_name_def,strlen_strcat,strlen_implode])
  >> simp []
QED

Theorem choose_name_fresh[local]:
  bump x 0 ≤ n ∧
  (∀k. n ≤ k ⇒ FLOOKUP used (make_name k) = NONE) ∧
  choose_name bound x (n,ds,used) = (y,n1,ds1,used1) ⇒
  n ≤ n1 ∧ ds1 = ds ∧ FLOOKUP used y = NONE ∧
  used1 = used |+ (x,()) |+ (y,()) ∧
  (∀k. n1 ≤ k ⇒ FLOOKUP used1 (make_name k) = NONE)
Proof
  rw [choose_name_def]
  >> gvs [FLOOKUP_UPDATE,make_name_injective]
  >> qmatch_goalsub_rename_tac ‘make_name counter’ >> ‘bump x 0 ≤ counter’ by decide_tac
  >> metis_tac [bump_make_name]
QED

Theorem delete_all_domain[local]:
  FDOM (delete_all xs fm) = FDOM fm DIFF set xs
Proof
  Induct_on ‘xs’
  >> simp [delete_all_def,FDOM_DOMSUB,EXTENSION] >> metis_tac []
QED

Theorem delete_all_empty[local,simp]:
  delete_all names FEMPTY = FEMPTY
Proof
  simp [GSYM FDOM_EQ_EMPTY,delete_all_domain]
QED

Theorem bump_patterns_le[local]:
  (∀n p. n ≤ bump_pat n p) ∧
  (∀n ps. n ≤ bump_pats n ps)
Proof
  ho_match_mp_tac bump_pat_ind
  >> rw [bump_pat_def] >> metis_tac [bump_le,LESS_EQ_TRANS]
QED

Theorem annotate_free_name_bound[local]:
  (∀t e tree n fvs x.
     annotate_exp t e = (tree,n,fvs) ∧ x ∈ FDOM fvs ⇒ bump x 0 ≤ n) ∧
  (∀t es trees n fvs x.
     annotate_exps t es = (trees,n,fvs) ∧ x ∈ FDOM fvs ⇒ bump x 0 ≤ n) ∧
  (∀t pes trees n fvs x.
     annotate_pes t pes = (trees,n,fvs) ∧ x ∈ FDOM fvs ⇒ bump x 0 ≤ n) ∧
  (∀t funs trees n fvs x.
     annotate_funs t funs = (trees,n,fvs) ∧ x ∈ FDOM fvs ⇒ bump x 0 ≤ n)
Proof
  ho_match_mp_tac annotate_exp_ind >> rpt conj_tac >> rpt gen_tac
  >> rw [Once annotate_exp_def] >> rpt (pairarg_tac >> gvs [])
  >> gvs [FDOM_FUNION,FDOM_DOMSUB,delete_all_domain,str_empty_def]
  >>~- ([‘_ ≤ bump_all _ _’], metis_tac [bump_all_le,MAX_LE,LESS_EQ_TRANS])
  >- metis_tac [bump_le,LESS_EQ_TRANS]
  >- (Cases_on ‘x’ >> gvs [])
  >- (Cases_on ‘name’ >> simp [] >> metis_tac [bump_le,MAX_LE,LESS_EQ_TRANS])
  >- (Cases_on ‘name’ >> gvs [FDOM_DOMSUB] >> metis_tac [bump_le,MAX_LE,LESS_EQ_TRANS])
  >- (Cases_on ‘NULL es’ >> gvs [FDOM_FUNION])
  >- metis_tac [bump_patterns_le,LESS_EQ_TRANS]
  >- metis_tac [bump_le,LESS_EQ_TRANS]
QED

Inductive constant_exp:
  (∀l. constant_exp (Lit l)) ∧
  (∀x e. constant_exp (Fun x e)) ∧
  (∀cn es. EVERY constant_exp es ⇒ constant_exp (Con cn es)) ∧
  (∀e ty. constant_exp e ⇒ constant_exp (Tannot e ty)) ∧
  (∀e loc. constant_exp e ⇒ constant_exp (Lannot e loc))
End

Theorem annotate_value_sound[local]:
  (∀t e tree n fvs.
     annotate_exp t e = (tree,n,fvs) ∧ tree_value tree ⇒ constant_exp e) ∧
  (∀t es trees n fvs.
     annotate_exps t es = (trees,n,fvs) ∧ EVERY tree_value trees ⇒
     EVERY constant_exp es) ∧
  (∀t pes trees n fvs.
     annotate_pes t pes = (trees,n,fvs) ∧ EVERY tree_value trees ⇒
     EVERY (λ(p,e). constant_exp e) pes) ∧
  (∀t funs trees n fvs.
     annotate_funs t funs = (trees,n,fvs) ∧ EVERY tree_value trees ⇒
     EVERY (λ(f,x,e). constant_exp e) funs)
Proof
  ho_match_mp_tac annotate_exp_ind >> rpt conj_tac >> rpt gen_tac
  >> rw [Once annotate_exp_def]
  >> rpt (pairarg_tac >> gvs [tree_value_def,constant_exp_rules])
  >> gvs [tree_value_def,constant_exp_rules] >> Cases_on ‘NULL es’ >> gvs [NULL_EQ]
QED

Theorem evaluate_value_binding[local]:
  evaluate s env [e] = (s,Rval [v]) ∧ check_exp_constructors env.c e ⇒
  evaluate_decs s env [Dlet NoLocs (Pvar x) e] =
    (s,Rval <|v := alist_to_ns [(x,v)]; c := nsEmpty|>)
Proof
  rw []
  >> simp [evaluate_decs_def,pat_bindings_def,pmatch_def]
QED

Theorem rename_var_shadow_other[local]:
  x ≠ y ⇒ rename_var (fdomsub ren x) (Short y) = rename_var ren (Short y)
Proof
  simp [rename_var_def,DOMSUB_FLOOKUP_THM]
QED

Definition lift_env_rel_def:
  lift_env_rel R (fvs:mlstring |-> unit) ren (env:v sem_env) env' ⇔
    env.c = env'.c ∧
    (∀m x. OPTREL R (nsLookup env.v (Long m x))
                   (nsLookup env'.v (Long m x))) ∧
    (∀x. x ∈ FDOM fvs ⇒
      OPTREL R (nsLookup env.v (Short x))
               (nsLookup env'.v (rename_var ren (Short x))))
End

Theorem lift_env_rel_lookup[local]:
  lift_env_rel R fvs ren env env' ∧
  (∀x. id = Short x ⇒ x ∈ FDOM fvs) ⇒
  OPTREL R (nsLookup env.v id) (nsLookup env'.v (rename_var ren id))
Proof
  Cases_on ‘id’
    >> simp [lift_env_rel_def,rename_var_def]
QED

Theorem lift_env_rel_bind[local]:
  lift_env_rel R (fdomsub fvs x) ren env env' ∧ R v v' ∧
  (∀z. z ∈ FDOM fvs ∧ z ≠ x ⇒ rename_var ren (Short z) ≠ (Short x:(mlstring,mlstring) id)) ⇒
  lift_env_rel R fvs (fdomsub ren x)
    (env with v := nsBind x v env.v)
    (env' with v := nsBind x v' env'.v)
Proof
  rw [lift_env_rel_def,FDOM_DOMSUB]
    >> qmatch_goalsub_rename_tac ‘nsLookup _ (Short z)’ >> Cases_on ‘z = x’
    >> gvs [rename_var_shadow,rename_var_shadow_other]
QED

Inductive value_ready:
  (∀env l. value_ready env (Lit l)) ∧
  (∀env x e. value_ready env (Fun x e)) ∧
  (∀env id v. nsLookup env.v id = SOME v ⇒ value_ready env (Var id)) ∧
  (∀env cn es.
    do_con_check env.c cn (LENGTH es) ∧ EVERY (value_ready env) es ⇒
    value_ready env (Con cn es)) ∧
  (∀env e ty. value_ready env e ⇒ value_ready env (Tannot e ty)) ∧
  (∀env e loc. value_ready env e ⇒ value_ready env (Lannot e loc))
End

Definition lift_state_extends_def:
  lift_state_extends (n:num,ds:dec list,used:mlstring |-> unit) (n1,ds1,used1) ⇔
    n ≤ n1 ∧ FDOM used ⊆ FDOM used1 ∧ ∃extra. ds1 = extra ++ ds
End

Theorem lift_state_extends_refl[local]:
  lift_state_extends st st
Proof
  PairCases_on ‘st’
    >> simp [lift_state_extends_def]
QED

Theorem lift_state_extends_trans[local]:
  lift_state_extends st st1 ∧ lift_state_extends st1 st2 ⇒
  lift_state_extends st st2
Proof
  PairCases_on ‘st’
    >> PairCases_on ‘st1’ >> PairCases_on ‘st2’ >> rw [lift_state_extends_def]
    >> metis_tac [LESS_EQ_TRANS,SUBSET_TRANS,APPEND_ASSOC]
QED

Theorem choose_name_extends[local]:
  choose_name bound x st = (y,st1) ⇒ lift_state_extends st st1
Proof
  PairCases_on ‘st’
    >> rw [choose_name_def] >> gvs [lift_state_extends_def,SUBSET_DEF]
QED

Theorem choose_names_extends[local]:
  ∀xs bound st ys st1.
    choose_names bound xs st = (ys,st1) ⇒ lift_state_extends st st1
Proof
  Induct_on ‘xs’
    >> rw [Once choose_names_def,lift_state_extends_refl] >> rpt (pairarg_tac >> gvs [])
    >> metis_tac [choose_name_extends,lift_state_extends_trans]
QED

Theorem emit_dec_extends[local]:
  lift_state_extends st (emit_dec d st)
Proof
  PairCases_on ‘st’
    >> simp [emit_dec_def,lift_state_extends_def] >> qexists_tac ‘[d]’ >> simp []
QED

Theorem emit_value_extends[local]:
  emit_value e st = (e1,st1) ⇒ lift_state_extends st st1
Proof
  PairCases_on ‘st’
    >> rw [emit_value_def] >> simp [lift_state_extends_def,SUBSET_DEF]
    >> metis_tac [APPEND]
QED

Theorem lift_exp_state_extends[local]:
  (∀mode bound ren st tree e st1.
    lift_exp mode bound ren st tree = (e,st1) ⇒ lift_state_extends st st1) ∧
  (∀mode bound ren st tree e st1.
    lower_exp mode bound ren st tree = (e,st1) ⇒ lift_state_extends st st1) ∧
  (∀mode bound ren st trees es st1.
    lift_exps mode bound ren st trees = (es,st1) ⇒ lift_state_extends st st1) ∧
  (∀mode bound ren st ps trees pes st1.
    lift_pes mode bound ren st ps trees = (pes,st1) ⇒ lift_state_extends st st1) ∧
  (∀bound ren st fs trees funs st1.
    lift_funs bound ren st fs trees = (funs,st1) ⇒ lift_state_extends st st1)
Proof
  ho_match_mp_tac lift_exp_ind
  >> rpt conj_tac >> rpt gen_tac >> rw [Once lift_exp_def,lift_state_extends_refl]
  >> rpt (pairarg_tac >> gvs [])
  >>~- ([‘emit_value _ _’], metis_tac [emit_value_extends,lift_state_extends_trans])
  >>~- ([‘choose_names _ _ _’],
    drule choose_names_extends >> metis_tac [emit_dec_extends,lift_state_extends_trans])
  >>~- ([‘choose_name _ _ _’],
    drule choose_name_extends >> metis_tac [emit_dec_extends,lift_state_extends_trans])
  >> metis_tac [lift_state_extends_trans]
QED

Theorem lift_output_lengths[local]:
  (∀mode bound ren st trees es st1.
    lift_exps mode bound ren st trees = (es,st1) ⇒ LENGTH es = LENGTH trees) ∧
  (∀mode bound ren st ps trees pes st1.
    lift_pes mode bound ren st ps trees = (pes,st1) ⇒
    LENGTH pes = MIN (LENGTH ps) (LENGTH trees)) ∧
  (∀bound ren st fs trees funs st1.
    lift_funs bound ren st fs trees = (funs,st1) ⇒
    LENGTH funs = MIN (LENGTH fs) (LENGTH trees))
Proof
  ho_match_mp_tac (SRULE []
      (Q.SPECL [‘λmode bound ren st tree. T’,‘λmode bound ren st tree. T’]
        lift_exp_ind))
    >> rpt conj_tac >> rpt gen_tac >> rw [Once lift_exp_def]
    >> rpt (pairarg_tac >> gvs []) >> simp [MIN_DEF]
QED

Inductive tree_constructors:
  (∀c e fvs value children.
    check_exp_constructors c e ∧ EVERY (tree_constructors c) children ∧
    (∀cn es. e = Con cn es ⇒ do_con_check c cn (LENGTH children)) ⇒
    tree_constructors c (Lift e fvs value children))
End

Theorem tree_constructors_Lift[local]:
  tree_constructors c (Lift e fvs value children) ⇔
  check_exp_constructors c e ∧ EVERY (tree_constructors c) children ∧
  (∀cn es. e = Con cn es ⇒ do_con_check c cn (LENGTH children))
Proof
  simp [Once tree_constructors_cases]
QED

Theorem annotate_constructors[local]:
  (∀t e tree n fvs c.
    annotate_exp t e = (tree,n,fvs) ∧ check_exp_constructors c e ⇒
    tree_constructors c tree) ∧
  (∀t es trees n fvs c.
    annotate_exps t es = (trees,n,fvs) ∧ EVERY (check_exp_constructors c) es ⇒
    EVERY (tree_constructors c) trees) ∧
  (∀t pes trees n fvs c.
    annotate_pes t pes = (trees,n,fvs) ∧
    EVERY (λ(p,e). check_exp_constructors c e) pes ⇒
    EVERY (tree_constructors c) trees) ∧
  (∀t funs trees n fvs c.
    annotate_funs t funs = (trees,n,fvs) ∧
    EVERY (λ(f,x,e). check_exp_constructors c e) funs ⇒
    EVERY (tree_constructors c) trees)
Proof
  ho_match_mp_tac annotate_exp_ind
    >> rpt conj_tac >> rpt gen_tac >> rw [Once annotate_exp_def]
    >> rpt (pairarg_tac >> gvs [])
    >> gvs [tree_constructors_Lift,check_exp_constructors_def]
    >- metis_tac [annotate_LENGTH]
    >- metis_tac []
    >> Cases_on ‘NULL es’ >> gvs []
QED

Theorem emit_value_constructors[local]:
  emit_value e st = (e1,st1) ⇒ check_exp_constructors c e1
Proof
  PairCases_on ‘st’
    >> simp [emit_value_def] >> rpt strip_tac >> gvs [check_exp_constructors_def]
QED

Theorem lift_exp_constructors[local]:
  (∀mode bound ren st tree e st1 c.
    lift_exp mode bound ren st tree = (e,st1) ∧ tree_constructors c tree ⇒
    check_exp_constructors c e) ∧
  (∀mode bound ren st tree e st1 c.
    lower_exp mode bound ren st tree = (e,st1) ∧ tree_constructors c tree ⇒
    check_exp_constructors c e) ∧
  (∀mode bound ren st trees es st1 c.
    lift_exps mode bound ren st trees = (es,st1) ∧
    EVERY (tree_constructors c) trees ⇒ EVERY (check_exp_constructors c) es) ∧
  (∀mode bound ren st ps trees pes st1 c.
    lift_pes mode bound ren st ps trees = (pes,st1) ∧
    EVERY (tree_constructors c) trees ⇒
    EVERY (λ(p,e). check_exp_constructors c e) pes) ∧
  (∀bound ren st fs trees funs st1 c.
    lift_funs bound ren st fs trees = (funs,st1) ∧
    EVERY (tree_constructors c) trees ⇒
    EVERY (λ(f,x,e). check_exp_constructors c e) funs)
Proof
  ho_match_mp_tac lift_exp_ind
    >> rpt conj_tac >> rpt gen_tac >> rw [Once lift_exp_def]
    >> rpt (pairarg_tac >> gvs [])
    >> gvs [tree_constructors_Lift,check_exp_constructors_def]
    >> metis_tac [emit_value_constructors,CONJUNCT1 lift_output_lengths]
QED

Inductive lift_value_rel:
  (∀C E l. lift_value_rel C E (Litv l) (Litv l)) ∧
  (∀C E b loc. lift_value_rel C E (Loc b loc) (Loc b loc)) ∧
  (∀C E stamp xs ys.
    LIST_REL (lift_value_rel C E) xs ys ⇒
    lift_value_rel C E (Conv stamp xs) (Conv stamp ys)) ∧
  (∀C E xs ys.
    LIST_REL (lift_value_rel C E) xs ys ⇒
    lift_value_rel C E (Vectorv xs) (Vectorv ys)) ∧
  (∀C E env x e env' x' e'.
    C (Closure env x e) (Closure env' x' e') ⇒
    lift_value_rel C E (Closure env x e) (Closure env' x' e')) ∧
  (∀C E env funs f env' funs' f'.
    C (Recclosure env funs f) (Recclosure env' funs' f') ⇒
    lift_value_rel C E (Recclosure env funs f) (Recclosure env' funs' f')) ∧
  (∀C E env env' id.
    E env env' ⇒ lift_value_rel C E (Env env id) (Env env' id))
End

Theorem lift_value_rel_cases_l[local]:
  (lift_value_rel C E (Litv l) value ⇔ value = Litv l) ∧
  (lift_value_rel C E (Loc b loc) value ⇔ value = Loc b loc) ∧
  (lift_value_rel C E (Conv stamp xs) value ⇔
    ∃ys. value = Conv stamp ys ∧ LIST_REL (lift_value_rel C E) xs ys) ∧
  (lift_value_rel C E (Vectorv xs) value ⇔
    ∃ys. value = Vectorv ys ∧ LIST_REL (lift_value_rel C E) xs ys) ∧
  (lift_value_rel C E (Closure env x e) value ⇔
    ∃env' x' e'. value = Closure env' x' e' ∧
      C (Closure env x e) (Closure env' x' e')) ∧
  (lift_value_rel C E (Recclosure env funs f) value ⇔
    ∃env' funs' f'. value = Recclosure env' funs' f' ∧
      C (Recclosure env funs f) (Recclosure env' funs' f')) ∧
  (lift_value_rel C E (Env env id) value ⇔
    ∃env'. value = Env env' id ∧ E env env')
Proof
  rpt conj_tac
  >> simp [Once lift_value_rel_cases]
QED

Theorem lift_value_rel_mono[local,mono]:
  (∀v w. C v w ⇒ C' v w) ∧ (∀env env'. E env env' ⇒ E' env env') ⇒
  lift_value_rel C E v w ⇒ lift_value_rel C' E' v w
Proof
  qsuff_tac ‘∀C E v w. lift_value_rel C E v w ⇒
    ∀C' E'. (∀a b. C a b ⇒ C' a b) ∧
      (∀env env'. E env env' ⇒ E' env env') ⇒ lift_value_rel C' E' v w’
  >- metis_tac []
  >> ho_match_mp_tac lift_value_rel_ind >> rw [lift_value_rel_cases_l]
  >> qpat_x_assum ‘LIST_REL _ _ _’ mp_tac >> match_mp_tac LIST_REL_mono >> rw []
QED

Theorem bump_pattern_names[local]:
  (∀n p x. MEM x (pat_bindings p) ⇒ bump x 0 ≤ bump_pat n p) ∧
  (∀n ps x. MEM x (pats_bindings ps) ⇒ bump x 0 ≤ bump_pats n ps)
Proof
  ho_match_mp_tac bump_pat_ind
  >> rw [bump_pat_def,pat_bindings_def]
  >> metis_tac [bump_mono,bump_patterns_le,ZERO_LESS_EQ,LESS_EQ_TRANS]
QED

Definition exp_names_def:
  exp_names (Raise e) = exp_names e ∧
  exp_names (Handle e pes) = exp_names e ∪ exp_names_pes pes ∧
  exp_names (Lit l) = {} ∧
  exp_names (Con cn es) = exp_names_exps es ∧
  exp_names (Var (Short x)) = {x} ∧
  exp_names (Var (Long mn x)) = {} ∧
  exp_names (Fun x e) = x INSERT exp_names e ∧
  exp_names (App op es) = exp_names_exps es ∧
  exp_names (Log op e1 e2) = exp_names e1 ∪ exp_names e2 ∧
  exp_names (If e1 e2 e3) = exp_names e1 ∪ exp_names e2 ∪ exp_names e3 ∧
  exp_names (Mat e pes) = exp_names e ∪ exp_names_pes pes ∧
  exp_names (Let NONE e1 e2) = exp_names e1 ∪ exp_names e2 ∧
  exp_names (Let (SOME x) e1 e2) = x INSERT (exp_names e1 ∪ exp_names e2) ∧
  exp_names (Letrec funs e) = exp_names_funs funs ∪ exp_names e ∧
  exp_names (Tannot e ty) = exp_names e ∧
  exp_names (Lannot e loc) = exp_names e ∧
  exp_names (Open path e) = exp_names e ∧
  exp_names_exps [] = {} ∧
  exp_names_exps (e::es) = exp_names e ∪ exp_names_exps es ∧
  exp_names_pes [] = {} ∧
  exp_names_pes ((p,e)::pes) =
    set (pat_bindings p) ∪ exp_names e ∪ exp_names_pes pes ∧
  exp_names_funs [] = {} ∧
  exp_names_funs ((f,x,e)::funs) =
    f INSERT (x INSERT (exp_names e ∪ exp_names_funs funs))
Termination
  WF_REL_TAC ‘inv_image $< $ λx. case x of
   | INL e => exp_size e
   | INR (INL es) => list_size exp_size es
   | INR (INR (INL pes)) => list_size (pair_size pat_size exp_size) pes
   | INR (INR (INR funs)) =>
       list_size (pair_size mlstring_size
                  (pair_size mlstring_size exp_size)) funs’
End

Theorem no_Open_thm[local]:
  (no_Open (Raise e) ⇔ no_Open e) ∧
  (no_Open (Handle e pes) ⇔ no_Open e ∧ EVERY (λ(p,e). no_Open e) pes) ∧
  (no_Open (Lit l) ⇔ T) ∧
  (no_Open (Con cn es) ⇔ EVERY no_Open es) ∧
  (no_Open (Var v) ⇔ T) ∧
  (no_Open (Fun x e) ⇔ no_Open e) ∧
  (no_Open (App op es) ⇔ EVERY no_Open es) ∧
  (no_Open (Log lop e1 e2) ⇔ no_Open e1 ∧ no_Open e2) ∧
  (no_Open (If e1 e2 e3) ⇔ no_Open e1 ∧ no_Open e2 ∧ no_Open e3) ∧
  (no_Open (Mat e pes) ⇔ no_Open e ∧ EVERY (λ(p,e). no_Open e) pes) ∧
  (no_Open (Let xo e1 e2) ⇔ no_Open e1 ∧ no_Open e2) ∧
  (no_Open (Letrec funs e) ⇔
     no_Open e ∧ EVERY (λ(f,x,e). no_Open e) funs) ∧
  (no_Open (Tannot e t) ⇔ no_Open e) ∧
  (no_Open (Lannot e a) ⇔ no_Open e) ∧
  (no_Open (Open path e) ⇔ F)
Proof
  ‘no_Open = every_exp (λx. ¬is_Open x)’
    by simp [FUN_EQ_THM,source_dceTheory.no_Open_def]
  >> simp [source_dceTheory.is_Open_def,SF ETA_ss]
QED

Theorem annotate_exp_tree_properties[local]:
  ∀e t tree limit captures.
    annotate_exp t e = (tree,limit,captures) ⇒
    source_dce$no_Open (tree_exp tree) = source_dce$no_Open e ∧
    exp_names (tree_exp tree) = exp_names e ∧
    ∀constructors.
      check_exp_constructors constructors (tree_exp tree) =
      check_exp_constructors constructors e
Proof
  Induct_on ‘e’
  >> simp [Once annotate_exp_def] >> rw [] >> rpt (pairarg_tac >> gvs [])
  >> simp [tree_exp_def,no_Open_thm,exp_names_def,check_exp_constructors_def]
  >> metis_tac []
QED

Theorem annotate_all_name_bound[local]:
  (∀t e tree n fvs x.
    annotate_exp t e = (tree,n,fvs) ∧ source_dce$no_Open e ∧
    x ∈ exp_names e ⇒ bump x 0 ≤ n) ∧
  (∀t es trees n fvs x.
    annotate_exps t es = (trees,n,fvs) ∧ EVERY source_dce$no_Open es ∧
    x ∈ exp_names_exps es ⇒ bump x 0 ≤ n) ∧
  (∀t pes trees n fvs x.
    annotate_pes t pes = (trees,n,fvs) ∧
    EVERY (λ(p,e). source_dce$no_Open e) pes ∧
    x ∈ exp_names_pes pes ⇒ bump x 0 ≤ n) ∧
  (∀t funs trees n fvs x.
    annotate_funs t funs = (trees,n,fvs) ∧
    EVERY (λ(f,x,e). source_dce$no_Open e) funs ∧
    x ∈ exp_names_funs funs ⇒ bump x 0 ≤ n)
Proof
  ho_match_mp_tac annotate_exp_ind >> rpt conj_tac >> rpt gen_tac
  >> rw [Once annotate_exp_def] >> rpt (pairarg_tac >> gvs [])
  >> gvs [exp_names_def,no_Open_thm]
  >- metis_tac [bump_mono,ZERO_LESS_EQ]
  >- metis_tac [bump_le,LESS_EQ_TRANS]
  >- metis_tac [bump_all_le,MAX_LE,LESS_EQ_TRANS]
  >- metis_tac [bump_all_le,MAX_LE,LESS_EQ_TRANS]
  >- (
    qmatch_asmsub_rename_tac ‘exp_names (Var identifier)’
    >> Cases_on ‘identifier’
    >> gvs [exp_names_def])
  >- (
    Cases_on ‘name’
    >> gvs [exp_names_def]
    >> metis_tac [bump_le,bump_mono,ZERO_LESS_EQ,MAX_LE,LESS_EQ_TRANS])
  >- (Cases_on ‘NULL es’ >> gvs [])
  >- (Cases_on ‘NULL es’ >> gvs [] >> gvs [NULL_EQ,exp_names_def])
  >- metis_tac [bump_pattern_names]
  >- metis_tac [bump_patterns_le,LESS_EQ_TRANS]
  >- metis_tac [bump_mono,ZERO_LESS_EQ]
  >- metis_tac [bump_mono,bump_le,ZERO_LESS_EQ,LESS_EQ_TRANS]
  >- metis_tac [bump_le,LESS_EQ_TRANS]
QED

Theorem rename_var_bind_other[local]:
  x ≠ z ⇒ rename_var (ren |+ (x,y)) (Short z) = rename_var ren (Short z)
Proof
  simp [rename_var_def,FLOOKUP_UPDATE]
QED

Theorem lift_env_rel_rename_bind[local]:
  lift_env_rel R (fdomsub fvs x) ren env env' ∧ R v v' ∧
  (∀z. z ∈ FDOM fvs ∧ z ≠ x ⇒
    rename_var ren (Short z) ≠ (Short y:(mlstring,mlstring) id)) ⇒
  lift_env_rel R fvs (ren |+ (x,y))
    (env with v := nsBind x v env.v)
    (env' with v := nsBind y v' env'.v)
Proof
  rw [lift_env_rel_def,FDOM_DOMSUB]
  >> qmatch_goalsub_rename_tac ‘nsLookup _ (Short z)’ >> Cases_on ‘z = x’
  >> gvs [rename_var_bind,rename_var_bind_other]
QED

Definition lift_match_rel_def:
  (lift_match_rel R (Match bs) (Match bs') ⇔
    LIST_REL (λa b. FST a = FST b ∧ R (SND a) (SND b)) bs bs') ∧
  (lift_match_rel R No_match No_match ⇔ T) ∧
  (lift_match_rel R Match_type_error Match_type_error ⇔ T) ∧
  (lift_match_rel R _ _ ⇔ F)
End

Theorem lift_match_rel_cases[local]:
  lift_match_rel R r r' ⇔
    r = No_match ∧ r' = No_match ∨
    r = Match_type_error ∧ r' = Match_type_error ∨
    ∃bs bs'. r = Match bs ∧ r' = Match bs' ∧
      LIST_REL (λa b. FST a = FST b ∧ R (SND a) (SND b)) bs bs'
Proof
  Cases_on ‘r’ >> Cases_on ‘r'’ >> simp [lift_match_rel_def]
QED

Theorem lift_value_rel_pmatch[local]:
  (∀envC refs p v bs refs' v' bs' C E.
    lift_value_rel C E v v' ∧
    LIST_REL (λa b. FST a = FST b ∧ lift_value_rel C E (SND a) (SND b)) bs bs' ∧
    (∀loc. OPTREL (sv_rel (lift_value_rel C E))
      (store_lookup loc refs) (store_lookup loc refs')) ⇒
    lift_match_rel (lift_value_rel C E)
      (pmatch envC refs p v bs) (pmatch envC refs' p v' bs')) ∧
  (∀envC refs ps vs bs refs' vs' bs' C E.
    LIST_REL (lift_value_rel C E) vs vs' ∧
    LIST_REL (λa b. FST a = FST b ∧ lift_value_rel C E (SND a) (SND b)) bs bs' ∧
    (∀loc. OPTREL (sv_rel (lift_value_rel C E))
      (store_lookup loc refs) (store_lookup loc refs')) ⇒
    lift_match_rel (lift_value_rel C E)
      (pmatch_list envC refs ps vs bs) (pmatch_list envC refs' ps vs' bs'))
Proof
  ho_match_mp_tac pmatch_ind >> rpt conj_tac >> rpt gen_tac
  >> rw [lift_value_rel_cases_l,LIST_REL_CONS1] >> imp_res_tac LIST_REL_LENGTH
  >> simp [Once pmatch_def] >> simp [Once pmatch_def,lift_match_rel_def]
  >- (rpt IF_CASES_TAC >> simp [lift_match_rel_def])
  >- (
    namedCases_on ‘nsLookup envC n’ ["","entry"] >> simp [lift_match_rel_def]
    >> PairCases_on ‘entry’ >> rw [lift_match_rel_def] >> metis_tac [])
  >- (IF_CASES_TAC >> gvs [lift_match_rel_def] >> metis_tac [])
  >- (
    qmatch_goalsub_rename_tac ‘store_lookup location refs’
    >> qpat_assum ‘∀loc. OPTREL _ _ _’ (qspec_then ‘location’ mp_tac)
    >> Cases_on ‘store_lookup location refs’ >> Cases_on ‘store_lookup location refs'’
    >> rw [sv_rel_cases] >> gvs [lift_match_rel_def] >> metis_tac [])
  >> first_x_assum drule_all >> strip_tac >> gvs [lift_match_rel_cases]
  >> first_x_assum drule_all >> strip_tac >> gvs []
QED

Theorem lift_can_pmatch_all[local]:
  ∀ps envC refs refs' v v' C E.
    lift_value_rel C E v v' ∧
    LIST_REL (sv_rel (lift_value_rel C E)) refs refs' ⇒
    can_pmatch_all envC refs ps v = can_pmatch_all envC refs' ps v'
Proof
  Induct_on ‘ps’ >> rpt gen_tac >> strip_tac
  >> simp [can_pmatch_all_def]
  >> qmatch_goalsub_rename_tac ‘pmatch envC refs pattern v []’
  >> have ‘lift_match_rel (lift_value_rel C E)
        (pmatch envC refs pattern v [])
        (pmatch envC refs' pattern v' [])’
  >- (
    irule (CONJUNCT1 lift_value_rel_pmatch) >> simp []
    >> gen_tac >> irule LIST_REL_OPTREL_store_lookup
    >> simp [])
  >> gvs [lift_match_rel_cases] >> metis_tac []
QED

Theorem lift_env_rel_build_rec_env[local]:
  lift_env_rel R (delete_all (MAP FST funs) fvs) ren env env' ∧
  (∀x y. x ∈ FDOM fvs ∧
    rename_var ren (Short x) = (Short y:(mlstring,mlstring) id) ⇒
    (MEM x (MAP FST funs) ⇔ MEM y (MAP FST funs')) ∧
    (MEM x (MAP FST funs) ⇒
      R (Recclosure env funs x) (Recclosure capture_env funs' y))) ⇒
  lift_env_rel R fvs ren
    (env with v := build_rec_env funs env env.v)
    (env' with v := build_rec_env funs' capture_env env'.v)
Proof
  rw [lift_env_rel_def,delete_all_domain]
  >> simp [nsLookup_build_rec_env]
  >> qmatch_goalsub_rename_tac ‘nsLookup _ (Short name)’
  >> namedCases_on ‘FLOOKUP ren name’ ["","renamed"]
  >> gvs [rename_var_def,nsLookup_build_rec_env]
  >> qpat_x_assum ‘∀x y. _’ (qspec_then ‘name’ mp_tac) >> simp [] >> strip_tac
  >> Cases_on ‘MEM name (MAP FST funs)’ >> gvs []
  >> qpat_x_assum ‘∀x. x ∈ FDOM fvs ∧ _ ⇒ _’ (qspec_then ‘name’ mp_tac) >> simp []
QED

Definition exp_free_names_def:
  exp_free_names (Raise e) = exp_free_names e ∧
  exp_free_names (Handle e pes) = exp_free_names e ∪ exp_free_names_pes pes ∧
  exp_free_names (Lit l) = {} ∧
  exp_free_names (Con cn es) = exp_free_names_exps es ∧
  exp_free_names (Var (Short x)) = {x} ∧
  exp_free_names (Var (Long mn x)) = {} ∧
  exp_free_names (Fun x e) = exp_free_names e DELETE x ∧
  exp_free_names (App op es) = exp_free_names_exps es ∧
  exp_free_names (Log op e1 e2) = exp_free_names e1 ∪ exp_free_names e2 ∧
  exp_free_names (If e1 e2 e3) =
    exp_free_names e1 ∪ exp_free_names e2 ∪ exp_free_names e3 ∧
  exp_free_names (Mat e pes) = exp_free_names e ∪ exp_free_names_pes pes ∧
  exp_free_names (Let NONE e1 e2) = exp_free_names e1 ∪ exp_free_names e2 ∧
  exp_free_names (Let (SOME x) e1 e2) =
    exp_free_names e1 ∪ (exp_free_names e2 DELETE x) ∧
  exp_free_names (Letrec funs e) =
    (exp_free_names_funs funs ∪ exp_free_names e) DIFF set (MAP FST funs) ∧
  exp_free_names (Tannot e ty) = exp_free_names e ∧
  exp_free_names (Lannot e loc) = exp_free_names e ∧
  exp_free_names (Open path e) = exp_free_names e ∧
  exp_free_names_exps [] = {} ∧
  exp_free_names_exps (e::es) = exp_free_names e ∪ exp_free_names_exps es ∧
  exp_free_names_pes [] = {} ∧
  exp_free_names_pes ((p,e)::pes) =
    (exp_free_names e DIFF set (pat_bindings p)) ∪ exp_free_names_pes pes ∧
  exp_free_names_funs [] = {} ∧
  exp_free_names_funs ((f,x,e)::funs) =
    (exp_free_names e DELETE x) ∪ exp_free_names_funs funs
Termination
  WF_REL_TAC ‘inv_image $< $ λx. case x of
   | INL e => exp_size e
   | INR (INL es) => list_size exp_size es
   | INR (INR (INL pes)) => list_size (pair_size pat_size exp_size) pes
   | INR (INR (INR funs)) =>
       list_size (pair_size mlstring_size
                  (pair_size mlstring_size exp_size)) funs’
End

Theorem annotate_free_names[local]:
  (∀t e tree n fvs.
    annotate_exp t e = (tree,n,fvs) ∧ source_dce$no_Open e ⇒
    FDOM fvs = exp_free_names e) ∧
  (∀t es trees n fvs.
    annotate_exps t es = (trees,n,fvs) ∧ EVERY source_dce$no_Open es ⇒
    FDOM fvs = exp_free_names_exps es) ∧
  (∀t pes trees n fvs.
    annotate_pes t pes = (trees,n,fvs) ∧
    EVERY (λ(p,e). source_dce$no_Open e) pes ⇒
    FDOM fvs = exp_free_names_pes pes) ∧
  (∀t funs trees n fvs.
    annotate_funs t funs = (trees,n,fvs) ∧
    EVERY (λ(f,x,e). source_dce$no_Open e) funs ⇒
    FDOM fvs = exp_free_names_funs funs)
Proof
  ho_match_mp_tac annotate_exp_ind >> rpt conj_tac >> rpt gen_tac
  >> rw [Once annotate_exp_def] >> rpt (pairarg_tac >> gvs [])
  >> gvs [exp_free_names_def,FDOM_FUNION,FDOM_DOMSUB,
          delete_all_domain,str_empty_def,no_Open_thm]
  >- metis_tac [UNION_COMM]
  >- (
    qmatch_goalsub_rename_tac ‘exp_free_names (Var identifier)’
    >> Cases_on ‘identifier’
    >> simp [exp_free_names_def])
  >- simp [UNION_ASSOC]
  >- (
    qmatch_goalsub_rename_tac ‘exp_free_names (Let binder _ _)’
    >> Cases_on ‘binder’
    >> simp [exp_free_names_def,FDOM_DOMSUB])
  >- (
    qmatch_goalsub_rename_tac ‘exp_free_names_exps expressions’
    >> Cases_on ‘expressions’
    >> gvs [exp_free_names_def,FDOM_FUNION])
QED

Definition lift_state_fresh_def:
  lift_state_fresh (n:num,ds:dec list,used:mlstring |-> unit) ⇔
    ∀k. n ≤ k ⇒ FLOOKUP used (make_name k) = NONE
End

Theorem lift_state_fresh_used[local]:
  lift_state_fresh (n,ds,used) ∧ name ∈ FDOM used ∧ n ≤ k ⇒ name ≠ make_name k
Proof
  rw [lift_state_fresh_def] >> metis_tac [flookup_thm]
QED

Theorem bind_all_state_fresh[local]:
  (∀x. x ∈ FDOM used ⇒ bump x 0 ≤ n) ∧
  EVERY (λx. bump x 0 ≤ n) names ⇒
  lift_state_fresh (n,ds,bind_all names used)
Proof
  rw [lift_state_fresh_def,bind_all_lookup,EVERY_MEM,FLOOKUP_DEF]
  >> metis_tac [bump_make_name,LESS_EQ_TRANS]
QED

Theorem choose_name_state_fresh[local]:
  lift_state_fresh (n,ds,used) ∧ bump x 0 ≤ n ∧
  choose_name bound x (n,ds,used) = (y,st1) ⇒
  lift_state_fresh st1 ∧ FLOOKUP used y = NONE
Proof
  PairCases_on ‘st1’
  >> simp [lift_state_fresh_def] >> strip_tac >> drule_all choose_name_fresh >> simp []
QED

Theorem emit_dec_state_fresh[local]:
  lift_state_fresh st ⇒ lift_state_fresh (emit_dec d st)
Proof
  PairCases_on ‘st’
  >> simp [emit_dec_def,lift_state_fresh_def]
QED

Theorem emit_value_state_fresh[local]:
  lift_state_fresh st ∧ emit_value e st = (e1,st1) ⇒
  lift_state_fresh st1
Proof
  PairCases_on ‘st’
  >> rw [emit_value_def] >> rw [lift_state_fresh_def,FLOOKUP_UPDATE,make_name_injective]
  >> fs [lift_state_fresh_def] >> qpat_x_assum ‘∀k. _’ irule >> decide_tac
QED

Theorem choose_names_fresh[local]:
  ∀xs bound n ds used ys n1 ds1 used1.
    EVERY (λx. bump x 0 ≤ n) xs ∧ lift_state_fresh (n,ds,used) ∧
    choose_names bound xs (n,ds,used) = (ys,n1,ds1,used1) ⇒
    lift_state_fresh (n1,ds1,used1) ∧ n ≤ n1 ∧ ds1 = ds ∧
    LENGTH ys = LENGTH xs ∧ ALL_DISTINCT ys ∧
    FDOM used1 = FDOM used ∪ set xs ∪ set ys ∧
    (∀y. MEM y ys ⇒ FLOOKUP used y = NONE) ∧
    LIST_REL (λx y. x = y ∧ FLOOKUP bound y = NONE ∨ ∃k. n ≤ k ∧ y = make_name k)
      xs ys
Proof
  Induct_on ‘xs’
  >- (rw [choose_names_def] >> gvs [])
  >> qpat_x_assum ‘∀bound n ds used ys n1 ds1 used1. _’ (assume_named_tac "IH")
  >> rpt gen_tac >> strip_tac >> gvs [Once choose_names_def]
  >> rpt (pairarg_tac >> gvs [])
  >> qmatch_asmsub_rename_tac ‘choose_name bound x _ = (y,middle)’
  >> PairCases_on ‘middle’ >> gvs [lift_state_fresh_def]
  >> drule_all choose_name_fresh >> strip_tac >> gvs []
  >> asm_x "IH"
    (drule_at (Pat ‘choose_names _ _ _ = _’) o REWRITE_RULE [lift_state_fresh_def])
  >> impl_tac >- (fs [EVERY_MEM] >> metis_tac [LESS_EQ_TRANS])
  >> strip_tac >> gvs [FLOOKUP_UPDATE] >> rpt conj_tac
  >- metis_tac []
  >- (simp [EXTENSION] >> metis_tac [])
  >- metis_tac []
  >- (
    qpat_x_assum ‘choose_name _ _ _ = _’ mp_tac >> rw [choose_name_def]
    >> metis_tac [LESS_EQ_REFL])
  >> qpat_x_assum ‘LIST_REL _ xs _’ mp_tac >> match_mp_tac LIST_REL_mono
  >> rw [] >> metis_tac [LESS_EQ_TRANS]
QED

Theorem initial_let_state_fresh[local]:
  annotate_exp t e = (tree,n,fvs) ⇒
  lift_state_fresh (bump_pat n p,[],bind_all (pat_bindings p) fvs)
Proof
  strip_tac
  >> irule bind_all_state_fresh >> rw [EVERY_MEM]
  >- metis_tac [CONJUNCT1 annotate_free_name_bound,
                CONJUNCT1 bump_patterns_le,LESS_EQ_TRANS]
  >> metis_tac [CONJUNCT1 bump_pattern_names]
QED

Theorem choose_names_renaming_hygiene[local]:
  EVERY (λname. bump name 0 ≤ n) names ∧ lift_state_fresh (n,ds,used) ∧
  choose_names bound names (n,ds,used) = (names',n1,ds1,used1) ∧
  (∀name. name ∈ source_names ⇒ bump name 0 ≤ n) ∧
  (∀original mapped. FLOOKUP ren original = SOME mapped ∧ mapped ≠ original ⇒
    mapped ∉ source_names) ⇒
  ∀original mapped.
    FLOOKUP (ren |++ ZIP (names,names')) original = SOME mapped ∧ mapped ≠ original ⇒
    mapped ∉ source_names
Proof
  strip_tac >> drule_all choose_names_fresh >> strip_tac
  >> rw [miscTheory.flookup_update_list_some]
  >- (
    imp_res_tac ALOOKUP_MEM >> gvs [MEM_REVERSE,LIST_REL_EVERY_ZIP,EVERY_MEM]
    >> qpat_x_assum ‘∀e. MEM e (ZIP _) ⇒ _’ drule
    >> rw [] >> metis_tac [bump_make_name,LESS_EQ_TRANS])
  >> metis_tac []
QED

Theorem recursive_names_all_names[local]:
  ∀funs name. MEM name (MAP FST funs) ⇒ name ∈ exp_names_funs funs
Proof
  Induct_on ‘funs’
  >- simp []
  >> qx_genl_tac [‘binding’,‘name’] >> PairCases_on ‘binding’ >> rw [exp_names_def]
  >> metis_tac []
QED

Theorem initial_letrec_state_fresh[local]:
  annotate_funs t funs = (trees,n,fvs) ∧
  EVERY (λ(f,x,e). source_dce$no_Open e) funs ⇒
  lift_state_fresh (n,[],bind_all (MAP FST funs) fvs)
Proof
  strip_tac
  >> irule bind_all_state_fresh >> rw [EVERY_MEM]
  >- metis_tac [cj 4 annotate_free_name_bound]
  >> metis_tac [cj 4 annotate_all_name_bound,recursive_names_all_names]
QED

Inductive tree_names_bounded:
  (∀limit e fvs value children.
    (∀x. x ∈ exp_names e ⇒ bump x 0 ≤ limit) ∧
    EVERY (tree_names_bounded limit) children ⇒
    tree_names_bounded limit (Lift e fvs value children))
End

Theorem tree_names_bounded_Lift[local]:
  tree_names_bounded limit (Lift e fvs value children) ⇔
  (∀x. x ∈ exp_names e ⇒ bump x 0 ≤ limit) ∧
  EVERY (tree_names_bounded limit) children
Proof
  simp [Once tree_names_bounded_cases]
QED

Theorem lift_state_extends_counter[local]:
  lift_state_extends st st1 ⇒ FST st ≤ FST st1
Proof
  PairCases_on ‘st’
  >> PairCases_on ‘st1’ >> simp [lift_state_extends_def]
QED

Theorem annotate_tree_names_within[local]:
  (∀t e tree n fvs m.
    annotate_exp t e = (tree,n,fvs) ∧ (∀x. x ∈ exp_names e ⇒ bump x 0 ≤ m) ⇒
    tree_names_bounded m tree) ∧
  (∀t es trees n fvs m.
    annotate_exps t es = (trees,n,fvs) ∧
    (∀x. x ∈ exp_names_exps es ⇒ bump x 0 ≤ m) ⇒
    EVERY (tree_names_bounded m) trees) ∧
  (∀t pes trees n fvs m.
    annotate_pes t pes = (trees,n,fvs) ∧
    (∀x. x ∈ exp_names_pes pes ⇒ bump x 0 ≤ m) ⇒
    EVERY (tree_names_bounded m) trees) ∧
  (∀t funs trees n fvs m.
    annotate_funs t funs = (trees,n,fvs) ∧
    (∀x. x ∈ exp_names_funs funs ⇒ bump x 0 ≤ m) ⇒
    EVERY (tree_names_bounded m) trees)
Proof
  ho_match_mp_tac annotate_exp_ind >> rpt conj_tac >> rpt gen_tac
  >> rw [Once annotate_exp_def] >> rpt (pairarg_tac >> gvs [])
  >> gvs [tree_names_bounded_Lift,exp_names_def]
  >~ [‘Let name’] >- (Cases_on ‘name’ >> gvs [exp_names_def] >> metis_tac [])
  >~ [‘NULL es’] >- (Cases_on ‘NULL es’ >> gvs [] >> metis_tac [])
  >> metis_tac []
QED

Theorem annotate_tree_names_bounded[local]:
  (∀t e tree n fvs.
    annotate_exp t e = (tree,n,fvs) ∧ source_dce$no_Open e ⇒
    tree_names_bounded n tree) ∧
  (∀t es trees n fvs.
    annotate_exps t es = (trees,n,fvs) ∧ EVERY source_dce$no_Open es ⇒
    EVERY (tree_names_bounded n) trees) ∧
  (∀t pes trees n fvs.
    annotate_pes t pes = (trees,n,fvs) ∧
    EVERY (λ(p,e). source_dce$no_Open e) pes ⇒
    EVERY (tree_names_bounded n) trees) ∧
  (∀t funs trees n fvs.
    annotate_funs t funs = (trees,n,fvs) ∧
    EVERY (λ(f,x,e). source_dce$no_Open e) funs ⇒
    EVERY (tree_names_bounded n) trees)
Proof
  rw [] >> metis_tac [annotate_tree_names_within,annotate_all_name_bound]
QED

Theorem lift_env_rel_bindings[local]:
  LIST_REL (λ(x,v) (y,w). x = y ∧ R v w) bindings bindings' ∧
  lift_env_rel R (delete_all (MAP FST bindings) fvs) ren env env' ∧
  (∀x y. x ∈ FDOM fvs ∧ ¬MEM x (MAP FST bindings) ∧
          MEM y (MAP FST bindings) ⇒
    rename_var ren (Short x) ≠ (Short y:(mlstring,mlstring) id)) ⇒
  lift_env_rel R fvs (delete_all (MAP FST bindings) ren)
    (env with v := nsBindList bindings env.v)
    (env' with v := nsBindList bindings' env'.v)
Proof
  strip_tac
  >> drule LIST_REL_MAP_FST >> strip_tac >> fs [lift_env_rel_def,delete_all_domain]
  >> rw [nsBindList_long_lookup] >> qmatch_goalsub_rename_tac
    ‘nsLookup _ (Short lookup_name:(mlstring,mlstring) id)’
  >> drule ALOOKUP_LIST_REL_OPTREL >> disch_then (qspec_then ‘lookup_name’ assume_tac)
  >> Cases_on ‘MEM lookup_name (MAP FST bindings)’
  >> fs [rename_var_def,delete_all_lookup]
  >- (
    Cases_on ‘ALOOKUP bindings lookup_name’
    >> Cases_on ‘ALOOKUP bindings' lookup_name’
    >> gvs [nsBindList_short_lookup,ALOOKUP_NONE])
  >> ‘ALOOKUP bindings lookup_name = NONE ∧
   ALOOKUP bindings' lookup_name = NONE’ by metis_tac [ALOOKUP_NONE]
  >> qpat_x_assum ‘∀x y. _ ⇒ _’ (qspec_then ‘lookup_name’ assume_tac)
  >> Cases_on ‘FLOOKUP ren lookup_name’
  >> gvs [nsBindList_short_lookup,lift_env_rel_def,delete_all_domain,
          rename_var_def]
  >> qpat_x_assum ‘∀x. x ∈ FDOM fvs ∧ _ ⇒ _’ (qspec_then ‘lookup_name’ mp_tac)
  >> gvs [GSYM ALOOKUP_NONE]
QED

Definition lift_function_body_def:
  lift_function_body bound ren st x body =
    if is_Fun (tree_exp body) then
      lower_exp LiftValues (bound |+ (x,())) (fdomsub ren x) st body
    else
      lift_exp LiftValues (bound |+ (x,())) (fdomsub ren x) st body
End

Theorem lower_function_body[local]:
  lower_exp mode bound ren st (Lift (Fun x e) fvs value [body]) =
    let (e',st') = lift_function_body bound ren st x body in
      (Fun x e',st')
Proof
  simp [Once lift_exp_def,lift_function_body_def]
QED

Theorem lower_annotated_function_shape[local]:
  annotate_exp t e = (tree,limit,captures) ∧ is_Fun (tree_exp tree) ∧
  lower_exp mode bound ren st tree = (compiled,st') ⇒
  ∃arg body body'. tree_exp tree = Fun arg body ∧ compiled = Fun arg body'
Proof
  strip_tac
  >> have ‘∃arg body. tree_exp tree = Fun arg body’
  >- (Cases_on ‘tree_exp tree’ >> gvs [is_Fun_def])
  >> qmatch_asmsub_rename_tac ‘tree_exp tree = Fun arg body’
  >> drule annotate_exp_reannotate >> simp [] >> disch_tac
  >> qpat_x_assum ‘annotate_exp t (Fun arg body) = _’
    (mp_tac o SRULE [Once annotate_exp_def])
  >> namedCases_on ‘annotate_exp t body’ ["body_tree body_limit body_captures"]
  >> strip_tac >> gvs [lower_function_body,tree_exp_def] >> rpt (pairarg_tac >> gvs [])
QED

Theorem lift_function_body_state_extends[local]:
  lift_function_body bound ren st x body = (e,st') ⇒
  lift_state_extends st st'
Proof
  rw [lift_function_body_def]
  >> metis_tac [lift_exp_state_extends]
QED

Theorem lift_function_body_constructors[local]:
  lift_function_body bound ren st x tree = (e,st') ∧ tree_constructors c tree ⇒
  check_exp_constructors c e
Proof
  rw [lift_function_body_def]
  >> metis_tac [lift_exp_constructors]
QED

Definition lift_decs_env_def:
  (lift_decs_env (s:'ffi semanticPrimitives$state) [] env target ⇔
    target = env) ∧
  (lift_decs_env s (d::ds) env target ⇔
    ∃delta.
      evaluate_decs s env [d] = (s,Rval delta) ∧
      lift_decs_env s ds (extend_dec_env delta env) target)
End

Theorem lift_decs_env_evaluates[local]:
  ∀ds env target.
    lift_decs_env s ds env target ⇒
    ∃delta. evaluate_decs s env ds = (s,Rval delta) ∧
      target = extend_dec_env delta env
Proof
  Induct_on ‘ds’ >> rw [lift_decs_env_def]
  >- simp [extend_dec_env_def,sem_env_component_equality]
  >> first_x_assum drule >> rw []
  >> simp [Once evaluate_decs_cons,combine_dec_result_def] >> simp [extend_dec_env_def]
QED

Theorem make_local_evaluates[local]:
  lift_decs_env (s:'ffi semanticPrimitives$state) (REVERSE ds) env target ⇒
  evaluate_decs s env [make_local ds d] = evaluate_decs s target [d]
Proof
  strip_tac
  >> Cases_on ‘ds’
  >- gvs [lift_decs_env_def,make_local_def]
  >> drule lift_decs_env_evaluates
  >> disch_then (qx_choose_then ‘delta’ strip_assume_tac)
  >> fs [make_local_def,Once evaluate_decs_def,fix_clock_def]
QED

Definition lift_state_rel_def:
  lift_state_rel R D (s:'ffi semanticPrimitives$state) s' ⇔
    s.clock = s'.clock ∧ s.ffi = s'.ffi ∧
    s.ptr_eq_oracle = s'.ptr_eq_oracle ∧
    s.next_type_stamp = s'.next_type_stamp ∧
    s.next_exn_stamp = s'.next_exn_stamp ∧
    D s.eval_state s'.eval_state ∧
    LIST_REL (sv_rel R) s.refs s'.refs
End

Definition lift_result_rel_def:
  (lift_result_rel success_rel R (Rval x) (Rval y) ⇔ success_rel x y) ∧
  (lift_result_rel success_rel R (Rerr (Rraise x)) (Rerr (Rraise y)) ⇔ R x y) ∧
  (lift_result_rel success_rel R (Rerr (Rabort a)) (Rerr (Rabort b)) ⇔ a = b) ∧
  (lift_result_rel success_rel R _ _ ⇔ F)
End

Theorem lift_result_rel_cases[local]:
  lift_result_rel success_rel R r r' ⇔
    (∃x y. r = Rval x ∧ r' = Rval y ∧ success_rel x y) ∨
    (∃x y. r = Rerr (Rraise x) ∧ r' = Rerr (Rraise y) ∧ R x y) ∨
    (∃a. r = Rerr (Rabort a) ∧ r' = Rerr (Rabort a))
Proof
  map_every Cases_on [‘r’,‘r'’] >> simp [lift_result_rel_def]
  >> qmatch_goalsub_rename_tac ‘lift_result_rel _ _ (Rerr e1) (Rerr e2)’
  >> map_every Cases_on [‘e1’,‘e2’] >> simp [lift_result_rel_def,EQ_SYM_EQ]
QED

Definition lift_eval_result_rel_def:
  lift_eval_result_rel R D success_rel (s,r) (s',r') ⇔
    lift_state_rel R D s s' ∧ lift_result_rel success_rel R r r'
End

Theorem lift_state_rel_dec_clock[local]:
  lift_state_rel R D s s' ⇒
  lift_state_rel R D (dec_clock s) (dec_clock s')
Proof
  simp [lift_state_rel_def,dec_clock_def]
QED

Theorem lift_value_rel_bool[local]:
  lift_value_rel C E v v' ⇒ (v = Boolv b ⇔ v' = Boolv b)
Proof
  Cases_on ‘v’
  >> Cases_on ‘b’ >> rw [lift_value_rel_cases_l,Boolv_def]
  >> imp_res_tac LIST_REL_LENGTH >> metis_tac [LENGTH_NIL]
QED

Theorem lift_value_rel_build_conv[local]:
  LIST_REL (lift_value_rel C E) vs vs' ⇒
  OPTREL (lift_value_rel C E)
    (build_conv c cn vs) (build_conv c cn vs')
Proof
  strip_tac
  >> namedCases_on ‘cn’ ["","constructor"]
  >> simp [build_conv_def,lift_value_rel_cases_l]
  >> namedCases_on ‘nsLookup c constructor’ ["","entry"] >> simp [] >> Cases_on ‘entry’
  >> simp [lift_value_rel_cases_l]
QED

Theorem lift_funs_bindings_prefix[local]:
  ∀fs trees bound ren st funs st'.
    lift_funs bound ren st fs trees = (funs,st') ⇒
    MAP (λ(f,x,e). (f,x)) funs = TAKE (LENGTH trees) fs
Proof
  Induct_on ‘fs’ >> rpt gen_tac
  >> Cases_on ‘trees’ >> simp [Once lift_exp_def]
  >> qmatch_goalsub_rename_tac ‘lift_funs _ _ _ (entry::fs) _’
  >> PairCases_on ‘entry’ >> rw [Once lift_exp_def]
  >> rpt (pairarg_tac >> gvs []) >> metis_tac []
QED

Theorem lift_funs_names_prefix[local]:
  lift_funs bound ren st fs trees = (funs,st') ⇒
  MAP FST funs = TAKE (LENGTH trees) (MAP FST fs)
Proof
  strip_tac
  >> drule lift_funs_bindings_prefix >> disch_then (mp_tac o Q.AP_TERM ‘MAP FST’)
  >> simp [MAP_MAP_o,o_DEF,ELIM_UNCURRY,ETA_THM,MAP_TAKE]
QED

Theorem lift_pes_patterns[local]:
  ∀ps trees mode bound ren st pes st1.
    lift_pes mode bound ren st ps trees = (pes,st1) ∧
    LENGTH ps ≤ LENGTH trees ⇒ MAP FST pes = ps
Proof
  Induct_on ‘ps’ >> rpt gen_tac
  >> Cases_on ‘trees’ >> rw [Once lift_exp_def]
  >> rpt (pairarg_tac >> gvs []) >> metis_tac []
QED

Theorem lift_annotated_pes_patterns[local]:
  annotate_pes t pes = (trees,n,fvs) ∧
  lift_pes mode bound ren st (MAP FST pes) trees = (pes',st1) ⇒
  MAP FST pes' = MAP FST pes
Proof
  strip_tac
  >> drule_all (cj 2 annotate_LENGTH) >> strip_tac >> drule lift_pes_patterns >> simp []
QED

Theorem lift_value_rel_opapp[local]:
  (∀f f' arg arg'. C f f' ∧ lift_value_rel C E arg arg' ⇒
    OPTREL P (do_opapp [f;arg]) (do_opapp [f';arg'])) ∧
  LIST_REL (lift_value_rel C E) vs vs' ⇒
  OPTREL P (do_opapp vs) (do_opapp vs')
Proof
  strip_tac
  >> namedCases_on ‘vs’ ["","source_function source_args"]
  >> namedCases_on ‘vs'’ ["","target_function target_args"] >> gvs []
  >- simp [do_opapp_def]
  >> namedCases_on ‘source_args’ ["","source_argument source_tail"]
  >> namedCases_on ‘target_args’ ["","target_argument target_tail"] >> gvs []
  >- simp [do_opapp_def]
  >> Cases_on ‘source_tail’ >> Cases_on ‘target_tail’ >> gvs []
  >> Cases_on ‘source_function’ >> gvs [lift_value_rel_cases_l] >> simp [do_opapp_def]
  >> qpat_x_assum ‘∀f f' arg arg'. _’ imp_res_tac >> gvs [do_opapp_def]
QED

Theorem lift_value_rel_v_to_list[local]:
  ∀v v'. lift_value_rel C E v v' ⇒
    OPTREL (LIST_REL (lift_value_rel C E)) (v_to_list v) (v_to_list v')
Proof
  ho_match_mp_tac v_to_list_ind >> rpt conj_tac >> rpt gen_tac
  >> rw [lift_value_rel_cases_l,LIST_REL_CONS1,v_to_list_def] >> gvs [v_to_list_def]
  >> qmatch_goalsub_rename_tac
    ‘OPTREL _
      (case v_to_list source_tail of NONE => NONE | SOME vs => SOME (source_head::vs))
      (case v_to_list target_tail of NONE => NONE | SOME vs => SOME (target_head::vs))’
  >> qpat_x_assum ‘∀v'. _’ (qspec_then ‘target_tail’ mp_tac) >> simp []
  >> Cases_on ‘v_to_list source_tail’ >> Cases_on ‘v_to_list target_tail’ >> simp []
QED

Definition lift_thunk_result_rel_def:
  (lift_thunk_result_rel R BadRef BadRef ⇔ T) ∧
  (lift_thunk_result_rel R NotThunk NotThunk ⇔ T) ∧
  (lift_thunk_result_rel R (IsThunk mode value) (IsThunk mode' value') ⇔
    mode = mode' ∧ R value value') ∧
  (lift_thunk_result_rel R _ _ ⇔ F)
End

Theorem lift_value_rel_dest_thunk[local]:
  LIST_REL (sv_rel (lift_value_rel C E)) refs refs' ∧
  LIST_REL (lift_value_rel C E) vs vs' ⇒
  lift_thunk_result_rel (lift_value_rel C E)
    (dest_thunk vs refs) (dest_thunk vs' refs')
Proof
  strip_tac
  >> namedCases_on ‘vs’ ["","source_value source_tail"]
  >> namedCases_on ‘vs'’ ["","target_value target_tail"] >> gvs []
  >- simp [dest_thunk_def,lift_thunk_result_rel_def]
  >> Cases_on ‘source_tail’ >> Cases_on ‘target_tail’
  >> gvs [dest_thunk_def,lift_thunk_result_rel_def] >> Cases_on ‘source_value’
  >> gvs [lift_value_rel_cases_l,dest_thunk_def,lift_thunk_result_rel_def]
  >> qmatch_goalsub_rename_tac ‘store_lookup location refs’
  >> have ‘OPTREL (sv_rel (lift_value_rel C E))
        (store_lookup location refs) (store_lookup location refs')’
  >- metis_tac [LIST_REL_OPTREL_store_lookup]
  >> namedCases_on ‘store_lookup location refs’ ["","source_cell"]
  >> namedCases_on ‘store_lookup location refs'’ ["","target_cell"] >> gvs []
  >~ [‘lift_thunk_result_rel _ BadRef BadRef’] >- simp [lift_thunk_result_rel_def]
  >> Cases_on ‘source_cell’ >> Cases_on ‘target_cell’
  >> gvs [sv_rel_def,lift_thunk_result_rel_def] >> rename1 ‘Thunk mode _’ >> Cases_on ‘mode’
  >> rpt IF_CASES_TAC >> simp [lift_thunk_result_rel_def]
QED

Theorem lift_value_rel_update_thunk_call[local]:
  LIST_REL (sv_rel (lift_value_rel C E)) refs refs' ∧
  lift_value_rel C E value value' ⇒
  OPTREL (LIST_REL (sv_rel (lift_value_rel C E)))
    (update_thunk [Loc F location] refs [value])
    (update_thunk [Loc F location] refs' [value'])
Proof
  strip_tac
  >> have ‘lift_thunk_result_rel (lift_value_rel C E)
        (dest_thunk [value] refs) (dest_thunk [value'] refs')’
  >- (irule lift_value_rel_dest_thunk >> simp [])
  >> Cases_on ‘dest_thunk [value] refs’ >> Cases_on ‘dest_thunk [value'] refs'’
  >> gvs [update_thunk_def,lift_thunk_result_rel_def]
  >> irule store_assign_OPTREL_sv_rel >> simp [sv_rel_def]
QED

Theorem lift_value_rel_update_thunk[local]:
  ∀vs refs values vs' refs' values'.
    LIST_REL (sv_rel (lift_value_rel C E)) refs refs' ∧
    LIST_REL (lift_value_rel C E) vs vs' ∧
    LIST_REL (lift_value_rel C E) values values' ⇒
    OPTREL (LIST_REL (sv_rel (lift_value_rel C E)))
      (update_thunk vs refs values) (update_thunk vs' refs' values')
Proof
  ho_match_mp_tac update_thunk_ind >> rpt conj_tac >> rpt gen_tac
  >> rw [LIST_REL_CONS1,lift_value_rel_cases_l]
  >~ [‘update_thunk [Loc F _] _ [_]’] >- (
    irule lift_value_rel_update_thunk_call
    >> simp [])
  >> simp [update_thunk_def]
QED

Theorem lift_value_rel_shape[local]:
  shape_val_rel (lift_value_rel C E)
Proof
  rw [shape_val_rel_def,lift_value_rel_cases_l] >> simp [is_clos_def]
QED

Theorem lift_value_rel_concrete[local]:
  (∀v v'. lift_value_rel C E v v' ⇒
    concrete_v v = concrete_v v' ∧ (concrete_v v ⇒ v = v')) ∧
  (∀vs vs'. LIST_REL (lift_value_rel C E) vs vs' ⇒
    concrete_v_list vs = concrete_v_list vs' ∧
    (concrete_v_list vs ⇒ vs = vs'))
Proof
  ho_match_mp_tac concrete_v_ind >> rpt conj_tac
  >- (
    qx_gen_tac ‘value’
    >> Cases_on ‘value’ >> rw [lift_value_rel_cases_l,Once concrete_v_def]
    >> gvs [Once concrete_v_def]
    >> metis_tac [])
  >- simp []
  >> rw [LIST_REL_CONS1,CONJUNCT2 concrete_v_def] >> gvs [CONJUNCT2 concrete_v_def]
  >> metis_tac []
QED

Theorem lift_value_rel_compiler_literals[local]:
  lift_value_rel C E v v' ⇒
  v_to_mlstring v = v_to_mlstring v' ∧ v_to_word64 v = v_to_word64 v'
Proof
  strip_tac
  >> Cases_on ‘v’ >> gvs [lift_value_rel_cases_l,v_to_mlstring_def,v_to_word64_def]
QED

Theorem lift_value_rel_compiler_words[local]:
  lift_value_rel C E v v' ⇒ v_to_word64_list v = v_to_word64_list v'
Proof
  strip_tac
  >> drule lift_value_rel_v_to_list >> namedCases_on ‘v_to_list v’ ["","source_values"]
  >> namedCases_on ‘v_to_list v'’ ["","target_values"]
  >> gvs [v_to_word64_list_def] >> strip_tac
  >> have ‘MAP v_to_word64 source_values = MAP v_to_word64 target_values’
  >- (
    simp [MAP_EQ_LIST_REL] >> conj_tac
    >- metis_tac [LIST_REL_LENGTH]
    >> qpat_x_assum ‘LIST_REL _ source_values target_values’ mp_tac
    >> match_mp_tac LIST_REL_mono >> rw []
    >> metis_tac [lift_value_rel_compiler_literals])
  >> simp []
QED

Theorem lift_value_rel_compiler_agrees[local]:
  lift_value_rel C E previous previous' ∧
  lift_value_rel C E compiler_value compiler_value' ∧
  lift_value_rel C E bytes bytes' ∧ lift_value_rel C E words words' ⇒
  compiler_agrees compiler (id,previous,decs) (compiler_value,bytes,words) =
  compiler_agrees compiler (id,previous',decs) (compiler_value',bytes',words')
Proof
  strip_tac
  >> have ‘v_to_mlstring bytes = v_to_mlstring bytes' ∧
      v_to_word64_list words = v_to_word64_list words'’
  >- metis_tac [lift_value_rel_compiler_literals,lift_value_rel_compiler_words]
  >> eq_tac >> strip_tac >> imp_res_tac compiler_agrees_concrete
  >> ‘previous = previous' ∧ compiler_value = compiler_value'’ by
       metis_tac [CONJUNCT1 lift_value_rel_concrete]
  >> gvs [compiler_agrees_def]
QED

Theorem do_eval_decs_shape[local]:
  do_eval vs (SOME (EvalDecs s)) = SOME r ⇒
  ∃env id previous program compiler_value bytes words.
    vs = [Env env id; previous; program; compiler_value; bytes; words]
Proof
  simp [do_eval_def,AllCaseEqs()] >> rw [] >> simp []
QED

Theorem lift_value_rel_do_eval_decs_call[local]:
  E env env' ∧
  lift_value_rel C E previous previous' ∧ lift_value_rel C E program program' ∧
  lift_value_rel C E compiler_value compiler_value' ∧
  lift_value_rel C E bytes bytes' ∧ lift_value_rel C E words words' ⇒
  OPTREL (λ(env,decs,es) (env',decs',es').
    E env env' ∧ decs = decs' ∧ es = es')
    (do_eval [Env env id; previous; program; compiler_value; bytes; words]
      (SOME (EvalDecs eval_decs)))
    (do_eval [Env env' id; previous'; program'; compiler_value'; bytes'; words']
      (SOME (EvalDecs eval_decs)))
Proof
  strip_tac
  >> have ‘concrete_v program = concrete_v program' ∧
      (concrete_v program ⇒ program = program')’
  >- metis_tac [CONJUNCT1 lift_value_rel_concrete]
  >> Cases_on ‘concrete_v program’ >> gvs []
  >- (
    namedCases_on ‘eval_decs.decode_decs program’ ["","decoded"]
    >> simp [do_eval_def]
    >> have ‘compiler_agrees eval_decs.compiler (id,previous,decoded)
          (compiler_value,bytes,words) =
        compiler_agrees eval_decs.compiler (id,previous',decoded)
          (compiler_value',bytes',words')’
    >- (irule lift_value_rel_compiler_agrees >> qexistsl_tac [‘C’,‘E’] >> simp [])
    >> Cases_on ‘compiler_agrees eval_decs.compiler (id,previous,decoded)
                   (compiler_value,bytes,words)’
    >> gvs [] >> imp_res_tac compiler_agrees_concrete
    >> imp_res_tac (CONJUNCT1 lift_value_rel_concrete) >> gvs [] >> IF_CASES_TAC
    >> simp [])
  >> Cases_on ‘eval_decs.decode_decs program’
  >> Cases_on ‘eval_decs.decode_decs program'’ >> simp [do_eval_def]
QED

Theorem lift_value_rel_do_eval_decs[local]:
  LIST_REL (lift_value_rel C E) vs vs' ⇒
  OPTREL (λ(env,decs,es) (env',decs',es').
    E env env' ∧ decs = decs' ∧ es = es')
    (do_eval vs (SOME (EvalDecs eval_decs)))
    (do_eval vs' (SOME (EvalDecs eval_decs)))
Proof
  strip_tac
  >> Cases_on ‘∃env id previous program compiler_value bytes words.
       vs = [Env env id; previous; program; compiler_value; bytes; words]’
  >- (
    gvs [LIST_REL_CONS1,lift_value_rel_cases_l]
    >> irule lift_value_rel_do_eval_decs_call >> metis_tac [])
  >> Cases_on ‘do_eval vs (SOME (EvalDecs eval_decs))’
  >- (
    Cases_on ‘do_eval vs' (SOME (EvalDecs eval_decs))’ >> simp []
    >> drule do_eval_decs_shape >> strip_tac >> gvs [LIST_REL_CONS2]
    >> qpat_x_assum ‘lift_value_rel _ _ _ (Env _ _)’
         (strip_assume_tac o ONCE_REWRITE_RULE [lift_value_rel_cases])
    >> gvs [])
  >> drule do_eval_decs_shape >> metis_tac []
QED

Theorem lift_do_eval_res[local]:
  lift_state_rel R D (s:'ffi semanticPrimitives$state) s' ∧
  OPTREL (λ(env,decs,es) (env',decs',es').
    E env env' ∧ P decs decs' ∧ D es es')
    (do_eval vs s.eval_state) (do_eval vs' s'.eval_state) ⇒
  lift_eval_result_rel R D
    (λ(env,decs) (env',decs'). E env env' ∧ P decs decs')
    (do_eval_res vs s) (do_eval_res vs' s')
Proof
  strip_tac
  >> namedCases_on ‘do_eval vs s.eval_state’ ["","source_eval"]
  >> namedCases_on ‘do_eval vs' s'.eval_state’ ["","target_eval"]
  >> gvs [do_eval_res_def,lift_eval_result_rel_def,lift_result_rel_def]
  >> PairCases_on ‘source_eval’ >> PairCases_on ‘target_eval’
  >> gvs [lift_eval_result_rel_def,lift_result_rel_def,lift_state_rel_def]
QED

Inductive lift_pure_value:
  (∀env lit. lift_pure_value env (Lit lit) (Litv lit)) ∧
  (∀env x e. lift_pure_value env (Fun x e) (Closure env x e)) ∧
  (∀env id v. nsLookup env.v id = SOME v ⇒ lift_pure_value env (Var id) v) ∧
  (∀env cn es vs v.
    LIST_REL (lift_pure_value env) es vs ∧
    do_con_check env.c cn (LENGTH es) ∧ build_conv env.c cn vs = SOME v ⇒
    lift_pure_value env (Con cn es) v) ∧
  (∀env e v ty. lift_pure_value env e v ⇒ lift_pure_value env (Tannot e ty) v) ∧
  (∀env e v loc. lift_pure_value env e v ⇒ lift_pure_value env (Lannot e loc) v)
End

Theorem lift_pure_value_evaluates[local]:
  ∀env e v. lift_pure_value env e v ⇒
  ∀s:'ffi semanticPrimitives$state. evaluate s env [e] = (s,Rval [v])
Proof
  ho_match_mp_tac lift_pure_value_ind >> rpt conj_tac >> rpt gen_tac
  >> simp [Once evaluate_def] >> strip_tac
  >> have ‘∀s:'ffi semanticPrimitives$state.
        evaluate s env (REVERSE es) = (s,Rval (REVERSE vs))’
  >- (irule evaluate_known_value_list >> simp [LIST_REL_REVERSE])
  >> simp []
QED

Inductive lift_global_decs:
  (∀env. lift_global_decs [] env env) ∧
  (∀env name e v ds target.
    lift_pure_value env e v ∧ check_exp_constructors env.c e ∧
    lift_global_decs ds (env with v := nsBind name v env.v) target ⇒
    lift_global_decs (Dlet NoLocs (Pvar name) e::ds) env target) ∧
  (∀env funs ds target.
    ALL_DISTINCT (MAP FST funs) ∧
    EVERY (λ(f,x,e). check_exp_constructors env.c e) funs ∧
    lift_global_decs ds (env with v := build_rec_env funs env env.v) target ⇒
    lift_global_decs (Dletrec NoLocs funs::ds) env target)
End

Theorem lift_global_decs_evaluates[local]:
  ∀ds env target. lift_global_decs ds env target ⇒
  ∀s:'ffi semanticPrimitives$state. lift_decs_env s ds env target
Proof
  ho_match_mp_tac lift_global_decs_ind >> rpt conj_tac >> rpt gen_tac
  >> simp [Once lift_decs_env_def] >> strip_tac
  >- (
    drule lift_pure_value_evaluates >> disch_tac
    >> gen_tac >> qexists_tac ‘<|v := alist_to_ns [(name,v)]; c := nsEmpty|>’
    >> simp [extend_dec_env_sing,evaluate_value_binding])
  >> gen_tac >> qexists_tac ‘<|v := build_rec_env funs env nsEmpty; c := nsEmpty|>’
  >> simp [Once evaluate_decs_def,extend_dec_env_build_rec_env,ELIM_UNCURRY,ETA_THM]
QED

Theorem lift_global_decs_append[local]:
  ∀xs env middle. lift_global_decs xs env middle ⇒
  ∀ys target. lift_global_decs ys middle target ⇒
    lift_global_decs (xs ++ ys) env target
Proof
  ho_match_mp_tac lift_global_decs_ind >> rpt conj_tac >> rpt gen_tac >> simp []
  >> rpt strip_tac >> simp [Once lift_global_decs_cases] >> asm_exists_tac >> simp []
QED

Theorem emit_value_global_decs[local]:
  lift_global_decs (REVERSE ds) base target ∧
  lift_pure_value target e v ∧ check_exp_constructors target.c e ∧
  emit_value e (n,ds,used) = (result,n1,ds1,used1) ⇒
  lift_global_decs (REVERSE ds1) base
    (target with v := nsBind (make_name n) v target.v)
Proof
  rw [emit_value_def]
  >> have ‘lift_global_decs [Dlet NoLocs (Pvar (make_name n)) e] target
        (target with v := nsBind (make_name n) v target.v)’
  >- (
    simp [Once lift_global_decs_cases] >> qexists_tac ‘v’
    >> simp [Once lift_global_decs_cases])
  >> simp [REVERSE_DEF] >> irule lift_global_decs_append
  >> qexists_tac ‘target’ >> simp []
QED

Theorem emit_rec_global_decs[local]:
  lift_global_decs (REVERSE ds) base target ∧
  ALL_DISTINCT (MAP FST funs) ∧
  EVERY (λ(f,x,e). check_exp_constructors target.c e) funs ∧
  emit_dec (Dletrec NoLocs funs) (n,ds,used) = (n1,ds1,used1) ⇒
  lift_global_decs (REVERSE ds1) base
    (target with v := build_rec_env funs target target.v)
Proof
  rw [emit_dec_def]
  >> have ‘lift_global_decs [Dletrec NoLocs funs] target
        (target with v := build_rec_env funs target target.v)’
  >- (simp [Once lift_global_decs_cases] >> simp [Once lift_global_decs_cases])
  >> simp [REVERSE_DEF] >> irule lift_global_decs_append
  >> qexists_tac ‘target’ >> simp []
QED

Theorem emit_let_global_decs[local]:
  lift_global_decs (REVERSE ds) base target ∧
  lift_pure_value target e v ∧ check_exp_constructors target.c e ∧
  emit_dec (Dlet NoLocs (Pvar x) e) (n,ds,used) = (n1,ds1,used1) ⇒
  lift_global_decs (REVERSE ds1) base (target with v := nsBind x v target.v)
Proof
  rw [emit_dec_def] >> simp [REVERSE_DEF] >> irule lift_global_decs_append
  >> first_assum (irule_at Any) >> irule (cj 2 lift_global_decs_rules)
  >> simp [Once lift_global_decs_cases] >> metis_tac []
QED

Theorem lift_pure_value_list_exists[local]:
  ∀es. EVERY (λe. ∃v. lift_pure_value env e v) es ⇒
    ∃vs. LIST_REL (lift_pure_value env) es vs
Proof
  Induct_on ‘es’
  >- simp []
  >> qx_gen_tac ‘e’ >> rw [] >> qpat_x_assum ‘EVERY _ es ⇒ ∃vs. _’ mp_tac >> simp []
  >> disch_then (qx_choose_then ‘values’ assume_tac)
  >> qmatch_asmsub_rename_tac ‘lift_pure_value env e value’
  >> qexistsl_tac [‘value’,‘values’] >> simp []
QED

Theorem lift_pure_value_cases_l[local]:
  (lift_pure_value env (Lit lit) v ⇔ v = Litv lit) ∧
  (lift_pure_value env (Fun x e) v ⇔ v = Closure env x e) ∧
  (lift_pure_value env (Var id) v ⇔ nsLookup env.v id = SOME v) ∧
  (lift_pure_value env (Con cn es) v ⇔
    ∃vs. LIST_REL (lift_pure_value env) es vs ∧
      do_con_check env.c cn (LENGTH es) ∧ build_conv env.c cn vs = SOME v) ∧
  (lift_pure_value env (Tannot e ty) v ⇔ lift_pure_value env e v) ∧
  (lift_pure_value env (Lannot e loc) v ⇔ lift_pure_value env e v)
Proof
  rpt conj_tac
  >> simp [Once lift_pure_value_cases]
QED

Theorem value_ready_pure[local]:
  ∀env e. value_ready env e ⇒ ∃v. lift_pure_value env e v
Proof
  ho_match_mp_tac value_ready_ind >> rpt conj_tac >> rpt gen_tac
  >> simp [lift_pure_value_cases_l] >> strip_tac >> drule lift_pure_value_list_exists
  >> disch_then (qx_choose_then ‘values’ assume_tac)
  >> ‘∃v. build_conv env.c cn values = SOME v’ by metis_tac [do_con_check_build_conv]
  >> qmatch_asmsub_rename_tac ‘build_conv env.c cn values = SOME value’
  >> qexistsl_tac [‘value’,‘values’] >> simp []
QED

Theorem lift_env_rel_mono[local]:
  (∀v w. R v w ⇒ R' v w) ∧ lift_env_rel R fvs ren env env' ⇒
  lift_env_rel R' fvs ren env env'
Proof
  rw [lift_env_rel_def]
  >> irule OPTREL_MONO >> qexists_tac ‘R’ >> simp []
QED

(* ------------------------------------------------------------------------
   Scopes, closure certificates and the runtime value relation
   ------------------------------------------------------------------------ *)

Definition lift_renaming_wf_def:
  lift_renaming_wf (ren:mlstring |-> mlstring) (used:mlstring |-> unit) ⇔
    (∀name renamed. FLOOKUP ren name = SOME renamed ⇒ renamed ∈ FDOM used) ∧
    (∀name other renamed.
      FLOOKUP ren name = SOME renamed ∧ FLOOKUP ren other = SOME renamed ⇒
      name = other)
End

Theorem lift_renaming_wf_delete_all[local]:
  lift_renaming_wf ren used ⇒ lift_renaming_wf (delete_all names ren) used
Proof
  rw [lift_renaming_wf_def,delete_all_lookup]
  >> metis_tac []
QED

Theorem lift_renaming_wf_fdomsub[local]:
  lift_renaming_wf ren used ⇒ lift_renaming_wf (fdomsub ren name) used
Proof
  rw [lift_renaming_wf_def,DOMSUB_FLOOKUP_THM] >> metis_tac []
QED

Theorem lift_renaming_wf_used_subset[local]:
  lift_renaming_wf ren used ∧ FDOM used ⊆ FDOM used1 ⇒
  lift_renaming_wf ren used1
Proof
  rw [lift_renaming_wf_def,SUBSET_DEF]
  >> metis_tac []
QED

Theorem lift_renaming_wf_update[local]:
  lift_renaming_wf ren used ∧ renamed ∉ FDOM used ∧
  renamed ∈ FDOM used1 ∧ FDOM used ⊆ FDOM used1 ⇒
  lift_renaming_wf (ren |+ (name,renamed)) used1
Proof
  rw [lift_renaming_wf_def,FLOOKUP_UPDATE,SUBSET_DEF]
  >- (
    qmatch_asmsub_rename_tac
      ‘if name = original then SOME renamed else FLOOKUP ren original’
    >> Cases_on ‘name = original’ >> gvs []
    >> metis_tac [])
  >> qmatch_goalsub_rename_tac ‘left_name = right_name’ >> Cases_on ‘name = left_name’
  >> Cases_on ‘name = right_name’ >> gvs [] >> metis_tac []
QED

Definition lift_scope_def:
  lift_scope R captures (bound:mlstring |-> unit) ren
    (n:num,ds:dec list,used:mlstring |-> unit) source global locals ⇔
    lift_renaming_wf ren used ∧
    lift_env_rel R captures ren source
      (global with v := nsBindList locals global.v) ∧
    lift_env_rel R (DRESTRICT captures (COMPL (FDOM bound))) ren source global ∧
    (∀name local_value. MEM (name,local_value) locals ⇒
      name ∈ FDOM used ∨
      ∃original. original ∈ FDOM bound ∧
        rename_var ren (Short original) = (Short name:(mlstring,mlstring) id)) ∧
    (∀name renamed. name ∈ FDOM captures ∧ name ∈ FDOM bound ∧
      rename_var ren (Short name) = (Short renamed:(mlstring,mlstring) id) ⇒
      IS_SOME (ALOOKUP locals renamed)) ∧
    (∀name. name ∈ FDOM captures ∧ name ∉ FDOM bound ⇒
      ∃renamed. rename_var ren (Short name) = (Short renamed:(mlstring,mlstring) id) ∧
        renamed ∈ FDOM used) ∧
    (∀name k. name ∈ FDOM captures ∧ n ≤ k ⇒
      rename_var ren (Short name) ≠ (Short (make_name k):(mlstring,mlstring) id)) ∧
    (∀k. n ≤ k ⇒ ALOOKUP locals (make_name k) = NONE)
End

Theorem lift_scope_mono[local]:
  (∀v w. R v w ⇒ R' v w) ∧
  lift_scope R captures bound ren st source global locals ⇒
  lift_scope R' captures bound ren st source global locals
Proof
  PairCases_on ‘st’ >> rw [lift_scope_def] >> metis_tac [lift_env_rel_mono]
QED

Theorem lift_scope_constructors[local]:
  lift_scope R captures bound ren st source global locals ⇒ source.c = global.c
Proof
  PairCases_on ‘st’ >> rw [lift_scope_def,lift_env_rel_def]
QED

Definition lift_function_certificate_def:
  lift_function_certificate R source x e target e' ⇔
  ∃body limit captures bound ren n ds used n1 ds1 used1 base initial final locals.
    annotate_exp [] e = (body,limit,captures) ∧
    source_dce$no_Open e ∧ check_exp_constructors source.c e ∧
    bump x 0 ≤ n ∧ limit ≤ n ∧ lift_state_fresh (n,ds,used) ∧
    lift_function_body bound ren (n,ds,used) x body = (e',n1,ds1,used1) ∧
    lift_global_decs (REVERSE ds) base initial ∧
    lift_global_decs (REVERSE ds1) base final ∧
    target.c = final.c ∧
    (∀id. (∀name. id = Short name ⇒ name ∈ (exp_free_names e' DELETE x)) ⇒
      nsLookup target.v id = nsLookup (nsBindList locals final.v) id) ∧
    check_exp_constructors target.c e' ∧
    lift_scope R (fdomsub captures x) bound ren (n,ds,used) source initial locals ∧
    (∀name renamed. FLOOKUP ren name = SOME renamed ∧ renamed ≠ name ⇒
      ∀original. original ∈ exp_names e ∨ original = x ⇒ renamed ≠ original)
End

Theorem lift_function_certificate_mono[local]:
  (∀v w. R v w ⇒ R' v w) ∧
  lift_function_certificate R source x e target e' ⇒
  lift_function_certificate R' source x e target e'
Proof
  rw [lift_function_certificate_def] >> drule_all lift_scope_mono >> strip_tac
  >> rpt (first_assum $ irule_at Any) >> metis_tac []
QED

Theorem lift_global_decs_constructors[local]:
  ∀ds env target. lift_global_decs ds env target ⇒ target.c = env.c
Proof
  ho_match_mp_tac lift_global_decs_ind >> rw []
QED

Definition lift_rec_certificate_def:
  lift_rec_certificate R source funs target funs' ren ⇔
  ∃trees limit captures bound n ds used n1 ds1 used1 base initial final locals.
    annotate_funs [] funs = (trees,limit,captures) ∧
    EVERY (λ(f,x,e). source_dce$no_Open e ∧ check_exp_constructors source.c e) funs ∧
    ALL_DISTINCT (MAP FST funs) ∧ ALL_DISTINCT (MAP FST funs') ∧
    LIST_REL (λf f'. rename_var ren (Short f) = (Short f':(mlstring,mlstring) id))
      (MAP FST funs) (MAP FST funs') ∧
    limit ≤ n ∧ lift_state_fresh (n,ds,used) ∧
    lift_funs (bind_all (MAP FST funs) bound) ren (n,ds,used)
      (ZIP (MAP FST funs',MAP (FST o SND) funs)) trees = (funs',n1,ds1,used1) ∧
    lift_global_decs (REVERSE ds) base initial ∧
    lift_global_decs (REVERSE ds1) base final ∧
    target.c = final.c ∧
    (∀id. (∀name. id = Short name ⇒
        name ∈ (exp_free_names_funs funs' DIFF set (MAP FST funs'))) ⇒
      nsLookup target.v id = nsLookup (nsBindList locals final.v) id) ∧
    EVERY (λ(f,x,e). check_exp_constructors target.c e) funs' ∧
    lift_scope R (delete_all (MAP FST funs) captures) bound ren (n,ds,used)
      source initial locals ∧
    (∀name renamed. name ∈ FDOM captures ∧
      rename_var ren (Short name) = (Short renamed:(mlstring,mlstring) id) ⇒
      (MEM name (MAP FST funs) ⇔ MEM renamed (MAP FST funs'))) ∧
    (∀name k. name ∈ FDOM captures ∧ n ≤ k ⇒
      rename_var ren (Short name) ≠ (Short (make_name k):(mlstring,mlstring) id)) ∧
    (∀name renamed. FLOOKUP ren name = SOME renamed ∧ renamed ≠ name ⇒
      ∀original. original ∈ exp_names_funs funs ⇒ renamed ≠ original)
End

Theorem lift_rec_certificate_mono[local]:
  (∀v w. R v w ⇒ R' v w) ∧
  lift_rec_certificate R source funs target funs' ren ⇒
  lift_rec_certificate R' source funs target funs' ren
Proof
  rw [lift_rec_certificate_def] >> drule_all lift_scope_mono >> strip_tac
  >> rpt (first_assum $ irule_at Any) >> metis_tac []
QED

Theorem lift_rec_certificate_constructors[local]:
  lift_rec_certificate R source funs target funs' ren ⇒
  source.c = target.c ∧
  EVERY (λ(f,x,e). check_exp_constructors source.c e) funs ∧
  EVERY (λ(f,x,e). check_exp_constructors target.c e) funs'
Proof
  rw [lift_rec_certificate_def,ELIM_UNCURRY,EVERY_CONJ]
  >> imp_res_tac lift_global_decs_constructors >> fs [lift_scope_def,lift_env_rel_def]
QED

Theorem lift_rec_certificate_function_names[local]:
  lift_rec_certificate R source funs target funs' ren ⇒
  LIST_REL (λentry entry'.
    rename_var ren (Short (FST entry)) =
      (Short (FST entry'):(mlstring,mlstring) id) ∧
    FST (SND entry) = FST (SND entry')) funs funs'
Proof
  rw [lift_rec_certificate_def]
  >> imp_res_tac (cj 3 annotate_LENGTH) >> imp_res_tac LIST_REL_LENGTH
  >> drule lift_funs_bindings_prefix
  >> disch_then (mp_tac o AP_TERM “MAP SND : (mlstring # mlstring) list -> mlstring list”)
  >> gvs [TAKE_LENGTH_TOO_LONG,MAP_MAP_o,o_DEF,ELIM_UNCURRY,MAP_ZIP]
  >> rw [LIST_REL_EL_EQN] >> gvs [LIST_REL_EL_EQN,LIST_EQ_REWRITE,EL_MAP]
QED

Definition lift_runtime_env_def:
  lift_runtime_env R (env:v sem_env) (env':v sem_env) ⇔
    env.c = env'.c ∧
    (∀path. nsLookupMod env.v path = NONE ⇔ nsLookupMod env'.v path = NONE) ∧
    ∀id. OPTREL R (nsLookup env.v id) (nsLookup env'.v id)
End

Theorem lift_runtime_env_namespace[local]:
  lift_runtime_env R env env' ⇔
  env.c = env'.c ∧ nsAll2 (λid. R) env.v env'.v
Proof
  simp [lift_runtime_env_def,namespaceTheory.nsAll2_def,namespaceTheory.nsSub_def]
  >> eq_tac >> rpt strip_tac >> gvs []
  >- (
    qmatch_goalsub_rename_tac ‘nsLookup env'.v lookup_id’
    >> qpat_x_assum ‘∀id. OPTREL _ _ _’ (qspec_then ‘lookup_id’ mp_tac)
    >> simp [OPTREL_def])
  >- (
    qmatch_goalsub_rename_tac ‘nsLookup env.v lookup_id’
    >> qpat_x_assum ‘∀id. OPTREL _ _ _’ (qspec_then ‘lookup_id’ mp_tac)
    >> simp [OPTREL_def])
  >- metis_tac []
  >> qmatch_goalsub_rename_tac ‘nsLookup env.v lookup_id’
  >> namedCases_on ‘nsLookup env.v lookup_id’ ["","source_value"]
  >> namedCases_on ‘nsLookup env'.v lookup_id’ ["","target_value"] >> simp [OPTREL_def]
  >> metis_tac [SOME_11,NOT_SOME_NONE]
QED

Theorem lift_runtime_env_mono[local,mono]:
  (∀v w. R v w ⇒ R' v w) ⇒ lift_runtime_env R env env' ⇒
  lift_runtime_env R' env env'
Proof
  rw [lift_runtime_env_def]
  >> irule OPTREL_MONO >> qexists_tac ‘R’ >> simp []
QED

Definition lift_closure_certificate_def:
  lift_closure_certificate R v w ⇔
    (∃env x e env' e'.
      v = Closure env x e ∧ w = Closure env' x e' ∧
      lift_function_certificate R env x e env' e') ∨
    (∃env x e env'.
      v = Closure env x e ∧ w = Closure env' x e ∧
      lift_runtime_env R env env') ∨
    (∃env funs f env' funs' f' ren.
      v = Recclosure env funs f ∧ w = Recclosure env' funs' f' ∧
      lift_rec_certificate R env funs env' funs' ren ∧
      MEM f (MAP FST funs) ∧ MEM f' (MAP FST funs') ∧
      rename_var ren (Short f) = (Short f':(mlstring,mlstring) id)) ∨
    (∃env funs f env'.
      v = Recclosure env funs f ∧ w = Recclosure env' funs f ∧
      lift_runtime_env R env env')
End

Theorem lift_closure_certificate_mono[local,mono]:
  (∀v w. R v w ⇒ R' v w) ⇒ lift_closure_certificate R v w ⇒
  lift_closure_certificate R' v w
Proof
  rw [lift_closure_certificate_def]
  >- (disj1_tac >> drule_all lift_function_certificate_mono >> simp [])
  >- (disj2_tac >> drule_all lift_runtime_env_mono >> simp [])
  >- (
    disj1_tac
    >> qexists_tac ‘ren’ >> simp [] >> drule_all lift_rec_certificate_mono
    >> simp [])
  >> disj2_tac >> drule_all lift_runtime_env_mono >> simp []
QED

Inductive lift_runtime_rel:
  (∀v w.
    lift_value_rel (lift_closure_certificate lift_runtime_rel)
      (lift_runtime_env lift_runtime_rel) v w ⇒ lift_runtime_rel v w)
End

Theorem lift_runtime_rel_unfold[local]:
  lift_runtime_rel v w ⇔
  lift_value_rel (lift_closure_certificate lift_runtime_rel)
    (lift_runtime_env lift_runtime_rel) v w
Proof
  simp [Once lift_runtime_rel_cases]
QED

Theorem lift_runtime_rel_value_rel[local]:
  lift_value_rel (lift_closure_certificate lift_runtime_rel)
    (lift_runtime_env lift_runtime_rel) = lift_runtime_rel
Proof
  simp [FUN_EQ_THM,lift_runtime_rel_unfold]
QED

fun runtime_inst th =
  REWRITE_RULE [lift_runtime_rel_value_rel]
    (Q.INST [‘C’ |-> ‘lift_closure_certificate lift_runtime_rel’,
             ‘E’ |-> ‘lift_runtime_env lift_runtime_rel’] (SPEC_ALL th));

Theorem lift_runtime_rel_cases_l[local]:
  (lift_runtime_rel (Litv lit) value ⇔ value = Litv lit) ∧
  (lift_runtime_rel (Loc b loc) value ⇔ value = Loc b loc) ∧
  (lift_runtime_rel (Conv stamp xs) value ⇔
    ∃ys. value = Conv stamp ys ∧ LIST_REL lift_runtime_rel xs ys) ∧
  (lift_runtime_rel (Vectorv xs) value ⇔
    ∃ys. value = Vectorv ys ∧ LIST_REL lift_runtime_rel xs ys) ∧
  (lift_runtime_rel (Closure env x e) value ⇔
    ∃env' x' e'. value = Closure env' x' e' ∧
      lift_closure_certificate lift_runtime_rel (Closure env x e) (Closure env' x' e')) ∧
  (lift_runtime_rel (Recclosure env funs f) value ⇔
    ∃env' funs' f'. value = Recclosure env' funs' f' ∧
      lift_closure_certificate lift_runtime_rel
        (Recclosure env funs f) (Recclosure env' funs' f')) ∧
  (lift_runtime_rel (Env env id) value ⇔
    ∃env'. value = Env env' id ∧ lift_runtime_env lift_runtime_rel env env')
Proof
  rpt conj_tac
  >> once_rewrite_tac [lift_runtime_rel_unfold]
  >> once_rewrite_tac [lift_value_rel_cases_l] >> simp [lift_runtime_rel_value_rel]
QED

Theorem lift_runtime_env_self[local]:
  (∀v. v ∈ sem_envSET env ⇒ R v v) ⇒ lift_runtime_env R env env
Proof
  Cases_on ‘env’ >> rw [lift_runtime_env_def,sem_envSET_thm]
  >> Cases_on ‘nsLookup n id’ >> simp []
  >> metis_tac [nsLookup_namespaceSET3]
QED

Theorem lift_runtime_rel_refl[local]:
  lift_runtime_rel value value
Proof
  qid_spec_tac ‘value’ >> ho_match_mp_tac v_induction
  >> rw [lift_runtime_rel_cases_l,lift_closure_certificate_def,EVERY2_refl]
  >> metis_tac [lift_runtime_env_self]
QED

Theorem lift_runtime_env_refl[local]:
  lift_runtime_env lift_runtime_rel env env
Proof
  irule lift_runtime_env_self >> simp [lift_runtime_rel_refl]
QED

Theorem lift_runtime_env_bind[local]:
  lift_runtime_env R env env' ∧ R value value' ⇒
  lift_runtime_env R (env with v := nsBind name value env.v)
    (env' with v := nsBind name value' env'.v)
Proof
  rw [lift_runtime_env_namespace]
  >> irule namespacePropsTheory.nsAll2_nsBind >> simp []
QED

Theorem lift_runtime_env_build_rec_env[local]:
  lift_runtime_env lift_runtime_rel env env' ⇒
  lift_runtime_env lift_runtime_rel
    (env with v := build_rec_env funs env env.v)
    (env' with v := build_rec_env funs env' env'.v)
Proof
  strip_tac
  >> have ‘∀name. lift_runtime_rel (Recclosure env funs name)
        (Recclosure env' funs name)’
  >- simp [lift_runtime_rel_cases_l,lift_closure_certificate_def]
  >> fs [lift_runtime_env_namespace,build_rec_env_nsBindList]
  >> irule namespacePropsTheory.nsAll2_nsBindList
  >> simp [LIST_REL_EL_EQN,EL_MAP,ELIM_UNCURRY]
QED

Theorem lift_runtime_store_refl[local]:
  sv_rel lift_runtime_rel stored stored
Proof
  Cases_on ‘stored’
  >> simp [sv_rel_def,lift_runtime_rel_refl,EVERY2_refl]
QED

Theorem lift_runtime_state_refl[local]:
  D s.eval_state s.eval_state ⇒
  lift_state_rel lift_runtime_rel D (s:'ffi semanticPrimitives$state) s
Proof
  rw [lift_state_rel_def]
  >> irule LIST_REL_refl >> simp [lift_runtime_store_refl]
QED

Theorem lift_global_decs_list_cases[local]:
  (lift_global_decs [] env target ⇔ target = env) ∧
  (lift_global_decs (d::ds) env target ⇔
    (∃name e value.
      d = Dlet NoLocs (Pvar name) e ∧
      lift_pure_value env e value ∧ check_exp_constructors env.c e ∧
      lift_global_decs ds (env with v := nsBind name value env.v) target) ∨
    (∃funs.
      d = Dletrec NoLocs funs ∧ ALL_DISTINCT (MAP FST funs) ∧
      EVERY (λ(f,x,e). check_exp_constructors env.c e) funs ∧
      lift_global_decs ds (env with v := build_rec_env funs env env.v) target))
Proof
  conj_tac
  >> simp [Once lift_global_decs_cases]
QED

Theorem lift_global_decs_append_iff[local]:
  ∀xs ys env target.
    lift_global_decs (xs ++ ys) env target ⇔
    ∃middle. lift_global_decs xs env middle ∧ lift_global_decs ys middle target
Proof
  Induct_on ‘xs’
  >- simp [lift_global_decs_list_cases] >> rpt gen_tac
  >> simp [lift_global_decs_list_cases] >> metis_tac []
QED

Theorem lift_funs_cons[local]:
  lift_funs bound ren st ((name,arg)::fs) (tree::trees) =
    let (body,middle) = lift_function_body bound ren st arg tree in
    let (funs,final) = lift_funs bound ren middle fs trees in
      ((name,arg,body)::funs,final)
Proof
  simp [Once lift_exp_def,lift_function_body_def]
QED

Theorem lift_funs_body_trace[local]:
  ∀fs trees bound ren st funs final index.
    lift_funs bound ren st fs trees = (funs,final) ∧
    LENGTH fs ≤ LENGTH trees ∧ index < LENGTH fs ⇒
    ∃before after.
      lift_state_extends st before ∧ lift_state_extends after final ∧
      lift_funs bound ren st (TAKE index fs) (TAKE index trees) =
        (TAKE index funs,before) ∧
      lift_function_body bound ren before (SND (EL index fs)) (EL index trees) =
        (SND (SND (EL index funs)),after) ∧
      lift_funs bound ren after (DROP (SUC index) fs) (DROP (SUC index) trees) =
        (DROP (SUC index) funs,final)
Proof
  Induct_on ‘fs’
  >- simp []
  >> qx_genl_tac [‘entry’,‘trees’,‘bound’,‘ren’,‘st’,‘funs’,‘final’,‘index’]
  >> namedCases_on ‘entry’ ["name arg"] >> namedCases_on ‘trees’ ["","tree rest"]
  >- simp []
  >> namedCases_on ‘lift_function_body bound ren st arg tree’
       ["head_body middle_n middle_ds middle_used"]
  >> namedCases_on ‘lift_funs bound ren (middle_n,middle_ds,middle_used) fs rest’
       ["tail_funs final_n final_ds final_used"]
  >> simp [lift_funs_cons] >> strip_tac >> gvs []
  >> namedCases_on ‘index’ ["","previous"] >> simp []
  >- (
    qexistsl_tac [‘st’,‘(middle_n,middle_ds,middle_used)’]
    >> simp [lift_state_extends_refl,Once lift_exp_def]
    >> drule (List.last (CONJUNCTS lift_exp_state_extends))
    >> simp [])
  >> qpat_x_assum ‘∀trees bound ren st funs final index. _’
       (qspecl_then [‘rest’,‘bound’,‘ren’,‘(middle_n,middle_ds,middle_used)’,
         ‘tail_funs’,‘(final_n,final_ds,final_used)’,‘previous’] mp_tac)
  >> simp [] >> disch_then (qx_choosel_then [‘before’,‘after’] strip_assume_tac)
  >> qexistsl_tac [‘before’,‘after’] >> simp [lift_funs_cons]
  >> metis_tac [lift_function_body_state_extends,lift_state_extends_trans]
QED

Theorem lift_global_decs_state_prefix[local]:
  lift_state_extends (n,ds,used) (n1,ds1,used1) ∧
  lift_global_decs (REVERSE ds1) base target ⇒
  ∃initial extra.
    ds1 = extra ++ ds ∧ lift_global_decs (REVERSE ds) base initial ∧
    lift_global_decs (REVERSE extra) initial target
Proof
  rw [lift_state_extends_def]
  >> fs [REVERSE_APPEND,lift_global_decs_append_iff] >> asm_exists_tac >> simp []
QED

Theorem annotate_funs_body[local]:
  ∀funs t trees limit captures index.
    annotate_funs t funs = (trees,limit,captures) ∧ index < LENGTH funs ⇒
    ∃body_limit body_captures.
      annotate_exp t (SND (SND (EL index funs))) =
        (EL index trees,body_limit,body_captures) ∧
      body_limit ≤ limit ∧ bump (FST (SND (EL index funs))) 0 ≤ limit ∧
      FDOM (fdomsub body_captures (FST (SND (EL index funs)))) ⊆ FDOM captures
Proof
  Induct_on ‘funs’
  >- simp []
  >> qx_genl_tac [‘entry’,‘t’,‘trees’,‘limit’,‘captures’,‘index’]
  >> namedCases_on ‘entry’ ["name arg body"]
  >> namedCases_on ‘annotate_exp t body’ ["body_tree head_limit head_captures"]
  >> namedCases_on ‘annotate_funs t funs’ ["rest_trees rest_limit rest_captures"]
  >> simp [Once annotate_exp_def] >> strip_tac >> gvs []
  >> namedCases_on ‘index’ ["","previous"] >> simp []
  >- (‘0 ≤ head_limit’ by simp [] >> metis_tac [bump_le,bump_mono,LESS_EQ_TRANS])
  >> qpat_x_assum ‘∀t trees limit captures index. _’
       (qspecl_then [‘t’,‘rest_trees’,‘rest_limit’,‘rest_captures’,‘previous’] mp_tac)
  >> simp []
  >> disch_then (qx_choosel_then [‘selected_limit’,‘selected_captures’]
       strip_assume_tac)
  >> qexistsl_tac [‘selected_limit’,‘selected_captures’] >> fs [SUBSET_DEF]
QED

Theorem lift_rec_certificate_name_membership[local]:
  lift_rec_certificate R source funs target funs' ren ∧
  MEM name (MAP FST funs) ∧
  rename_var ren (Short name) = (Short renamed:(mlstring,mlstring) id) ⇒
  MEM renamed (MAP FST funs')
Proof
  rw [lift_rec_certificate_def]
  >> drule_all LIST_REL_MEM_IMP
  >> disch_then (qx_choose_then ‘target_name’ strip_assume_tac) >> gvs []
QED

Theorem lift_rec_certificate_runtime_rel[local]:
  lift_rec_certificate lift_runtime_rel source funs target funs' ren ∧
  MEM name (MAP FST funs) ∧
  rename_var ren (Short name) = (Short renamed:(mlstring,mlstring) id) ⇒
  lift_runtime_rel (Recclosure source funs name) (Recclosure target funs' renamed)
Proof
  strip_tac
  >> drule_all lift_rec_certificate_name_membership >> disch_tac
  >> simp [lift_runtime_rel_cases_l,lift_closure_certificate_def] >> disj1_tac
  >> qexists_tac ‘ren’ >> simp []
QED

Theorem lift_rec_certificate_capture_env[local]:
  lift_rec_certificate lift_runtime_rel source funs target funs' ren ∧
  annotate_funs [] funs = (trees,limit,captures) ∧
  lift_env_rel lift_runtime_rel (delete_all (MAP FST funs) captures) ren
    source initial ⇒
  lift_env_rel lift_runtime_rel captures ren
    (source with v := build_rec_env funs source source.v)
    (initial with v := build_rec_env funs' target initial.v)
Proof
  strip_tac
  >> qpat_assum ‘lift_rec_certificate lift_runtime_rel source funs target funs' ren’
       (mp_tac o REWRITE_RULE [lift_rec_certificate_def])
  >> strip_tac >> gvs []
  >> irule lift_env_rel_build_rec_env >> simp [] >> rpt gen_tac >> rpt strip_tac
  >> drule_all lift_rec_certificate_runtime_rel >> simp []
QED

Theorem lift_rec_certificate_argument_shadow[local]:
  lift_rec_certificate R source funs target funs' ren ∧ arg ∈ exp_names_funs funs ⇒
  ∀name. name ≠ arg ⇒
    rename_var ren (Short name) ≠ (Short arg:(mlstring,mlstring) id)
Proof
  rw [lift_rec_certificate_def]
  >> qmatch_goalsub_rename_tac ‘rename_var ren (Short original)’
  >> namedCases_on ‘FLOOKUP ren original’ ["","mapped"]
  >> simp [rename_var_def] >> strip_tac
  >> qpat_x_assum ‘∀name renamed. FLOOKUP ren name = SOME renamed ∧ renamed ≠ name ⇒ _’
       (qspecl_then [‘original’,‘arg’] mp_tac)
  >> simp []
QED

Theorem lift_rec_certificate_find_recfun_index[local]:
  lift_rec_certificate R source funs target funs' ren ∧
  find_recfun name funs = SOME (arg,body) ∧
  rename_var ren (Short name) = (Short name':(mlstring,mlstring) id) ⇒
  ∃index body'.
    index < LENGTH funs ∧ EL index funs = (name,arg,body) ∧
    EL index funs' = (name',arg,body') ∧
    find_recfun name' funs' = SOME (arg,body')
Proof
  strip_tac
  >> have ‘ALL_DISTINCT (MAP FST funs) ∧ ALL_DISTINCT (MAP FST funs')’
  >- fs [lift_rec_certificate_def]
  >> ‘MEM (name,arg,body) funs’ by fs [find_recfun_mem]
  >> qpat_x_assum ‘MEM (name,arg,body) funs’ (mp_tac o REWRITE_RULE [MEM_EL])
  >> disch_then (qx_choose_then ‘index’ strip_assume_tac)
  >> drule lift_rec_certificate_function_names >> rewrite_tac [LIST_REL_EL_EQN]
  >> disch_then strip_assume_tac >> qpat_x_assum ‘∀n. n < LENGTH funs ⇒ _’
       (mp_tac o Q.SPEC ‘index’)
  >> namedCases_on ‘EL index funs'’ ["target_name target_arg target_body"] >> simp []
  >> strip_tac >> qexistsl_tac [‘index’,‘target_body’] >> simp []
  >> qpat_x_assum ‘(name,arg,body) = EL index funs’ (assume_tac o SYM) >> fs []
  >> simp [find_recfun_mem,MEM_EL] >> qexists_tac ‘index’ >> simp []
QED

Theorem lift_function_certificate_env_cong[local]:
  lift_function_certificate R source arg body target body' ∧
  target'.c = target.c ∧
  (∀id. (∀name. id = Short name ⇒ name ∈ (exp_free_names body' DELETE arg)) ⇒
    nsLookup target'.v id = nsLookup target.v id) ⇒
  lift_function_certificate R source arg body target' body'
Proof
  rw [lift_function_certificate_def]
  >> rpt (first_assum $ irule_at Any) >> gvs []
QED

Theorem lift_rec_certificate_env_cong[local]:
  lift_rec_certificate R source funs target funs' ren ∧
  target'.c = target.c ∧
  (∀id. (∀name. id = Short name ⇒
      name ∈ (exp_free_names_funs funs' DIFF set (MAP FST funs'))) ⇒
    nsLookup target'.v id = nsLookup target.v id) ⇒
  lift_rec_certificate R source funs target' funs' ren
Proof
  rw [lift_rec_certificate_def]
  >> rpt (first_assum $ irule_at Any) >> gvs []
QED

Definition lift_decs_avoid_def:
  lift_decs_avoid (names:mlstring set) ds ⇔
    (∀loc name e. MEM (Dlet loc (Pvar name) e) ds ⇒ name ∉ names) ∧
    (∀loc funs name. MEM (Dletrec loc funs) ds ∧ MEM name (MAP FST funs) ⇒
      name ∉ names)
End

Theorem lift_decs_avoid_append[local]:
  lift_decs_avoid names (xs ++ ys) ⇔
  lift_decs_avoid names xs ∧ lift_decs_avoid names ys
Proof
  simp [lift_decs_avoid_def,MEM_APPEND]
  >> metis_tac []
QED

Theorem lift_decs_avoid_mono[local]:
  names' ⊆ names ∧ lift_decs_avoid names ds ⇒ lift_decs_avoid names' ds
Proof
  rw [lift_decs_avoid_def,SUBSET_DEF]
  >> metis_tac []
QED

Theorem lift_decs_avoid_reverse[local]:
  lift_decs_avoid names (REVERSE ds) ⇔ lift_decs_avoid names ds
Proof
  simp [lift_decs_avoid_def,MEM_REVERSE]
QED

Theorem lift_decs_avoid_list_cases[local]:
  lift_decs_avoid names [] ∧
  (lift_decs_avoid names (Dlet loc (Pvar name) e::ds) ⇔
    name ∉ names ∧ lift_decs_avoid names ds) ∧
  (lift_decs_avoid names (Dletrec loc funs::ds) ⇔
    DISJOINT (set (MAP FST funs)) names ∧ lift_decs_avoid names ds)
Proof
  simp [lift_decs_avoid_def,IN_DISJOINT]
  >> metis_tac []
QED

Definition lift_state_decs_avoid_def:
  lift_state_decs_avoid (n:num,ds:dec list,used:mlstring |-> unit)
    (n1:num,ds1:dec list,used1:mlstring |-> unit) ⇔
    ∃extra. ds1 = extra ++ ds ∧ lift_decs_avoid (FDOM used) extra
End

Theorem lift_state_decs_avoid_refl[local]:
  ∀st. lift_state_decs_avoid st st
Proof
  gen_tac
  >> namedCases_on ‘st’ ["n ds used"]
  >> simp [lift_state_decs_avoid_def,lift_decs_avoid_list_cases]
QED

Theorem lift_state_decs_avoid_trans[local]:
  lift_state_decs_avoid st middle ∧ lift_state_decs_avoid middle final ∧
  lift_state_extends st middle ⇒ lift_state_decs_avoid st final
Proof
  namedCases_on ‘st’ ["n ds used"]
  >> namedCases_on ‘middle’ ["middle_n middle_ds middle_used"]
  >> namedCases_on ‘final’ ["final_n final_ds final_used"] >> strip_tac
  >> ‘FDOM used ⊆ FDOM middle_used’ by fs [lift_state_extends_def]
  >> qpat_x_assum ‘lift_state_decs_avoid (n,ds,used) _’
       (mp_tac o REWRITE_RULE [lift_state_decs_avoid_def])
  >> disch_then (qx_choose_then ‘earlier’ strip_assume_tac)
  >> qpat_x_assum ‘lift_state_decs_avoid (middle_n,middle_ds,middle_used) _’
       (mp_tac o REWRITE_RULE [lift_state_decs_avoid_def])
  >> disch_then (qx_choose_then ‘later’ strip_assume_tac)
  >> ‘lift_decs_avoid (FDOM used) later’ by metis_tac [lift_decs_avoid_mono]
  >> rewrite_tac [lift_state_decs_avoid_def] >> qexists_tac ‘later ++ earlier’
  >> simp [APPEND_ASSOC,lift_decs_avoid_append]
QED

Theorem emit_value_decs_avoid[local]:
  lift_state_fresh st ∧ emit_value e st = (result,st') ⇒
  lift_state_decs_avoid st st'
Proof
  namedCases_on ‘st’ ["n ds used"]
  >> rw [emit_value_def] >> rewrite_tac [lift_state_decs_avoid_def]
  >> qexists_tac ‘[Dlet NoLocs (Pvar (make_name n)) e]’
  >> simp [lift_decs_avoid_list_cases] >> fs [lift_state_fresh_def,FLOOKUP_DEF]
QED

Theorem lift_state_decs_avoid_same_decs[local]:
  FST (SND st') = FST (SND st) ⇒ lift_state_decs_avoid st st'
Proof
  namedCases_on ‘st’ ["n ds used"]
  >> namedCases_on ‘st'’ ["next_n next_ds next_used"]
  >> simp [lift_state_decs_avoid_def,lift_decs_avoid_list_cases]
QED

Theorem emit_dec_decs_avoid[local]:
  lift_state_decs_avoid st middle ∧
  lift_decs_avoid (FDOM (SND (SND st))) [d] ⇒
  lift_state_decs_avoid st (emit_dec d middle)
Proof
  namedCases_on ‘st’ ["n ds used"]
  >> namedCases_on ‘middle’ ["middle_n middle_ds middle_used"] >> strip_tac
  >> qpat_x_assum ‘lift_state_decs_avoid _ _’
       (mp_tac o REWRITE_RULE [lift_state_decs_avoid_def])
  >> disch_then (qx_choose_then ‘extra’ strip_assume_tac)
  >> rewrite_tac [emit_dec_def,lift_state_decs_avoid_def] >> qexists_tac ‘d::extra’
  >> fs [lift_decs_avoid_def] >> metis_tac []
QED

Theorem lift_exp_fresh[local]:
  (∀mode bound ren st tree e st1.
    lift_exp mode bound ren st tree = (e,st1) ∧
    tree_names_bounded limit tree ∧ limit ≤ FST st ∧ lift_state_fresh st ⇒
    lift_state_fresh st1 ∧ lift_state_decs_avoid st st1) ∧
  (∀mode bound ren st tree e st1.
    lower_exp mode bound ren st tree = (e,st1) ∧
    tree_names_bounded limit tree ∧ limit ≤ FST st ∧ lift_state_fresh st ⇒
    lift_state_fresh st1 ∧ lift_state_decs_avoid st st1) ∧
  (∀mode bound ren st trees es st1.
    lift_exps mode bound ren st trees = (es,st1) ∧
    EVERY (tree_names_bounded limit) trees ∧ limit ≤ FST st ∧ lift_state_fresh st ⇒
    lift_state_fresh st1 ∧ lift_state_decs_avoid st st1) ∧
  (∀mode bound ren st ps trees pes st1.
    lift_pes mode bound ren st ps trees = (pes,st1) ∧
    EVERY (tree_names_bounded limit) trees ∧ limit ≤ FST st ∧ lift_state_fresh st ⇒
    lift_state_fresh st1 ∧ lift_state_decs_avoid st st1) ∧
  (∀bound ren st fs trees funs st1.
    lift_funs bound ren st fs trees = (funs,st1) ∧
    EVERY (tree_names_bounded limit) trees ∧ limit ≤ FST st ∧ lift_state_fresh st ⇒
    lift_state_fresh st1 ∧ lift_state_decs_avoid st st1)
Proof
  ho_match_mp_tac lift_exp_ind >> rpt conj_tac >> rpt gen_tac
  >> rw [Once lift_exp_def,lift_state_decs_avoid_refl] >> rpt (pairarg_tac >> gvs [])
  >> fs [tree_names_bounded_Lift]
  >>~- ([‘choose_names _ _ _ = _’],
    qmatch_asmsub_rename_tac ‘choose_names _ _ st = (chosen_names,named_state)’
    >> qmatch_asmsub_rename_tac
      ‘lift_funs _ _ named_state _ _ = (compiled_funs,functions_state)’
    >> ‘EVERY (λx. bump x 0 ≤ FST st) (MAP FST funs)’ by (
      fs [EVERY_MEM,exp_names_def] >> metis_tac [recursive_names_all_names,LESS_EQ_TRANS])
    >> namedCases_on ‘st’ ["initial_n initial_ds initial_used"]
    >> namedCases_on ‘named_state’ ["named_n named_ds named_used"] >> fs []
    >> drule_all choose_names_fresh >> strip_tac >> gvs []
    >> drule choose_names_extends >> disch_tac
    >> ‘lift_state_decs_avoid (initial_n,initial_ds,initial_used)
          (named_n,initial_ds,named_used)’ by (irule lift_state_decs_avoid_same_decs >> simp [])
    >> ‘limit ≤ named_n’ by decide_tac >> fs []
    >> drule (cj 5 lift_exp_state_extends) >> disch_tac
    >> ‘lift_state_fresh (emit_dec (Dletrec NoLocs compiled_funs) functions_state) ∧
        limit ≤ FST (emit_dec (Dletrec NoLocs compiled_funs) functions_state)’ by (
      namedCases_on ‘functions_state’ ["fn_n fn_ds fn_used"]
      >> imp_res_tac lift_state_extends_counter >> fs [emit_dec_def,lift_state_fresh_def])
    >> fs [] >> drule lift_funs_names_prefix >> strip_tac
    >> ‘lift_decs_avoid (FDOM initial_used) [Dletrec NoLocs compiled_funs]’ by (
      gvs [lift_decs_avoid_list_cases,IN_DISJOINT,MAP_ZIP,FLOOKUP_DEF]
      >> metis_tac [rich_listTheory.MEM_TAKE])
    >> ‘lift_state_decs_avoid (initial_n,initial_ds,initial_used)
          (emit_dec (Dletrec NoLocs compiled_funs) functions_state)’ by (
      irule emit_dec_decs_avoid >> simp [] >> metis_tac [lift_state_decs_avoid_trans])
    >> metis_tac [lift_state_decs_avoid_trans,lift_state_extends_trans,emit_dec_extends])
  >>~- ([‘choose_name _ _ _ = _’],
    qmatch_asmsub_rename_tac ‘lower_exp _ _ _ st _ = (lowered,lowered_state)’
    >> qmatch_asmsub_rename_tac ‘choose_name _ name lowered_state = (chosen,named_state)’
    >> drule (cj 2 lift_exp_state_extends) >> disch_tac
    >> drule choose_name_extends >> disch_tac
    >> imp_res_tac lift_state_extends_counter
    >> ‘bump name 0 ≤ FST lowered_state’ by (
      qpat_x_assum ‘∀x. x ∈ exp_names _ ⇒ _’ (qspec_then ‘name’ mp_tac)
      >> simp [exp_names_def] >> decide_tac)
    >> namedCases_on ‘lowered_state’ ["lowered_n lowered_ds lowered_used"] >> fs []
    >> drule_all choose_name_state_fresh >> strip_tac
    >> namedCases_on ‘named_state’ ["named_n named_ds named_used"]
    >> ‘named_ds = lowered_ds’ by (
      qpat_x_assum ‘choose_name _ _ _ = _’ mp_tac >> rw [choose_name_def])
    >> ‘lift_state_fresh (emit_dec (Dlet NoLocs (Pvar chosen) lowered)
          (named_n,named_ds,named_used)) ∧
        limit ≤ FST (emit_dec (Dlet NoLocs (Pvar chosen) lowered)
          (named_n,named_ds,named_used))’ by fs [emit_dec_def,lift_state_fresh_def]
    >> fs []
    >> ‘lift_decs_avoid (FDOM (SND (SND st))) [Dlet NoLocs (Pvar chosen) lowered]’ by (
      namedCases_on ‘st’ ["initial_n initial_ds initial_used"]
      >> fs [lift_decs_avoid_list_cases,lift_state_extends_def,FLOOKUP_DEF,SUBSET_DEF]
      >> metis_tac [])
    >> ‘lift_state_decs_avoid st (emit_dec (Dlet NoLocs (Pvar chosen) lowered)
          (named_n,named_ds,named_used))’ by (
      irule emit_dec_decs_avoid >> simp []
      >> metis_tac [lift_state_decs_avoid_trans,lift_state_decs_avoid_same_decs,FST,SND])
    >> metis_tac [lift_state_decs_avoid_trans,lift_state_extends_trans,emit_dec_extends])
  >> imp_res_tac lift_exp_state_extends >> imp_res_tac lift_state_extends_counter
  >> metis_tac [LESS_EQ_TRANS,lift_state_decs_avoid_trans,lift_state_extends_trans,
                emit_value_state_fresh,emit_value_decs_avoid]
QED

Theorem lift_global_decs_avoid_lookup[local]:
  lift_global_decs ds initial final ∧ lift_decs_avoid names ds ∧
  (∀name. id = Short name ⇒ name ∈ names) ⇒
  nsLookup final.v id = nsLookup initial.v id
Proof
  qsuff_tac ‘∀ds initial final. lift_global_decs ds initial final ⇒
    lift_decs_avoid names ds ∧ (∀name. id = Short name ⇒ name ∈ names) ⇒
    nsLookup final.v id = nsLookup initial.v id’
  >- metis_tac []
  >> ho_match_mp_tac lift_global_decs_ind
  >> rw [lift_decs_avoid_list_cases,namespacePropsTheory.nsLookup_nsBind]
  >> Cases_on ‘id’
  >> gvs [namespacePropsTheory.nsLookup_nsBind,nsLookup_build_rec_env,IN_DISJOINT]
  >- (‘n ≠ name’ by metis_tac [] >> simp [namespacePropsTheory.nsLookup_nsBind])
  >> rw [] >> metis_tac []
QED

Theorem lift_global_decs_avoid_locals_lookup[local]:
  lift_global_decs ds initial final ∧ lift_decs_avoid names ds ∧
  (∀name. id = Short name ⇒ name ∈ names ∨ IS_SOME (ALOOKUP locals name)) ⇒
  nsLookup (nsBindList locals final.v) id =
    nsLookup (nsBindList locals initial.v) id
Proof
  strip_tac
  >> namedCases_on ‘id’ ["name","module_name nested_id"]
  >- (
    namedCases_on ‘ALOOKUP locals name’ ["","local_value"]
    >> simp [nsBindList_short_lookup] >> irule lift_global_decs_avoid_lookup
    >> qexistsl_tac [‘ds’,‘names’]
    >> fs [])
  >> simp [nsBindList_long_lookup] >> irule lift_global_decs_avoid_lookup
  >> qexistsl_tac [‘ds’,‘names’] >> simp []
QED

Theorem lift_global_decs_avoid_env_rel[local]:
  lift_global_decs ds initial final ∧ lift_decs_avoid names ds ∧
  lift_env_rel R captures ren source (initial with v := nsBindList locals initial.v) ∧
  (∀x name. x ∈ FDOM captures ∧
    rename_var ren (Short x) = (Short name:(mlstring,mlstring) id) ⇒
    name ∈ names ∨ IS_SOME (ALOOKUP locals name)) ⇒
  lift_env_rel R captures ren source (final with v := nsBindList locals final.v)
Proof
  strip_tac
  >> drule lift_global_decs_constructors >> disch_tac
  >> have ‘∀id. (∀name. id = Short name ⇒
        name ∈ names ∨ IS_SOME (ALOOKUP locals name)) ⇒
      nsLookup (nsBindList locals final.v) id =
        nsLookup (nsBindList locals initial.v) id’
  >- (
    rpt strip_tac
    >> irule lift_global_decs_avoid_locals_lookup >> qexistsl_tac [‘ds’,‘names’]
    >> simp [])
  >> fs [lift_env_rel_def] >> metis_tac []
QED

Theorem lift_pure_value_deterministic[local]:
  lift_pure_value env e v ∧ lift_pure_value env e w ⇒ v = w
Proof
  strip_tac
  >> qpat_x_assum ‘lift_pure_value env e v’
       (mp_tac o Q.SPEC ‘ARB’ o
        MATCH_MP lift_pure_value_evaluates)
  >> qpat_x_assum ‘lift_pure_value env e w’
       (mp_tac o Q.SPEC ‘ARB’ o
        MATCH_MP lift_pure_value_evaluates)
  >> simp []
QED

Theorem lift_global_decs_deterministic[local]:
  ∀ds initial final. lift_global_decs ds initial final ⇒
  ∀other. lift_global_decs ds initial other ⇒ final = other
Proof
  ho_match_mp_tac lift_global_decs_ind >> rpt conj_tac >> rpt gen_tac
  >> simp [lift_global_decs_list_cases] >> rpt strip_tac
  >> metis_tac [lift_pure_value_deterministic]
QED

Theorem lift_global_decs_state_suffix[local]:
  lift_state_decs_avoid (n,ds,used) (n1,ds1,used1) ∧
  lift_global_decs (REVERSE ds) base initial ∧
  lift_global_decs (REVERSE ds1) base final ⇒
  ∃extra. ds1 = extra ++ ds ∧
    lift_global_decs (REVERSE extra) initial final ∧
    lift_decs_avoid (FDOM used) extra
Proof
  rw [lift_state_decs_avoid_def]
  >> fs [REVERSE_APPEND,lift_global_decs_append_iff]
  >> metis_tac [lift_global_decs_deterministic]
QED

Theorem lift_state_decs_avoid_env_rel[local]:
  lift_state_decs_avoid (n,ds,used) (n1,ds1,used1) ∧
  lift_global_decs (REVERSE ds) base initial ∧
  lift_global_decs (REVERSE ds1) base final ∧
  lift_env_rel R captures ren source (initial with v := nsBindList locals initial.v) ∧
  (∀x name. x ∈ FDOM captures ∧
    rename_var ren (Short x) = (Short name:(mlstring,mlstring) id) ⇒
    name ∈ FDOM used ∨ IS_SOME (ALOOKUP locals name)) ⇒
  lift_env_rel R captures ren source (final with v := nsBindList locals final.v)
Proof
  strip_tac
  >> drule_all lift_global_decs_state_suffix
  >> disch_then (qx_choose_then ‘extra’ strip_assume_tac)
  >> irule lift_global_decs_avoid_env_rel
  >> qexistsl_tac [‘REVERSE extra’,‘initial’,‘FDOM used’]
  >> simp [lift_decs_avoid_reverse] >> qpat_x_assum ‘∀x name. _’ ACCEPT_TAC
QED

Theorem lift_state_decs_avoid_lookup[local]:
  lift_state_decs_avoid (n,ds,used) (n1,ds1,used1) ∧
  lift_global_decs (REVERSE ds) base initial ∧
  lift_global_decs (REVERSE ds1) base final ∧
  (∀name. id = Short name ⇒ name ∈ FDOM used ∨ IS_SOME (ALOOKUP locals name)) ⇒
  nsLookup (nsBindList locals final.v) id =
    nsLookup (nsBindList locals initial.v) id
Proof
  strip_tac
  >> drule_all lift_global_decs_state_suffix
  >> disch_then (qx_choose_then ‘extra’ strip_assume_tac)
  >> irule lift_global_decs_avoid_locals_lookup
  >> qexistsl_tac [‘REVERSE extra’,‘FDOM used’] >> simp [lift_decs_avoid_reverse]
QED

Theorem lift_function_body_fresh[local]:
  lift_function_body bound ren st x tree = (body,st1) ∧
  tree_names_bounded limit tree ∧ limit ≤ FST st ∧ lift_state_fresh st ⇒
  lift_state_fresh st1 ∧ lift_state_decs_avoid st st1
Proof
  rw [lift_function_body_def] >> metis_tac [lift_exp_fresh]
QED

Definition lift_renamed_names_def:
  lift_renamed_names ren names =
    {name | ∃original. original ∈ names ∧
      rename_var ren (Short original) = (Short name:(mlstring,mlstring) id)}
End

Theorem lift_renamed_names_shadow[local]:
  lift_renamed_names (fdomsub ren x) names DELETE x ⊆
    lift_renamed_names ren (names DELETE x)
Proof
  simp [lift_renamed_names_def,SUBSET_DEF]
  >> metis_tac [rename_var_shadow,rename_var_shadow_other,namespaceTheory.id_11]
QED

Theorem lift_exp_free_names_from_lower[local]:
  (∀mode e st1. lower_exp mode bound ren st tree = (e,st1) ⇒
    exp_free_names e ⊆ names ∪ FDOM (SND (SND st1))) ⇒
  ∀mode e st1. lift_exp mode bound ren st tree = (e,st1) ⇒
    exp_free_names e ⊆ names ∪ FDOM (SND (SND st1))
Proof
  namedCases_on ‘tree’ ["source fvs value children"]
  >> rw [Once lift_exp_def] >> rpt (pairarg_tac >> gvs []) >> gvs [AllCaseEqs()]
  >>~- ([‘emit_value _ middle = _’],
    namedCases_on ‘middle’ ["n ds used"]
    >> gvs [emit_value_def,exp_free_names_def])
  >> metis_tac []
QED

Theorem lift_exp_free_names_lower_iff[local]:
  (∀mode e st1. lower_exp mode bound ren st tree = (e,st1) ⇒
    exp_free_names e ⊆ names ∪ FDOM (SND (SND st1))) ⇔
  (∀mode e st1.
    lower_exp mode bound ren st tree = (e,st1) ∨
    lift_exp mode bound ren st tree = (e,st1) ⇒
    exp_free_names e ⊆ names ∪ FDOM (SND (SND st1)))
Proof
  eq_tac
  >- (strip_tac >> drule lift_exp_free_names_from_lower >> metis_tac [])
  >> metis_tac []
QED

Theorem lift_state_extends_used[local]:
  lift_state_extends st st1 ⇒
  FDOM (SND (SND st)) ⊆ FDOM (SND (SND st1))
Proof
  namedCases_on ‘st’ ["n ds used"]
  >> namedCases_on ‘st1’ ["n1 ds1 used1"] >> simp [lift_state_extends_def]
QED

Theorem rename_var_delete_all[local]:
  rename_var (delete_all names ren) (Short x) =
    if MEM x names then (Short x:(mlstring,mlstring) id)
    else rename_var ren (Short x)
Proof
  Cases_on ‘MEM x names’
  >> simp [rename_var_def,delete_all_lookup]
QED

Theorem rename_var_delete_all_mem[local]:
  (∀original mapped. FLOOKUP ren original = SOME mapped ∧ mapped ≠ original ⇒
     ¬MEM mapped names) ∧
  rename_var (delete_all names ren) (Short name) = (Short renamed:(mlstring,mlstring) id) ⇒
  (MEM name names ⇔ MEM renamed names)
Proof
  rw [rename_var_delete_all] >> Cases_on ‘FLOOKUP ren name’
  >> gvs [rename_var_def] >> metis_tac []
QED

Theorem choose_name_used[local]:
  choose_name bound x st = (y,st1) ⇒ y ∈ FDOM (SND (SND st1))
Proof
  namedCases_on ‘st’ ["n ds used"]
  >> rw [choose_name_def] >> gvs []
QED

Theorem choose_name_renaming_wf[local]:
  lift_renaming_wf ren used ∧ lift_state_fresh (n,ds,used) ∧
  bump x 0 ≤ n ∧ choose_name bound x (n,ds,used) = (y,n1,ds1,used1) ⇒
  lift_renaming_wf (ren |+ (x,y)) used1
Proof
  strip_tac
  >> drule_all choose_name_state_fresh >> strip_tac
  >> drule choose_name_extends >> disch_tac >> drule choose_name_used >> disch_tac
  >> irule lift_renaming_wf_update >> fs [lift_state_extends_def,FLOOKUP_DEF]
  >> qexists_tac ‘used’ >> simp []
QED

Theorem emit_dec_used[local]:
  SND (SND (emit_dec d st)) = SND (SND st)
Proof
  namedCases_on ‘st’ ["n ds used"]
  >> simp [emit_dec_def]
QED

Theorem choose_names_used[local]:
  ∀xs bound (st:num # dec list # (mlstring |-> unit)) ys st1.
    choose_names bound xs st = (ys,st1) ⇒
    LENGTH ys = LENGTH xs ∧ set ys ⊆ FDOM (SND (SND st1))
Proof
  Induct_on ‘xs’
  >> rw [Once choose_names_def] >> rpt (pairarg_tac >> gvs [])
  >> imp_res_tac choose_name_used >> imp_res_tac choose_names_extends
  >> imp_res_tac lift_state_extends_used >> fs [SUBSET_DEF] >> metis_tac []
QED

Theorem choose_names_renaming_wf[local]:
  ∀xs bound n ds used ys n1 ds1 used1 ren.
    lift_renaming_wf ren used ∧ lift_state_fresh (n,ds,used) ∧
    EVERY (λx. bump x 0 ≤ n) xs ∧
    choose_names bound xs (n,ds,used) = (ys,n1,ds1,used1) ⇒
    lift_renaming_wf (ren |++ ZIP (xs,ys)) used1
Proof
  Induct_on ‘xs’
  >- (rw [choose_names_def] >> gvs [FUPDATE_LIST_THM])
  >> rpt gen_tac >> strip_tac >> gvs [Once choose_names_def]
  >> rpt (pairarg_tac >> gvs [])
  >> qmatch_asmsub_rename_tac ‘choose_name bound x _ = (y,middle)’ >> PairCases_on ‘middle’
  >> drule_all choose_name_renaming_wf >> strip_tac
  >> drule_all choose_name_state_fresh >> strip_tac
  >> drule choose_name_extends >> strip_tac
  >> first_x_assum (drule_at (Pat ‘choose_names _ _ _ = _’))
  >> simp [FUPDATE_LIST_THM] >> disch_then irule
  >> fs [lift_state_extends_def,EVERY_MEM] >> metis_tac [LESS_EQ_TRANS]
QED

Theorem rename_var_updates[local]:
  ∀bindings ren x y.
    rename_var (ren |++ bindings) (Short x) = (Short y:(mlstring,mlstring) id) ⇒
    (¬MEM x (MAP FST bindings) ∧ rename_var ren (Short x) = (Short y:(mlstring,mlstring) id)) ∨
    MEM y (MAP SND bindings)
Proof
  Induct_on ‘bindings’
  >- (simp [FUPDATE_LIST_THM] >> metis_tac [])
  >> qx_gen_tac ‘entry’ >> namedCases_on ‘entry’ ["original mapped"]
  >> simp [FUPDATE_LIST_THM] >> rpt strip_tac
  >> metis_tac [rename_var_bind,rename_var_bind_other,namespaceTheory.id_11]
QED

Theorem rename_var_updates_other[local]:
  ∀bindings ren x.
    ¬MEM x (MAP FST bindings) ⇒
    rename_var (ren |++ bindings) (Short x) =
      (rename_var ren (Short x):(mlstring,mlstring) id)
Proof
  Induct_on ‘bindings’
  >> simp [FUPDATE_LIST_THM] >> qx_gen_tac ‘entry’
  >> namedCases_on ‘entry’ ["original mapped"] >> simp [rename_var_bind_other]
QED

Theorem choose_names_capture_membership[local]:
  EVERY (λname. bump name 0 ≤ n) names ∧ lift_state_fresh (n,ds,used) ∧
  choose_names bound names (n,ds,used) = (names',n1,ds1,used1) ∧
  lift_renaming_wf ren used ∧
  (∀name. name ∈ captures ⇒ bump name 0 ≤ n) ⇒
  ∀name mapped.
    name ∈ captures ∧
    rename_var (ren |++ ZIP (names,names')) (Short name) =
      (Short mapped:(mlstring,mlstring) id) ⇒
    (MEM name names ⇔ MEM mapped names')
Proof
  strip_tac
  >> drule_all choose_names_fresh >> strip_tac
  >> ‘MAP FST (ZIP (names,names')) = names ∧ MAP SND (ZIP (names,names')) = names'’ by
    simp [MAP_ZIP]
  >> qx_genl_tac [‘name’,‘mapped’] >> strip_tac >> Cases_on ‘MEM name names’
  >- (
    drule rename_var_updates
    >> simp_tac (srw_ss()) [] >> strip_tac >> fs []
    >> metis_tac [])
  >> have ‘rename_var ren (Short name) = (Short mapped:(mlstring,mlstring) id)’
  >- metis_tac [rename_var_updates_other]
  >> simp [] >> CCONTR_TAC >> namedCases_on ‘FLOOKUP ren name’ ["","renamed"]
  >> fs [rename_var_def,namespaceTheory.id_11]
  >- (
    drule_all LIST_REL_MEM_IMP_R >> strip_tac >> fs []
    >- metis_tac []
    >> qmatch_asmsub_rename_tac ‘mapped = make_name counter’
    >> ‘bump mapped 0 ≤ counter’ by metis_tac [LESS_EQ_TRANS]
    >> metis_tac [bump_make_name])
  >> fs [lift_renaming_wf_def,FLOOKUP_DEF] >> metis_tac []
QED

Theorem lift_annotated_free_names[local]:
  (∀t e tree n fvs.
    annotate_exp t e = (tree,n,fvs) ∧ source_dce$no_Open e ⇒
    ∀bound ren st mode result st1.
      lower_exp mode bound ren st tree = (result,st1) ∨
      lift_exp mode bound ren st tree = (result,st1) ⇒
      exp_free_names result ⊆
        lift_renamed_names ren (exp_free_names e) ∪ FDOM (SND (SND st1))) ∧
  (∀t es trees n fvs.
    annotate_exps t es = (trees,n,fvs) ∧ EVERY source_dce$no_Open es ⇒
    ∀mode bound ren st results st1.
      lift_exps mode bound ren st trees = (results,st1) ⇒
      exp_free_names_exps results ⊆
        lift_renamed_names ren (exp_free_names_exps es) ∪ FDOM (SND (SND st1))) ∧
  (∀t pes trees n fvs.
    annotate_pes t pes = (trees,n,fvs) ∧
    EVERY (λ(p,e). source_dce$no_Open e) pes ⇒
    ∀mode bound ren st results st1.
      lift_pes mode bound ren st (MAP FST pes) trees = (results,st1) ⇒
      exp_free_names_pes results ⊆
        lift_renamed_names ren (exp_free_names_pes pes) ∪ FDOM (SND (SND st1))) ∧
  (∀t funs trees n fvs.
    annotate_funs t funs = (trees,n,fvs) ∧
    EVERY (λ(f,x,e). source_dce$no_Open e) funs ⇒
    ∀bound ren st names results st1.
      LENGTH names = LENGTH funs ∧
      lift_funs bound ren st (ZIP (names,MAP (FST o SND) funs)) trees =
        (results,st1) ⇒
      exp_free_names_funs results ⊆
        lift_renamed_names ren (exp_free_names_funs funs) ∪ FDOM (SND (SND st1)))
Proof
  ho_match_mp_tac annotate_exp_ind >> rpt conj_tac >> rpt gen_tac
  >> rewrite_tac [GSYM lift_exp_free_names_lower_iff] >> rw [Once annotate_exp_def]
  >> rpt (pairarg_tac >> gvs []) >> fs [no_Open_thm]
  >> RULE_ASSUM_TAC (REWRITE_RULE [lift_exp_free_names_lower_iff])
  >~ [‘exp_free_names (Fun _ _)’] >- (
    fs [Once lift_exp_def] >> pairarg_tac >> gvs [exp_free_names_def,AllCaseEqs()]
    >> fs [SUBSET_DEF] >> metis_tac [SRULE [SUBSET_DEF] lift_renamed_names_shadow])
  >~ [‘exp_free_names (Letrec _ _)’] >- (
    fs [Once lift_exp_def] >> rpt (pairarg_tac >> gvs []) >> gvs [AllCaseEqs()]
    >> imp_res_tac (cj 3 annotate_LENGTH) >> imp_res_tac choose_names_used
    >> imp_res_tac (cj 1 lift_exp_state_extends)
    >> imp_res_tac (cj 5 lift_exp_state_extends) >> imp_res_tac lift_state_extends_used
    >> fs [emit_dec_used] >> qmatch_asmsub_rename_tac ‘choose_names _ _ _ = (chosen,_)’
    >> qspec_then ‘ZIP (MAP FST funs,chosen)’ mp_tac rename_var_updates
    >> simp [MAP_ZIP] >> disch_tac >> qpat_assum ‘∀bound ren st names results st1. _’
         (qspecl_then [‘bind_all (MAP FST funs) bound’,
           ‘delete_all (MAP FST funs) ren’,‘st’,‘MAP FST funs’] mp_tac)
    >> simp [ZIP_MAP_MAP,o_DEF,ELIM_UNCURRY] >> disch_tac
    >> imp_res_tac lift_funs_names_prefix >> fs [MAP_MAP_o,o_DEF,ELIM_UNCURRY,ETA_THM]
    >> fs [MAP_ZIP,TAKE_LENGTH_TOO_LONG]
    >> fs [exp_free_names_def,lift_renamed_names_def,SUBSET_DEF]
    >> simp [GSYM MAP_TAKE,TAKE_LENGTH_ID]
    >> metis_tac [rename_var_delete_all,namespaceTheory.id_11])
  >~ [‘exp_free_names (Var vid)’] >- (
    gvs [Once lift_exp_def]
    >> namedCases_on ‘vid’ ["original","module_name nested_id"]
    >> simp [rename_var_def,exp_free_names_def]
    >> namedCases_on ‘FLOOKUP ren original’ ["","mapped"]
    >> simp [rename_var_def,exp_free_names_def,lift_renamed_names_def])
  >~ [‘exp_free_names (Let _ _ _)’] >- (
    namedCases_on ‘name’ ["","arg"] >> fs [Once lift_exp_def]
    >> rpt (pairarg_tac >> gvs []) >> gvs [AllCaseEqs()]
    >> imp_res_tac (cj 1 lift_exp_state_extends) >> imp_res_tac lift_state_extends_used
    >> imp_res_tac choose_name_used
    >> fs [exp_free_names_def,lift_renamed_names_def,SUBSET_DEF,emit_dec_used]
    >> metis_tac [rename_var_shadow,rename_var_shadow_other,
         rename_var_bind,rename_var_bind_other,namespaceTheory.id_11])
  >~ [‘exp_free_names_exps (_::_)’] >- (
    Cases_on ‘NULL es’ >> gvs [NULL_EQ] >> fs [Once lift_exp_def]
    >> rpt (pairarg_tac >> gvs []) >> fs [Once lift_exp_def]
    >> imp_res_tac (cj 3 lift_exp_state_extends) >> imp_res_tac lift_state_extends_used
    >> fs [exp_free_names_def,lift_renamed_names_def,SUBSET_DEF] >> metis_tac [])
  >~ [‘exp_free_names_pes (_::_)’] >- (
    fs [Once lift_exp_def] >> rpt (pairarg_tac >> gvs [])
    >> imp_res_tac (cj 4 lift_exp_state_extends) >> imp_res_tac lift_state_extends_used
    >> fs [exp_free_names_def,lift_renamed_names_def,SUBSET_DEF]
    >> metis_tac [rename_var_delete_all,namespaceTheory.id_11])
  >~ [‘exp_free_names_funs (_::_)’] >- (
    namedCases_on ‘names’ ["","name rest"] >> gvs [] >> fs [Once lift_exp_def]
    >> rpt (pairarg_tac >> gvs []) >> gvs [AllCaseEqs()]
    >> imp_res_tac (cj 5 lift_exp_state_extends) >> imp_res_tac lift_state_extends_used
    >> fs [exp_free_names_def,lift_renamed_names_def,SUBSET_DEF]
    >> metis_tac [rename_var_shadow,rename_var_shadow_other,namespaceTheory.id_11])
  >> gvs [Once lift_exp_def] >> rpt (pairarg_tac >> gvs [])
  >> imp_res_tac lift_exp_state_extends >> imp_res_tac lift_state_extends_used
  >> fs [exp_free_names_def,lift_renamed_names_def,SUBSET_DEF] >> metis_tac []
QED

Theorem lift_rec_free_names[local]:
  annotate_funs t funs = (trees,limit,captures) ∧
  EVERY (λ(f,x,e). source_dce$no_Open e) funs ∧
  LIST_REL (λname renamed.
    rename_var ren (Short name) = (Short renamed:(mlstring,mlstring) id))
    (MAP FST funs) (MAP FST funs') ∧
  lift_funs bound ren st (ZIP (MAP FST funs',MAP (FST o SND) funs)) trees =
    (funs',st1) ⇒
  exp_free_names_funs funs' DIFF set (MAP FST funs') ⊆
    lift_renamed_names ren (exp_free_names_funs funs DIFF set (MAP FST funs)) ∪
    FDOM (SND (SND st1))
Proof
  strip_tac
  >> imp_res_tac LIST_REL_LENGTH >> drule (cj 4 lift_annotated_free_names)
  >> disch_then (qspecl_then [‘bound’,‘ren’,‘st’,‘MAP FST funs'’,
       ‘funs'’,‘st1’] mp_tac)
  >> simp [] >> strip_tac
  >> have ‘∀name. MEM name (MAP FST funs) ⇒
        ∃renamed. MEM renamed (MAP FST funs') ∧
          rename_var ren (Short name) = (Short renamed:(mlstring,mlstring) id)’
  >- (rpt strip_tac >> drule_all LIST_REL_MEM_IMP >> simp [])
  >> fs [lift_renamed_names_def,SUBSET_DEF] >> metis_tac [namespaceTheory.id_11]
QED

Theorem lift_rec_decs_lookup[local]:
  annotate_funs t funs = (trees,limit,captures) ∧
  EVERY (λ(f,x,e). source_dce$no_Open e) funs ∧
  LIST_REL (λname renamed.
    rename_var ren (Short name) = (Short renamed:(mlstring,mlstring) id))
    (MAP FST funs) (MAP FST funs') ∧
  lift_funs bound ren (n,ds,used)
    (ZIP (MAP FST funs',MAP (FST o SND) funs)) trees = (funs',n1,ds1,used1) ∧
  lift_state_decs_avoid (n1,ds1,used1) (n2,ds2,used2) ∧
  lift_global_decs (REVERSE ds1) base initial ∧
  lift_global_decs (REVERSE ds2) base final ∧
  (∀original name.
    original ∈ exp_free_names_funs funs DIFF set (MAP FST funs) ∧
    rename_var ren (Short original) = (Short name:(mlstring,mlstring) id) ⇒
    name ∈ FDOM used ∨ IS_SOME (ALOOKUP locals name)) ∧
  (∀name. id = Short name ⇒
    name ∈ exp_free_names_funs funs' DIFF set (MAP FST funs')) ⇒
  nsLookup (nsBindList locals final.v) id =
    nsLookup (nsBindList locals initial.v) id
Proof
  strip_tac
  >> drule_all lift_rec_free_names >> disch_tac >> drule (cj 5 lift_exp_state_extends)
  >> disch_then (assume_tac o MATCH_MP lift_state_extends_used)
  >> have ‘∀name. id = Short name ⇒
        name ∈ FDOM used1 ∨ IS_SOME (ALOOKUP locals name)’
  >- (fs [lift_renamed_names_def,SUBSET_DEF] >> metis_tac [])
  >> metis_tac [lift_state_decs_avoid_lookup]
QED

Theorem lift_funs_body_trace_lookup[local]:
  lift_funs bound ren st fs trees = (funs,n1,ds1,used1) ∧
  LENGTH fs ≤ LENGTH trees ∧ index < LENGTH fs ∧
  EVERY (tree_names_bounded limit) trees ∧ limit ≤ FST st ∧
  lift_state_fresh st ∧ lift_global_decs (REVERSE ds1) base target ⇒
  ∃before after before_env after_env.
    lift_funs bound ren st (TAKE index fs) (TAKE index trees) =
      (TAKE index funs,before) ∧
    lift_function_body bound ren before (SND (EL index fs)) (EL index trees) =
      (SND (SND (EL index funs)),after) ∧
    lift_state_extends st before ∧ lift_state_extends after (n1,ds1,used1) ∧
    lift_state_fresh before ∧ lift_state_fresh after ∧
    lift_state_decs_avoid st before ∧ lift_state_decs_avoid before after ∧
    lift_state_decs_avoid after (n1,ds1,used1) ∧
    lift_global_decs (REVERSE (FST (SND before))) base before_env ∧
    lift_global_decs (REVERSE (FST (SND after))) base after_env ∧
    (∀locals id. (∀name. id = Short name ⇒
        name ∈ FDOM (SND (SND after)) ∨ IS_SOME (ALOOKUP locals name)) ⇒
      nsLookup (nsBindList locals target.v) id =
        nsLookup (nsBindList locals after_env.v) id)
Proof
  strip_tac
  >> drule_all lift_funs_body_trace
  >> disch_then (qx_choosel_then [‘before’,‘after’] strip_assume_tac)
  >> ‘EVERY (tree_names_bounded limit) (TAKE index trees) ∧
      tree_names_bounded limit (EL index trees) ∧
      EVERY (tree_names_bounded limit) (DROP (SUC index) trees)’ by
    fs [EVERY_TAKE,EVERY_DROP,EVERY_EL]
  >> ‘lift_state_fresh before ∧ lift_state_decs_avoid st before’ by (
    irule (cj 5 lift_exp_fresh)
    >> first_assum $ irule_at (Pat ‘lift_funs _ _ _ _ _ = _’)
    >> qexists_tac ‘limit’ >> simp [])
  >> ‘limit ≤ FST before’ by metis_tac [lift_state_extends_counter,LESS_EQ_TRANS]
  >> drule_all lift_function_body_fresh >> strip_tac
  >> drule lift_function_body_state_extends >> disch_tac
  >> ‘limit ≤ FST after’ by metis_tac [lift_state_extends_counter,LESS_EQ_TRANS]
  >> ‘lift_state_decs_avoid after (n1,ds1,used1)’ by (
    irule (cj 2 (cj 5 lift_exp_fresh))
    >> first_assum $ irule_at (Pat ‘lift_funs _ _ _ _ _ = _’)
    >> qexists_tac ‘limit’ >> simp [])
  >> ‘lift_state_extends before (n1,ds1,used1)’ by metis_tac [lift_state_extends_trans]
  >> namedCases_on ‘before’ ["before_n before_ds before_used"]
  >> namedCases_on ‘after’ ["after_n after_ds after_used"]
  >> ‘∃before_env. lift_global_decs (REVERSE before_ds) base before_env’ by
    metis_tac [lift_global_decs_state_prefix]
  >> ‘∃after_env. lift_global_decs (REVERSE after_ds) base after_env’ by
    metis_tac [lift_global_decs_state_prefix]
  >> qexistsl_tac [‘(before_n,before_ds,before_used)’,‘(after_n,after_ds,after_used)’,
       ‘before_env’,‘after_env’]
  >> rw [] >> metis_tac [lift_state_decs_avoid_lookup]
QED

Theorem exp_names_funs_member[local]:
  ∀funs name arg body. MEM (name,arg,body) funs ⇒
    name ∈ exp_names_funs funs ∧ arg ∈ exp_names_funs funs ∧
    exp_names body ⊆ exp_names_funs funs
Proof
  Induct_on ‘funs’
  >- simp []
  >> qx_gen_tac ‘entry’
  >> namedCases_on ‘entry’ ["head_name head_arg head_body"] >> rpt gen_tac
  >> simp [exp_names_def,SUBSET_DEF] >> metis_tac [SUBSET_DEF]
QED

Theorem lift_runtime_rel_opapp[local]:
  (∀source arg body target body' value value'.
    lift_function_certificate lift_runtime_rel source arg body target body' ∧
    lift_runtime_rel value value' ⇒
    P (source with v := nsBind arg value source.v) body
      (target with v := nsBind arg value' target.v) body') ∧
  (∀source funs target funs' ren name name' arg body body' value value'.
    lift_rec_certificate lift_runtime_rel source funs target funs' ren ∧
    rename_var ren (Short name) = (Short name':(mlstring,mlstring) id) ∧
    find_recfun name funs = SOME (arg,body) ∧
    find_recfun name' funs' = SOME (arg,body') ∧ lift_runtime_rel value value' ⇒
    P (source with v := nsBind arg value (build_rec_env funs source source.v)) body
      (target with v := nsBind arg value' (build_rec_env funs' target target.v)) body') ∧
  (∀source target body. lift_runtime_env lift_runtime_rel source target ⇒
    P source body target body) ⇒
  ∀values values'. LIST_REL lift_runtime_rel values values' ⇒
    OPTREL (λ(env,body) (env',body'). P env body env' body')
      (do_opapp values) (do_opapp values')
Proof
  strip_tac >> rpt gen_tac >> strip_tac
  >> irule (runtime_inst lift_value_rel_opapp) >> simp []
  >> qx_genl_tac [‘f’,‘f'’,‘value’,‘value'’] >> strip_tac
  >> qpat_x_assum ‘lift_closure_certificate lift_runtime_rel f f'’
       (mp_tac o REWRITE_RULE [lift_closure_certificate_def])
  >> rw []
  >~ [‘lift_function_certificate _ _ _ _ _ _’] >- (simp [do_opapp_def] >> metis_tac [])
  >~ [‘do_opapp [Closure _ _ _;_]’] >- (
    simp [do_opapp_def]
    >> metis_tac [lift_runtime_env_bind])
  >~ [‘lift_rec_certificate _ source funs target funs' ren’] >- (
    qmatch_asmsub_rename_tac ‘rename_var ren (Short name) = Short renamed’
    >> ‘IS_SOME (find_recfun name funs)’ by simp [find_recfun_defined]
    >> namedCases_on ‘find_recfun name funs’ ["","entry"] >> gvs []
    >> namedCases_on ‘entry’ ["arg body"] >> drule_all lift_rec_certificate_find_recfun_index
    >> disch_then (qx_choosel_then [‘index’,‘compiled_body’] strip_assume_tac)
    >> have ‘ALL_DISTINCT (MAP FST funs) ∧ ALL_DISTINCT (MAP FST funs')’
    >- fs [lift_rec_certificate_def]
    >> simp [do_opapp_def,ELIM_UNCURRY,ETA_THM]
    >> metis_tac [])
  >> qmatch_goalsub_rename_tac ‘Recclosure source funs name’
  >> qmatch_asmsub_rename_tac ‘lift_runtime_env _ source target’ >> simp [do_opapp_def]
  >> IF_CASES_TAC >> simp []
  >> namedCases_on ‘find_recfun name funs’ ["","entry"] >> simp []
  >> namedCases_on ‘entry’ ["arg body"] >> simp []
  >> drule lift_runtime_env_build_rec_env >> disch_then (qspec_then ‘funs’ assume_tac)
  >> qpat_x_assum ‘∀source target body. _’ irule >> drule_all lift_runtime_env_bind
  >> disch_then (qspec_then ‘arg’ mp_tac) >> simp []
QED

Theorem lift_closure_certificate_runtime_rel[local]:
  lift_closure_certificate lift_runtime_rel value value' ⇒
  lift_runtime_rel value value'
Proof
  strip_tac
  >> qpat_assum ‘lift_closure_certificate _ _ _’
       (mp_tac o REWRITE_RULE [lift_closure_certificate_def])
  >> rw [] >> simp [lift_runtime_rel_cases_l]
QED

Theorem lift_runtime_rel_function_closure[local]:
  lift_function_certificate lift_runtime_rel env x e env' e' ⇒
  lift_runtime_rel (Closure env x e) (Closure env' x e')
Proof
  rw [] >> irule lift_closure_certificate_runtime_rel
  >> simp [lift_closure_certificate_def]
QED

Theorem lift_runtime_env_extend[local]:
  lift_runtime_env R env env' ∧ lift_runtime_env R delta delta' ⇒
  lift_runtime_env R (extend_dec_env delta env) (extend_dec_env delta' env')
Proof
  rw [lift_runtime_env_namespace,extend_dec_env_def]
  >> irule namespacePropsTheory.nsAll2_nsAppend >> simp []
QED

Theorem lift_runtime_env_bindings[local]:
  lift_runtime_env R env env' ∧
  LIST_REL (λa b. FST a = FST b ∧ R (SND a) (SND b)) bindings bindings' ⇒
  lift_runtime_env R
    (env with v := nsAppend (alist_to_ns bindings) env.v)
    (env' with v := nsAppend (alist_to_ns bindings') env'.v)
Proof
  rw [lift_runtime_env_namespace]
  >> irule namespacePropsTheory.nsAll2_nsAppend >> simp []
  >> irule namespacePropsTheory.nsAll2_alist_to_ns >> fs [ELIM_UNCURRY]
QED

Theorem lift_runtime_env_open[local]:
  lift_runtime_env R env env' ⇒
  OPTREL (lift_runtime_env R) (open_dec_env path env) (open_dec_env path env')
Proof
  rw [lift_runtime_env_namespace]
  >> namedCases_on ‘nsOpen path env'.c’ ["","constructors"]
  >> namedCases_on ‘nsOpen path env.v’ ["","source_values"]
  >> namedCases_on ‘nsOpen path env'.v’ ["","target_values"]
  >> gvs [open_dec_env_def,OPTREL_def,lift_runtime_env_namespace]
  >> imp_res_tac namespacePropsTheory.nsAll2_after_nsOpen
  >> imp_res_tac namespacePropsTheory.nsAll2_before_nsOpen >> gvs []
QED

Theorem lift_eval_result_rel_mono[local]:
  (∀value value'. success_rel value value' ⇒ success_rel' value value') ∧
  lift_eval_result_rel R D success_rel
    (source_eval:'ffi semanticPrimitives$state # ('a,v) result) target_eval ⇒
  lift_eval_result_rel R D success_rel' source_eval target_eval
Proof
  rpt strip_tac >> PairCases_on ‘source_eval’ >> PairCases_on ‘target_eval’
  >> gvs [lift_eval_result_rel_def,lift_result_rel_cases]
QED

Theorem rename_var_used_or_original[local]:
  lift_renaming_wf ren used ∧
  rename_var ren (Short original) = (Short mapped:(mlstring,mlstring) id) ⇒
  original = mapped ∨ mapped ∈ FDOM used
Proof
  namedCases_on ‘FLOOKUP ren original’ ["","renamed"]
  >> gvs [rename_var_def,lift_renaming_wf_def] >> metis_tac []
QED

Theorem lift_scope_choose_names_locals[local]:
  lift_scope R captures bound ren (n,ds,used) source global locals ∧
  EVERY (λname. bump name 0 ≤ n) names ∧ lift_state_fresh (n,ds,used) ∧
  choose_names bound names (n,ds,used) = (names',n1,ds1,used1) ⇒
  ∀mapped. MEM mapped names' ⇒ ALOOKUP locals mapped = NONE
Proof
  strip_tac
  >> drule_all choose_names_fresh >> strip_tac >> qx_gen_tac ‘mapped’ >> strip_tac
  >> drule_all LIST_REL_MEM_IMP_R
  >> disch_then (qx_choose_then ‘original’ strip_assume_tac)
  >> ‘mapped ∉ FDOM used’ by metis_tac [flookup_thm] >> fs [lift_scope_def]
  >> namedCases_on ‘ALOOKUP locals mapped’ ["","local_value"] >> simp []
  >> drule ALOOKUP_MEM >> disch_tac
  >> qpat_assum ‘∀name local_value. MEM (name,local_value) locals ⇒ _’
    (qspecl_then [‘mapped’,‘local_value’] mp_tac)
  >> simp [] >> metis_tac [rename_var_used_or_original,flookup_thm]
QED

Theorem lift_scope_emit_dec[local]:
  lift_scope R captures bound ren st source global locals ∧
  emit_dec d st = st' ⇒
  lift_scope R captures bound ren st' source global locals
Proof
  PairCases_on ‘st’ >> rw [emit_dec_def] >> fs [lift_scope_def] >> metis_tac []
QED

Theorem lift_scope_env_rel[local]:
  lift_scope R captures bound ren st source global locals ⇒
  lift_env_rel R captures ren source
    (global with v := nsBindList locals global.v)
Proof
  namedCases_on ‘st’ ["n ds used"]
  >> simp [lift_scope_def]
QED

Theorem lift_scope_domain_subset[local]:
  FDOM captures' ⊆ FDOM captures ∧
  lift_scope R captures bound ren st source global locals ⇒
  lift_scope R captures' bound ren st source global locals
Proof
  namedCases_on ‘st’ ["n ds used"]
  >> rw [lift_scope_def,lift_env_rel_def,SUBSET_DEF,FDOM_DRESTRICT] >> metis_tac []
QED

Theorem lift_env_rel_subset[local]:
  lift_env_rel R C ren env env' ∧ FDOM C' ⊆ FDOM C ∧
  (∀x. x ∈ FDOM C' ⇒ rename_var ren' (Short x) = rename_var ren (Short x)) ⇒
  lift_env_rel R C' ren' env env'
Proof
  rw [lift_env_rel_def,SUBSET_DEF] >> metis_tac []
QED

Theorem bind_all_domain[local]:
  FDOM (bind_all names bound) = set names ∪ FDOM bound
Proof
  qid_spec_tac ‘bound’
  >> Induct_on ‘names’ >> simp [bind_all_def,EXTENSION] >> metis_tac []
QED

Theorem lift_scope_rename_global_binding[local]:
  lift_scope R (fdomsub captures arg) bound ren (n,ds,used) source global locals ∧
  arg ∉ FDOM bound ∧ R value value' ∧ ALOOKUP locals renamed = NONE ∧
  (∀name. name ∈ FDOM captures ∧ name ≠ arg ⇒
    rename_var ren (Short name) ≠ (Short renamed:(mlstring,mlstring) id)) ∧
  lift_renaming_wf (ren |+ (arg,renamed)) used' ∧
  FDOM used ⊆ FDOM used' ∧ renamed ∈ FDOM used' ∧ n ≤ n' ∧
  lift_state_fresh (n',ds',used') ⇒
  lift_scope R captures bound (ren |+ (arg,renamed)) (n',ds',used')
    (source with v := nsBind arg value source.v)
    (global with v := nsBind renamed value' global.v) locals
Proof
  strip_tac
  >> have ‘lift_env_rel R captures (ren |+ (arg,renamed))
       (source with v := nsBind arg value source.v)
       (global with v := nsBindList locals (nsBind renamed value' global.v))’
  >- (
    drule lift_scope_env_rel >> disch_tac
    >> drule_all lift_env_rel_rename_bind
    >> simp [lift_env_rel_def,nsBindList_global_bind_commute_lookup])
  >> have ‘lift_env_rel R (DRESTRICT captures (COMPL (FDOM bound)))
       (ren |+ (arg,renamed)) (source with v := nsBind arg value source.v)
       (global with v := nsBind renamed value' global.v)’
  >- (
    have ‘fdomsub (DRESTRICT captures (COMPL (FDOM bound))) arg =
         DRESTRICT (fdomsub captures arg) (COMPL (FDOM bound))’
    >- (rw [fmap_eq_flookup,FLOOKUP_DRESTRICT,DOMSUB_FLOOKUP_THM] >> rw [])
    >> irule lift_env_rel_rename_bind >> simp [FDOM_DRESTRICT]
    >> fs [lift_scope_def])
  >> gvs [lift_scope_def] >> rpt conj_tac
  >- (rpt strip_tac >> fs [SUBSET_DEF] >> metis_tac [rename_var_bind_other])
  >- (rw [] >> metis_tac [rename_var_bind_other])
  >- (
    qx_gen_tac ‘captured_name’ >> strip_tac
    >> Cases_on ‘captured_name = arg’ >> simp [rename_var_bind,rename_var_bind_other]
    >> fs [SUBSET_DEF]
    >> metis_tac [])
  >> qx_genl_tac [‘captured_name’,‘counter’] >> strip_tac
  >> Cases_on ‘captured_name = arg’ >> simp [rename_var_bind,rename_var_bind_other]
  >> metis_tac [lift_state_fresh_used]
QED

Theorem lift_scope_discard_reserved_bindings[local]:
  lift_scope R captures bound ren (n,ds,used) source global locals ∧
  DISJOINT (FDOM captures) (set names) ∧ FDOM used ⊆ FDOM used' ∧
  set names ⊆ FDOM used' ∧ n ≤ n' ⇒
  lift_scope R captures (delete_all names bound) ren (n',ds',used') source global locals
Proof
  strip_tac
  >> have ‘lift_renaming_wf ren used'’
  >- (irule lift_renaming_wf_used_subset >> qexists_tac ‘used’ >> fs [lift_scope_def])
  >> fs [lift_scope_def,DISJOINT_ALT]
  >> simp [lift_scope_def,delete_all_domain] >> rpt conj_tac
  >- (
    irule lift_env_rel_subset >> first_assum (irule_at Any)
    >> rw [FDOM_DRESTRICT,SUBSET_DEF] >> metis_tac [])
  >- (
    qx_genl_tac [‘local_name’,‘local_value’] >> strip_tac
    >> Cases_on ‘local_name ∈ FDOM used'’ >> simp []
    >> qpat_assum ‘∀name local_value. MEM (name,local_value) locals ⇒ _’
      (qspecl_then [‘local_name’,‘local_value’] mp_tac)
    >> simp []
    >> have ‘local_name ∉ FDOM used ∧ ¬MEM local_name names’
    >- (fs [SUBSET_DEF] >> metis_tac [])
    >> simp [] >> metis_tac [rename_var_used_or_original])
  >- (rw [] >> metis_tac [])
  >> fs [SUBSET_DEF] >> metis_tac []
QED

Theorem lift_scope_bind[local]:
  lift_scope R (fdomsub captures arg) bound ren (n,ds,used) source global locals ∧
  R value value' ∧ bump arg 0 ≤ n ∧
  (∀name. name ∈ FDOM captures ∧ name ≠ arg ⇒
    rename_var ren (Short name) ≠ (Short arg:(mlstring,mlstring) id)) ⇒
  lift_scope R captures (bound |+ (arg,())) (fdomsub ren arg) (n,ds,used)
    (source with v := nsBind arg value source.v) global ((arg,value')::locals)
Proof
  strip_tac
  >> ‘∀k. n ≤ k ⇒ arg ≠ make_name k’ by metis_tac [bump_make_name,LESS_EQ_TRANS]
  >> fs [lift_scope_def] >> rewrite_tac [lift_scope_def] >> conj_tac
  >- (irule lift_renaming_wf_fdomsub >> simp []) >> rpt conj_tac
  >- (drule_all lift_env_rel_bind >> simp [namespaceTheory.nsBindList_def])
  >- (
    qpat_x_assum ‘lift_env_rel R (DRESTRICT (fdomsub captures arg) (COMPL (FDOM bound)))
        ren source global’
      (strip_assume_tac o SRULE [lift_env_rel_def,FDOM_DRESTRICT])
    >> rw [lift_env_rel_def,FDOM_DRESTRICT,rename_var_shadow_other]
    >> metis_tac [])
  >- (
    rw []
    >> metis_tac [rename_var_shadow,rename_var_shadow_other,rename_var_used_or_original])
  >- (
    qx_genl_tac [‘name’,‘renamed’] >> strip_tac
    >> Cases_on ‘name = arg’ >> gvs [rename_var_shadow,rename_var_shadow_other]
    >> rpt IF_CASES_TAC >> gvs []
    >> metis_tac [])
  >- (rw [rename_var_shadow_other] >> metis_tac [])
  >> qx_genl_tac [‘name’,‘k’] >> strip_tac >> Cases_on ‘name = arg’
  >> gvs [rename_var_shadow,rename_var_shadow_other] >> metis_tac []
QED

Theorem lift_scope_bindings[local]:
  lift_scope R (delete_all names captures) bound ren (n,ds,used) source global locals ∧
  MAP FST bindings = names ∧
  LIST_REL (λ(x,v) (y,w). x = y ∧ R v w) bindings bindings' ∧
  EVERY (λname. bump name 0 ≤ n) names ∧
  (∀name binding. name ∈ FDOM captures ∧ ¬MEM name names ∧ MEM binding names ⇒
    rename_var ren (Short name) ≠ (Short binding:(mlstring,mlstring) id)) ⇒
  lift_scope R captures (bind_all names bound) (delete_all names ren) (n,ds,used)
    (source with v := nsBindList bindings source.v) global (bindings' ++ locals)
Proof
  strip_tac
  >> drule LIST_REL_MAP_FST >> disch_tac
  >> have ‘∀name k. MEM name names ∧ n ≤ k ⇒ name ≠ make_name k’
  >- (fs [EVERY_MEM] >> metis_tac [bump_make_name,LESS_EQ_TRANS])
  >> fs [lift_scope_def,delete_all_domain]
  >> simp [lift_scope_def,bind_all_domain,rename_var_delete_all,MEM_APPEND,
           ALOOKUP_APPEND,lift_renaming_wf_delete_all]
  >> rpt conj_tac
  >- (
    mp_tac (Q.INST [‘fvs’ |-> ‘captures’,‘env’ |-> ‘source’,
        ‘env'’ |-> ‘global with v := nsBindList locals global.v’]
      (SPEC_ALL lift_env_rel_bindings))
    >> simp [nsBindList_append])
  >- (
    qpat_x_assum ‘lift_env_rel R
        (DRESTRICT (delete_all names captures) (COMPL (FDOM bound))) ren source global’
      (strip_assume_tac o SRULE
        [lift_env_rel_def,FDOM_DRESTRICT,delete_all_domain])
    >> rw [lift_env_rel_def,FDOM_DRESTRICT,rename_var_delete_all,
           nsBindList_long_lookup]
    >> qmatch_goalsub_rename_tac ‘nsLookup _ (Short lookup_name)’
    >> ‘ALOOKUP bindings lookup_name = NONE’ by metis_tac [ALOOKUP_NONE]
    >> simp [nsBindList_short_lookup]
    >> metis_tac [])
  >- (
    rpt strip_tac
    >> Cases_on ‘name ∈ FDOM used’ >> simp []
    >- (
      ‘MEM name names’ by metis_tac [MEM_MAP,pairTheory.FST]
      >> qexists_tac ‘name’
      >> simp [])
    >> qpat_x_assum ‘∀name local_value. MEM _ locals ⇒ _’
      (qspecl_then [‘name’,‘local_value’] mp_tac)
    >> simp [] >> disch_then (qx_choose_then ‘original’ strip_assume_tac)
    >> qexists_tac ‘original’ >> metis_tac [rename_var_used_or_original])
  >- (
    qx_genl_tac [‘name’,‘renamed’]
    >> Cases_on ‘MEM name names’ >> simp [] >> strip_tac
    >> namedCases_on ‘ALOOKUP bindings' renamed’ ["","lookup_value"] >> gvs []
    >> metis_tac [ALOOKUP_NONE])
  >- (rpt strip_tac >> Cases_on ‘MEM name names’ >> gvs [] >> metis_tac [])
  >> qx_gen_tac ‘k’ >> strip_tac
  >> ‘ALOOKUP bindings' (make_name k) = NONE’ by metis_tac [ALOOKUP_NONE] >> simp []
QED

Theorem lift_scope_closed[local]:
  lift_scope R captures bound ren st source global locals ∧
  maps_disjoint captures bound ⇒
  lift_scope R captures bound ren st source global []
Proof
  namedCases_on ‘st’ ["n ds used"] >> strip_tac
  >> have ‘DISJOINT (FDOM bound) (FDOM captures)’
  >- fs [maps_disjoint_def,str_empty_def,GSYM DRESTRICT_EQ_FEMPTY]
  >> fs [lift_scope_def,disjoint_drestrict]
  >> rw [lift_scope_def,namespaceTheory.nsBindList_def,disjoint_drestrict]
  >> metis_tac [IN_DISJOINT]
QED

Theorem lift_scope_captures_protected[local]:
  lift_scope R captures bound ren (n,ds,used) source global locals ⇒
  ∀name renamed. name ∈ FDOM captures ∧
    rename_var ren (Short name) = (Short renamed:(mlstring,mlstring) id) ⇒
    renamed ∈ FDOM used ∨ IS_SOME (ALOOKUP locals renamed)
Proof
  strip_tac
  >> fs [lift_scope_def] >> qx_genl_tac [‘name’,‘renamed’] >> strip_tac
  >> Cases_on ‘name ∈ FDOM bound’
  >- (
    qpat_assum ‘∀name renamed. _ ⇒ IS_SOME (ALOOKUP locals renamed)’
      (qspecl_then [‘name’,‘renamed’] mp_tac)
    >> simp [])
  >> qpat_x_assum ‘∀name. name ∈ FDOM captures ∧ name ∉ FDOM bound ⇒ _’
       (qspec_then ‘name’ mp_tac)
  >> simp []
QED

Theorem lift_scope_compiled_lookup[local]:
  lift_scope R captures bound ren (n,ds,used) source initial locals ∧
  lift_state_decs_avoid (n,ds,used) (n1,ds1,used1) ∧
  lift_global_decs (REVERSE ds) base initial ∧
  lift_global_decs (REVERSE ds1) base final ∧
  exp_free_names e ⊆ lift_renamed_names ren (FDOM captures) ∪ FDOM used ⇒
  ∀id. (∀name. id = Short name ⇒ name ∈ exp_free_names e) ⇒
    nsLookup (nsBindList locals final.v) id =
      nsLookup (nsBindList locals initial.v) id
Proof
  strip_tac
  >> drule lift_scope_captures_protected >> disch_tac
  >> drule_all lift_global_decs_state_suffix
  >> disch_then (qx_choose_then ‘extra’ strip_assume_tac)
  >> qx_gen_tac ‘id’ >> strip_tac >> irule lift_global_decs_avoid_locals_lookup
  >> qexistsl_tac [‘REVERSE extra’,‘FDOM used’] >> simp [lift_decs_avoid_reverse]
  >> fs [SUBSET_DEF,lift_renamed_names_def] >> metis_tac []
QED

Theorem lift_scope_decs_avoid[local]:
  lift_scope R captures bound ren (n,ds,used) source initial locals ∧
  lift_state_extends (n,ds,used) (n1,ds1,used1) ∧
  lift_state_decs_avoid (n,ds,used) (n1,ds1,used1) ∧
  lift_global_decs (REVERSE ds) base initial ∧
  lift_global_decs (REVERSE ds1) base final ⇒
  lift_scope R captures bound ren (n1,ds1,used1) source final locals
Proof
  strip_tac
  >> drule lift_scope_captures_protected >> disch_tac
  >> qpat_x_assum ‘lift_scope R captures bound ren (n,ds,used) source initial locals’
       (mp_tac o REWRITE_RULE [lift_scope_def])
  >> strip_tac
  >> have ‘lift_env_rel R captures ren source
        (final with v := nsBindList locals final.v)’
  >- (drule_all lift_state_decs_avoid_env_rel >> simp [])
  >> have ‘∀name renamed.
        name ∈ FDOM (DRESTRICT captures (COMPL (FDOM bound))) ∧
        rename_var ren (Short name) = (Short renamed:(mlstring,mlstring) id) ⇒
        renamed ∈ FDOM used’
  >- (
    rw [FDOM_DRESTRICT]
    >> qpat_x_assum ‘∀name. name ∈ FDOM captures ∧ name ∉ FDOM bound ⇒ _’
         (qspec_then ‘name’ mp_tac)
    >> simp [])
  >> have ‘lift_env_rel R (DRESTRICT captures (COMPL (FDOM bound))) ren source final’
  >- (
    drule_all (SRULE [namespaceTheory.nsBindList_def]
      (Q.INST [‘locals’ |-> ‘[]’] (SPEC_ALL lift_state_decs_avoid_env_rel)))
    >> simp [])
  >> ‘n ≤ n1 ∧ FDOM used ⊆ FDOM used1’ by fs [lift_state_extends_def]
  >> drule_all lift_renaming_wf_used_subset >> disch_tac
  >> simp [lift_scope_def] >> rpt conj_tac
  >- (
    qx_genl_tac [‘name’,‘local_value’] >> strip_tac
    >> qpat_assum ‘∀name local_value. MEM (name,local_value) locals ⇒ _’
      (qspecl_then [‘name’,‘local_value’] mp_tac)
    >> simp [] >> strip_tac
    >- (disj1_tac >> fs [SUBSET_DEF])
    >> disj2_tac
    >> metis_tac [])
  >- metis_tac []
  >> qx_gen_tac ‘name’ >> strip_tac
  >> qpat_x_assum ‘∀name. name ∈ FDOM captures ∧ name ∉ FDOM bound ⇒ _’
       (qspec_then ‘name’ mp_tac)
  >> simp [] >> disch_then (qx_choose_then ‘renamed’ strip_assume_tac)
  >> qexists_tac ‘renamed’ >> fs [SUBSET_DEF]
QED

Theorem lift_scope_local_names[local]:
  lift_scope R captures bound ren (n,ds,used) source global locals ∧
  MEM (name,value) locals ⇒ name ∈ FDOM used ∨ name ∈ FDOM bound
Proof
  rw [lift_scope_def]
  >> Cases_on ‘name ∈ FDOM used’ >> simp []
  >> qpat_assum ‘∀local_name local_value. MEM (local_name,local_value) locals ⇒ _’
    (qspecl_then [‘name’,‘value’] mp_tac)
  >> simp [] >> metis_tac [rename_var_used_or_original]
QED

Theorem lift_scope_choose_name[local]:
  lift_scope R captures bound ren (n,ds,used) source global locals ∧
  choose_name bound name (n,ds,used) = (renamed,st) ⇒
  ALOOKUP locals renamed = NONE ∧
  (∀original. original ∈ FDOM captures ∧ original ≠ name ⇒
    rename_var ren (Short original) ≠ (Short renamed:(mlstring,mlstring) id))
Proof
  rw [choose_name_def]
  >- (
    namedCases_on ‘ALOOKUP locals name’ ["","value"] >> gvs []
    >> ‘MEM (name,value) locals’ by metis_tac [ALOOKUP_MEM]
    >> drule_all lift_scope_local_names
    >> fs [FLOOKUP_DEF])
  >- (fs [lift_scope_def,FLOOKUP_DEF] >> metis_tac [rename_var_used_or_original])
  >- fs [lift_scope_def]
  >> fs [lift_scope_def]
QED

Theorem lift_scope_function_certificate[local]:
  annotate_exp [] body = (tree,limit,captures) ∧
  source_dce$no_Open body ∧ check_exp_constructors source.c body ∧
  bump arg 0 ≤ n ∧ limit ≤ n ∧ lift_state_fresh (n,ds,used) ∧
  lift_function_body bound ren (n,ds,used) arg tree = (body',n1,ds1,used1) ∧
  lift_global_decs (REVERSE ds) base initial ∧
  lift_global_decs (REVERSE ds1) base final ∧
  lift_scope R (fdomsub captures arg) bound ren (n,ds,used) source initial locals ∧
  (∀name renamed. FLOOKUP ren name = SOME renamed ∧ renamed ≠ name ⇒
    ∀original. original ∈ exp_names body ∨ original = arg ⇒ renamed ≠ original) ⇒
  lift_function_certificate R source arg body
    (final with v := nsBindList locals final.v) body'
Proof
  strip_tac
  >> drule_all (cj 1 annotate_constructors) >> disch_tac
  >> drule_all lift_function_body_constructors >> disch_tac
  >> ‘source.c = initial.c’ by fs [lift_scope_def,lift_env_rel_def]
  >> imp_res_tac lift_global_decs_constructors >> ‘source.c = final.c’ by fs []
  >> rewrite_tac [lift_function_certificate_def]
  >> first_assum $ irule_at (Pat ‘lift_function_body _ _ _ _ _ = _’)
  >> qexistsl_tac [‘locals’,‘limit’,‘initial’,‘final’,‘captures’,‘base’] >> gvs [] >> metis_tac []
QED

Theorem rename_var_updates_distinct[local]:
  ALL_DISTINCT (MAP FST bindings) ⇒
  EVERY (λ(original,mapped).
    rename_var (ren |++ bindings) (Short original) = (Short mapped:(mlstring,mlstring) id))
    bindings
Proof
  strip_tac
  >> simp_tac (srw_ss()) [EVERY_MEM,FORALL_PROD]
  >> qx_genl_tac [‘original’,‘mapped’] >> strip_tac
  >> have ‘FLOOKUP (ren |++ bindings) original = SOME mapped’
  >- (
    rewrite_tac [miscTheory.flookup_update_list_some]
    >> disj1_tac >> irule ALOOKUP_ALL_DISTINCT_MEM
    >> simp [MAP_REVERSE,ALL_DISTINCT_REVERSE,MEM_REVERSE])
  >> simp [rename_var_def]
QED

Theorem lift_scope_renaming_cong[local]:
  lift_scope R captures bound ren (n,ds,used) source global locals ∧
  lift_renaming_wf ren' used ∧
  (∀name. name ∈ FDOM captures ∨ name ∈ FDOM bound ⇒
    rename_var ren' (Short name) = (rename_var ren (Short name):(mlstring,mlstring) id)) ⇒
  lift_scope R captures bound ren' (n,ds,used) source global locals
Proof
  strip_tac
  >> fs [lift_scope_def,lift_env_rel_def] >> fs [FDOM_DRESTRICT] >> rpt conj_tac
  >> metis_tac []
QED

Theorem lift_scope_delete_renaming[local]:
  lift_scope R captures bound ren st source global locals ∧
  DISJOINT (FDOM captures) (set names) ⇒
  lift_scope R captures bound (delete_all names ren) st source global locals
Proof
  namedCases_on ‘st’ ["n ds used"] >> strip_tac
  >> fs [lift_scope_def,DISJOINT_ALT]
  >> simp [lift_scope_def,lift_renaming_wf_delete_all,rename_var_delete_all]
  >> rpt conj_tac
  >- (
    fs [lift_env_rel_def]
    >> rw [lift_env_rel_def,rename_var_delete_all]
    >> metis_tac [])
  >- (
    fs [lift_env_rel_def,FDOM_DRESTRICT]
    >> rw [lift_env_rel_def,FDOM_DRESTRICT,rename_var_delete_all]
    >> metis_tac [])
  >- (
    qx_genl_tac [‘local_name’,‘local_value’] >> strip_tac
    >> Cases_on ‘local_name ∈ FDOM used’ >> simp []
    >> qpat_assum ‘∀name local_value. MEM (name,local_value) locals ⇒ _’
      (qspecl_then [‘local_name’,‘local_value’] mp_tac)
    >> simp [] >> disch_then (qx_choose_then ‘original’ strip_assume_tac)
    >> qexists_tac ‘original’ >> metis_tac [rename_var_used_or_original])
  >> qx_genl_tac [‘capture_name’,‘mapped’] >> strip_tac
  >> ‘¬MEM capture_name names’ by metis_tac [] >> fs [] >> metis_tac []
QED

Theorem lift_env_rel_renamed_bindings[local]:
  lift_env_rel R C ren env (env' with v := nsBindList locals env'.v) ∧
  (∀name. name ∈ FDOM fvs ∧ ¬MEM name (MAP FST bindings) ⇒ name ∈ FDOM C) ∧
  (∀name. MEM name (MAP FST bindings') ⇒ ALOOKUP locals name = NONE) ∧
  (∀name mapped. name ∈ FDOM fvs ∧
    rename_var ren (Short name) = (Short mapped:(mlstring,mlstring) id) ⇒
    (MEM name (MAP FST bindings) ⇔ MEM mapped (MAP FST bindings')) ∧
    (MEM name (MAP FST bindings) ⇒
      OPTREL R (ALOOKUP bindings name) (ALOOKUP bindings' mapped))) ⇒
  lift_env_rel R fvs ren (env with v := nsBindList bindings env.v)
    (env' with v := nsBindList locals (nsBindList bindings' env'.v))
Proof
  rw [lift_env_rel_def] >> fs [lift_env_rel_def,nsBindList_long_lookup]
  >> ‘∃mapped. rename_var ren (Short x) = (Short mapped:(mlstring,mlstring) id)’
    by (Cases_on ‘FLOOKUP ren x’ >> simp [rename_var_def])
  >> simp [nsBindList_short_lookup]
  >> Cases_on ‘MEM x (MAP FST bindings)’
  >- (
    ‘ALOOKUP locals mapped = NONE ∧
     OPTREL R (ALOOKUP bindings x) (ALOOKUP bindings' mapped)’ by metis_tac []
    >> Cases_on ‘ALOOKUP bindings x’ >- metis_tac [ALOOKUP_NONE]
    >> Cases_on ‘ALOOKUP bindings' mapped’ >> gvs [OPTREL_def])
  >> ‘¬MEM mapped (MAP FST bindings') ∧ x ∈ FDOM C’ by metis_tac []
  >> qpat_x_assum ‘∀x. x ∈ FDOM C ⇒ _’ (qspec_then ‘x’ mp_tac)
  >> gvs [GSYM ALOOKUP_NONE,nsBindList_short_lookup]
QED

Theorem lift_scope_renamed_global_bindings[local]:
  lift_scope R (delete_all names captures) bound ren (n,ds,used) source global locals ∧
  MAP FST bindings = names ∧ MAP FST bindings' = names' ∧
  DISJOINT (set names) (FDOM bound) ∧ set names' ⊆ FDOM used ∧
  (∀name mapped. name ∈ FDOM captures ∧
    rename_var ren (Short name) = (Short mapped:(mlstring,mlstring) id) ⇒
    (MEM name names ⇔ MEM mapped names')) ∧
  (∀name mapped. name ∈ FDOM captures ∧ MEM name names ∧
    rename_var ren (Short name) = (Short mapped:(mlstring,mlstring) id) ⇒
    OPTREL R (ALOOKUP bindings name) (ALOOKUP bindings' mapped)) ∧
  (∀name. MEM name names' ⇒ ALOOKUP locals name = NONE) ∧
  (∀name k. MEM name names' ∧ n ≤ k ⇒ name ≠ make_name k) ⇒
  lift_scope R captures bound ren (n,ds,used)
    (source with v := nsBindList bindings source.v)
    (global with v := nsBindList bindings' global.v) locals
Proof
  strip_tac
  >> fs [lift_scope_def,delete_all_domain] >> simp [lift_scope_def] >> rpt conj_tac
  >- (
    irule lift_env_rel_renamed_bindings >> first_assum (irule_at Any)
    >> rw [delete_all_domain] >> metis_tac [])
  >- (
    irule (SRULE [nsBindList_clauses]
      (Q.INST [‘locals’ |-> ‘[]’] lift_env_rel_renamed_bindings))
    >> first_assum (irule_at Any) >> rw [FDOM_DRESTRICT,delete_all_domain] >> metis_tac [])
  >- (qpat_assum ‘∀name local_value. MEM (name,local_value) locals ⇒ _’ ACCEPT_TAC)
  >- (rpt strip_tac >> fs [DISJOINT_ALT] >> metis_tac [])
  >- (
    qx_gen_tac ‘capture_name’ >> strip_tac
    >> Cases_on ‘MEM capture_name names’ >- (
      ‘∃mapped. rename_var ren (Short capture_name) = (Short mapped:(mlstring,mlstring) id)’
        by (Cases_on ‘FLOOKUP ren capture_name’ >> simp [rename_var_def])
      >> qexists_tac ‘mapped’ >> fs [SUBSET_DEF] >> metis_tac [])
    >> metis_tac [])
  >> qx_genl_tac [‘capture_name’,‘counter’] >> strip_tac >> CCONTR_TAC
  >> Cases_on ‘MEM capture_name names’ >> metis_tac []
QED

Theorem lift_scope_rec_certificate[local]:
  annotate_funs [] funs = (trees,limit,captures) ∧
  EVERY (λ(f,x,e). source_dce$no_Open e ∧ check_exp_constructors source.c e) funs ∧
  ALL_DISTINCT (MAP FST funs) ∧ ALL_DISTINCT (MAP FST funs') ∧
  LIST_REL (λname renamed.
    rename_var ren (Short name) = (Short renamed:(mlstring,mlstring) id))
    (MAP FST funs) (MAP FST funs') ∧
  limit ≤ n ∧ lift_state_fresh (n,ds,used) ∧
  lift_funs (bind_all (MAP FST funs) bound) ren (n,ds,used)
    (ZIP (MAP FST funs',MAP (FST o SND) funs)) trees = (funs',n1,ds1,used1) ∧
  lift_global_decs (REVERSE ds) base initial ∧
  lift_global_decs (REVERSE ds1) base final ∧
  lift_scope R (delete_all (MAP FST funs) captures) bound ren (n,ds,used)
    source initial locals ∧
  (∀name renamed. name ∈ FDOM captures ∧
    rename_var ren (Short name) = (Short renamed:(mlstring,mlstring) id) ⇒
    (MEM name (MAP FST funs) ⇔ MEM renamed (MAP FST funs'))) ∧
  (∀name k. MEM name (MAP FST funs') ∧ n ≤ k ⇒ name ≠ make_name k) ∧
  (∀name renamed. FLOOKUP ren name = SOME renamed ∧ renamed ≠ name ⇒
    ∀original. original ∈ exp_names_funs funs ⇒ renamed ≠ original) ⇒
  lift_rec_certificate R source funs
    (final with v := nsBindList locals final.v) funs' ren
Proof
  strip_tac
  >> have ‘EVERY (λ(f,x,e). check_exp_constructors source.c e) funs’
  >- fs [ELIM_UNCURRY,EVERY_CONJ]
  >> drule_all (cj 4 annotate_constructors) >> disch_tac
  >> drule_all (cj 5 lift_exp_constructors) >> disch_tac
  >> ‘source.c = initial.c’ by fs [lift_scope_def,lift_env_rel_def]
  >> imp_res_tac lift_global_decs_constructors >> ‘source.c = final.c’ by fs []
  >> simp [lift_rec_certificate_def]
  >> first_assum $ irule_at (Pat ‘lift_funs _ _ _ _ _ = _’)
  >> qexistsl_tac [‘locals’,‘initial’,‘final’,‘base’] >> simp [] >> rpt conj_tac
  >- metis_tac []
  >- (
    rpt strip_tac >> Cases_on ‘MEM name (MAP FST funs)’
    >> gvs [lift_scope_def,delete_all_domain] >> metis_tac [])
  >> metis_tac []
QED

(* ------------------------------------------------------------------------
   Evaluation refinement and congruences for unchanged constructs
   ------------------------------------------------------------------------ *)

Definition lift_eval_refinement_def:
  lift_eval_refinement R D success_rel source target ⇔
    SND source = Rerr (Rabort Rtype_error) ∨
    lift_eval_result_rel R D success_rel source target
End

Theorem lift_eval_refinement_nonfailure[local]:
  lift_eval_refinement R D success_rel source target ∧
  SND source ≠ Rerr (Rabort Rtype_error) ⇒
  lift_eval_result_rel R D success_rel source target
Proof
  rw [lift_eval_refinement_def]
QED

Theorem lift_evaluate_simple[local]:
  getOpClass op = Simple ∧
  lift_state_rel (lift_value_rel C E) D (s:'ffi semanticPrimitives$state) s' ∧
  lift_eval_result_rel (lift_value_rel C E) D (LIST_REL (lift_value_rel C E))
    (evaluate s env (REVERSE es)) (evaluate s' env' (REVERSE es')) ⇒
  lift_eval_refinement (lift_value_rel C E) D (LIST_REL (lift_value_rel C E))
    (evaluate s env [App op es]) (evaluate s' env' [App op es'])
Proof
  strip_tac
  >> Cases_on ‘evaluate s env (REVERSE es)’ >> Cases_on ‘evaluate s' env' (REVERSE es')’
  >> gvs [evaluate_def,lift_eval_refinement_def,lift_eval_result_rel_def,
          lift_result_rel_cases]
  >> rename1 ‘evaluate s env (REVERSE es) = (t,Rval vs)’
  >> rename1 ‘evaluate s' env' (REVERSE es') = (t',Rval vs')’
  >> Cases_on ‘do_app (t.refs,t.ffi) op (REVERSE vs)’ >> simp []
  >> rename1 ‘do_app _ _ _ = SOME result’ >> PairCases_on ‘result’
  >> ‘t.ffi = t'.ffi’ by fs [lift_state_rel_def]
  >> drule_at (Pos last) shape_val_rel_do_app
  >> disch_then (qspecl_then [‘REVERSE vs'’,‘lift_value_rel C E’,‘t'.refs’] mp_tac)
  >> gvs [lift_value_rel_shape,LIST_REL_REVERSE_EQ,lift_state_rel_def]
  >> strip_tac >> simp [lift_eval_result_rel_def,lift_state_rel_def]
  >> Cases_on ‘result2’ >> gvs [list_result_def,lift_result_rel_cases]
  >> rename1 ‘exc_rel _ err _’ >> Cases_on ‘err’
  >> gvs [exc_rel_raise1,exc_rel_type_error1]
QED

Theorem lift_evaluate_ptr_eq[local]:
  lift_eval_result_rel (lift_value_rel C E) D (LIST_REL (lift_value_rel C E))
    (evaluate (s:'ffi semanticPrimitives$state) env (REVERSE es))
    (evaluate s' env' (REVERSE es')) ⇒
  lift_eval_refinement (lift_value_rel C E) D (LIST_REL (lift_value_rel C E))
    (evaluate s env [App PtrEq es]) (evaluate s' env' [App PtrEq es'])
Proof
  strip_tac
  >> Cases_on ‘evaluate s env (REVERSE es)’ >> Cases_on ‘evaluate s' env' (REVERSE es')’
  >> gvs [evaluate_def,lift_eval_refinement_def,lift_eval_result_rel_def,
          lift_result_rel_cases]
  >> rename1 ‘evaluate s env (REVERSE es) = (t,Rval vs)’
  >> rename1 ‘evaluate s' env' (REVERSE es') = (t',Rval vs')’
  >> ‘LIST_REL (lift_value_rel C E) (REVERSE vs) (REVERSE vs')’
       by simp [LIST_REL_REVERSE_EQ]
  >> Cases_on ‘∃v1 v2. REVERSE vs = [v1; v2]’
  >- (
    gvs []
    >> ‘LIST_REL (lift_value_rel C E) [v1; v2] (REVERSE vs')’
         by metis_tac [LIST_REL_REVERSE_EQ]
    >> qpat_x_assum ‘LIST_REL _ [_; _] _’
         (strip_assume_tac o SIMP_RULE std_ss [LIST_REL_CONS1,LIST_REL_NIL])
    >> rename1 ‘lift_value_rel C E v1 w1’ >> rename1 ‘lift_value_rel C E v2 w2’
    >> ‘do_eq w1 w2 = do_eq v1 v2’
         by metis_tac [shape_val_rel_do_eq_eq,lift_value_rel_shape]
    >> gvs []
    >> Cases_on ‘do_eq v1 v2’
    >> gvs [lift_eval_result_rel_def,lift_state_rel_def,lift_result_rel_def,
            Boolv_def,lift_value_rel_cases_l]
    >> rw [lift_value_rel_cases_l])
  >> disj1_tac
  >> Cases_on ‘REVERSE vs’ >> simp []
  >> rename1 ‘REVERSE vs = _::rest’ >> Cases_on ‘rest’ >> simp []
  >> rename1 ‘REVERSE vs = _::_::rest’ >> Cases_on ‘rest’ >> gvs []
QED

Theorem lift_evaluate_append_refinement[local]:
  lift_eval_refinement R D (LIST_REL R)
    (evaluate (s:'ffi semanticPrimitives$state) env xs)
    (evaluate s' env' xs') ∧
  (∀(t:'ffi semanticPrimitives$state) t'.
    t.clock ≤ s.clock ∧ lift_state_rel R D t t' ⇒
    lift_eval_refinement R D (LIST_REL R)
      (evaluate t env ys) (evaluate t' env' ys')) ⇒
  lift_eval_refinement R D (LIST_REL R)
    (evaluate s env (xs ++ ys)) (evaluate s' env' (xs' ++ ys'))
Proof
  strip_tac
  >> namedCases_on ‘evaluate s env xs’ ["source_state source_result"]
  >> namedCases_on ‘evaluate s' env' xs'’ ["target_state target_result"]
  >> imp_res_tac (cj 1 evaluate_clock)
  >> gvs [lift_eval_refinement_def,lift_eval_result_rel_def,lift_result_rel_cases,
          evaluate_append]
  >> qpat_x_assum ‘∀t t'. _’ (qspecl_then [‘source_state’,‘target_state’] mp_tac)
  >> Cases_on ‘evaluate source_state env ys’ >> Cases_on ‘evaluate target_state env' ys'’
  >> rw [lift_eval_refinement_def,lift_eval_result_rel_def,lift_result_rel_cases]
  >> simp [lift_eval_result_rel_def,lift_result_rel_cases,LIST_REL_APPEND_suff]
QED

Theorem lift_evaluate_list_refinement[local]:
  LIST_REL (λe e'.
    ∀(t:'ffi semanticPrimitives$state) t'.
      t.clock ≤ clock ∧ lift_state_rel R D t t' ⇒
      lift_eval_refinement R D (LIST_REL R)
        (evaluate t env [e]) (evaluate t' env' [e'])) es es' ⇒
  ∀(s:'ffi semanticPrimitives$state) s'.
    s.clock ≤ clock ∧ lift_state_rel R D s s' ⇒
    lift_eval_refinement R D (LIST_REL R)
      (evaluate s env es) (evaluate s' env' es')
Proof
  qid_spec_tac ‘es'’
  >> Induct_on ‘es’ >> namedCases_on ‘es'’ ["","target_head target_tail"] >> simp []
  >- (
    simp [cj 1 evaluate_def,lift_eval_refinement_def,
          lift_eval_result_rel_def,lift_result_rel_def])
  >> qx_gen_tac ‘source_head’ >> strip_tac >> qx_genl_tac [‘s’,‘s'’] >> strip_tac
  >> irule (SRULE []
       (Q.INST [‘xs’ |-> ‘[source_head]’,‘xs'’ |-> ‘[target_head]’]
         (SPEC_ALL lift_evaluate_append_refinement)))
  >> simp [] >> metis_tac [LESS_EQ_TRANS]
QED

Theorem lift_eval_refinement_single[local]:
  lift_eval_refinement R D (LIST_REL R)
    (evaluate (s:'ffi semanticPrimitives$state) env [e]) (evaluate s' env' [e']) ⇒
  ∃t r t' r'.
    evaluate s env [e] = (t,r) ∧ evaluate s' env' [e'] = (t',r') ∧
    t.clock ≤ s.clock ∧
    (r = Rerr (Rabort Rtype_error) ∨
     lift_state_rel R D t t' ∧
     ((∃v v'. r = Rval [v] ∧ r' = Rval [v'] ∧ R v v') ∨
      (∃v v'. r = Rerr (Rraise v) ∧ r' = Rerr (Rraise v') ∧ R v v') ∨
      (∃a. r = Rerr (Rabort a) ∧ r' = Rerr (Rabort a))))
Proof
  Cases_on ‘evaluate s env [e]’ >> Cases_on ‘evaluate s' env' [e']’
  >> rw [lift_eval_refinement_def,lift_eval_result_rel_def,lift_result_rel_cases]
  >> imp_res_tac (cj 1 evaluate_clock) >> imp_res_tac evaluate_length
  >> gvs [LENGTH_EQ_NUM_compute]
QED

Inductive lift_declared_value:
  (∀ds lit. lift_declared_value ds (Lit lit)) ∧
  (∀ds arg body. lift_declared_value ds (Fun arg body)) ∧
  (∀ds loc name body. MEM (Dlet loc (Pvar name) body) ds ⇒
    lift_declared_value ds (Var (Short name))) ∧
  (∀ds cn es. EVERY (lift_declared_value ds) es ⇒
    lift_declared_value ds (Con cn es))
End

Theorem lift_declared_value_mono[local]:
  ∀ds e. lift_declared_value ds e ⇒
    ∀ds'. set ds ⊆ set ds' ⇒ lift_declared_value ds' e
Proof
  ho_match_mp_tac lift_declared_value_ind >> rpt conj_tac >> rpt strip_tac
  >> simp [Once lift_declared_value_cases] >> fs [EVERY_MEM,SUBSET_DEF] >> metis_tac []
QED

Theorem lift_global_decs_defined[local]:
  ∀ds base final. lift_global_decs ds base final ⇒
    ∀name.
      IS_SOME (nsLookup base.v (Short name)) ∨
      (∃loc body. MEM (Dlet loc (Pvar name) body) ds) ⇒
      IS_SOME (nsLookup final.v (Short name))
Proof
  ho_match_mp_tac lift_global_decs_ind >> rpt conj_tac >> rpt gen_tac >> simp []
  >> rpt strip_tac
  >> qpat_x_assum ‘∀name. _ ⇒ IS_SOME (nsLookup final.v (Short name))’ irule
  >> simp [namespacePropsTheory.nsLookup_nsBind,nsLookup_build_rec_env]
  >~ [‘nsLookup (nsBind binding_name binding_value _) (Short lookup_name)’] >- (
    Cases_on ‘lookup_name = binding_name’
    >> fs [namespacePropsTheory.nsLookup_nsBind]
    >> metis_tac [])
  >> rpt IF_CASES_TAC >> simp [] >> metis_tac []
QED

Theorem lift_declared_value_ready[local]:
  ∀ds e. lift_declared_value ds e ⇒
    ∀base final.
      lift_global_decs (REVERSE ds) base final ∧ check_exp_constructors final.c e ⇒
      value_ready final e
Proof
  ho_match_mp_tac lift_declared_value_ind >> rpt conj_tac >> rpt strip_tac
  >> simp [Once value_ready_cases] >> fs [check_exp_constructors_def,EVERY_MEM]
  >> metis_tac [lift_global_decs_defined,MEM_REVERSE,IS_SOME_EXISTS]
QED

Theorem lift_evaluate_con_refinement[local]:
  env.c = env'.c ∧ LENGTH es = LENGTH es' ∧
  lift_state_rel (lift_value_rel C E) D (s:'ffi semanticPrimitives$state) s' ∧
  lift_eval_refinement (lift_value_rel C E) D (LIST_REL (lift_value_rel C E))
    (evaluate s env (REVERSE es)) (evaluate s' env' (REVERSE es')) ⇒
  lift_eval_refinement (lift_value_rel C E) D (LIST_REL (lift_value_rel C E))
    (evaluate s env [Con cn es]) (evaluate s' env' [Con cn es'])
Proof
  strip_tac
  >> simp [evaluate_def] >> IF_CASES_TAC
  >> gvs [lift_eval_refinement_def,lift_eval_result_rel_def,lift_result_rel_def]
  >> Cases_on ‘evaluate s env (REVERSE es)’ >> Cases_on ‘evaluate s' env' (REVERSE es')’
  >> gvs [lift_eval_refinement_def,lift_eval_result_rel_def,lift_result_rel_cases]
  >> ‘OPTREL (lift_value_rel C E) (build_conv env'.c cn (REVERSE x))
        (build_conv env'.c cn (REVERSE y))’ by
    metis_tac [LIST_REL_REVERSE,lift_value_rel_build_conv]
  >> Cases_on ‘build_conv env'.c cn (REVERSE x)’
  >> Cases_on ‘build_conv env'.c cn (REVERSE y)’
  >> gvs [lift_eval_result_rel_def,lift_result_rel_def]
QED

Theorem lift_evaluate_raise_refinement[local]:
  lift_eval_refinement R D (LIST_REL R)
    (evaluate s env [e]) (evaluate s' env' [e']) ⇒
  lift_eval_refinement R D (LIST_REL R)
    (evaluate s env [Raise e]) (evaluate s' env' [Raise e'])
Proof
  strip_tac >> drule lift_eval_refinement_single >> rw []
  >> gvs [evaluate_def,lift_eval_refinement_def,lift_eval_result_rel_def,
          lift_result_rel_def]
QED

Theorem lift_evaluate_let_refinement[local]:
  lift_eval_refinement R D (LIST_REL R)
    (evaluate (s:'ffi semanticPrimitives$state) source [rhs])
    (evaluate s' target [rhs']) ∧
  (∀(t:'ffi semanticPrimitives$state) t' value value'.
    t.clock ≤ s.clock ∧ lift_state_rel R D t t' ∧ R value value' ⇒
    lift_eval_refinement R D (LIST_REL R)
      (evaluate t (source with v := nsOptBind name value source.v) [body])
      (evaluate t' (target with v := nsOptBind name' value' target.v) [body'])) ⇒
  lift_eval_refinement R D (LIST_REL R)
    (evaluate s source [Let name rhs body])
    (evaluate s' target [Let name' rhs' body'])
Proof
  strip_tac >> drule lift_eval_refinement_single >> rw []
  >> gvs [cj 13 evaluate_def,lift_eval_result_rel_def,lift_result_rel_def,
       lift_eval_refinement_def]
QED

Theorem lift_evaluate_handle_refinement[local]:
  env.c = env'.c ∧ MAP FST pes = MAP FST pes' ∧
  lift_eval_refinement (lift_value_rel C E) D (LIST_REL (lift_value_rel C E))
    (evaluate (s:'ffi semanticPrimitives$state) env [e])
    (evaluate s' env' [e']) ∧
  (∀(t:'ffi semanticPrimitives$state) t' v v'.
    t.clock ≤ s.clock ∧ lift_state_rel (lift_value_rel C E) D t t' ∧
    lift_value_rel C E v v' ⇒
    lift_eval_refinement (lift_value_rel C E) D (LIST_REL (lift_value_rel C E))
      (evaluate_match t env v pes v) (evaluate_match t' env' v' pes' v')) ⇒
  lift_eval_refinement (lift_value_rel C E) D (LIST_REL (lift_value_rel C E))
    (evaluate s env [Handle e pes]) (evaluate s' env' [Handle e' pes'])
Proof
  strip_tac >> drule lift_eval_refinement_single >> rw []
  >> gvs [cj 5 evaluate_def,lift_eval_result_rel_def,lift_result_rel_def,
          lift_eval_refinement_def]
  >> ‘LIST_REL (sv_rel (lift_value_rel C E)) t.refs t'.refs’ by fs [lift_state_rel_def]
  >> ‘can_pmatch_all env'.c t.refs (MAP FST pes') v =
      can_pmatch_all env'.c t'.refs (MAP FST pes') v'’ by metis_tac [lift_can_pmatch_all]
  >> simp [] >> IF_CASES_TAC >> simp [] >> metis_tac []
QED

Theorem lift_evaluate_match_list_refinement[local]:
  ∀pes pes' (s:'ffi semanticPrimitives$state) s' v v' err err'.
    LIST_REL (λ(p,e) (p',e'). p = p' ∧
      ∀(t:'ffi semanticPrimitives$state) t' bindings bindings'.
        t.clock ≤ s.clock ∧ MAP FST bindings = pat_bindings p ∧
        lift_state_rel (lift_value_rel C E) D t t' ∧
        LIST_REL (λa b. FST a = FST b ∧ lift_value_rel C E (SND a) (SND b))
          bindings bindings' ⇒
        lift_eval_refinement (lift_value_rel C E) D (LIST_REL (lift_value_rel C E))
          (evaluate t (env with v := nsAppend (alist_to_ns bindings) env.v) [e])
          (evaluate t' (env' with v := nsAppend (alist_to_ns bindings') env'.v) [e']))
      pes pes' ∧
    env.c = env'.c ∧ lift_state_rel (lift_value_rel C E) D s s' ∧
    lift_value_rel C E v v' ∧ lift_value_rel C E err err' ⇒
    lift_eval_refinement (lift_value_rel C E) D (LIST_REL (lift_value_rel C E))
      (evaluate_match s env v pes err) (evaluate_match s' env' v' pes' err')
Proof
  Induct_on ‘pes’ >> rpt gen_tac
  >> namedCases_on ‘pes'’ ["","target_entry target_tail"]
  >> simp [Once evaluate_def,lift_eval_refinement_def,lift_eval_result_rel_def,
           lift_result_rel_def]
  >- simp [evaluate_def,lift_eval_refinement_def,lift_eval_result_rel_def,
           lift_result_rel_def]
  >> qmatch_goalsub_rename_tac ‘evaluate_match s env v (source_entry::pes) err’
  >> namedCases_on ‘source_entry’ ["pattern source_body"]
  >> namedCases_on ‘target_entry’ ["target_pattern target_body"] >> rw [evaluate_def]
  >> gvs [lift_eval_result_rel_def,lift_result_rel_def,lift_eval_refinement_def]
  >> ‘LIST_REL (sv_rel (lift_value_rel C E)) s.refs s'.refs’ by fs [lift_state_rel_def]
  >> have ‘lift_match_rel (lift_value_rel C E)
        (pmatch env'.c s.refs pattern v [])
        (pmatch env'.c s'.refs pattern v' [])’
  >- (irule (CONJUNCT1 lift_value_rel_pmatch) >> simp [LIST_REL_OPTREL_store_lookup])
  >> gvs [lift_match_rel_cases,lift_eval_result_rel_def,lift_result_rel_def,
          lift_eval_refinement_def]
  >> imp_res_tac (cj 1 pmatch_extend) >> gvs [] >> metis_tac [LESS_EQ_REFL]
QED

Theorem lift_evaluate_mat_refinement[local]:
  env.c = env'.c ∧ MAP FST pes = MAP FST pes' ∧
  lift_eval_refinement (lift_value_rel C E) D (LIST_REL (lift_value_rel C E))
    (evaluate (s:'ffi semanticPrimitives$state) env [e])
    (evaluate s' env' [e']) ∧
  (∀(t:'ffi semanticPrimitives$state) t' v v'.
    t.clock ≤ s.clock ∧ lift_state_rel (lift_value_rel C E) D t t' ∧
    lift_value_rel C E v v' ⇒
    lift_eval_refinement (lift_value_rel C E) D (LIST_REL (lift_value_rel C E))
      (evaluate_match t env v pes bind_exn_v)
      (evaluate_match t' env' v' pes' bind_exn_v)) ⇒
  lift_eval_refinement (lift_value_rel C E) D (LIST_REL (lift_value_rel C E))
    (evaluate s env [Mat e pes]) (evaluate s' env' [Mat e' pes'])
Proof
  strip_tac >> drule lift_eval_refinement_single >> rw []
  >> gvs [cj 12 evaluate_def,lift_eval_result_rel_def,lift_result_rel_def,
          lift_eval_refinement_def]
  >> ‘LIST_REL (sv_rel (lift_value_rel C E)) t.refs t'.refs’ by fs [lift_state_rel_def]
  >> ‘can_pmatch_all env'.c t.refs (MAP FST pes') v =
      can_pmatch_all env'.c t'.refs (MAP FST pes') v'’ by metis_tac [lift_can_pmatch_all]
  >> simp [] >> IF_CASES_TAC >> simp [] >> metis_tac []
QED

Theorem lift_evaluate_if_refinement[local]:
  lift_eval_refinement (lift_value_rel C E) D (LIST_REL (lift_value_rel C E))
    (evaluate (s:'ffi semanticPrimitives$state) env [e1]) (evaluate s' env' [e1']) ∧
  (∀(t:'ffi semanticPrimitives$state) t'.
    t.clock ≤ s.clock ∧ lift_state_rel (lift_value_rel C E) D t t' ⇒
    lift_eval_refinement (lift_value_rel C E) D (LIST_REL (lift_value_rel C E))
      (evaluate t env [e2]) (evaluate t' env' [e2'])) ∧
  (∀(t:'ffi semanticPrimitives$state) t'.
    t.clock ≤ s.clock ∧ lift_state_rel (lift_value_rel C E) D t t' ⇒
    lift_eval_refinement (lift_value_rel C E) D (LIST_REL (lift_value_rel C E))
      (evaluate t env [e3]) (evaluate t' env' [e3'])) ⇒
  lift_eval_refinement (lift_value_rel C E) D (LIST_REL (lift_value_rel C E))
    (evaluate s env [If e1 e2 e3]) (evaluate s' env' [If e1' e2' e3'])
Proof
  strip_tac >> drule lift_eval_refinement_single >> rw []
  >> gvs [cj 11 evaluate_def,lift_eval_result_rel_def,lift_result_rel_def,
          lift_eval_refinement_def]
  >> ‘(v = Boolv T ⇔ v' = Boolv T) ∧ (v = Boolv F ⇔ v' = Boolv F)’ by
    metis_tac [lift_value_rel_bool]
  >> simp [do_if_def] >> rpt IF_CASES_TAC >> gvs [] >> metis_tac []
QED

Theorem lift_evaluate_log_refinement[local]:
  lift_eval_refinement (lift_value_rel C E) D (LIST_REL (lift_value_rel C E))
    (evaluate (s:'ffi semanticPrimitives$state) env [e1])
    (evaluate s' env' [e1']) ∧
  (∀(t:'ffi semanticPrimitives$state) t'.
    t.clock ≤ s.clock ∧ lift_state_rel (lift_value_rel C E) D t t' ⇒
    lift_eval_refinement (lift_value_rel C E) D (LIST_REL (lift_value_rel C E))
      (evaluate t env [e2]) (evaluate t' env' [e2'])) ⇒
  lift_eval_refinement (lift_value_rel C E) D (LIST_REL (lift_value_rel C E))
    (evaluate s env [Log lop e1 e2]) (evaluate s' env' [Log lop e1' e2'])
Proof
  strip_tac >> drule lift_eval_refinement_single >> rw []
  >> gvs [cj 10 evaluate_def,lift_eval_result_rel_def,lift_result_rel_def,
          lift_eval_refinement_def]
  >> ‘(v = Boolv T ⇔ v' = Boolv T) ∧ (v = Boolv F ⇔ v' = Boolv F)’ by
    metis_tac [lift_value_rel_bool]
  >> simp [do_log_def] >> rpt IF_CASES_TAC >> gvs []
  >> simp [lift_eval_result_rel_def,lift_result_rel_def]
QED

Theorem lift_annotated_variable[local]:
  annotate_exp t (Var id) = (tree,limit,captures) ⇒
  lower_exp mode bound ren st tree = (Var (rename_var ren id),st) ∧
  lift_exp mode bound ren st tree = (Var (rename_var ren id),st)
Proof
  namedCases_on ‘id’ ["name","module_name nested_id"]
  >> rw [annotate_exp_def] >> simp [cj 1 lift_exp_def,cj 5 lift_exp_def]
QED

Theorem lift_annotated_literal[local]:
  annotate_exp t (Lit lit) = (tree,limit,captures) ∧
  (lower_exp mode bound ren st tree = (compiled,st') ∨
   lift_exp mode bound ren st tree = (compiled,st')) ⇒
  (compiled = Lit lit ∧ st' = st) ∨ emit_value (Lit lit) st = (compiled,st')
Proof
  strip_tac
  >> gvs [annotate_exp_def] >> Cases_on ‘mode = LiftValues ∧ ¬is_trivial (Lit lit)’
  >> gvs [cj 1 lift_exp_def,cj 17 lift_exp_def,
          str_empty_def,maps_disjoint_def,is_Fun_def]
QED

Theorem lift_annotated_constructor[local]:
  annotate_exp t (Con cn es) = (tree,limit,captures) ∧
  annotate_exps t es = (trees,list_limit,list_captures) ∧
  (lower_exp mode bound ren st tree = (compiled,st') ∨
   lift_exp mode bound ren st tree = (compiled,st')) ⇒
  ∃child_mode arguments middle.
    lift_exps child_mode bound ren st trees = (arguments,middle) ∧
    ((child_mode = mode ∧ compiled = Con cn arguments ∧ st' = middle) ∨
     child_mode = LiftFunctions ∧ EVERY tree_value trees ∧
     maps_disjoint captures bound ∧
     emit_value (Con cn arguments) middle = (compiled,st'))
Proof
  strip_tac
  >> gvs [annotate_exp_def]
  >> Cases_on ‘mode = LiftValues ∧ EVERY tree_value trees ∧
       maps_disjoint captures bound ∧ ¬is_trivial (Con cn es)’
  >> gvs [cj 1 lift_exp_def,cj 2 lift_exp_def,is_Fun_def] >> rpt (pairarg_tac >> gvs [])
  >~ [‘(if _ then _ else _) = _’] >- (
    qpat_x_assum ‘(if _ then _ else _) = _’ mp_tac
    >> IF_CASES_TAC >> gvs [] >> strip_tac >> gvs [EVERY_MEM,EXISTS_MEM,o_DEF]
    >> asm_exists_tac
    >> simp [EVERY_MEM])
  >> asm_exists_tac >> simp []
QED

Theorem lift_function_body_routes[local]:
  lift_function_body bound ren st arg tree = (compiled,st') ⇒
  lower_exp LiftValues (bound |+ (arg,())) (fdomsub ren arg) st tree = (compiled,st') ∨
  lift_exp LiftValues (bound |+ (arg,())) (fdomsub ren arg) st tree = (compiled,st')
Proof
  rw [lift_function_body_def]
QED

Theorem lift_annotated_function[local]:
  annotate_exp t (Fun arg body) = (tree,limit,captures) ∧
  annotate_exp t body = (body_tree,body_limit,body_captures) ∧
  (lower_exp mode bound ren st tree = (compiled,st') ∨
   lift_exp mode bound ren st tree = (compiled,st')) ⇒
  ∃body' body_state.
    lift_function_body bound ren st arg body_tree = (body',body_state) ∧
    ((compiled = Fun arg body' ∧ st' = body_state) ∨
     maps_disjoint captures bound ∧
     emit_value (Fun arg body') body_state = (compiled,st'))
Proof
  strip_tac
  >> namedCases_on ‘lift_function_body bound ren st arg body_tree’
       ["compiled_body body_n body_ds body_used"]
  >> qexistsl_tac [‘compiled_body’,‘(body_n,body_ds,body_used)’]
  >> gvs [annotate_exp_def]
  >> fs [cj 1 lift_exp_def,lower_function_body,is_Fun_def,is_trivial_def]
  >> Cases_on ‘(mode = LiftValues ∨ mode = LiftFunctions) ∧
       maps_disjoint (fdomsub body_captures arg) bound’
  >> gvs []
QED

Theorem lift_annotated_state_properties[local]:
  annotate_exp t e = (tree,limit,captures) ∧ source_dce$no_Open e ∧
  limit ≤ n ∧ lift_state_fresh (n,ds,used) ∧
  (lower_exp mode bound ren (n,ds,used) tree = (compiled,n1,ds1,used1) ∨
   lift_exp mode bound ren (n,ds,used) tree = (compiled,n1,ds1,used1)) ⇒
  lift_state_fresh (n1,ds1,used1) ∧
  lift_state_extends (n,ds,used) (n1,ds1,used1) ∧
  lift_state_decs_avoid (n,ds,used) (n1,ds1,used1) ∧
  exp_free_names compiled ⊆ lift_renamed_names ren (FDOM captures) ∪ FDOM used1
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th))
  >> ‘tree_names_bounded limit tree’ by metis_tac [cj 1 annotate_tree_names_bounded]
  >> ‘FDOM captures = exp_free_names e’ by metis_tac [cj 1 annotate_free_names]
  >> rpt conj_tac
  >- metis_tac [cj 1 lift_exp_fresh,cj 2 lift_exp_fresh,pairTheory.FST]
  >- metis_tac [cj 1 lift_exp_state_extends,cj 2 lift_exp_state_extends]
  >- metis_tac [cj 1 lift_exp_fresh,cj 2 lift_exp_fresh,pairTheory.FST]
  >> drule_all (cj 1 lift_annotated_free_names) >> simp []
QED

Theorem lift_annotated_state_properties_lift[local] =
  cj 2 (SRULE [LEFT_AND_OVER_OR,DISJ_IMP_THM]
    lift_annotated_state_properties);

Theorem lift_exps_declared_values[local]:
  ∀es.
    (∀e. MEM e es ⇒
      ∀t tree limit captures mode bound ren st compiled n1 ds1 used1.
        annotate_exp t e = (tree,limit,captures) ∧
        lift_exp mode bound ren st tree = (compiled,n1,ds1,used1) ⇒
        lift_declared_value ds1 compiled) ⇒
    ∀t trees limit captures mode bound ren st compiled n1 ds1 used1.
      annotate_exps t es = (trees,limit,captures) ∧
      lift_exps mode bound ren st trees = (compiled,n1,ds1,used1) ⇒
      EVERY (lift_declared_value ds1) compiled
Proof
  Induct_on ‘es’
  >- (rw [annotate_exp_def] >> gvs [Once lift_exp_def])
  >> qx_gen_tac ‘head’ >> strip_tac
  >> qx_genl_tac [‘t’,‘trees’,‘limit’,‘captures’,‘mode’,‘bound’,‘ren’,‘st’,
       ‘compiled’,‘out_n’,‘out_ds’,‘out_used’]
  >> strip_tac
  >> namedCases_on ‘annotate_exp t head’ ["head_tree head_limit head_captures"]
  >> namedCases_on ‘annotate_exps t es’ ["tail_trees tail_limit tail_captures"]
  >> drule_all annotate_exps_CONS
  >> disch_then (qx_choose_then ‘combined_captures’ strip_assume_tac)
  >> gvs [map_eq_def] >> namedCases_on ‘lift_exp mode bound ren st head_tree’
       ["head_result head_n head_ds head_used"]
  >> namedCases_on ‘lift_exps mode bound ren (head_n,head_ds,head_used) tail_trees’
       ["tail_results tail_n tail_ds tail_used"]
  >> gvs [Once lift_exp_def]
  >> qpat_assum ‘∀e. e = head ∨ MEM e es ⇒ _’ (qspec_then ‘head’ mp_tac) >> simp []
  >> disch_then (qspecl_then [‘t’,‘head_tree’,‘head_limit’,‘head_captures’,‘mode’,
       ‘bound’,‘ren’,‘st’,‘head_result’,‘head_n’,‘head_ds’,‘head_used’] mp_tac)
  >> simp [] >> disch_tac >> qpat_x_assum ‘(∀e. MEM e es ⇒ _) ⇒ _’ mp_tac >> impl_tac
  >- (
    qx_gen_tac ‘e’ >> strip_tac
    >> qpat_assum ‘∀e. e = head ∨ MEM e es ⇒ _’ (qspec_then ‘e’ mp_tac)
    >> simp [])
  >> disch_then (qspecl_then [‘t’,‘tail_trees’,‘tail_limit’,‘tail_captures’,‘mode’,
       ‘bound’,‘ren’,‘(head_n,head_ds,head_used)’,‘tail_results’,
       ‘out_n’,‘out_ds’,‘out_used’] mp_tac)
  >> simp [] >> disch_tac
  >> have ‘set head_ds ⊆ set out_ds’
  >- (
    imp_res_tac (cj 3 lift_exp_state_extends)
    >> fs [lift_state_extends_def,SUBSET_DEF]
    >> metis_tac [MEM_APPEND])
  >> have ‘lift_declared_value out_ds head_result’
  >- (irule lift_declared_value_mono >> qexists_tac ‘head_ds’ >> simp [])
  >> simp []
QED

Theorem lift_constant_declared_value[local]:
  ∀e. constant_exp e ⇒
    ∀t tree limit captures mode bound ren st compiled n1 ds1 used1.
      annotate_exp t e = (tree,limit,captures) ∧
      (lower_exp mode bound ren st tree = (compiled,n1,ds1,used1) ∨
       lift_exp mode bound ren st tree = (compiled,n1,ds1,used1)) ⇒
      lift_declared_value ds1 compiled
Proof
  ho_match_mp_tac constant_exp_ind >> rpt conj_tac
  >- (
    qx_genl_tac [‘lit’,‘t’,‘tree’,‘limit’,‘captures’,‘mode’,‘bound’,‘ren’,‘st’,
         ‘compiled’,‘out_n’,‘out_ds’,‘out_used’]
    >> disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th))
    >> namedCases_on ‘st’ ["n ds used"] >> drule_all lift_annotated_literal
    >> qpat_x_assum ‘lower_exp _ _ _ _ _ = _ ∨ lift_exp _ _ _ _ _ = _’ kall_tac
    >> strip_tac >> gvs [emit_value_def] >> simp [Once lift_declared_value_cases]
    >> qexistsl_tac [‘NoLocs’,‘Lit lit’] >> simp [])
  >- (
    qx_genl_tac [‘arg’,‘body’,‘t’,‘tree’,‘limit’,‘captures’,‘mode’,‘bound’,‘ren’,
         ‘st’,‘compiled’,‘out_n’,‘out_ds’,‘out_used’]
    >> disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th))
    >> namedCases_on ‘annotate_exp t body’ ["body_tree body_limit body_captures"]
    >> drule_all lift_annotated_function
    >> qpat_x_assum ‘lower_exp _ _ _ _ _ = _ ∨ lift_exp _ _ _ _ _ = _’ kall_tac
    >> disch_then (qx_choose_then ‘compiled_body’
         (qx_choose_then ‘body_state’
           (fn th => MAP_EVERY assume_tac (CONJUNCTS th))))
    >> namedCases_on ‘body_state’ ["body_n body_ds body_used"] >> gvs [emit_value_def]
    >> simp [Once lift_declared_value_cases]
    >> qexistsl_tac [‘NoLocs’,‘Fun arg compiled_body’] >> simp [])
  >- (
    qx_genl_tac [‘cn’,‘es’] >> strip_tac
    >> qx_genl_tac [‘t’,‘tree’,‘limit’,‘captures’,‘mode’,‘bound’,‘ren’,‘st’,
         ‘compiled’,‘out_n’,‘out_ds’,‘out_used’]
    >> disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th))
    >> namedCases_on ‘annotate_exps t es’ ["trees list_limit list_captures"]
    >> drule_all lift_annotated_constructor
    >> qpat_x_assum ‘lower_exp _ _ _ _ _ = _ ∨ lift_exp _ _ _ _ _ = _’ kall_tac
    >> disch_then (qx_choose_then ‘child_mode’
         (qx_choose_then ‘arguments’
           (qx_choose_then ‘middle’
             (fn th => MAP_EVERY assume_tac (CONJUNCTS th)))))
    >> namedCases_on ‘middle’ ["list_n list_ds list_used"]
    >> have ‘EVERY (lift_declared_value list_ds) arguments’
    >- (
      irule lift_exps_declared_values
      >> qexistsl_tac [‘bound’,‘list_captures’,‘es’,‘list_limit’,‘child_mode’,
           ‘list_n’,‘ren’,‘st’,‘t’,‘trees’,‘list_used’]
      >> simp [] >> qpat_x_assum ‘EVERY _ es’ mp_tac >> simp_tac pure_ss [EVERY_MEM]
      >> metis_tac [])
    >> gvs [emit_value_def] >> simp [Once lift_declared_value_cases]
    >> qexistsl_tac [‘NoLocs’,‘Con cn arguments’] >> simp [])
  >> simp [annotate_exp_def]
QED

Theorem lift_emitted_con_pure[local]:
  annotate_exps t es = (trees,limit,captures) ∧ EVERY tree_value trees ∧
  check_exp_constructors env.c (Con cn es) ∧
  lift_exps LiftFunctions bound ren st trees = (arguments,n1,ds1,used1) ∧
  lift_global_decs (REVERSE ds1) base env ⇒
  ∃v. lift_pure_value env (Con cn arguments) v ∧
    check_exp_constructors env.c (Con cn arguments)
Proof
  strip_tac >> drule_all (cj 2 annotate_value_sound) >> disch_tac
  >> ‘LENGTH arguments = LENGTH es’ by metis_tac [annotate_LENGTH,cj 1 lift_output_lengths]
  >> ‘EVERY (check_exp_constructors env.c) arguments’
    by metis_tac [cj 2 annotate_constructors,cj 3 lift_exp_constructors,
         check_exp_constructors_def]
  >> ‘EVERY (lift_declared_value ds1) arguments’ by (
    irule lift_exps_declared_values >> rpt (first_assum (irule_at Any))
    >> fs [EVERY_MEM] >> metis_tac [lift_constant_declared_value])
  >> ‘check_exp_constructors env.c (Con cn arguments)’
    by fs [check_exp_constructors_def,EVERY_MEM]
  >> ‘lift_declared_value ds1 (Con cn arguments)’ by simp [Once lift_declared_value_cases]
  >> metis_tac [lift_declared_value_ready,value_ready_pure]
QED

Theorem lift_bound_lookup[local]:
  MAP FST bindings = (names:mlstring list) ∧
  (∀(id:(mlstring,mlstring) id).
    (∀name. id = Short name ⇒ name ∈ fvs DIFF set names) ⇒
    nsLookup globals id = nsLookup globals' id) ⇒
  ∀(id:(mlstring,mlstring) id).
    (∀name. id = Short name ⇒ name ∈ fvs) ⇒
    nsLookup (nsBindList bindings globals) id =
      nsLookup (nsBindList bindings globals') id
Proof
  strip_tac
  >> qx_gen_tac ‘id’ >> strip_tac >> namedCases_on ‘id’ ["name","module_name nested_id"]
  >- (
    fs []
    >> namedCases_on ‘ALOOKUP bindings name’ ["","value"]
    >> simp [nsBindList_short_lookup] >> ‘¬MEM name names’ by metis_tac [ALOOKUP_NONE]
    >> qpat_assum ‘∀id. _ ⇒ nsLookup globals id = _’ (qspec_then ‘Short name’ mp_tac)
    >> simp [])
  >> qpat_assum ‘∀id. _ ⇒ nsLookup globals id = _’
    (qspec_then ‘Long module_name nested_id’ mp_tac)
  >> simp [nsBindList_long_lookup]
QED

Theorem annotate_pes_cons_shape[local]:
  annotate_pes t ((pattern,body)::pes) = (trees,limit,captures) ∧
  annotate_exp t body = (body_tree,body_limit,body_captures) ∧
  annotate_pes t pes = (tail_trees,tail_limit,tail_captures) ⇒
  trees = body_tree::tail_trees ∧
  limit = MAX (bump_pat body_limit pattern) tail_limit ∧
  captures = FUNION (delete_all (pat_bindings pattern) body_captures) tail_captures
Proof
  strip_tac
  >> gvs [annotate_exp_def]
QED

(* ------------------------------------------------------------------------
   Expression simulation
   ------------------------------------------------------------------------ *)

Definition lift_app_sim_def:
  lift_app_sim (:'ffi) clock D ⇔
    ∀op es es' (s:'ffi semanticPrimitives$state) s' env env'.
      s.clock ≤ clock ∧ lift_state_rel lift_runtime_rel D s s' ∧
      lift_eval_refinement lift_runtime_rel D (LIST_REL lift_runtime_rel)
        (evaluate s env (REVERSE es)) (evaluate s' env' (REVERSE es')) ⇒
      lift_eval_refinement lift_runtime_rel D (LIST_REL lift_runtime_rel)
        (evaluate s env [App op es]) (evaluate s' env' [App op es'])
End

Definition lift_exp_sim_def:
  lift_exp_sim (:'ffi) clock D e ⇔
    ∀tree limit captures mode bound ren n ds used compiled n1 ds1 used1 base initial.
      annotate_exp [] e = (tree,limit,captures) ∧ source_dce$no_Open e ∧
      check_exp_constructors base.c e ∧ limit ≤ n ∧ lift_state_fresh (n,ds,used) ∧
      lift_global_decs (REVERSE ds) base initial ∧
      (∀name renamed. FLOOKUP ren name = SOME renamed ∧ renamed ≠ name ⇒
        ∀original. original ∈ exp_names e ⇒ renamed ≠ original) ∧
      (lower_exp mode bound ren (n,ds,used) tree = (compiled,n1,ds1,used1) ∨
       lift_exp mode bound ren (n,ds,used) tree = (compiled,n1,ds1,used1)) ⇒
      ∃final.
        lift_global_decs (REVERSE ds1) base final ∧
        ∀source locals.
          lift_scope lift_runtime_rel captures bound ren (n,ds,used) source initial locals ⇒
          lift_scope lift_runtime_rel captures bound ren (n1,ds1,used1) source final locals ∧
          ∀(s:'ffi semanticPrimitives$state) s' target.
            s.clock ≤ clock ∧ lift_state_rel lift_runtime_rel D s s' ∧
            target.c = final.c ∧
            (∀id. (∀name. id = Short name ⇒ name ∈ exp_free_names compiled) ⇒
              nsLookup target.v id = nsLookup (nsBindList locals final.v) id) ⇒
            lift_eval_refinement lift_runtime_rel D (LIST_REL lift_runtime_rel)
              (evaluate s source [e]) (evaluate s' target [compiled])
End

Theorem lift_exp_sim_routes[local] = lift_exp_sim_def |> SPEC_ALL |> EQ_IMP_RULE |> fst
  |> UNDISCH |> SIMP_RULE bool_ss [LEFT_AND_OVER_OR,DISJ_IMP_THM,FORALL_AND_THM]
  |> DISCH_ALL |> GEN_ALL

Theorem lift_exp_sim_lift[local] = cj 2 lift_exp_sim_routes

Theorem lift_bound_exp_simulation[local]:
  lift_exp_sim (:'ffi) clock D body ⇒
  annotate_exp [] body = (tree,limit,captures) ∧ source_dce$no_Open body ∧
  check_exp_constructors base.c body ∧ limit ≤ n ∧ lift_state_fresh (n,ds,used) ∧
  EVERY (λname. bump name 0 ≤ n) names ∧ lift_global_decs (REVERSE ds) base initial ∧
  (∀name renamed. FLOOKUP ren name = SOME renamed ∧ renamed ≠ name ⇒
    ∀original. original ∈ exp_names body ∨ MEM original names ⇒ renamed ≠ original) ∧
  lift_exp mode (bind_all names bound) (delete_all names ren) (n,ds,used) tree =
    (compiled,n1,ds1,used1) ⇒
  ∃final.
    lift_global_decs (REVERSE ds1) base final ∧
    ∀source locals.
      lift_scope lift_runtime_rel (delete_all names captures) bound ren (n,ds,used)
        source initial locals ⇒
      lift_scope lift_runtime_rel (delete_all names captures) bound ren (n1,ds1,used1)
        source final locals ∧
      ∀bindings bindings'.
        MAP FST bindings = names ∧
        LIST_REL (λ(x,v) (y,w). x = y ∧ lift_runtime_rel v w) bindings bindings' ⇒
        lift_scope lift_runtime_rel captures (bind_all names bound) (delete_all names ren)
          (n1,ds1,used1) (source with v := nsBindList bindings source.v) final
          (bindings' ++ locals) ∧
        ∀(s:'ffi semanticPrimitives$state) s' target.
          s.clock ≤ clock ∧ lift_state_rel lift_runtime_rel D s s' ∧ target.c = final.c ∧
          (∀id. (∀name. id = Short name ⇒ name ∈ exp_free_names compiled) ⇒
            nsLookup target.v id = nsLookup
              (nsBindList (bindings' ++ locals) final.v) id) ⇒
          lift_eval_refinement lift_runtime_rel D (LIST_REL lift_runtime_rel)
            (evaluate s (source with v := nsBindList bindings source.v) [body])
            (evaluate s' target [compiled])
Proof
  strip_tac
  >> disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th))
  >> have ‘∀name renamed.
         FLOOKUP (delete_all names ren) name = SOME renamed ∧ renamed ≠ name ⇒
       renamed ∉ exp_names body’
  >- (rw [delete_all_lookup] >> metis_tac [])
  >> drule_all lift_exp_sim_lift >> disch_then (qx_choose_then ‘final’ strip_assume_tac)
  >> qexists_tac ‘final’ >> asm_rewrite_tac [] >> qx_genl_tac [‘source’,‘locals’] >> strip_tac
  >> drule_all lift_annotated_state_properties_lift >> strip_tac
  >> drule_all lift_scope_decs_avoid >> simp [] >> disch_tac
  >> qx_genl_tac [‘bindings’,‘bindings'’] >> strip_tac
  >> have ‘∀name binding. name ∈ FDOM captures ∧ ¬MEM name names ∧ MEM binding names ⇒
       rename_var ren (Short name) ≠ (Short binding:(mlstring,mlstring) id)’
  >- (
    qx_genl_tac [‘name’,‘binding’] >> strip_tac
    >> namedCases_on ‘FLOOKUP ren name’ ["","renamed"] >> simp [rename_var_def]
    >> metis_tac [])
  >> have ‘lift_scope lift_runtime_rel captures (bind_all names bound) (delete_all names ren)
       (n,ds,used) (source with v := nsBindList bindings source.v) initial
       (bindings' ++ locals)’
  >- (irule lift_scope_bindings >> simp [])
  >> qpat_x_assum ‘∀source locals. _’ drule >> simp []
QED

Theorem lift_funs_global_decs[local]:
  ∀funs trees limit captures fs bound ren n ds used compiled n1 ds1 used1 base initial.
    (∀f x e. MEM (f,x,e) funs ⇒ lift_exp_sim (:'ffi) clock D e) ∧
    annotate_funs [] funs = (trees,limit,captures) ∧ MAP SND fs = MAP (FST o SND) funs ∧
    EVERY (λ(f,x,e). source_dce$no_Open e ∧ check_exp_constructors base.c e) funs ∧
    limit ≤ n ∧ lift_state_fresh (n,ds,used) ∧ lift_global_decs (REVERSE ds) base initial ∧
    (∀name renamed. FLOOKUP ren name = SOME renamed ∧ renamed ≠ name ⇒
      renamed ∉ exp_names_funs funs) ∧
    lift_funs bound ren (n,ds,used) fs trees = (compiled,n1,ds1,used1) ⇒
    ∃final. lift_global_decs (REVERSE ds1) base final
Proof
  Induct
  >- (rw [Once annotate_exp_def] >> gvs [Once lift_exp_def] >> metis_tac [])
  >> qx_gen_tac ‘entry’ >> PairCases_on ‘entry’ >> rename1 ‘(name,arg,body)::funs’
  >> rpt gen_tac >> strip_tac
  >> namedCases_on ‘fs’ ["","head rest"] >> gvs [] >> PairCases_on ‘head’
  >> namedCases_on ‘annotate_exp [] body’ ["body_tree body_limit body_captures"]
  >> namedCases_on ‘annotate_funs [] funs’ ["tail_trees tail_limit tail_captures"]
  >> gvs [Once annotate_exp_def,lift_funs_cons,DISJ_IMP_THM,FORALL_AND_THM,exp_names_def]
  >> qmatch_asmsub_rename_tac ‘lift_function_body _ _ _ arg _’
  >> namedCases_on ‘lift_function_body bound ren (n,ds,used) arg body_tree’
       ["compiled_body middle_n middle_ds middle_used"]
  >> namedCases_on ‘lift_funs bound ren (middle_n,middle_ds,middle_used) rest tail_trees’
       ["compiled_tail tail_n tail_ds tail_used"]
  >> gvs [] >> ‘body_limit ≤ n’ by metis_tac [bump_le_imp]
  >> have ‘∀name renamed. FLOOKUP (fdomsub ren arg) name = SOME renamed ∧ renamed ≠ name ⇒
       ∀original. original ∈ exp_names body ⇒ renamed ≠ original’
  >- (rw [DOMSUB_FLOOKUP_THM] >> metis_tac [])
  >> drule lift_function_body_routes >> disch_tac
  >> qpat_x_assum ‘lift_exp_sim _ _ _ body’ (drule_all o REWRITE_RULE [lift_exp_sim_def])
  >> disch_then (qx_choose_then ‘middle_env’ strip_assume_tac)
  >> drule_all (cj 1 annotate_tree_names_bounded) >> disch_tac
  >> ‘body_limit ≤ FST (n,ds,used)’ by simp []
  >> drule_all lift_function_body_fresh >> strip_tac
  >> drule lift_function_body_state_extends >> disch_tac
  >> drule lift_state_extends_counter >> simp [] >> disch_tac
  >> ‘tail_limit ≤ middle_n’ by decide_tac
  >> ‘∀name renamed. FLOOKUP ren name = SOME renamed ∧ renamed ≠ name ⇒
        renamed ∉ exp_names_funs funs’ by metis_tac []
  >> last_x_assum drule_all >> simp []
QED

Theorem lift_runtime_evaluate_match_refinement[local]:
  LIST_REL (λ(pattern,body) (pattern',body'). pattern = pattern' ∧
    ∀(t:'ffi semanticPrimitives$state) t' bindings bindings'.
      t.clock ≤ clock ∧ lift_state_rel lift_runtime_rel D t t' ∧
      MAP FST bindings = pat_bindings pattern ∧
      LIST_REL (λ(x,v) (y,w). x = y ∧ lift_runtime_rel v w) bindings bindings' ⇒
      lift_eval_refinement lift_runtime_rel D (LIST_REL lift_runtime_rel)
        (evaluate t (source with v := nsBindList bindings source.v) [body])
        (evaluate t' (target with v := nsBindList bindings' target.v) [body']))
    pes compiled ∧
  (s:'ffi semanticPrimitives$state).clock ≤ clock ∧ source.c = target.c ∧
  lift_state_rel lift_runtime_rel D s s' ∧
  lift_runtime_rel value value' ∧ lift_runtime_rel err err' ⇒
  lift_eval_refinement lift_runtime_rel D (LIST_REL lift_runtime_rel)
    (evaluate_match s source value pes err)
    (evaluate_match s' target value' compiled err')
Proof
  strip_tac
  >> irule (runtime_inst lift_evaluate_match_list_refinement)
  >> simp [namespacePropsTheory.nsAppend_to_nsBindList]
  >> qmatch_asmsub_abbrev_tac ‘LIST_REL branch_rel pes compiled’ >> irule LIST_REL_mono
  >> qexists_tac ‘branch_rel’ >> simp [Abbr ‘branch_rel’,FORALL_PROD]
  >> qx_genl_tac [‘pattern’,‘body’,‘compiled_body’] >> strip_tac
  >> qx_genl_tac [‘source_state’,‘target_state’,‘bindings’,‘bindings'’] >> strip_tac
  >> qpat_assum ‘∀t t' bindings bindings'. _ ⇒ lift_eval_refinement _ _ _ _ _’
    (qspecl_then [‘source_state’,‘target_state’,‘bindings’,‘bindings'’] match_mp_tac)
  >> simp [ELIM_UNCURRY] >> decide_tac
QED

Theorem lift_pes_simulation[local]:
  ∀pes.
    (∀pattern body. MEM (pattern,body) pes ⇒ lift_exp_sim (:'ffi) clock D body) ⇒
    ∀trees limit captures mode bound ren n ds used compiled n1 ds1 used1 base initial.
      annotate_pes [] pes = (trees,limit,captures) ∧
      EVERY (λ(p,body). source_dce$no_Open body ∧ check_exp_constructors base.c body) pes ∧
      limit ≤ n ∧ lift_state_fresh (n,ds,used) ∧
      lift_global_decs (REVERSE ds) base initial ∧
      (∀name renamed. FLOOKUP ren name = SOME renamed ∧ renamed ≠ name ⇒
        ∀original. original ∈ exp_names_pes pes ⇒ renamed ≠ original) ∧
      lift_pes mode bound ren (n,ds,used) (MAP FST pes) trees =
        (compiled,n1,ds1,used1) ⇒
      ∃final.
        lift_global_decs (REVERSE ds1) base final ∧
        ∀source locals.
          lift_scope lift_runtime_rel captures bound ren (n,ds,used) source initial locals ⇒
          lift_scope lift_runtime_rel captures bound ren (n1,ds1,used1) source final locals ∧
          ∀target.
            target.c = final.c ∧
            (∀id. (∀name. id = Short name ⇒ name ∈ exp_free_names_pes compiled) ⇒
              nsLookup target.v id = nsLookup (nsBindList locals final.v) id) ⇒
            LIST_REL (λ(pattern,body) (pattern',body'). pattern = pattern' ∧
              ∀(state:'ffi semanticPrimitives$state) state' bindings bindings'.
                state.clock ≤ clock ∧ lift_state_rel lift_runtime_rel D state state' ∧
                MAP FST bindings = pat_bindings pattern ∧
                LIST_REL (λ(x,v) (y,w). x = y ∧ lift_runtime_rel v w) bindings bindings' ⇒
                lift_eval_refinement lift_runtime_rel D (LIST_REL lift_runtime_rel)
                  (evaluate state (source with v := nsBindList bindings source.v) [body])
                  (evaluate state' (target with v := nsBindList bindings' target.v) [body']))
              pes compiled
Proof
  Induct_on ‘pes’
  >- (rw [Once annotate_exp_def,Once lift_exp_def] >> qexists_tac ‘initial’ >> simp [])
  >> qx_gen_tac ‘entry’ >> namedCases_on ‘entry’ ["pattern body"]
  >> qpat_x_assum ‘(∀pattern body. _) ⇒ _’ (assume_named_tac "IH") >> strip_tac
  >> qx_genl_tac [‘trees’,‘limit’,‘captures’,‘mode’,‘bound’,‘ren’,‘n’,‘ds’,‘used’,
       ‘compiled’,‘n1’,‘ds1’,‘used1’,‘base’,‘initial’]
  >> strip_tac
  >> namedCases_on ‘annotate_exp [] body’ ["body_tree body_limit body_captures"]
  >> namedCases_on ‘annotate_pes [] pes’ ["tail_trees tail_limit tail_captures"]
  >> drule_all annotate_pes_cons_shape >> strip_tac >> gvs [] >> fs [Once lift_exp_def]
  >> rpt (pairarg_tac >> gvs []) >> qmatch_asmsub_rename_tac
       ‘lift_exp mode (bind_all (pat_bindings pattern) bound)
         (delete_all (pat_bindings pattern) ren) (n,ds,used) body_tree =
         (compiled_body,middle)’
  >> namedCases_on ‘middle’ ["middle_n middle_ds middle_used"] >> gvs []
  >> qmatch_asmsub_rename_tac
       ‘lift_pes mode bound ren (middle_n,middle_ds,middle_used)
         (MAP FST pes) tail_trees = (compiled_tail,n1,ds1,used1)’
  >> ‘body_limit ≤ n’ by metis_tac [cj 1 bump_patterns_le,LESS_EQ_TRANS]
  >> have ‘EVERY (λname. bump name 0 ≤ n) (pat_bindings pattern)’
  >- (rw [EVERY_MEM] >> metis_tac [bump_pattern_names,LESS_EQ_TRANS])
  >> have ‘∀name renamed. FLOOKUP ren name = SOME renamed ∧ renamed ≠ name ⇒
       ∀original. original ∈ exp_names body ∨ MEM original (pat_bindings pattern) ⇒
         renamed ≠ original’
  >- (fs [exp_names_def] >> metis_tac [])
  >> qpat_assum ‘∀pattern body. _ ⇒ lift_exp_sim _ _ _ _’
    (assume_tac o SRULE [] o Q.SPECL [‘pattern’,‘body’])
  >> drule_all lift_bound_exp_simulation
  >> disch_then (qx_choose_then ‘head_final’ strip_assume_tac)
  >> drule_all lift_annotated_state_properties_lift >> strip_tac
  >> ‘n ≤ middle_n ∧ tail_limit ≤ middle_n’ by (fs [lift_state_extends_def] >> decide_tac)
  >> ‘∀name renamed. FLOOKUP ren name = SOME renamed ∧ renamed ≠ name ⇒
        ∀original. original ∈ exp_names_pes pes ⇒ renamed ≠ original’
    by (fs [exp_names_def] >> metis_tac [])
  >> asm_x "IH" mp_tac >> impl_tac
  >- (rpt strip_tac >> first_x_assum irule >> metis_tac [MEM])
  >> disch_then (qspecl_then [‘tail_trees’,‘tail_limit’,‘tail_captures’]
       (drule_all o REWRITE_RULE []))
  >> disch_then (qx_choose_then ‘final’ strip_assume_tac)
  >> qexists_tac ‘final’ >> asm_rewrite_tac [] >> qx_genl_tac [‘source’,‘locals’] >> strip_tac
  >> have ‘lift_scope lift_runtime_rel (delete_all (pat_bindings pattern) body_captures)
       bound ren (n,ds,used) source initial locals’
  >- (
    irule lift_scope_domain_subset
    >> qexists_tac ‘FUNION (delete_all (pat_bindings pattern) body_captures) tail_captures’
    >> simp [FDOM_FUNION])
  >> qpat_x_assum ‘∀source locals. lift_scope _ (delete_all _ _) _ _ _ _ _ _ ⇒ _’ drule
  >> strip_tac
  >> qpat_assum ‘lift_scope _ (FUNION _ _) bound ren (n,ds,used) source initial locals’
    (mp_then (Pos hd) drule_all lift_scope_decs_avoid)
  >> disch_tac
  >> have ‘lift_scope lift_runtime_rel tail_captures bound ren
       (middle_n,middle_ds,middle_used) source head_final locals’
  >- (
    irule lift_scope_domain_subset
    >> qexists_tac ‘FUNION (delete_all (pat_bindings pattern) body_captures) tail_captures’
    >> simp [FDOM_FUNION])
  >> qpat_x_assum ‘∀source locals. lift_scope _ tail_captures _ _ _ _ _ _ ⇒ _’ drule
  >> strip_tac
  >> ‘EVERY (λ(p,body). source_dce$no_Open body) pes’ by fs [ELIM_UNCURRY,EVERY_CONJ]
  >> drule_all (cj 3 annotate_tree_names_bounded) >> disch_tac
  >> ‘tail_limit ≤ FST (middle_n,middle_ds,middle_used)’ by simp []
  >> drule_all (cj 2 (cj 4 lift_exp_fresh)) >> disch_tac
  >> drule (cj 4 lift_exp_state_extends) >> disch_tac
  >> qpat_assum ‘lift_scope _ (FUNION _ _) bound ren
       (middle_n,middle_ds,middle_used) source head_final locals’
    (mp_then (Pos hd) drule_all lift_scope_decs_avoid)
  >> disch_tac >> asm_rewrite_tac []
  >> ‘head_final.c = final.c’ by metis_tac [lift_global_decs_constructors]
  >> qx_gen_tac ‘target’ >> strip_tac >> reverse conj_tac
  >- (
    qpat_assum ‘∀target. _ ⇒ LIST_REL _ pes compiled_tail’
      (qspec_then ‘target’ match_mp_tac)
    >> simp [] >> qx_gen_tac ‘id’ >> strip_tac
    >> qpat_assum ‘∀id. _ ⇒ nsLookup target.v id = _’ (qspec_then ‘id’ match_mp_tac)
    >> qx_gen_tac ‘name’ >> strip_tac
    >> qpat_assum ‘∀name. id = Short name ⇒ name ∈ exp_free_names_pes compiled_tail’
      (qspec_then ‘name’ mp_tac)
    >> simp [exp_free_names_def])
  >> qx_genl_tac [‘source_state’,‘target_state’,‘bindings’,‘bindings'’] >> strip_tac
  >> drule LIST_REL_MAP_FST >> disch_tac
  >> ‘MAP FST bindings' = pat_bindings pattern’ by metis_tac []
  >> qpat_assum ‘∀bindings bindings'. _ ⇒ lift_scope _ _ _ _ _ _ _ _ ∧ _’
    (qspecl_then [‘bindings’,‘bindings'’] mp_tac)
  >> simp [] >> strip_tac
  >> mp_tac (Q.INST [‘R’ |-> ‘lift_runtime_rel’,‘captures’ |-> ‘body_captures’,
       ‘bound’ |-> ‘bind_all (pat_bindings pattern) bound’,
       ‘ren’ |-> ‘delete_all (pat_bindings pattern) ren’,
       ‘n’ |-> ‘middle_n’,‘ds’ |-> ‘middle_ds’,‘used’ |-> ‘middle_used’,
       ‘source’ |-> ‘source with v := nsBindList bindings source.v’,
       ‘initial’ |-> ‘head_final’,‘locals’ |-> ‘bindings' ++ locals’,
       ‘e’ |-> ‘compiled_body’] (SPEC_ALL lift_scope_compiled_lookup))
  >> simp [] >> disch_tac
  >> have ‘∀id. (∀name. id = Short name ⇒ name ∈ exp_free_names compiled_body) ⇒
       nsLookup (nsBindList bindings' target.v) id =
       nsLookup (nsBindList (bindings' ++ locals) final.v) id’
  >- (
    once_rewrite_tac [nsBindList_append]
    >> match_mp_tac (Q.INST [‘names’ |-> ‘pat_bindings pattern’]
         (INST_TYPE [“:'a” |-> “:v”] lift_bound_lookup))
    >> simp [] >> qx_gen_tac ‘id’ >> strip_tac
    >> qpat_assum ‘∀id. _ ⇒ nsLookup target.v id = _’ (qspec_then ‘id’ match_mp_tac)
    >> qx_gen_tac ‘name’ >> strip_tac >> qpat_assum ‘∀name. id = Short name ⇒ _’
      (qspec_then ‘name’ mp_tac)
    >> simp [exp_free_names_def])
  >> qpat_assum ‘∀s s' target'. _ ⇒ lift_eval_refinement _ _ _
       (evaluate s (source with v := nsBindList bindings source.v) [body]) _’
    (qspecl_then [‘source_state’,‘target_state’,
       ‘target with v := nsBindList bindings' target.v’] match_mp_tac)
  >> simp [] >> qx_gen_tac ‘id’ >> strip_tac
  >> qpat_assum ‘∀id. _ ⇒ nsLookup (nsBindList bindings' target.v) id = _’
    (qspec_then ‘id’ mp_tac)
  >> qpat_assum ‘∀id. _ ⇒ nsLookup (nsBindList (bindings' ++ locals) final.v) id = _’
    (qspec_then ‘id’ mp_tac)
  >> simp []
QED

Theorem lift_sim_head[local]:
  lift_exp_sim (:'ffi) clock D e ∧ annotate_exp [] e = (t1,l1,c1) ∧
  source_dce$no_Open e ∧ check_exp_constructors base.c e ∧ l1 ≤ n ∧
  lift_state_fresh (n,ds,used) ∧ lift_global_decs (REVERSE ds) base initial ∧
  (∀name renamed. FLOOKUP ren name = SOME renamed ∧ renamed ≠ name ⇒
    renamed ∉ exp_names e) ∧
  lift_exp mode bound ren (n,ds,used) t1 = (r1,n2,ds2,u2) ⇒
  ∃final.
    lift_global_decs (REVERSE ds2) base final ∧ lift_state_fresh (n2,ds2,u2) ∧ n ≤ n2 ∧
    ∀c2 source locals.
      lift_scope lift_runtime_rel (FUNION c1 c2) bound ren (n,ds,used) source initial
        locals ⇒
      lift_scope lift_runtime_rel c2 bound ren (n2,ds2,u2) source final locals ∧
      ∀n1 ds1 used1 final2.
        lift_state_extends (n2,ds2,u2) (n1,ds1,used1) ∧
        lift_state_decs_avoid (n2,ds2,u2) (n1,ds1,used1) ∧
        lift_global_decs (REVERSE ds1) base final2 ⇒
        lift_scope lift_runtime_rel (FUNION c1 c2) bound ren (n1,ds1,used1) source final2
          locals ∧
        ∀target.
          target.c = final2.c ∧
          (∀id. (∀name. id = Short name ⇒ name ∈ exp_free_names r1) ⇒
            nsLookup target.v id = nsLookup (nsBindList locals final2.v) id) ⇒
          ∀(s:'ffi semanticPrimitives$state) s'.
            s.clock ≤ clock ∧ lift_state_rel lift_runtime_rel D s s' ⇒
            lift_eval_refinement lift_runtime_rel D (LIST_REL lift_runtime_rel)
              (evaluate s source [e]) (evaluate s' target [r1])
Proof
  strip_tac
  >> drule_all lift_annotated_state_properties_lift >> strip_tac
  >> drule_all lift_exp_sim_lift >> disch_then (qx_choose_then ‘final’ strip_assume_tac)
  >> ‘n ≤ n2’ by fs [lift_state_extends_def]
  >> qexists_tac ‘final’ >> asm_rewrite_tac [] >> qx_genl_tac [‘c2’,‘source’,‘locals’] >> strip_tac
  >> have ‘lift_scope lift_runtime_rel c1 bound ren (n,ds,used) source initial locals’
  >- (
    irule lift_scope_domain_subset >> qexists_tac ‘FUNION c1 c2’ >> simp [FDOM_FUNION])
  >> first_x_assum drule >> strip_tac
  >> qpat_assum ‘lift_scope _ (FUNION c1 c2) _ _ (n,ds,used) _ initial _’
       (mp_then (Pos hd) drule_all lift_scope_decs_avoid)
  >> disch_tac >> conj_tac
  >- (
    irule lift_scope_domain_subset >> qexists_tac ‘FUNION c1 c2’
    >> simp [FDOM_FUNION,SUBSET_DEF])
  >> rpt gen_tac >> strip_tac
  >> qpat_assum ‘lift_scope _ (FUNION c1 c2) _ _ (n2,ds2,u2) _ final _’
       (mp_then (Pos hd) drule_all lift_scope_decs_avoid)
  >> disch_tac
  >> qpat_assum ‘lift_scope _ c1 _ _ (n2,ds2,u2) _ final _’
       (mp_then (Pos hd) (qspecl_then [‘used1’,‘n1’,‘final2’,‘r1’,‘ds1’,‘base’] mp_tac)
         lift_scope_compiled_lookup)
  >> simp [] >> strip_tac >> imp_res_tac lift_global_decs_constructors
  >> rw [] >> qpat_x_assum ‘∀s s' target. _’ irule >> rw []
QED

Theorem lift_exps_sim[local]:
  ∀es trees limit captures mode bound ren n ds used compiled n1 ds1 used1 base initial.
    (∀e. MEM e es ⇒ lift_exp_sim (:'ffi) clock D e) ∧
    annotate_exps [] es = (trees,limit,captures) ∧ EVERY source_dce$no_Open es ∧
    EVERY (check_exp_constructors base.c) es ∧
    limit ≤ n ∧ lift_state_fresh (n,ds,used) ∧ lift_global_decs (REVERSE ds) base initial ∧
    (∀name renamed. FLOOKUP ren name = SOME renamed ∧ renamed ≠ name ⇒
      ∀original. original ∈ exp_names_exps es ⇒ renamed ≠ original) ∧
    lift_exps mode bound ren (n,ds,used) trees = (compiled,n1,ds1,used1) ⇒
    ∃final.
      lift_global_decs (REVERSE ds1) base final ∧
      ∀source locals.
        lift_scope lift_runtime_rel captures bound ren (n,ds,used) source initial locals ⇒
        lift_scope lift_runtime_rel captures bound ren (n1,ds1,used1) source final locals ∧
        ∀target.
          target.c = final.c ∧
          (∀id. (∀name. id = Short name ⇒ name ∈ exp_free_names_exps compiled) ⇒
            nsLookup target.v id = nsLookup (nsBindList locals final.v) id) ⇒
          LIST_REL (λe c. ∀(s:'ffi semanticPrimitives$state) s'.
            s.clock ≤ clock ∧ lift_state_rel lift_runtime_rel D s s' ⇒
            lift_eval_refinement lift_runtime_rel D (LIST_REL lift_runtime_rel)
              (evaluate s source [e]) (evaluate s' target [c])) es compiled
Proof
  Induct
  >- (rw [annotate_exp_def] >> gvs [Once lift_exp_def] >> metis_tac [])
  >> rpt gen_tac >> strip_tac >> namedCases_on ‘annotate_exp [] h’ ["t1 l1 c1"]
  >> namedCases_on ‘annotate_exps [] es’ ["t2 l2 c2"]
  >> drule_all annotate_exps_CONS >> strip_tac >> gvs [map_eq_def]
  >> namedCases_on ‘lift_exp mode bound ren (n,ds,used) t1’ ["r1 n2 ds2 u2"]
  >> namedCases_on ‘lift_exps mode bound ren (n2,ds2,u2) t2’ ["rs n3 ds3 u3"]
  >> qpat_x_assum ‘∀e. _ ⇒ lift_exp_sim _ _ _ e’
       (strip_assume_tac o SRULE [DISJ_IMP_THM,FORALL_AND_THM])
  >> qpat_x_assum ‘∀name renamed. _’
       (strip_assume_tac o SRULE [exp_names_def,DISJ_IMP_THM,FORALL_AND_THM,IMP_CONJ_THM])
  >> gvs [Once lift_exp_def]
  >> drule_all lift_sim_head >> strip_tac >> ‘l2 ≤ n2’ by decide_tac
  >> last_x_assum drule_all >> disch_then (qx_choose_then ‘final2’ strip_assume_tac)
  >> drule_all (cj 2 annotate_tree_names_bounded) >> strip_tac
  >> ‘l2 ≤ FST (n2,ds2,u2)’ by simp [] >> drule_all (cj 3 lift_exp_fresh) >> strip_tac
  >> imp_res_tac (cj 3 lift_exp_state_extends)
  >> qexists_tac ‘final2’ >> simp [] >> qx_genl_tac [‘source’,‘locals’] >> strip_tac
  >> qpat_x_assum ‘∀c2 source locals. _’ drule >> strip_tac
  >> qpat_x_assum ‘∀source locals. lift_scope _ c2 _ _ _ _ _ _ ⇒ _’ drule >> strip_tac
  >> qpat_x_assum ‘∀n1 ds1 used1 final2. _’ drule_all >> rw []
  >- (
    qpat_x_assum ‘∀target. _ ⇒ ∀s s'. _’ irule >> rw []
    >> first_x_assum irule >> Cases_on ‘id’ >> rw [exp_free_names_def])
  >> qpat_x_assum ‘∀target. _ ⇒ LIST_REL _ es rs’ irule >> rw []
  >> first_x_assum irule >> gvs [exp_free_names_def]
QED

Theorem lift_exp_pes_sim[local]:
  ∀clock D e pes t1 l1 c1 bs l2 c2 n ds used initial base
    mode bound ren r1 n2 ds2 u2 rs n1 ds1 used1.
  lift_exp_sim (:'ffi) clock D e ∧
  (∀p x. MEM (p,x) pes ⇒ lift_exp_sim (:'ffi) clock D x) ∧
  annotate_exp [] e = (t1,l1,c1) ∧ annotate_pes [] pes = (bs,l2,c2) ∧
  source_dce$no_Open e ∧ check_exp_constructors base.c e ∧
  EVERY (λ(p,x). source_dce$no_Open x ∧ check_exp_constructors base.c x) pes ∧
  l1 ≤ n ∧ l2 ≤ n ∧ lift_state_fresh (n,ds,used) ∧
  lift_global_decs (REVERSE ds) base initial ∧
  (∀name renamed. FLOOKUP ren name = SOME renamed ∧ renamed ≠ name ⇒
    renamed ∉ exp_names e ∧ renamed ∉ exp_names_pes pes) ∧
  lift_exp mode bound ren (n,ds,used) t1 = (r1,n2,ds2,u2) ∧
  lift_pes mode bound ren (n2,ds2,u2) (MAP FST pes) bs = (rs,n1,ds1,used1) ⇒
  ∃final.
    lift_global_decs (REVERSE ds1) base final ∧
    ∀source locals.
      lift_scope lift_runtime_rel (FUNION c1 c2) bound ren (n,ds,used) source initial
        locals ⇒
      lift_scope lift_runtime_rel (FUNION c1 c2) bound ren (n1,ds1,used1) source final
        locals ∧
      ∀target.
        target.c = final.c ∧
        (∀id. (∀name. id = Short name ⇒
            name ∈ exp_free_names r1 ∨ name ∈ exp_free_names_pes rs) ⇒
          nsLookup target.v id = nsLookup (nsBindList locals final.v) id) ⇒
        (∀(s:'ffi semanticPrimitives$state) s'.
          s.clock ≤ clock ∧ lift_state_rel lift_runtime_rel D s s' ⇒
          lift_eval_refinement lift_runtime_rel D (LIST_REL lift_runtime_rel)
            (evaluate s source [e]) (evaluate s' target [r1])) ∧
        LIST_REL (λ(pattern,body) (pattern',body'). pattern = pattern' ∧
          ∀(state:'ffi semanticPrimitives$state) state' bindings bindings'.
            state.clock ≤ clock ∧ lift_state_rel lift_runtime_rel D state state' ∧
            MAP FST bindings = pat_bindings pattern ∧
            LIST_REL (λ(x,v) (y,w). x = y ∧ lift_runtime_rel v w) bindings bindings' ⇒
            lift_eval_refinement lift_runtime_rel D (LIST_REL lift_runtime_rel)
              (evaluate state (source with v := nsBindList bindings source.v) [body])
              (evaluate state' (target with v := nsBindList bindings' target.v) [body']))
          pes rs
Proof
  rpt strip_tac
  >> qpat_x_assum ‘∀name renamed. _’
       (strip_assume_tac o SRULE [IMP_CONJ_THM,FORALL_AND_THM])
  >> drule_all lift_sim_head >> strip_tac >> ‘l2 ≤ n2’ by decide_tac
  >> qpat_assum ‘∀p x. MEM (p,x) pes ⇒ _’ (mp_tac o MATCH_MP lift_pes_simulation)
  >> disch_then (qspecl_then [‘bs’,‘l2’,‘c2’,‘mode’,‘bound’,‘ren’,‘n2’,‘ds2’,‘u2’,
       ‘rs’,‘n1’,‘ds1’,‘used1’,‘base’,‘final’] mp_tac)
  >> impl_tac >- (simp [] >> metis_tac [])
  >> disch_then (qx_choose_then ‘final2’ strip_assume_tac)
  >> have ‘EVERY (tree_names_bounded l2) bs’
  >- (
    irule (cj 3 annotate_tree_names_bounded) >> fs [EVERY_MEM,FORALL_PROD]
    >> metis_tac [])
  >> ‘l2 ≤ FST (n2,ds2,u2)’ by simp [] >> drule_all (cj 4 lift_exp_fresh) >> strip_tac
  >> imp_res_tac (cj 4 lift_exp_state_extends)
  >> qexists_tac ‘final2’ >> simp [] >> qx_genl_tac [‘source’,‘locals’] >> strip_tac
  >> qpat_x_assum ‘∀c2 source locals. _’ drule >> strip_tac
  >> qpat_x_assum ‘∀source locals. lift_scope _ c2 _ _ _ _ _ _ ⇒ _’ drule >> strip_tac
  >> qpat_x_assum ‘∀n1 ds1 used1 final2. _’ drule_all >> rw []
  >> qpat_x_assum ‘∀target. _ ⇒ ∀s s'. _’ irule >> rw []
QED

Theorem lift_exps_simulation[local]:
  (∀e. MEM e es ⇒ lift_exp_sim (:'ffi) clock D e) ⇒
  ∀trees limit captures mode bound ren n ds used compiled n1 ds1 used1 base initial.
    annotate_exps [] es = (trees,limit,captures) ∧ EVERY source_dce$no_Open es ∧
    EVERY (check_exp_constructors base.c) es ∧
    limit ≤ n ∧ lift_state_fresh (n,ds,used) ∧ lift_global_decs (REVERSE ds) base initial ∧
    (∀name renamed. FLOOKUP ren name = SOME renamed ∧ renamed ≠ name ⇒
      ∀original. original ∈ exp_names_exps es ⇒ renamed ≠ original) ∧
    lift_exps mode bound ren (n,ds,used) trees = (compiled,n1,ds1,used1) ⇒
    ∃final.
      lift_global_decs (REVERSE ds1) base final ∧
      ∀source locals.
        lift_scope lift_runtime_rel captures bound ren (n,ds,used) source initial locals ⇒
        lift_scope lift_runtime_rel captures bound ren (n1,ds1,used1) source final locals ∧
        ∀(s:'ffi semanticPrimitives$state) s' target.
          s.clock ≤ clock ∧ lift_state_rel lift_runtime_rel D s s' ∧
          target.c = final.c ∧
          (∀id. (∀name. id = Short name ⇒ name ∈ exp_free_names_exps compiled) ⇒
            nsLookup target.v id = nsLookup (nsBindList locals final.v) id) ⇒
          lift_eval_refinement lift_runtime_rel D (LIST_REL lift_runtime_rel)
            (evaluate s source (REVERSE es)) (evaluate s' target (REVERSE compiled))
Proof
  rpt strip_tac
  >> drule_all lift_exps_sim >> strip_tac >> qexists_tac ‘final’ >> asm_rewrite_tac []
  >> qx_genl_tac [‘source’,‘locals’] >> strip_tac >> first_x_assum drule >> rw []
  >> irule lift_evaluate_list_refinement >> simp [LIST_REL_REVERSE_EQ]
  >> qexists_tac ‘clock’ >> simp [] >> first_x_assum irule >> simp []
QED

Theorem lower_exp_exps[local]:
  (lower_exp mode bound ren st (Lift (If e1 e2 e3) fvs v [a;b;c]) = (r,st') ⇒
    ∃x y z. lift_exps mode bound ren st [a;b;c] = ([x;y;z],st') ∧ r = If x y z) ∧
  (lower_exp mode bound ren st (Lift (Log lop e1 e2) fvs v [a;b]) = (r,st') ⇒
    ∃x y. lift_exps mode bound ren st [a;b] = ([x;y],st') ∧ r = Log lop x y) ∧
  (lower_exp mode bound ren st (Lift (Let NONE e1 e2) fvs v [a;b]) = (r,st') ⇒
    ∃x y. lift_exps mode bound ren st [a;b] = ([x;y],st') ∧ r = Let NONE x y) ∧
  (lower_exp mode bound ren st (Lift (Raise e1) fvs v [a]) = (r,st') ⇒
    ∃x. lift_exps mode bound ren st [a] = ([x],st') ∧ r = Raise x)
Proof
  simp [cj 7 lift_exp_def,cj 8 lift_exp_def,cj 10 lift_exp_def,cj 11 lift_exp_def,
        cj 36 lift_exp_def,cj 37 lift_exp_def]
  >> rpt (pairarg_tac >> gvs [])
QED

Theorem lift_emit_value_sim[local]:
  lift_state_fresh (n,ds,used) ∧ lift_global_decs (REVERSE ds) base env ∧
  lift_pure_value env e v ∧ check_exp_constructors env.c e ∧
  emit_value e (n,ds,used) = (compiled,n1,ds1,used1) ⇒
  ∃final.
    lift_global_decs (REVERSE ds1) base final ∧
    ∀R captures bound ren source locals.
      lift_scope R captures bound ren (n,ds,used) source env locals ⇒
      lift_scope R captures bound ren (n1,ds1,used1) source final locals ∧
      ∀target.
        (∀id. (∀name. id = Short name ⇒ name ∈ exp_free_names compiled) ⇒
          nsLookup target.v id = nsLookup (nsBindList locals final.v) id) ⇒
        ∀s:'ffi semanticPrimitives$state. evaluate s target [compiled] = (s,Rval [v])
Proof
  strip_tac
  >> imp_res_tac emit_value_extends >> drule_all emit_value_decs_avoid >> disch_tac
  >> drule_all emit_value_global_decs >> disch_tac
  >> qexists_tac ‘env with v := nsBind (make_name n) v env.v’ >> simp []
  >> rpt gen_tac >> strip_tac >> drule_all lift_scope_decs_avoid >> disch_tac
  >> ‘ALOOKUP locals (make_name n) = NONE’ by fs [lift_scope_def]
  >> gvs [emit_value_def] >> rpt strip_tac
  >> qpat_x_assum ‘∀id. _ ⇒ nsLookup target.v id = _’
       (qspec_then ‘Short (make_name n)’ mp_tac)
  >> simp [exp_free_names_def,nsBindList_short_lookup,cj 7 evaluate_def]
QED

Theorem lift_exp_sim_letrec[local]:
  (∀f x e. MEM (f,x,e) funs ⇒ lift_exp_sim (:'ffi) clock D e) ∧
  lift_exp_sim (:'ffi) clock D body ⇒
  lift_exp_sim (:'ffi) clock D (Letrec funs body)
Proof
  strip_tac >> rewrite_tac [lift_exp_sim_def]
  >> qx_genl_tac [‘tree’,‘limit’,‘captures’,‘mode’,‘bound’,‘ren’,‘n’,‘ds’,‘used’,
       ‘compiled’,‘out_n’,‘out_ds’,‘out_used’,‘base’,‘initial’]
  >> disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th))
  >> qpat_x_assum ‘annotate_exp [] (Letrec funs body) = _’
    (mp_tac o SRULE [Once annotate_exp_def])
  >> namedCases_on ‘annotate_funs [] funs’ ["function_trees function_limit function_captures"]
  >> namedCases_on ‘annotate_exp [] body’ ["body_tree body_limit body_captures"]
  >> strip_tac >> qpat_x_assum ‘lower_exp _ _ _ _ _ = _ ∨ lift_exp _ _ _ _ _ = _’ mp_tac
  >> gvs [cj 1 lift_exp_def] >> strip_tac >> fs [cj 1 lift_exp_def,cj 4 lift_exp_def]
  >> gvs [exp_names_def,no_Open_thm,check_exp_constructors_def]
  >> ‘MAX function_limit body_limit ≤ n’ by metis_tac [bump_all_le,LESS_EQ_TRANS]
  >> ‘function_limit ≤ n ∧ body_limit ≤ n’ by fs []
  >> have ‘EVERY (λname. bump name 0 ≤ n) (MAP FST funs)’
  >- (
    rw [EVERY_MEM]
    >> metis_tac [cj 4 annotate_all_name_bound,recursive_names_all_names,LESS_EQ_TRANS])
  >> Cases_on ‘mode ≠ KeepValue ∧
       maps_disjoint (delete_all (MAP FST funs) function_captures) bound’
  >- (
    qpat_assum ‘mode ≠ KeepValue ∧ _’
      (fn hoisted => fs [hoisted] >> MAP_EVERY assume_tac (CONJUNCTS hoisted))
    >> namedCases_on ‘choose_names bound (MAP FST funs) (n,ds,used)’
      ["compiled_names chosen_n chosen_ds chosen_used"]
    >> gvs [] >> qabbrev_tac ‘group_ren = ren |++ ZIP (MAP FST funs,compiled_names)’
    >> namedCases_on ‘lift_funs (bind_all (MAP FST funs) (delete_all (MAP FST funs) bound))
         group_ren (chosen_n,chosen_ds,chosen_used)
         (ZIP (compiled_names,MAP (FST o SND) funs)) function_trees’
      ["compiled_funs function_n function_ds function_used"]
    >> gvs [Abbr ‘group_ren’]
    >> namedCases_on ‘emit_dec (Dletrec NoLocs compiled_funs)
         (function_n,function_ds,function_used)’ ["emitted_n emitted_ds emitted_used"]
    >> gvs [] >> drule_all choose_names_fresh >> strip_tac
    >> have ‘∀name. name ∈ exp_names_funs funs ∪ exp_names body ⇒ bump name 0 ≤ n’
    >- (
      rw [IN_UNION]
      >> metis_tac [cj 1 annotate_all_name_bound,cj 4 annotate_all_name_bound,LESS_EQ_TRANS])
    >> have ‘∀original mapped. FLOOKUP ren original = SOME mapped ∧ mapped ≠ original ⇒
         mapped ∉ exp_names_funs funs ∪ exp_names body’
    >- (simp_tac (srw_ss()) [IN_UNION] >> metis_tac [])
    >> have ‘∀original mapped.
         FLOOKUP (ren |++ ZIP (MAP FST funs,compiled_names)) original = SOME mapped ∧
         mapped ≠ original ⇒ mapped ∉ exp_names_funs funs ∪ exp_names body’
    >- (
      match_mp_tac (Q.INST [‘names’ |-> ‘MAP FST (funs:(mlstring # mlstring # exp) list)’,
        ‘n1’ |-> ‘chosen_n’,‘ds1’ |-> ‘chosen_ds’,‘used1’ |-> ‘chosen_used’]
        choose_names_renaming_hygiene)
      >> asm_rewrite_tac [])
    >> ‘function_limit ≤ chosen_n’ by decide_tac
    >> ‘lift_global_decs (REVERSE chosen_ds) base initial’ by gvs []
    >> ‘MAP SND (ZIP (compiled_names,MAP (FST o SND) funs)) = MAP (FST o SND) funs’
      by simp [MAP_ZIP]
    >> ‘EVERY (λ(f,x,e). source_dce$no_Open e ∧ check_exp_constructors base.c e) funs’
      by (fs [EVERY_MEM,FORALL_PROD] >> metis_tac [])
    >> ‘∀name renamed. FLOOKUP (ren |++ ZIP (MAP FST funs,compiled_names)) name = SOME renamed ∧
          renamed ≠ name ⇒ renamed ∉ exp_names_funs funs’ by metis_tac [IN_UNION]
    >> drule_all lift_funs_global_decs >> disch_then (qx_choose_then ‘function_env’ assume_tac)
    >> drule (cj 3 annotate_LENGTH) >> disch_tac
    >> have ‘MAP FST compiled_funs = compiled_names’
    >- (drule lift_funs_names_prefix >> simp [MAP_ZIP,TAKE_LENGTH_TOO_LONG])
    >> ‘ALL_DISTINCT (MAP FST compiled_funs)’ by fs []
    >> drule_all (cj 4 annotate_constructors) >> disch_tac
    >> drule_all (cj 5 lift_exp_constructors) >> disch_tac
    >> qpat_assum ‘lift_global_decs _ base function_env’
      (assume_tac o MATCH_MP lift_global_decs_constructors)
    >> ‘EVERY (λ(f,x,e). check_exp_constructors function_env.c e) compiled_funs’ by gvs []
    >> drule_all emit_rec_global_decs >> disch_tac
    >> qpat_assum ‘EVERY (λ(f,x,e). source_dce$no_Open e) funs’
      (assume_tac o SRULE [ELIM_UNCURRY])
    >> drule_all (SRULE [ELIM_UNCURRY] (cj 4 annotate_tree_names_bounded)) >> disch_tac
    >> ‘function_limit ≤ FST (chosen_n,chosen_ds,chosen_used)’ by simp []
    >> drule_all (cj 5 lift_exp_fresh) >> strip_tac
    >> drule (cj 5 lift_exp_state_extends) >> disch_tac
    >> ‘lift_state_fresh (emitted_n,emitted_ds,emitted_used)’
      by metis_tac [emit_dec_state_fresh]
    >> ‘lift_state_extends (function_n,function_ds,function_used)
          (emitted_n,emitted_ds,emitted_used)’ by metis_tac [emit_dec_extends]
    >> ‘chosen_n ≤ function_n ∧ function_n ≤ emitted_n’ by fs [lift_state_extends_def]
    >> ‘body_limit ≤ emitted_n’ by decide_tac
    >> have ‘lift_state_decs_avoid (n,ds,used) (chosen_n,chosen_ds,chosen_used)’
    >- (irule lift_state_decs_avoid_same_decs >> simp [])
    >> drule choose_names_extends >> disch_tac
    >> have ‘lift_state_decs_avoid (n,ds,used) (function_n,function_ds,function_used)’
    >- (
      irule lift_state_decs_avoid_trans >> qexists_tac ‘(chosen_n,chosen_ds,chosen_used)’
      >> simp [])
    >> have ‘lift_decs_avoid (FDOM used) [Dletrec NoLocs compiled_funs]’
    >- (
      qpat_assum ‘MAP FST compiled_funs = compiled_names’ mp_tac
      >> qpat_assum ‘∀y. MEM y compiled_names ⇒ FLOOKUP used y = NONE’ mp_tac
      >> POP_ASSUM_LIST (K ALL_TAC)
      >> rw [lift_decs_avoid_list_cases,DISJOINT_ALT,flookup_thm]
      >> metis_tac [])
    >> have ‘lift_state_decs_avoid (n,ds,used) (emitted_n,emitted_ds,emitted_used)’
    >- (
      qpat_assum ‘emit_dec (Dletrec NoLocs compiled_funs) _ = _’
        (fn emit => rewrite_tac [GSYM emit])
      >> irule emit_dec_decs_avoid >> simp_tac (srw_ss()) [] >> asm_rewrite_tac [])
    >> have ‘lift_state_extends (n,ds,used) (function_n,function_ds,function_used)’
    >- (
      irule lift_state_extends_trans >> qexists_tac ‘(chosen_n,chosen_ds,chosen_used)’
      >> simp [])
    >> have ‘lift_state_extends (n,ds,used) (emitted_n,emitted_ds,emitted_used)’
    >- (
      irule lift_state_extends_trans >> qexists_tac ‘(function_n,function_ds,function_used)’
      >> simp [])
    >> qabbrev_tac ‘compiled_bindings =
         MAP (λname. (name,Recclosure function_env compiled_funs name)) compiled_names’
    >> have ‘nsBindList compiled_bindings function_env.v =
         build_rec_env compiled_funs function_env function_env.v’
    >- simp [Abbr ‘compiled_bindings’,build_rec_env_nsBindList_names]
    >> have ‘lift_global_decs (REVERSE emitted_ds) base
         (function_env with v := nsBindList compiled_bindings function_env.v)’
    >- (
      qpat_assum ‘nsBindList compiled_bindings function_env.v = _’ (rewrite_tac o single)
      >> first_assum ACCEPT_TAC)
    >> have ‘∀original mapped.
         FLOOKUP (ren |++ ZIP (MAP FST funs,compiled_names)) original = SOME mapped ∧
         mapped ≠ original ⇒ mapped ∉ exp_names body’
    >- (
      rpt strip_tac
      >> qpat_x_assum ‘∀original mapped. FLOOKUP (ren |++ _) original = _ ∧ _ ⇒ _ ∉ _ ∪ _’
        drule_all
      >> simp [])
    >> drule_all lift_exp_sim_lift >> disch_then (qx_choose_then ‘final’ strip_assume_tac)
    >> drule_all lift_annotated_state_properties_lift >> strip_tac
    >> qexists_tac ‘final’ >> asm_rewrite_tac [] >> qx_genl_tac [‘source’,‘locals’] >> strip_tac
    >> qpat_assum ‘lift_scope _ _ _ _ (n,ds,used) source initial locals’
      (assume_tac o CONJUNCT1 o REWRITE_RULE [lift_scope_def])
    >> drule_all choose_names_renaming_wf >> disch_tac
    >> have ‘FDOM used ⊆ FDOM chosen_used ∧ set (MAP FST funs) ⊆ FDOM chosen_used ∧
         set compiled_names ⊆ FDOM chosen_used’
    >- (
      qpat_assum ‘FDOM chosen_used = _’
        (fn domain => simp_tac (srw_ss()) [domain,SUBSET_DEF]))
    >> ‘DISJOINT (FDOM (delete_all (MAP FST funs) (FUNION body_captures function_captures)))
         (set (MAP FST funs))’ by simp_tac (srw_ss()) [delete_all_domain,DISJOINT_ALT]
    >> drule_all lift_scope_discard_reserved_bindings >> disch_tac
    >> have ‘MAP FST (ZIP (MAP FST funs,compiled_names)) = MAP FST funs’
    >- (
      qpat_assum ‘LENGTH compiled_names = LENGTH (MAP FST funs)’
        (fn lengths => simp_tac (srw_ss()) [MAP_ZIP,GSYM lengths]))
    >> have ‘∀name. ¬MEM name (MAP FST funs) ⇒
         rename_var (ren |++ ZIP (MAP FST funs,compiled_names)) (Short name) =
           (rename_var ren (Short name):(mlstring,mlstring) id)’
    >- (
      qpat_assum ‘MAP FST (ZIP (MAP FST funs,compiled_names)) = MAP FST funs’
        (fn names => simp_tac (srw_ss()) [rename_var_updates_other,names]))
    >> have ‘∀name. name ∈ FDOM (delete_all (MAP FST funs)
           (FUNION body_captures function_captures)) ∨
         name ∈ FDOM (delete_all (MAP FST funs) bound) ⇒
         rename_var (ren |++ ZIP (MAP FST funs,compiled_names)) (Short name) =
           (rename_var ren (Short name):(mlstring,mlstring) id)’
    >- (
      qpat_assum ‘∀name. ¬MEM name (MAP FST funs) ⇒ rename_var _ _ = _’ mp_tac
      >> POP_ASSUM_LIST (K ALL_TAC) >> simp_tac (srw_ss()) [delete_all_domain]
      >> metis_tac [])
    >> qpat_x_assum ‘∀chosen_ds. lift_scope _ _ _ _ (chosen_n,chosen_ds,chosen_used)
         source initial locals’ (qspec_then ‘chosen_ds’ assume_tac)
    >> drule_all lift_scope_renaming_cong >> disch_tac
    >> have ‘lift_scope lift_runtime_rel (delete_all (MAP FST funs) function_captures)
         (delete_all (MAP FST funs) bound) (ren |++ ZIP (MAP FST funs,compiled_names))
         (chosen_n,chosen_ds,chosen_used) source initial locals’
    >- (
      irule lift_scope_domain_subset
      >> qexists_tac ‘delete_all (MAP FST funs) (FUNION body_captures function_captures)’
      >> simp_tac (srw_ss()) [delete_all_domain,FDOM_FUNION,SUBSET_DEF]
      >> first_assum ACCEPT_TAC)
    >> have ‘maps_disjoint (delete_all (MAP FST funs) function_captures)
         (delete_all (MAP FST funs) bound)’
    >- (
      qpat_assum ‘maps_disjoint _ bound’ mp_tac
      >> POP_ASSUM_LIST (K ALL_TAC)
      >> simp_tac (srw_ss()) [maps_disjoint_domains,delete_all_domain,DISJOINT_ALT]
      >> metis_tac [])
    >> drule_all lift_scope_closed >> disch_tac
    >> have ‘∀name mapped. name ∈ FDOM function_captures ∧
         rename_var (ren |++ ZIP (MAP FST funs,compiled_names)) (Short name) =
           (Short mapped:(mlstring,mlstring) id) ⇒
         (MEM name (MAP FST funs) ⇔ MEM mapped compiled_names)’
    >- (
      match_mp_tac (Q.INST [‘n1’ |-> ‘chosen_n’,‘ds1’ |-> ‘chosen_ds’,‘used1’ |-> ‘chosen_used’]
        choose_names_capture_membership)
      >> asm_rewrite_tac [] >> metis_tac [cj 4 annotate_free_name_bound,LESS_EQ_TRANS])
    >> have ‘∀name k. MEM name compiled_names ∧ chosen_n ≤ k ⇒ name ≠ make_name k’
    >- (
      qpat_assum ‘lift_state_fresh (chosen_n,chosen_ds,chosen_used)’ mp_tac
      >> qpat_assum ‘set compiled_names ⊆ FDOM chosen_used’ mp_tac
      >> POP_ASSUM_LIST (K ALL_TAC) >> metis_tac [lift_state_fresh_used,SUBSET_DEF])
    >> drule_all (Q.INST [‘captures’ |->
         ‘delete_all (MAP FST (funs:(mlstring # mlstring # exp) list))
           (FUNION body_captures function_captures)’,
         ‘final’ |->
           ‘function_env with v := build_rec_env compiled_funs function_env function_env.v’,
         ‘n1’ |-> ‘emitted_n’,‘ds1’ |-> ‘emitted_ds’,‘used1’ |-> ‘emitted_used’]
         (SPEC_ALL lift_scope_decs_avoid))
    >> disch_tac
    >> have ‘lift_scope lift_runtime_rel
         (delete_all (MAP FST funs) (FUNION body_captures function_captures)) bound ren
         (function_n,function_ds,function_used) source function_env locals’
    >- (
      irule lift_scope_decs_avoid
      >> qexistsl_tac [‘base’,‘ds’,‘initial’,‘n’,‘used’] >> asm_rewrite_tac [])
    >> have ‘FDOM chosen_used ⊆ FDOM function_used’
    >- (
      qpat_assum ‘lift_state_extends (chosen_n,chosen_ds,chosen_used)
           (function_n,function_ds,function_used)’ mp_tac
      >> POP_ASSUM_LIST (K ALL_TAC)
      >> simp [lift_state_extends_def])
    >> have ‘lift_scope lift_runtime_rel
         (delete_all (MAP FST funs) (FUNION body_captures function_captures))
         (delete_all (MAP FST funs) bound) ren
         (function_n,function_ds,function_used) source function_env locals’
    >- (
      irule lift_scope_discard_reserved_bindings >> conj_tac
      >- first_assum ACCEPT_TAC >> conj_tac
      >- metis_tac [SUBSET_TRANS]
      >> qexistsl_tac [‘function_ds’,‘function_n’,‘function_used’]
      >> simp_tac (srw_ss()) []
      >> first_assum ACCEPT_TAC)
    >> have ‘lift_renaming_wf (ren |++ ZIP (MAP FST funs,compiled_names)) function_used’
    >- (
      irule lift_renaming_wf_used_subset
      >> qexists_tac ‘chosen_used’ >> asm_rewrite_tac [])
    >> have ‘lift_scope lift_runtime_rel
         (delete_all (MAP FST funs) (FUNION body_captures function_captures))
         (delete_all (MAP FST funs) bound) (ren |++ ZIP (MAP FST funs,compiled_names))
         (function_n,function_ds,function_used) source function_env locals’
    >- (
      irule lift_scope_renaming_cong >> conj_tac
      >- first_assum ACCEPT_TAC
      >> qexists_tac ‘ren’ >> asm_rewrite_tac [])
    >> have ‘lift_scope lift_runtime_rel
         (delete_all (MAP FST funs) (FUNION body_captures function_captures))
         (delete_all (MAP FST funs) bound) (ren |++ ZIP (MAP FST funs,compiled_names))
         (emitted_n,emitted_ds,emitted_used) source function_env locals’
    >- (
      irule lift_scope_emit_dec
      >> qexistsl_tac [‘Dletrec NoLocs compiled_funs’,‘(function_n,function_ds,function_used)’]
      >> asm_rewrite_tac [])
    >> have ‘∀mapped. MEM mapped compiled_names ⇒ ALOOKUP locals mapped = NONE’
    >- (
      match_mp_tac (Q.INST [‘R’ |-> ‘lift_runtime_rel’,‘captures’ |->
        ‘delete_all (MAP FST (funs:(mlstring # mlstring # exp) list))
          (FUNION body_captures function_captures)’,‘global’ |-> ‘initial’,
        ‘names’ |-> ‘MAP FST (funs:(mlstring # mlstring # exp) list)’,
        ‘n1’ |-> ‘chosen_n’,‘ds1’ |-> ‘chosen_ds’,‘used1’ |-> ‘chosen_used’]
        (INST_TYPE [“:α” |-> “:v”] lift_scope_choose_names_locals))
      >> asm_rewrite_tac [])
    >> have ‘lift_scope lift_runtime_rel (delete_all (MAP FST funs) body_captures)
         (delete_all (MAP FST funs) bound) (ren |++ ZIP (MAP FST funs,compiled_names))
         (emitted_n,emitted_ds,emitted_used) source function_env locals’
    >- (
      irule lift_scope_domain_subset
      >> qexists_tac ‘delete_all (MAP FST funs) (FUNION body_captures function_captures)’
      >> simp_tac (srw_ss()) [delete_all_domain,FDOM_FUNION,SUBSET_DEF]
      >> first_assum ACCEPT_TAC)
    >> have ‘set compiled_names ⊆ FDOM emitted_used’
    >- (
      qpat_assum ‘lift_state_extends (function_n,function_ds,function_used)
           (emitted_n,emitted_ds,emitted_used)’ mp_tac
      >> qpat_assum ‘set compiled_names ⊆ FDOM chosen_used’ mp_tac
      >> qpat_assum ‘FDOM chosen_used ⊆ FDOM function_used’ mp_tac
      >> POP_ASSUM_LIST (K ALL_TAC)
      >> simp [lift_state_extends_def] >> metis_tac [SUBSET_TRANS])
    >> have ‘∀name mapped. name ∈ FDOM body_captures ∧
         rename_var (ren |++ ZIP (MAP FST funs,compiled_names)) (Short name) =
           (Short mapped:(mlstring,mlstring) id) ⇒
         (MEM name (MAP FST funs) ⇔ MEM mapped compiled_names)’
    >- (
      match_mp_tac (Q.INST [‘n1’ |-> ‘chosen_n’,‘ds1’ |-> ‘chosen_ds’,‘used1’ |-> ‘chosen_used’]
        choose_names_capture_membership)
      >> asm_rewrite_tac [] >> metis_tac [cj 1 annotate_free_name_bound,LESS_EQ_TRANS])
    >> have ‘∀name k. MEM name compiled_names ∧ emitted_n ≤ k ⇒ name ≠ make_name k’
    >- (
      rpt strip_tac >> ‘chosen_n ≤ k’ by decide_tac
      >> qpat_x_assum ‘∀name k. MEM name compiled_names ∧ chosen_n ≤ k ⇒ _’ drule_all
      >> simp [])
    >> have ‘MAP FST compiled_bindings = compiled_names’
    >- simp [Abbr ‘compiled_bindings’,MAP_MAP_o,o_DEF,ETA_AX]
    >> have ‘lift_scope lift_runtime_rel
         (delete_all (MAP FST funs) (FUNION body_captures function_captures)) bound ren
         (out_n,out_ds,out_used) source final locals’
    >- (
      irule lift_scope_decs_avoid
      >> qexistsl_tac [‘base’,‘emitted_ds’,
           ‘function_env with v := build_rec_env compiled_funs function_env function_env.v’,
           ‘emitted_n’,‘emitted_used’]
      >> asm_rewrite_tac [])
    >> simp [] >> qx_genl_tac [‘s’,‘s'’,‘target’] >> strip_tac
    >> Cases_on ‘ALL_DISTINCT (MAP FST funs)’
    >- (
      have ‘LIST_REL (λname mapped.
           rename_var (ren |++ ZIP (MAP FST funs,compiled_names)) (Short name) =
             (Short mapped:(mlstring,mlstring) id)) (MAP FST funs) compiled_names’
      >- (
        rewrite_tac [LIST_REL_EVERY_ZIP] >> conj_tac
        >- simp []
        >> irule rename_var_updates_distinct
        >> qpat_assum ‘MAP FST (ZIP (MAP FST funs,compiled_names)) = MAP FST funs’
          (simp_tac (srw_ss()) o single)
        >> first_assum ACCEPT_TAC)
      >> qpat_assum ‘lift_scope _ _ _ _ _ source initial _’
        (assume_tac o MATCH_MP lift_scope_constructors)
      >> qpat_assum ‘lift_global_decs _ base initial’
           (assume_tac o MATCH_MP lift_global_decs_constructors)
      >> ‘EVERY (λ(f,x,e). source_dce$no_Open e ∧ check_exp_constructors source.c e) funs’
        by simp []
      >> have ‘∀name mapped.
           FLOOKUP (ren |++ ZIP (MAP FST funs,compiled_names)) name = SOME mapped ∧
           mapped ≠ name ⇒ ∀original. original ∈ exp_names_funs funs ⇒ mapped ≠ original’
      >- (
        qpat_assum ‘∀original mapped. FLOOKUP (ren |++ _) original = SOME mapped ∧ _ ⇒
             mapped ∉ _ ∪ _’ mp_tac
        >> POP_ASSUM_LIST (K ALL_TAC) >> simp_tac (srw_ss()) [IN_UNION]
        >> metis_tac [])
      >> qpat_assum ‘MAP FST compiled_funs = compiled_names’ (fn names => drule_all
           (REWRITE_RULE [names] (Q.INST [‘funs'’ |-> ‘compiled_funs’] lift_scope_rec_certificate)))
      >> disch_then (assume_tac o SRULE [nsBindList_clauses])
      >> qabbrev_tac ‘actual_bindings =
           MAP (λname. (name,Recclosure source funs name)) (MAP FST funs)’
      >> have ‘∀name mapped. name ∈ FDOM body_captures ∧ MEM name (MAP FST funs) ∧
           rename_var (ren |++ ZIP (MAP FST funs,compiled_names)) (Short name) =
             (Short mapped:(mlstring,mlstring) id) ⇒
           OPTREL lift_runtime_rel (ALOOKUP actual_bindings name)
             (ALOOKUP compiled_bindings mapped)’
      >- (
        qx_genl_tac [‘name’,‘mapped’] >> strip_tac
        >> ‘MEM mapped compiled_names’ by metis_tac []
        >> simp [Abbr ‘actual_bindings’,Abbr ‘compiled_bindings’,ALOOKUP_MAP_names,OPTREL_def]
        >> irule lift_rec_certificate_runtime_rel >> conj_tac
        >- first_assum ACCEPT_TAC
        >> qexists_tac
             ‘ren |++ ZIP (MAP FST (funs:(mlstring # mlstring # exp) list),compiled_names)’
        >> asm_rewrite_tac [])
      >> have ‘MAP FST actual_bindings = MAP FST funs’
      >- simp [Abbr ‘actual_bindings’,MAP_MAP_o,o_DEF,ELIM_UNCURRY,ETA_AX]
      >> have ‘lift_scope lift_runtime_rel body_captures (delete_all (MAP FST funs) bound)
           (ren |++ ZIP (MAP FST funs,compiled_names)) (emitted_n,emitted_ds,emitted_used)
           (source with v := nsBindList actual_bindings source.v)
           (function_env with v := nsBindList compiled_bindings function_env.v) locals’
      >- (
        irule lift_scope_renamed_global_bindings
        >> qexistsl_tac [‘MAP FST (funs:(mlstring # mlstring # exp) list)’,‘compiled_names’]
        >> rpt conj_tac >> asm_rewrite_tac []
        >> simp_tac (srw_ss()) [delete_all_domain,DISJOINT_ALT])
      >> qpat_x_assum ‘∀source locals. lift_scope _ body_captures _ _ _ _ _ _ ⇒ _’ drule
      >> strip_tac
      >> have ‘nsBindList actual_bindings source.v = build_rec_env funs source source.v’
      >- simp [Abbr ‘actual_bindings’,build_rec_env_nsBindList_names]
      >> qpat_assum ‘ALL_DISTINCT (MAP FST funs)’ (fn distinct =>
           simp_tac (srw_ss())
             [SRULE [ELIM_UNCURRY,ETA_AX] evaluate_letrec_distinct,distinct])
      >> qpat_assum ‘nsBindList actual_bindings source.v = build_rec_env funs source source.v’
           (fn bindings =>
             qpat_x_assum ‘∀s s' target. _ ⇒ lift_eval_refinement _ _ _
                 (evaluate s (source with v := nsBindList actual_bindings source.v) [body]) _’
               (qspecl_then [‘s’,‘s'’,‘target’] match_mp_tac o REWRITE_RULE [bindings]))
      >> asm_rewrite_tac [])
    >> drule evaluate_letrec_duplicate
    >> disch_then (qspecl_then [‘s’,‘source’,‘body’]
         (fn eq => simp_tac (srw_ss()) [eq,lift_eval_refinement_def])))
  >- (
    qpat_x_assum ‘¬(mode ≠ KeepValue ∧
         maps_disjoint (delete_all (MAP FST funs) function_captures) bound)’
      (fs o single)
    >> namedCases_on ‘lift_funs (bind_all (MAP FST funs) bound)
         (delete_all (MAP FST funs) ren) (n,ds,used)
         (MAP (λ(f,x,e). (f,x)) funs) function_trees’
         ["compiled_funs middle_n middle_ds middle_used"]
    >> gvs []
    >> namedCases_on ‘lift_exp mode (bind_all (MAP FST funs) bound)
         (delete_all (MAP FST funs) ren) (middle_n,middle_ds,middle_used) body_tree’
         ["compiled_body final_n final_ds final_used"]
    >> gvs []
    >> have ‘∀original mapped. FLOOKUP ren original = SOME mapped ∧ mapped ≠ original ⇒
         mapped ∉ exp_names_funs funs ∧ ¬MEM mapped (MAP FST funs)’
    >- (
      qx_genl_tac [‘original’,‘mapped’] >> strip_tac
      >> qpat_assum ‘∀name renamed. FLOOKUP ren name = SOME renamed ∧ renamed ≠ name ⇒
           renamed ∉ exp_names_funs funs ∧ _’
        (qspecl_then [‘original’,‘mapped’] mp_tac)
      >> metis_tac [recursive_names_all_names])
    >> ‘EVERY (λ(f,x,e). source_dce$no_Open e ∧ check_exp_constructors base.c e) funs’
      by (fs [EVERY_MEM,FORALL_PROD] >> metis_tac [])
    >> ‘MAP SND (MAP (λ(f,x,e). (f,x)) funs) = MAP (FST o SND) funs’
      by simp [MAP_MAP_o,o_DEF,ELIM_UNCURRY]
    >> ‘∀name renamed. FLOOKUP (delete_all (MAP FST funs) ren) name = SOME renamed ∧
          renamed ≠ name ⇒ renamed ∉ exp_names_funs funs’
      by (rw [delete_all_lookup] >> metis_tac [])
    >> drule_all lift_funs_global_decs >> disch_then (qx_choose_then ‘function_env’ assume_tac)
    >> qpat_assum ‘EVERY (λ(f,x,e). source_dce$no_Open e) funs’
      (assume_tac o SRULE [ELIM_UNCURRY])
    >> drule_all (SRULE [ELIM_UNCURRY] (cj 4 annotate_tree_names_bounded)) >> disch_tac
    >> ‘function_limit ≤ FST (n,ds,used)’ by simp []
    >> drule_all (cj 5 lift_exp_fresh) >> strip_tac
    >> drule (cj 5 lift_exp_state_extends) >> disch_tac
    >> drule lift_state_extends_counter >> simp_tac (srw_ss()) [] >> disch_tac
    >> ‘body_limit ≤ middle_n’ by decide_tac
    >> have ‘EVERY (λname. bump name 0 ≤ middle_n) (MAP FST funs)’
    >- (
      qpat_assum ‘EVERY (λname. bump name 0 ≤ n) (MAP FST funs)’
        (mp_tac o REWRITE_RULE [EVERY_MEM])
      >> simp_tac pure_ss [EVERY_MEM]
      >> metis_tac [LESS_EQ_TRANS])
    >> have ‘∀name renamed. FLOOKUP ren name = SOME renamed ∧ renamed ≠ name ⇒
         ∀original. original ∈ exp_names body ∨ MEM original (MAP FST funs) ⇒
           renamed ≠ original’
    >- (
      rpt strip_tac
      >> qpat_assum ‘∀name renamed. FLOOKUP ren name = SOME renamed ∧ renamed ≠ name ⇒
           renamed ∉ exp_names_funs funs ∧ renamed ∉ exp_names body’ drule_all
      >> qpat_assum ‘∀original mapped. FLOOKUP ren original = SOME mapped ∧ _ ⇒ _ ∧ _’
           drule_all
      >> simp [])
    >> drule_all lift_bound_exp_simulation
    >> disch_then (qx_choose_then ‘final’ strip_assume_tac)
    >> drule_all lift_annotated_state_properties_lift >> strip_tac
    >> qexists_tac ‘final’ >> asm_rewrite_tac [] >> qx_genl_tac [‘source’,‘locals’] >> strip_tac
    >> have ‘lift_scope lift_runtime_rel (delete_all (MAP FST funs) function_captures)
         bound ren (n,ds,used) source initial locals’
    >- (
      irule lift_scope_domain_subset
      >> qexists_tac ‘delete_all (MAP FST funs) (FUNION body_captures function_captures)’
      >> simp [delete_all_domain,FDOM_FUNION,SUBSET_DEF])
    >> drule_all (Q.INST [‘captures’ |->
         ‘delete_all (MAP FST funs) (FUNION body_captures function_captures)’,
         ‘final’ |-> ‘function_env’] (SPEC_ALL lift_scope_decs_avoid))
    >> disch_tac
    >> have ‘lift_scope lift_runtime_rel (delete_all (MAP FST funs) body_captures) bound ren
         (middle_n,middle_ds,middle_used) source function_env locals’
    >- (
      irule lift_scope_domain_subset
      >> qexists_tac ‘delete_all (MAP FST funs) (FUNION body_captures function_captures)’
      >> simp [delete_all_domain,FDOM_FUNION,SUBSET_DEF])
    >> qpat_x_assum ‘∀source locals. lift_scope _ _ _ _ _ _ function_env _ ⇒ _’ drule
    >> strip_tac
    >> drule_all (Q.INST [‘captures’ |->
         ‘delete_all (MAP FST funs) (FUNION body_captures function_captures)’,
         ‘n’ |-> ‘middle_n’,‘ds’ |-> ‘middle_ds’,‘used’ |-> ‘middle_used’,
         ‘initial’ |-> ‘function_env’] (SPEC_ALL lift_scope_decs_avoid))
    >> disch_tac >> drule (cj 3 annotate_LENGTH) >> disch_tac
    >> have ‘MAP FST compiled_funs = MAP FST funs’
    >- (
      drule lift_funs_names_prefix
      >> simp [TAKE_LENGTH_TOO_LONG,MAP_MAP_o,o_DEF,ELIM_UNCURRY,ETA_AX])
    >> have ‘ZIP (MAP FST compiled_funs,MAP (FST o SND) funs) =
         MAP (λ(f,x,e). (f,x)) funs’
    >- (
      qpat_assum ‘MAP FST compiled_funs = MAP FST funs’
        (fn eq => simp_tac (srw_ss())
          [eq,rich_listTheory.ZIP_MAP_MAP,o_DEF,ELIM_UNCURRY]))
    >> have ‘lift_scope lift_runtime_rel (delete_all (MAP FST funs) function_captures)
         bound (delete_all (MAP FST funs) ren) (n,ds,used) source initial locals’
    >- (
      irule lift_scope_delete_renaming >> conj_tac
      >- simp_tac (srw_ss()) [delete_all_domain,DISJOINT_ALT]
      >> first_assum ACCEPT_TAC)
    >> simp [] >> qx_genl_tac [‘s’,‘s'’,‘target’] >> strip_tac
    >> Cases_on ‘ALL_DISTINCT (MAP FST funs)’
    >- (
      ‘ALL_DISTINCT (MAP FST compiled_funs)’ by asm_rewrite_tac []
      >> have ‘LIST_REL (λname renamed.
           rename_var (delete_all (MAP FST funs) ren) (Short name) =
             (Short renamed:(mlstring,mlstring) id))
           (MAP FST funs) (MAP FST compiled_funs)’
      >- (
        qpat_assum ‘MAP FST compiled_funs = MAP FST funs’ (rewrite_tac o single)
        >> irule LIST_REL_refl
        >> simp_tac (srw_ss()) [rename_var_delete_all])
      >> have ‘∀name renamed. name ∈ FDOM function_captures ∧
           rename_var (delete_all (MAP FST funs) ren) (Short name) =
             (Short renamed:(mlstring,mlstring) id) ⇒
           (MEM name (MAP FST funs) ⇔ MEM renamed (MAP FST compiled_funs))’
      >- (
        rw [] >> qpat_x_assum ‘MAP FST compiled_funs = MAP FST funs’ (rewrite_tac o single)
        >> irule rename_var_delete_all_mem >> qexists_tac ‘ren’ >> simp [] >> metis_tac [])
      >> have ‘∀name k. MEM name (MAP FST compiled_funs) ∧ n ≤ k ⇒ name ≠ make_name k’
      >- (
        qpat_assum ‘MAP FST compiled_funs = MAP FST funs’ (rewrite_tac o single)
        >> qpat_assum ‘EVERY (λname. bump name 0 ≤ n) (MAP FST funs)’
          (mp_tac o REWRITE_RULE [EVERY_MEM])
        >> POP_ASSUM_LIST (K ALL_TAC) >> metis_tac [bump_make_name,LESS_EQ_TRANS])
      >> have ‘∀name renamed. FLOOKUP (delete_all (MAP FST funs) ren) name = SOME renamed ∧
           renamed ≠ name ⇒ ∀original. original ∈ exp_names_funs funs ⇒ renamed ≠ original’
      >- (
        qpat_assum ‘∀original mapped. FLOOKUP ren original = SOME mapped ∧ mapped ≠ original ⇒
             mapped ∉ exp_names_funs funs ∧ ¬MEM mapped (MAP FST funs)’ mp_tac
        >> POP_ASSUM_LIST (K ALL_TAC) >> rw [delete_all_lookup]
        >> metis_tac [])
      >> qpat_assum ‘ZIP (MAP FST compiled_funs,MAP (FST o SND) funs) =
           MAP (λ(f,x,e). (f,x)) funs’ (fn names =>
        qpat_assum ‘lift_funs _ _ _ (MAP (λ(f,x,e). (f,x)) funs) function_trees = _’
          (assume_tac o REWRITE_RULE [GSYM names]))
      >> qpat_assum ‘lift_scope _ _ _ _ _ source initial _’
        (assume_tac o MATCH_MP lift_scope_constructors)
      >> qpat_assum ‘lift_global_decs _ base initial’
           (assume_tac o MATCH_MP lift_global_decs_constructors)
      >> ‘EVERY (λ(f,x,e). source_dce$no_Open e ∧ check_exp_constructors source.c e) funs’
        by simp []
      >> drule_all lift_scope_rec_certificate >> disch_tac
      >> drule lift_scope_captures_protected
      >> disch_tac >> drule_all (cj 4 annotate_free_names) >> disch_tac
      >> qpat_assum ‘FDOM function_captures = exp_free_names_funs funs’ (fn domain =>
        qpat_x_assum ‘∀name renamed. name ∈ FDOM (delete_all (MAP FST funs) function_captures) ∧
             _ ⇒ _’ (assume_tac o SRULE [delete_all_domain,domain]))
      >> have ‘∀id. (∀name. id = Short name ⇒
           name ∈ exp_free_names_funs compiled_funs DIFF set (MAP FST compiled_funs)) ⇒
           nsLookup (nsBindList locals final.v) id =
           nsLookup (nsBindList locals function_env.v) id’
      >- (
        simp_tac (srw_ss()) [] >> rpt strip_tac
        >> drule_all (SRULE [] lift_rec_decs_lookup) >> simp_tac std_ss [])
      >> qpat_assum ‘lift_global_decs _ base final’
           (assume_tac o MATCH_MP lift_global_decs_constructors)
      >> qpat_assum ‘lift_global_decs _ base function_env’
           (assume_tac o MATCH_MP lift_global_decs_constructors)
      >> ‘target.c = function_env.c’ by simp []
      >> have ‘∀id. (∀name. id = Short name ⇒
           name ∈ exp_free_names_funs compiled_funs DIFF set (MAP FST compiled_funs)) ⇒
           nsLookup target.v id = nsLookup (nsBindList locals function_env.v) id’
      >- (
        qpat_x_assum ‘∀id. _ ⇒ nsLookup target.v id = _’ mp_tac
        >> qpat_x_assum ‘∀id. _ ⇒ nsLookup (nsBindList locals final.v) id = _’ mp_tac
        >> rpt (pop_assum kall_tac) >> simp [cj 14 exp_free_names_def] >> metis_tac [])
      >> have ‘lift_rec_certificate lift_runtime_rel source funs target compiled_funs
           (delete_all (MAP FST funs) ren)’
      >- (
        irule lift_rec_certificate_env_cong
        >> qpat_assum ‘lift_rec_certificate _ _ _ _ _ _’ (irule_at Any) >> simp [])
      >> have ‘LIST_REL (λ(x,v) (y,w). x = y ∧ lift_runtime_rel v w)
           (MAP (λname. (name,Recclosure source funs name)) (MAP FST funs))
           (MAP (λname. (name,Recclosure target compiled_funs name)) (MAP FST funs))’
      >- (
        simp_tac (srw_ss()) [LIST_REL_MAP] >> irule LIST_REL_refl
        >> qx_gen_tac ‘entry’ >> strip_tac >> simp_tac (srw_ss()) []
        >> irule lift_rec_certificate_runtime_rel
        >> qpat_assum ‘lift_rec_certificate _ _ _ target _ _’ (irule_at Any)
        >> qpat_assum ‘MEM entry _’ (assume_tac o MATCH_MP (ISPEC “FST” MEM_MAP_f))
        >> simp [rename_var_delete_all])
      >> qpat_x_assum ‘∀bindings bindings'. _ ⇒ lift_scope _ _ _ _ _ _ _ _ ∧ ∀s s' target. _’
        (qspecl_then [
           ‘MAP (λname. (name,Recclosure source funs name)) (MAP FST funs)’,
           ‘MAP (λname. (name,Recclosure target compiled_funs name)) (MAP FST compiled_funs)’]
           mp_tac)
      >> impl_tac
      >- (
        conj_tac
        >- simp_tac (srw_ss()) [MAP_MAP_o,o_DEF,ELIM_UNCURRY,ETA_AX]
        >> qpat_assum ‘MAP FST compiled_funs = MAP FST funs’ (rewrite_tac o single)
        >> first_assum ACCEPT_TAC)
      >> disch_then (assume_tac o REWRITE_RULE
           [GSYM (SRULE [ELIM_UNCURRY] build_rec_env_nsBindList)] o
           SRULE [MAP_MAP_o,o_DEF,ELIM_UNCURRY] o CONJUNCT2)
      >> qpat_assum ‘ALL_DISTINCT (MAP FST funs)’ (fn distinct =>
        qpat_assum ‘ALL_DISTINCT (MAP FST compiled_funs)’ (fn compiled_distinct =>
          simp_tac (srw_ss()) [SRULE [ELIM_UNCURRY,ETA_AX]
            evaluate_letrec_distinct,distinct,compiled_distinct]))
      >> qpat_x_assum ‘∀s s' target'. _ ⇒ lift_eval_refinement _ _ _
           (evaluate s (source with v := build_rec_env funs source source.v) [body]) _’
        (qspecl_then [‘s’,‘s'’,‘target with v := build_rec_env compiled_funs target target.v’]
           match_mp_tac)
      >> simp_tac (srw_ss()) [] >> asm_rewrite_tac []
      >> rewrite_tac [SRULE [ELIM_UNCURRY] build_rec_env_nsBindList,
           nsBindList_append]
      >> match_mp_tac (Q.INST [‘names’ |->
           ‘MAP FST (compiled_funs:(mlstring # mlstring # exp) list)’] lift_bound_lookup)
      >> conj_tac >- simp_tac (srw_ss()) [MAP_MAP_o,o_DEF,ELIM_UNCURRY,ETA_AX]
      >> qpat_x_assum ‘∀id. _ ⇒ nsLookup target.v id = nsLookup (nsBindList locals final.v) id’
        mp_tac
      >> rpt (pop_assum kall_tac) >> simp [cj 14 exp_free_names_def] >> metis_tac [])
    >> drule evaluate_letrec_duplicate
    >> disch_then (qspecl_then [‘s’,‘source’,‘body’]
         (fn eq => simp_tac (srw_ss()) [eq,lift_eval_refinement_def])))
QED

Theorem lift_exp_sim_raise[local]:
  lift_exp_sim (:'ffi) clock D e ⇒ lift_exp_sim (:'ffi) clock D (Raise e)
Proof
  strip_tac >> rewrite_tac [lift_exp_sim_def] >> rpt gen_tac
  >> strip_tac >> qpat_x_assum ‘annotate_exp [] (Raise _) = _’
       (mp_tac o SRULE [annotate_exp_def])
  >> namedCases_on ‘annotate_exp [] e’ ["body child_limit child_captures"] >> strip_tac
  >> gvs [] >> fs [cj 1 lift_exp_def,cj 11 lift_exp_def]
  >> namedCases_on ‘lift_exp mode bound ren (n,ds,used) body’
       ["compiled_body child_n child_ds child_used"]
  >> gvs [exp_names_def,no_Open_thm,check_exp_constructors_def]
  >> drule_all lift_exp_sim_lift >> disch_then (qx_choose_then ‘final’ strip_assume_tac)
  >> qexists_tac ‘final’ >> simp [exp_free_names_def] >> rpt gen_tac >> strip_tac
  >> first_x_assum drule >> rw [] >> irule lift_evaluate_raise_refinement
  >> first_x_assum irule >> simp []
QED

Theorem lift_exp_sim_handle_mat[local]:
  (∀p x. MEM (p,x) pes ⇒ lift_exp_sim (:'ffi) clock D x) ∧
  lift_exp_sim (:'ffi) clock D e ⇒
  lift_exp_sim (:'ffi) clock D (Handle e pes) ∧ lift_exp_sim (:'ffi) clock D (Mat e pes)
Proof
  strip_tac
  >> simp [lift_exp_sim_def] >> conj_tac >> rpt gen_tac
  >> disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th))
  >> namedCases_on ‘annotate_exp [] e’ ["t1 l1 c1"]
  >> namedCases_on ‘annotate_pes [] pes’ ["bs l2 c2"] >> qpat_x_assum ‘_ ∨ _’ mp_tac
  >> gvs [annotate_exp_def,cj 1 lift_exp_def] >> strip_tac
  >> fs [cj 12 lift_exp_def,cj 13 lift_exp_def]
  >> namedCases_on ‘lift_exp mode bound ren (n,ds,used) t1’ ["r1 n2 ds2 u2"]
  >> namedCases_on ‘lift_pes mode bound ren (n2,ds2,u2) (MAP FST pes) bs’ ["rs n3 ds3 u3"]
  >> gvs [exp_names_def,no_Open_thm,check_exp_constructors_def]
  >> drule_at (Pos last) lift_exp_pes_sim
  >> disch_then (qspecl_then [‘clock’,‘D’,‘e’,‘t1’,‘l1’,‘c1’,‘l2’,‘c2’,‘n’,‘ds’,
       ‘used’,‘initial’,‘base’,‘r1’] mp_tac)
  >> (impl_tac >- (fs [EVERY_MEM,FORALL_PROD] >> metis_tac []))
  >> disch_then (qx_choose_then ‘final’ strip_assume_tac)
  >> qexists_tac ‘final’ >> asm_rewrite_tac [] >> qx_genl_tac [‘source’,‘locals’] >> strip_tac
  >> first_x_assum drule >> strip_tac >> simp [] >> rpt strip_tac
  >> first_x_assum (qspec_then ‘target’ mp_tac)
  >> (impl_tac >- (
    rw [] >> first_x_assum irule
    >> rw [] >> gvs [exp_free_names_def] >> metis_tac []))
  >> rw [] >> ‘MAP FST rs = MAP FST pes’ by metis_tac [lift_annotated_pes_patterns]
  >> qpat_assum ‘lift_scope _ _ bound ren _ source final locals’
       (assume_tac o CONJUNCT1 o REWRITE_RULE [lift_env_rel_def] o
        MATCH_MP lift_scope_env_rel)
  >~ [‘Handle _ _’]
  >- (
    irule (runtime_inst lift_evaluate_handle_refinement)
    >> rw [] >> irule lift_runtime_evaluate_match_refinement
    >> simp [lift_runtime_rel_refl] >> qexists_tac ‘clock’ >> simp [])
  >> irule (runtime_inst lift_evaluate_mat_refinement)
  >> rw [] >> irule lift_runtime_evaluate_match_refinement
  >> simp [lift_runtime_rel_refl] >> qexists_tac ‘clock’ >> simp []
QED

Theorem lift_exp_sim_lit[local]:
  lift_exp_sim (:'ffi) clock D (Lit lit)
Proof
  rewrite_tac [lift_exp_sim_def] >> rpt gen_tac
  >> disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th))
  >> drule_all lift_annotated_literal
  >> qpat_x_assum ‘lower_exp _ _ _ _ _ = _ ∨ lift_exp _ _ _ _ _ = _’ kall_tac
  >> strip_tac >> gvs [annotate_exp_def,str_empty_def]
  >- (
    qexists_tac ‘initial’
    >> simp [cj 3 evaluate_def,lift_eval_refinement_def,lift_eval_result_rel_def,
             lift_result_rel_def,lift_runtime_rel_refl])
  >> ‘lift_pure_value initial (Lit lit) (Litv lit)’ by simp [lift_pure_value_rules]
  >> ‘check_exp_constructors initial.c (Lit lit)’ by simp [check_exp_constructors_def]
  >> drule_all lift_emit_value_sim >> strip_tac >> qexists_tac ‘final’ >> asm_rewrite_tac []
  >> rpt gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >> simp []
  >> qx_genl_tac [‘s’,‘s'’,‘target’] >> strip_tac
  >> qpat_x_assum ‘∀target. _’ (drule_then (qspec_then ‘s'’ SUBST1_TAC))
  >> simp [cj 3 evaluate_def,lift_eval_refinement_def,lift_eval_result_rel_def,
           lift_result_rel_def,lift_runtime_rel_refl]
QED

Theorem lift_exp_sim_var[local]:
  lift_exp_sim (:'ffi) clock D (Var id)
Proof
  rewrite_tac [lift_exp_sim_def] >> rpt gen_tac
  >> strip_tac >> drule lift_annotated_variable >> disch_tac >> gvs []
  >> qexists_tac ‘initial’ >> simp [] >> qx_genl_tac [‘source’,‘locals’] >> strip_tac
  >> qx_genl_tac [‘s’,‘s'’,‘target’] >> strip_tac
  >> qpat_x_assum ‘lift_scope _ _ _ _ _ _ _ _’ (mp_tac o MATCH_MP lift_scope_env_rel)
  >> disch_tac
  >> ‘∀name. id = Short name ⇒ name ∈ FDOM captures’ by (
    namedCases_on ‘id’ ["name","module_name nested_id"]
    >> gvs [annotate_exp_def])
  >> drule_all lift_env_rel_lookup >> disch_then (assume_tac o SRULE [])
  >> qpat_x_assum ‘∀id. _ ⇒ nsLookup target.v id = _’
       (qspec_then ‘rename_var ren id’ mp_tac)
  >> simp [exp_free_names_def] >> disch_tac
  >> qpat_x_assum ‘nsLookup target.v _ = nsLookup _ _’ (SUBST_ALL_TAC o SYM)
  >> namedCases_on ‘nsLookup source.v id’ ["","source_value"]
  >> namedCases_on ‘nsLookup target.v (rename_var ren id)’ ["","target_value"] >> fs []
  >> simp [evaluate_def,lift_eval_refinement_def,lift_eval_result_rel_def,
          lift_result_rel_def]
QED

Theorem lift_exp_sim_app[local]:
  lift_app_sim (:'ffi) clock D ∧ (∀e. MEM e es ⇒ lift_exp_sim (:'ffi) clock D e) ⇒
  lift_exp_sim (:'ffi) clock D (App op es)
Proof
  strip_tac
  >> qpat_x_assum ‘∀e. MEM e es ⇒ _’ (assume_tac o MATCH_MP lift_exps_simulation)
  >> rewrite_tac [lift_exp_sim_def] >> rpt gen_tac
  >> disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th))
  >> namedCases_on ‘annotate_exps [] es’ ["trees list_limit list_captures"]
  >> qpat_x_assum ‘annotate_exp [] (App _ _) = _’ (mp_tac o SRULE [annotate_exp_def])
  >> simp [] >> strip_tac
  >> qpat_x_assum ‘lower_exp _ _ _ _ _ = _ ∨ lift_exp _ _ _ _ _ = _’ mp_tac
  >> gvs [cj 1 lift_exp_def] >> strip_tac >> fs [cj 6 lift_exp_def]
  >> namedCases_on ‘lift_exps (if allow_lift op es then mode else KeepValue)
       bound ren (n,ds,used) trees’ ["arguments list_n list_ds list_used"]
  >> gvs [exp_names_def,no_Open_thm,check_exp_constructors_def,SF ETA_ss]
  >> first_x_assum drule_all >> disch_then (qx_choose_then ‘final’ strip_assume_tac)
  >> qexists_tac ‘final’ >> asm_rewrite_tac [] >> qx_genl_tac [‘source’,‘locals’] >> strip_tac
  >> first_x_assum drule >> strip_tac >> simp [] >> qx_genl_tac [‘s’,‘s'’,‘target’]
  >> strip_tac
  >> have ‘lift_eval_refinement lift_runtime_rel D (LIST_REL lift_runtime_rel)
        (evaluate s source (REVERSE es)) (evaluate s' target (REVERSE arguments))’
  >- (
    qpat_assum ‘∀s s' target. _ ⇒ _ (evaluate _ _ (REVERSE es)) _’
         (qspecl_then [‘s’,‘s'’,‘target’] mp_tac)
    >> simp [exp_free_names_def])
  >> qpat_assum ‘lift_app_sim _ _ _’
       (qspecl_then [‘op’,‘es’,‘arguments’,‘s’,‘s'’,‘source’,‘target’] mp_tac o
        REWRITE_RULE [lift_app_sim_def])
  >> simp []
QED

Theorem lift_exp_sim_log[local]:
  lift_exp_sim (:'ffi) clock D e1 ∧ lift_exp_sim (:'ffi) clock D e2 ⇒
  lift_exp_sim (:'ffi) clock D (Log lop e1 e2)
Proof
  strip_tac
  >> simp [lift_exp_sim_def] >> rpt gen_tac
  >> disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th))
  >> namedCases_on ‘annotate_exp [] e1’ ["t1 l1 c1"]
  >> namedCases_on ‘annotate_exp [] e2’ ["t2 l2 c2"] >> qpat_x_assum ‘_ ∨ _’ mp_tac
  >> gvs [annotate_exp_def,cj 1 lift_exp_def] >> strip_tac
  >> drule (cj 2 lower_exp_exps) >> strip_tac >> gvs []
  >> gvs [exp_names_def,no_Open_thm,check_exp_constructors_def]
  >> ‘∀e. MEM e [e1;e2] ⇒ lift_exp_sim (:'ffi) clock D e’ by simp [DISJ_IMP_THM]
  >> drule_at (Pos last) lift_exps_sim
  >> disch_then (qspecl_then [‘clock’,‘D’,‘[e1;e2]’,‘MAX l1 l2’,
       ‘FUNION c1 c2’,‘base’,‘initial’] mp_tac)
  >> impl_tac >- (simp [annotate_exp_def,exp_names_def] >> metis_tac [])
  >> disch_then (qx_choose_then ‘final’ strip_assume_tac)
  >> qexists_tac ‘final’ >> asm_rewrite_tac [] >> qx_genl_tac [‘source’,‘locals’] >> strip_tac
  >> first_x_assum drule >> strip_tac >> simp [] >> rpt strip_tac
  >> first_x_assum (qspec_then ‘target’ mp_tac)
  >> impl_tac >- (
    rw [] >> first_x_assum irule
    >> rw [] >> gvs [exp_free_names_def] >> metis_tac [])
  >> rw []
  >> irule (runtime_inst lift_evaluate_log_refinement)
  >> rw [] >> first_x_assum irule >> simp []
QED

Theorem lift_exp_sim_if[local]:
  lift_exp_sim (:'ffi) clock D e1 ∧ lift_exp_sim (:'ffi) clock D e2 ∧
  lift_exp_sim (:'ffi) clock D e3 ⇒
  lift_exp_sim (:'ffi) clock D (If e1 e2 e3)
Proof
  strip_tac
  >> simp [lift_exp_sim_def] >> rpt gen_tac
  >> disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th))
  >> namedCases_on ‘annotate_exp [] e1’ ["t1 l1 c1"]
  >> namedCases_on ‘annotate_exp [] e2’ ["t2 l2 c2"]
  >> namedCases_on ‘annotate_exp [] e3’ ["t3 l3 c3"] >> qpat_x_assum ‘_ ∨ _’ mp_tac
  >> gvs [annotate_exp_def,cj 1 lift_exp_def] >> strip_tac
  >> drule (cj 1 lower_exp_exps) >> strip_tac >> gvs []
  >> gvs [exp_names_def,no_Open_thm,check_exp_constructors_def]
  >> ‘∀e. MEM e [e1;e2;e3] ⇒ lift_exp_sim (:'ffi) clock D e’ by simp [DISJ_IMP_THM]
  >> drule_at (Pos last) lift_exps_sim
  >> disch_then (qspecl_then [‘clock’,‘D’,‘[e1;e2;e3]’,‘MAX l1 (MAX l2 l3)’,
       ‘FUNION c1 (FUNION c2 c3)’,‘base’,‘initial’] mp_tac)
  >> impl_tac >- (simp [annotate_exp_def,exp_names_def] >> metis_tac [])
  >> disch_then (qx_choose_then ‘final’ strip_assume_tac)
  >> qexists_tac ‘final’ >> asm_rewrite_tac [] >> qx_genl_tac [‘source’,‘locals’] >> strip_tac
  >> first_x_assum drule >> strip_tac >> simp [] >> rpt strip_tac
  >> first_x_assum (qspec_then ‘target’ mp_tac)
  >> impl_tac >- (
    rw [] >> first_x_assum irule
    >> rw [] >> gvs [exp_free_names_def] >> metis_tac [])
  >> rw []
  >> irule (runtime_inst lift_evaluate_if_refinement)
  >> rw [] >> first_x_assum irule >> simp []
QED

Theorem lift_exp_sim_con[local]:
  (∀e. MEM e es ⇒ lift_exp_sim (:'ffi) clock D e) ⇒
  lift_exp_sim (:'ffi) clock D (Con cn es)
Proof
  strip_tac
  >> qpat_x_assum ‘∀e. MEM e es ⇒ _’ (assume_tac o MATCH_MP lift_exps_simulation)
  >> rewrite_tac [lift_exp_sim_def] >> rpt gen_tac
  >> disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th))
  >> namedCases_on ‘annotate_exps [] es’ ["trees list_limit list_captures"]
  >> drule_all lift_annotated_constructor
  >> disch_then (qx_choosel_then [‘child_mode’,‘arguments’,‘middle’]
       (fn th => MAP_EVERY assume_tac (CONJUNCTS th)))
  >> namedCases_on ‘middle’ ["list_n list_ds list_used"]
  >> qpat_x_assum ‘lower_exp _ _ _ _ _ = _ ∨ lift_exp _ _ _ _ _ = _’ kall_tac
  >> qpat_x_assum ‘(_ ∧ _ ∧ _) ∨ _’ mp_tac
  >> gvs [annotate_exp_def,exp_names_def,no_Open_thm,check_exp_constructors_def,SF ETA_ss]
  >> disch_tac
  >> qpat_x_assum ‘∀mode bound ren n ds used compiled n1 ds1 used1 base initial. _’ drule_all
  >> disch_then (qx_choose_then ‘list_env’ strip_assume_tac)
  >> have ‘LENGTH arguments = LENGTH es’
  >- metis_tac [annotate_LENGTH,cj 1 lift_output_lengths]
  >> qpat_x_assum ‘(_ ∧ _ ∧ _) ∨ _’ strip_assume_tac >> gvs []
  >- (
    qexists_tac ‘list_env’ >> asm_rewrite_tac [] >> qx_genl_tac [‘source’,‘locals’] >> strip_tac
    >> qpat_x_assum ‘∀source locals. _’ drule >> strip_tac >> simp []
    >> ‘source.c = list_env.c’ by fs [lift_scope_def,lift_env_rel_def]
    >> qx_genl_tac [‘s’,‘s'’,‘target’] >> strip_tac
    >> irule (runtime_inst lift_evaluate_con_refinement)
    >> simp [] >> qpat_assum ‘∀s s' target. _ ⇒ _ (evaluate _ _ (REVERSE es)) _’
         (qspecl_then [‘s’,‘s'’,‘target’] mp_tac)
    >> simp [exp_free_names_def])
  >> qpat_assum ‘lift_global_decs _ base list_env’
       (assume_tac o MATCH_MP lift_global_decs_constructors)
  >> ‘check_exp_constructors list_env.c (Con cn es)’
    by fs [check_exp_constructors_def,EVERY_MEM]
  >> drule_all lift_emitted_con_pure
  >> disch_then (qx_choose_then ‘target_value’ strip_assume_tac)
  >> drule_all (cj 2 annotate_tree_names_bounded) >> disch_tac
  >> ‘limit ≤ FST (n,ds,used)’ by simp []
  >> drule_all (cj 3 lift_exp_fresh) >> strip_tac
  >> drule_all lift_emit_value_sim
  >> disch_then (qx_choose_then ‘emitted_env’ strip_assume_tac)
  >> qexists_tac ‘emitted_env’ >> asm_rewrite_tac [] >> qx_genl_tac [‘source’,‘locals’] >> strip_tac
  >> qpat_assum ‘∀source locals. lift_scope _ _ _ _ (n,ds,used) _ _ _ ⇒ _’ drule
  >> strip_tac
  >> qpat_x_assum ‘∀R captures bound ren source locals. _’ drule >> strip_tac >> simp []
  >> qpat_assum ‘lift_scope _ captures _ _ (n,ds,used) _ initial locals’
       (mp_then (Pos hd) mp_tac lift_scope_closed)
  >> simp [] >> disch_tac
  >> qpat_x_assum ‘∀source locals. lift_scope _ _ _ _ (n,ds,used) _ _ _ ⇒ _’ drule
  >> strip_tac >> ‘source.c = list_env.c’ by fs [lift_scope_def,lift_env_rel_def]
  >> qx_genl_tac [‘s’,‘s'’,‘target’] >> strip_tac
  >> qpat_x_assum ‘∀target. _’ (drule_then (qspec_then ‘s'’ SUBST1_TAC))
  >> ‘evaluate s' list_env [Con cn arguments] = (s',Rval [target_value])’
       by metis_tac [lift_pure_value_evaluates]
  >> pop_assum (SUBST1_TAC o SYM)
  >> irule (runtime_inst lift_evaluate_con_refinement)
  >> qpat_assum ‘∀s s' target.
       _ ∧ _ ∧ _ ∧
       (∀id. _ ⇒ nsLookup target.v id = nsLookup (nsBindList [] list_env.v) id) ⇒ _’
       (irule_at Any)
  >> simp [namespaceTheory.nsBindList_def]
QED

Theorem lift_exp_sim_fun[local]:
  lift_exp_sim (:'ffi) clock D body ⇒ lift_exp_sim (:'ffi) clock D (Fun arg body)
Proof
  strip_tac >> rewrite_tac [lift_exp_sim_def] >> rpt gen_tac
  >> disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th))
  >> namedCases_on ‘annotate_exp [] body’ ["body_tree body_limit body_captures"]
  >> drule_all lift_annotated_function
  >> disch_then (qx_choosel_then [‘compiled_body’,‘body_state’]
       (fn th => MAP_EVERY assume_tac (CONJUNCTS th)))
  >> namedCases_on ‘body_state’ ["body_n body_ds body_used"]
  >> qpat_x_assum ‘lower_exp _ _ _ _ _ = _ ∨ lift_exp _ _ _ _ _ = _’ kall_tac
  >> qpat_x_assum ‘(_ = Fun _ _ ∧ _) ∨ _’ mp_tac
  >> gvs [annotate_exp_def,exp_names_def,no_Open_thm,check_exp_constructors_def]
  >> disch_tac
  >> qpat_assum ‘bump arg _ ≤ n’ (strip_assume_tac o MATCH_MP bump_le_imp)
  >> have ‘∀name renamed. FLOOKUP ren name = SOME renamed ∧ renamed ≠ name ⇒
       ∀original. original ∈ exp_names body ∨ original = arg ⇒ renamed ≠ original’
  >- metis_tac []
  >> have ‘∀name renamed. FLOOKUP (fdomsub ren arg) name = SOME renamed ∧ renamed ≠ name ⇒
       ∀original. original ∈ exp_names body ⇒ renamed ≠ original’
  >- (rw [DOMSUB_FLOOKUP_THM] >> metis_tac [])
  >> drule lift_function_body_routes >> disch_tac
  >> qpat_x_assum ‘lift_exp_sim _ _ _ body’ (drule_all o REWRITE_RULE [lift_exp_sim_def])
  >> disch_then (qx_choose_then ‘body_env’ strip_assume_tac)
  >> qpat_x_assum ‘lower_exp _ _ _ _ _ = _ ∨ lift_exp _ _ _ _ _ = _’ kall_tac
  >> drule_all (cj 1 annotate_tree_names_bounded) >> disch_tac
  >> ‘body_limit ≤ FST (n,ds,used)’ by simp []
  >> drule_all lift_function_body_fresh >> strip_tac
  >> drule lift_function_body_state_extends >> disch_tac
  >> qpat_x_assum ‘(_ = Fun _ _ ∧ _) ∨ _’ strip_assume_tac >> rveq
  >- (
    qexists_tac ‘body_env’ >> asm_rewrite_tac [] >> qx_genl_tac [‘source’,‘locals’] >> strip_tac
    >> drule_all lift_scope_decs_avoid >> disch_tac >> asm_rewrite_tac []
    >> qpat_assum ‘lift_scope _ _ _ _ _ source initial _’
      (assume_tac o MATCH_MP lift_scope_constructors)
    >> qpat_assum ‘lift_global_decs _ base initial’
         (assume_tac o MATCH_MP lift_global_decs_constructors)
    >> ‘check_exp_constructors source.c body’ by simp []
    >> drule_all lift_scope_function_certificate >> disch_tac
    >> qx_genl_tac [‘s’,‘s'’,‘target’] >> strip_tac
    >> have ‘lift_function_certificate lift_runtime_rel source arg body target
           compiled_body’
    >- (
      irule lift_function_certificate_env_cong
      >> qpat_assum ‘lift_function_certificate _ _ _ _ _ _’ (irule_at Any)
      >> qpat_assum ‘∀id. _ ⇒ nsLookup target.v id = _’
           (assume_tac o SRULE [exp_free_names_def])
      >> asm_simp_tac (srw_ss()) [])
    >> simp [cj 8 evaluate_def,lift_eval_refinement_def,lift_eval_result_rel_def,
             lift_result_rel_def,lift_runtime_rel_value_rel]
    >> irule lift_runtime_rel_function_closure >> first_assum ACCEPT_TAC)
  >> drule_all (cj 1 annotate_constructors) >> disch_tac
  >> drule_all lift_function_body_constructors >> disch_tac
  >> qpat_assum ‘lift_global_decs _ base body_env’
       (assume_tac o MATCH_MP lift_global_decs_constructors)
  >> ‘check_exp_constructors body_env.c (Fun arg compiled_body)’
    by simp [check_exp_constructors_def]
  >> ‘lift_pure_value body_env (Fun arg compiled_body)
        (Closure body_env arg compiled_body)’ by simp [lift_pure_value_rules]
  >> drule_all lift_emit_value_sim
  >> disch_then (qx_choose_then ‘emitted_env’ strip_assume_tac)
  >> qexists_tac ‘emitted_env’ >> asm_rewrite_tac [] >> qx_genl_tac [‘source’,‘locals’] >> strip_tac
  >> drule_all lift_scope_decs_avoid >> disch_tac
  >> qpat_x_assum ‘∀R captures bound ren source locals. _’ drule >> strip_tac >> simp []
  >> qpat_assum ‘lift_scope _ _ _ _ _ source initial _’
    (assume_tac o MATCH_MP lift_scope_constructors)
  >> qpat_assum ‘lift_global_decs _ base initial’
       (assume_tac o MATCH_MP lift_global_decs_constructors)
  >> ‘check_exp_constructors source.c body’ by simp []
  >> qpat_assum ‘lift_scope _ (fdomsub body_captures arg) bound ren
       (n,ds,used) source initial locals’
    (mp_then (Pos hd) mp_tac lift_scope_closed)
  >> simp [] >> disch_tac >> drule_all lift_scope_function_certificate
  >> disch_then (assume_tac o SRULE [namespaceTheory.nsBindList_def])
  >> have ‘lift_runtime_rel (Closure source arg body)
         (Closure body_env arg compiled_body)’
  >- (irule lift_runtime_rel_function_closure >> first_assum ACCEPT_TAC)
  >> qx_genl_tac [‘s’,‘s'’,‘target’] >> strip_tac
  >> qpat_x_assum ‘∀target. _’ (drule_then (qspec_then ‘s'’ SUBST1_TAC))
  >> simp [cj 8 evaluate_def,lift_eval_refinement_def,lift_eval_result_rel_def,
           lift_result_rel_def]
QED

Theorem lift_exp_sim_let[local]:
  lift_exp_sim (:'ffi) clock D rhs ∧ lift_exp_sim (:'ffi) clock D body ⇒
  lift_exp_sim (:'ffi) clock D (Let name_option rhs body)
Proof
  strip_tac >> rewrite_tac [lift_exp_sim_def]
  >> namedCases_on ‘name_option’ ["","name"]
  >- (
    rpt gen_tac >> disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th))
    >> namedCases_on ‘annotate_exp [] rhs’ ["t1 l1 c1"]
    >> namedCases_on ‘annotate_exp [] body’ ["t2 l2 c2"] >> qpat_x_assum ‘_ ∨ _’ mp_tac
    >> gvs [annotate_exp_def,cj 1 lift_exp_def] >> strip_tac
    >> drule (cj 3 lower_exp_exps) >> strip_tac >> gvs []
    >> gvs [exp_names_def,no_Open_thm,check_exp_constructors_def]
    >> ‘∀e. MEM e [rhs;body] ⇒ lift_exp_sim (:'ffi) clock D e’ by simp [DISJ_IMP_THM]
    >> drule_at (Pos last) lift_exps_sim
    >> disch_then (qspecl_then [‘clock’,‘D’,‘[rhs;body]’,‘MAX l1 l2’,
         ‘FUNION c1 c2’,‘base’,‘initial’] mp_tac)
    >> impl_tac >- (simp [annotate_exp_def,exp_names_def] >> metis_tac [])
    >> disch_then (qx_choose_then ‘final’ strip_assume_tac)
    >> qexists_tac ‘final’ >> asm_rewrite_tac [] >> qx_genl_tac [‘source’,‘locals’] >> strip_tac
    >> first_x_assum drule >> strip_tac >> simp [] >> rpt strip_tac
    >> first_x_assum (qspec_then ‘target’ mp_tac)
    >> impl_tac >- (
      simp [] >> rw [] >> first_x_assum irule
      >> rw [] >> gvs [exp_free_names_def] >> metis_tac [])
    >> rw []
    >> irule lift_evaluate_let_refinement >> simp [namespaceTheory.nsOptBind_def]
    >> rw [] >> first_x_assum irule >> simp [])
  >- (
    qx_genl_tac [‘tree’,‘limit’,‘captures’,‘mode’,‘bound’,‘ren’,‘n’,‘ds’,‘used’,
         ‘compiled’,‘out_n’,‘out_ds’,‘out_used’,‘base’,‘initial’]
    >> disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th))
    >> qpat_x_assum ‘annotate_exp [] (Let (SOME name) _ _) = _’
      (mp_tac o SRULE [annotate_exp_def])
    >> namedCases_on ‘annotate_exp [] rhs’ ["rhs_tree rhs_limit rhs_captures"]
    >> namedCases_on ‘annotate_exp [] body’ ["body_tree body_limit body_captures"]
    >> strip_tac
    >> qpat_x_assum ‘lower_exp _ _ _ _ _ = _ ∨ lift_exp _ _ _ _ _ = _’ mp_tac
    >> gvs [cj 1 lift_exp_def] >> strip_tac >> fs [cj 1 lift_exp_def,cj 9 lift_exp_def]
    >> gvs [exp_names_def,no_Open_thm,check_exp_constructors_def]
    >> ‘MAX rhs_limit body_limit ≤ n’ by metis_tac [bump_le,LESS_EQ_TRANS]
    >> ‘rhs_limit ≤ n ∧ body_limit ≤ n’ by fs []
    >> have ‘bump name 0 ≤ n’
    >- (
      irule LESS_EQ_TRANS
      >> qexists_tac ‘bump name (MAX rhs_limit body_limit)’
      >> simp [bump_mono])
    >> Cases_on ‘mode ≠ KeepValue ∧ is_Fun (tree_exp rhs_tree) ∧
         maps_disjoint (tree_fvs rhs_tree) bound’
    >- (
      qpat_x_assum ‘mode ≠ KeepValue ∧ is_Fun (tree_exp rhs_tree) ∧
           maps_disjoint (tree_fvs rhs_tree) bound’ (fn hoisted =>
             fs [hoisted] >> MAP_EVERY assume_tac (CONJUNCTS hoisted))
      >> namedCases_on ‘lower_exp mode bound ren (n,ds,used) rhs_tree’
           ["compiled_rhs middle_n middle_ds middle_used"]
      >> gvs []
      >> namedCases_on ‘choose_name bound name (middle_n,middle_ds,middle_used)’
           ["renamed chosen_n chosen_ds chosen_used"]
      >> gvs []
      >> namedCases_on ‘emit_dec (Dlet NoLocs (Pvar renamed) compiled_rhs)
           (chosen_n,chosen_ds,chosen_used)’
           ["emitted_n emitted_ds emitted_used"]
      >> gvs []
      >> drule_all (cj 1 (SRULE [LEFT_AND_OVER_OR,DISJ_IMP_THM] lift_annotated_state_properties))
      >> strip_tac >> ‘n ≤ middle_n’ by fs [lift_state_extends_def]
      >> ‘body_limit ≤ middle_n ∧ bump name 0 ≤ middle_n’ by decide_tac
      >> have ‘∀original mapped.
           FLOOKUP ren original = SOME mapped ∧ mapped ≠ original ⇒
           mapped ∉ exp_names rhs’
      >- (
        qx_genl_tac [‘original’,‘mapped’] >> strip_tac
        >> qpat_assum ‘∀original renamed. FLOOKUP ren original = SOME renamed ∧ _ ⇒ _’
          (qspecl_then [‘original’,‘mapped’] mp_tac)
        >> simp [])
      >> drule_all (cj 1 lift_exp_sim_routes)
      >> disch_then (qx_choose_then ‘rhs_env’ strip_assume_tac)
      >> drule_all lower_annotated_function_shape
      >> disch_then (qx_choosel_then [‘rhs_arg’,‘rhs_body’,‘compiled_rhs_body’]
           (fn th => MAP_EVERY assume_tac (CONJUNCTS th)))
      >> qpat_assum ‘annotate_exp [] rhs = _’
        (mp_then (Pos hd) mp_tac annotate_exp_reannotate)
      >> simp [] >> disch_tac >> namedCases_on ‘annotate_exp [] rhs_body’
           ["function_tree function_limit function_captures"]
      >> gvs [Once annotate_exp_def,tree_exp_def,tree_fvs_def,lower_function_body]
      >> have ‘source_dce$no_Open rhs_body ∧ check_exp_constructors base.c rhs_body ∧
           exp_names rhs = rhs_arg INSERT exp_names rhs_body’
      >- (
        qpat_assum ‘annotate_exp [] rhs = _’
          (mp_then (Pos hd) mp_tac annotate_exp_tree_properties)
        >> simp [tree_exp_def,no_Open_thm,check_exp_constructors_def,exp_names_def])
      >> have ‘lift_function_body bound ren (n,ds,used) rhs_arg function_tree =
           (compiled_rhs_body,middle_n,middle_ds,middle_used)’
      >- (
        namedCases_on ‘lift_function_body bound ren (n,ds,used) rhs_arg function_tree’
          ["lowered_body lowered_n lowered_ds lowered_used"]
        >> gvs [])
      >> ‘function_limit ≤ n’ by metis_tac [bump_le,LESS_EQ_TRANS]
      >> have ‘bump rhs_arg 0 ≤ n’
      >- (
        irule LESS_EQ_TRANS
        >> qexists_tac ‘bump rhs_arg function_limit’
        >> simp [bump_mono])
      >> have ‘∀original mapped.
           FLOOKUP ren original = SOME mapped ∧ mapped ≠ original ⇒
           mapped ∉ exp_names rhs_body ∧ mapped ≠ rhs_arg’
      >- (
        qx_genl_tac [‘original’,‘mapped’] >> strip_tac
        >> qpat_assum ‘∀original renamed. _ ⇒ renamed ∉ exp_names rhs’
          (qspecl_then [‘original’,‘mapped’] mp_tac)
        >> simp [])
      >> qpat_assum ‘annotate_exp [] rhs_body = _’
        (mp_then (Pos hd) drule (cj 1 annotate_constructors))
      >> disch_tac >> drule_all lift_function_body_constructors >> disch_tac
      >> qpat_assum ‘lift_global_decs _ base rhs_env’
        (assume_tac o MATCH_MP lift_global_decs_constructors)
      >> ‘bump name 0 ≤ middle_n’ by decide_tac
      >> drule_all choose_name_state_fresh >> strip_tac
      >> have ‘∀k. middle_n ≤ k ⇒ FLOOKUP middle_used (make_name k) = NONE’
      >- fs [lift_state_fresh_def]
      >> drule_all choose_name_fresh >> strip_tac >> rveq
      >> ‘emitted_n = chosen_n ∧ emitted_used = middle_used |+ (name,()) |+ (renamed,())’
        by fs [emit_dec_def]
      >> rveq
      >> ‘lift_pure_value rhs_env (Fun rhs_arg compiled_rhs_body)
            (Closure rhs_env rhs_arg compiled_rhs_body) ∧
          check_exp_constructors rhs_env.c (Fun rhs_arg compiled_rhs_body)’
        by simp [lift_pure_value_rules,check_exp_constructors_def]
      >> drule_all emit_let_global_decs >> disch_tac
      >> ‘lift_state_extends (middle_n,chosen_ds,middle_used)
            (chosen_n,emitted_ds,middle_used |+ (name,()) |+ (renamed,())) ∧
          lift_state_decs_avoid (middle_n,chosen_ds,middle_used)
            (chosen_n,emitted_ds,middle_used |+ (name,()) |+ (renamed,()))’
        by gvs [emit_dec_def,lift_state_extends_def,lift_state_decs_avoid_def,
             lift_decs_avoid_list_cases,SUBSET_DEF,FLOOKUP_DEF]
      >> qabbrev_tac ‘body_global = rhs_env with v := nsBind renamed
           (Closure rhs_env rhs_arg compiled_rhs_body) rhs_env.v’
      >> have ‘∀original mapped.
           FLOOKUP (ren |+ (name,renamed)) original = SOME mapped ∧ mapped ≠ original ⇒
           mapped ∉ exp_names body’
      >- (
        qpat_assum ‘annotate_exp [] body = _’
          (mp_then (Pos hd) mp_tac (cj 1 annotate_all_name_bound))
        >> simp [] >> disch_tac
        >> have ‘∀body_name. body_name ∈ exp_names body ⇒ make_name middle_n ≠ body_name’
        >- metis_tac [bump_make_name,LESS_EQ_TRANS]
        >> qx_genl_tac [‘original’,‘mapped’] >> strip_tac >> Cases_on ‘original = name’
        >- (
          qpat_x_assum ‘choose_name _ _ _ = _’ (mp_tac o REWRITE_RULE [choose_name_def])
          >> rw [AllCaseEqs()] >> gvs [FLOOKUP_UPDATE]
          >> metis_tac [])
        >> fs [FLOOKUP_UPDATE]
        >> qpat_assum ‘∀original mapped. FLOOKUP ren original = SOME mapped ∧ _ ⇒
             _ ∧ _ ∧ mapped ∉ exp_names body’
          (qspecl_then [‘original’,‘mapped’] mp_tac)
        >> simp [])
      >> ‘body_limit ≤ chosen_n’ by decide_tac
      >> ‘lift_state_fresh (chosen_n,emitted_ds,middle_used |+ (name,()) |+ (renamed,()))’
        by fs [lift_state_fresh_def]
      >> drule_all lift_exp_sim_lift >> disch_then (qx_choose_then ‘final’ strip_assume_tac)
      >> drule_all lift_annotated_state_properties_lift >> strip_tac
      >> ‘lift_state_extends (middle_n,chosen_ds,middle_used) (out_n,out_ds,out_used) ∧
          lift_state_decs_avoid (middle_n,chosen_ds,middle_used) (out_n,out_ds,out_used)’
        by metis_tac [lift_state_extends_trans,lift_state_decs_avoid_trans]
      >> qexists_tac ‘final’ >> asm_rewrite_tac [] >> qx_genl_tac [‘source’,‘locals’] >> strip_tac
      >> qpat_assum ‘lift_scope _ _ bound ren (n,ds,used) source initial locals’
        (mp_then (Pos hd) drule_all lift_scope_decs_avoid)
      >> disch_tac
      >> have ‘lift_scope lift_runtime_rel (fdomsub function_captures rhs_arg) bound ren
           (n,ds,used) source initial locals’
      >- (
        irule lift_scope_domain_subset
        >> qexists_tac ‘FUNION (fdomsub function_captures rhs_arg)
             (fdomsub body_captures name)’
        >> simp [FDOM_FUNION])
      >> qpat_assum ‘lift_scope _ _ _ _ _ source initial _’
        (assume_tac o MATCH_MP lift_scope_constructors)
      >> qpat_assum ‘lift_global_decs _ base initial’
        (assume_tac o MATCH_MP lift_global_decs_constructors)
      >> ‘check_exp_constructors source.c rhs_body’ by gvs []
      >> qpat_assum ‘lift_scope _ (fdomsub function_captures rhs_arg) bound ren
           (n,ds,used) source initial locals’
        (mp_then (Pos hd) mp_tac lift_scope_closed)
      >> simp [] >> disch_tac
      >> drule_all (SRULE [] lift_scope_function_certificate)
      >> disch_then (assume_tac o SRULE [namespaceTheory.nsBindList_def])
      >> have ‘lift_runtime_rel (Closure source rhs_arg rhs_body)
           (Closure rhs_env rhs_arg compiled_rhs_body)’
      >- (irule lift_runtime_rel_function_closure >> first_assum ACCEPT_TAC)
      >> have ‘lift_scope lift_runtime_rel (fdomsub body_captures name) bound ren
           (middle_n,chosen_ds,middle_used) source rhs_env locals’
      >- (
        irule lift_scope_domain_subset
        >> qexists_tac ‘FUNION (fdomsub function_captures rhs_arg)
             (fdomsub body_captures name)’
        >> simp [FDOM_FUNION])
      >> qpat_assum ‘lift_scope _ _ _ ren (_,_,middle_used) _ _ _’
        (assume_tac o CONJUNCT1 o REWRITE_RULE [lift_scope_def])
      >> drule_all choose_name_renaming_wf >> disch_tac
      >> qpat_assum ‘lift_scope _ (fdomsub body_captures name) bound ren
           (middle_n,chosen_ds,middle_used) source rhs_env locals’
        (mp_then (Pos hd) mp_tac lift_scope_choose_name)
      >> disch_then (qspecl_then
           [‘(chosen_n,chosen_ds,middle_used |+ (name,()) |+ (renamed,()))’,
            ‘renamed’,‘name’] mp_tac)
      >> simp [FDOM_DOMSUB] >> strip_tac
      >> have ‘lift_scope lift_runtime_rel (fdomsub body_captures name)
           (fdomsub bound name) ren
           (chosen_n,chosen_ds,middle_used |+ (name,()) |+ (renamed,()))
           source rhs_env locals’
      >- (
        irule (SRULE [delete_all_def]
          (Q.INST [‘names’ |-> ‘[name]’] (SPEC_ALL lift_scope_discard_reserved_bindings)))
        >> simp [FDOM_DOMSUB] >> qexistsl_tac [‘chosen_ds’,‘middle_n’,‘middle_used’]
        >> simp [SUBSET_DEF])
      >> have ‘lift_scope lift_runtime_rel body_captures (fdomsub bound name)
           (ren |+ (name,renamed))
           (chosen_n,emitted_ds,middle_used |+ (name,()) |+ (renamed,()))
           (source with v := nsBind name (Closure source rhs_arg rhs_body) source.v)
           body_global locals’
      >- (
        simp [Abbr ‘body_global’]
        >> irule lift_scope_rename_global_binding >> fs [lift_state_fresh_def]
        >> qexistsl_tac [‘chosen_ds’,‘chosen_n’,
             ‘middle_used |+ (name,()) |+ (renamed,())’]
        >> simp [SUBSET_DEF])
      >> qpat_x_assum ‘∀source locals. lift_scope _ body_captures _ _ _ _ _ _ ⇒ _’ drule
      >> strip_tac
      >> qpat_assum ‘lift_scope _ (FUNION _ _) bound ren (middle_n,chosen_ds,middle_used)
           source rhs_env locals’
        (mp_then (Pos hd) drule_all lift_scope_decs_avoid)
      >> disch_tac >> asm_rewrite_tac []
      >> qx_genl_tac [‘s’,‘s'’,‘target’] >> strip_tac
      >> qpat_assum ‘annotate_exp [] rhs = _’
        (mp_then (Pos hd) mp_tac annotate_exp_evaluate)
      >> disch_then (qspecl_then [‘s’,‘source’] mp_tac)
      >> simp [tree_exp_def,cj 8 evaluate_def] >> disch_then (assume_tac o SYM)
      >> drule evaluate_let_known_value
      >> disch_then (qspecl_then [‘name’,‘body’] SUBST1_TAC)
      >> qpat_assum ‘∀s s' target. _ ⇒ lift_eval_refinement _ _ _
           (evaluate _ (source with v := nsBind name _ source.v) [body]) _’ irule
      >> simp [])
    >- (
      qpat_x_assum ‘¬(mode ≠ KeepValue ∧ is_Fun (tree_exp rhs_tree) ∧
           maps_disjoint (tree_fvs rhs_tree) bound)’ (fs o single)
      >> namedCases_on ‘lift_exp mode bound ren (n,ds,used) rhs_tree’
           ["compiled_rhs middle_n middle_ds middle_used"]
      >> gvs []
      >> namedCases_on ‘lift_exp mode (bound |+ (name,())) (fdomsub ren name)
           (middle_n,middle_ds,middle_used) body_tree’
           ["compiled_body final_n final_ds final_used"]
      >> gvs []
      >> have ‘bump name body_limit ≤ n’
      >- (
        irule LESS_EQ_TRANS >> qexists_tac ‘bump name (MAX rhs_limit body_limit)’
        >> simp [bump_mono])
      >> have ‘annotate_pes [] [(Pvar name,body)] =
            ([body_tree],bump name body_limit,fdomsub body_captures name)’
      >- simp [annotate_exp_def,bump_pat_def,pat_bindings_def,delete_all_def,str_empty_def]
      >> have ‘lift_pes mode bound ren (middle_n,middle_ds,middle_used)
            (MAP FST [(Pvar name,body)]) [body_tree] =
            ([(Pvar name,compiled_body)],final_n,final_ds,final_used)’
      >- simp [cj 38 lift_exp_def,cj 40 lift_exp_def,pat_bindings_def,bind_all_def,
              delete_all_def]
      >> drule_at (Pos last) lift_exp_pes_sim
      >> disch_then (qspecl_then [‘clock’,‘D’,‘rhs’,‘rhs_tree’,‘rhs_limit’,‘rhs_captures’,
           ‘bump name body_limit’,‘fdomsub body_captures name’,‘n’,‘ds’,‘used’,
           ‘initial’,‘base’,‘compiled_rhs’] mp_tac)
      >> impl_tac >- (
        rw [exp_names_def,pat_bindings_def,DISJ_IMP_THM]
        >> qpat_x_assum ‘∀name' renamed. FLOOKUP ren _ = _ ∧ _ ⇒ _’ drule_all >> simp [])
      >> disch_then (qx_choose_then ‘final’ strip_assume_tac)
      >> qexists_tac ‘final’ >> asm_rewrite_tac [] >> qx_genl_tac [‘source’,‘locals’] >> strip_tac
      >> first_x_assum drule >> strip_tac >> simp [] >> rpt strip_tac
      >> first_x_assum (qspec_then ‘target’ mp_tac)
      >> impl_tac >- (
        rw [] >> first_x_assum irule
        >> rw [] >> gvs [exp_free_names_def,pat_bindings_def] >> metis_tac [])
      >> rw []
      >> irule lift_evaluate_let_refinement >> simp [namespaceTheory.nsOptBind_def]
      >> rw [] >> qpat_x_assum ‘∀state state' bindings bindings'. _’
           (qspecl_then [‘t’,‘t'’,‘[(name,value)]’,‘[(name,value')]’] mp_tac)
      >> simp [nsBindList_clauses,pat_bindings_def]))
QED

Theorem lift_exp_sim_thm[local]:
  lift_app_sim (:'ffi) clock D ⇒ ∀e. lift_exp_sim (:'ffi) clock D e
Proof
  strip_tac
  >> ho_match_mp_tac (SRULE []
       (Q.SPEC ‘λ(p:exp -> bool) (e:exp). P e’ every_exp_ind))
  >> rpt conj_tac >> rpt gen_tac
  >~ [‘Tannot _ _’] >- (
    rewrite_tac [lift_exp_sim_def]
    >> simp [annotate_exp_def,cj 15 evaluate_def,exp_names_def,no_Open_thm,
         check_exp_constructors_def])
  >~ [‘Lannot _ _’] >- (
    rewrite_tac [lift_exp_sim_def]
    >> simp [annotate_exp_def,cj 16 evaluate_def,exp_names_def,no_Open_thm,
         check_exp_constructors_def])
  >~ [‘Open _ _’] >- simp [lift_exp_sim_def,no_Open_thm]
  >> metis_tac [lift_exp_sim_raise,lift_exp_sim_handle_mat,lift_exp_sim_lit,lift_exp_sim_con,
       lift_exp_sim_var,lift_exp_sim_fun,lift_exp_sim_app,lift_exp_sim_log,lift_exp_sim_if,
       lift_exp_sim_let,lift_exp_sim_letrec]
QED

Theorem lift_exp_simulation[local] = REWRITE_RULE [lift_exp_sim_def] lift_exp_sim_thm

Theorem lift_scope_initial[local]:
  lift_runtime_env R source target ∧ FDOM captures ⊆ FDOM used ∧
  (∀name. name ∈ FDOM captures ⇒ bump name 0 ≤ n) ⇒
  lift_scope R captures FEMPTY FEMPTY (n,[],used) source target []
Proof
  rw [lift_scope_def,lift_renaming_wf_def,lift_env_rel_def,lift_runtime_env_def,
       rename_var_empty,nsBindList_clauses,SUBSET_DEF]
  >> metis_tac [bump_make_name,LESS_EQ_TRANS]
QED

Theorem initial_let_scope[local]:
  annotate_exp t e = (tree,n,captures) ∧ lift_runtime_env R source target ⇒
  lift_scope R captures FEMPTY FEMPTY
    (bump_pat n p,[],bind_all (pat_bindings p) captures) source target []
Proof
  strip_tac
  >> irule lift_scope_initial >> simp [bind_all_domain,SUBSET_DEF]
  >> metis_tac [cj 1 annotate_free_name_bound,cj 1 bump_patterns_le,LESS_EQ_TRANS]
QED

Theorem initial_letrec_scope[local]:
  annotate_funs t funs = (trees,n,captures) ∧ lift_runtime_env R source target ⇒
  lift_scope R captures FEMPTY FEMPTY
    (n,[],bind_all (MAP FST funs) captures) source target []
Proof
  strip_tac
  >> irule lift_scope_initial >> simp [bind_all_domain,SUBSET_DEF]
  >> metis_tac [cj 4 annotate_free_name_bound]
QED

Theorem lower_let_simulation[local]:
  lift_app_sim (:'ffi) clock D ⇒
  ∀e pattern tree n captures compiled out_n ds used source target.
    annotate_exp [] e = (tree,n,captures) ∧ source_dce$no_Open e ∧
    check_exp_constructors source.c e ∧ lift_runtime_env lift_runtime_rel source target ∧
    lower_exp KeepValue str_empty FEMPTY
      (bump_pat n pattern,[],bind_all (pat_bindings pattern) captures) tree =
      (compiled,out_n,ds,used) ⇒
    ∃final.
      lift_global_decs (REVERSE ds) target final ∧
      ∀(s:'ffi semanticPrimitives$state) s'.
        s.clock ≤ clock ∧ lift_state_rel lift_runtime_rel D s s' ⇒
        lift_eval_refinement lift_runtime_rel D (LIST_REL lift_runtime_rel)
          (evaluate s source [e]) (evaluate s' final [compiled])
Proof
  strip_tac
  >> qx_genl_tac [‘e’,‘pattern’,‘tree’,‘n’,‘captures’,‘compiled’,‘out_n’,‘ds’,‘used’,
       ‘source’,‘target’]
  >> strip_tac >> drule_all initial_let_state_fresh >> disch_tac
  >> drule_all initial_let_scope >> disch_tac
  >> qpat_assum ‘lift_app_sim _ _ _’ (mp_tac o MATCH_MP lift_exp_simulation)
  >> disch_then (qspecl_then [‘e’,‘tree’,‘n’,‘captures’,‘KeepValue’,
       ‘str_empty’,‘FEMPTY:mlstring |-> mlstring’,‘bump_pat n pattern’,
       ‘[]:dec list’,‘bind_all (pat_bindings pattern) captures’,
       ‘compiled’,‘out_n’,‘ds’,‘used’,‘target’,‘target’] mp_tac)
  >> impl_tac
  >- (
    fs [str_empty_def,lift_global_decs_rules,lift_runtime_env_def]
    >> metis_tac [cj 1 bump_patterns_le])
  >> disch_then (qx_choose_then ‘final’ strip_assume_tac)
  >> qexists_tac ‘final’ >> asm_rewrite_tac []
  >> qpat_x_assum ‘∀source locals. _’ (qspecl_then [‘source’,‘[]’] mp_tac)
  >> impl_tac >- fs [str_empty_def]
  >> strip_tac >> qx_genl_tac [‘s’,‘s'’] >> strip_tac
  >> qpat_x_assum ‘∀s s' target. _ ⇒ lift_eval_refinement _ _ _
       (evaluate s source [e]) _’
    (qspecl_then [‘s’,‘s'’,‘final’] match_mp_tac)
  >> simp [nsBindList_clauses]
QED

Theorem lift_evaluate_app_refinement[local]:
  lift_eval_result_rel (lift_value_rel C E) D (LIST_REL (lift_value_rel C E))
    (evaluate (s:'ffi semanticPrimitives$state) env (REVERSE es))
    (evaluate s' env' (REVERSE es')) ∧
  (∀f f' arg arg'. C f f' ∧ lift_value_rel C E arg arg' ⇒
    OPTREL (λ(body_env,body) (body_env',body').
      ∀(t:'ffi semanticPrimitives$state) t'.
        t.clock < s.clock ∧ lift_state_rel (lift_value_rel C E) D t t' ⇒
        lift_eval_refinement (lift_value_rel C E) D (LIST_REL (lift_value_rel C E))
          (evaluate t body_env [body]) (evaluate t' body_env' [body']))
      (do_opapp [f;arg]) (do_opapp [f';arg'])) ⇒
  lift_eval_refinement (lift_value_rel C E) D (LIST_REL (lift_value_rel C E))
    (evaluate s env [App Opapp es]) (evaluate s' env' [App Opapp es'])
Proof
  strip_tac
  >> simp_tac (srw_ss()) [lift_eval_refinement_def]
  >> namedCases_on ‘evaluate s env (REVERSE es)’ ["source_state source_result"]
  >> ‘source_state.clock ≤ s.clock’ by metis_tac [cj 1 evaluate_clock]
  >> namedCases_on ‘evaluate s' env' (REVERSE es')’ ["target_state target_result"]
  >> namedCases_on ‘source_result’ ["source_values","source_error"]
  >> namedCases_on ‘target_result’ ["target_values","target_error"]
  >> gvs [evaluate_def,lift_eval_result_rel_def,lift_result_rel_def]
  >> drule LIST_REL_REVERSE >> strip_tac >> drule_all lift_value_rel_opapp >> strip_tac
  >> namedCases_on ‘do_opapp (REVERSE source_values)’ ["","source_body_pair"]
  >> namedCases_on ‘do_opapp (REVERSE target_values)’ ["","target_body_pair"]
  >> gvs [lift_eval_result_rel_def,lift_result_rel_def]
  >> namedCases_on ‘source_body_pair’ ["source_body_env source_body"]
  >> namedCases_on ‘target_body_pair’ ["target_body_env target_body"] >> gvs []
  >> ‘source_state.clock = target_state.clock’ by fs [lift_state_rel_def]
  >> have ‘lift_state_rel (lift_value_rel C E) D
        (dec_clock source_state) (dec_clock target_state)’
  >- metis_tac [lift_state_rel_dec_clock]
  >> simp [] >> IF_CASES_TAC >> gvs [lift_eval_result_rel_def,lift_result_rel_def]
  >> rewrite_tac [GSYM lift_eval_refinement_def]
  >> qpat_x_assum ‘∀t t'. t.clock < s.clock ∧ _ ⇒ _’ irule
  >> simp [dec_clock_def] >> decide_tac
QED

Theorem lift_evaluate_force_refinement[local]:
  lift_eval_result_rel (lift_value_rel C E) D (LIST_REL (lift_value_rel C E))
    (evaluate (s:'ffi semanticPrimitives$state) env (REVERSE es))
    (evaluate s' env' (REVERSE es')) ∧
  (∀f f' arg arg'. C f f' ∧ lift_value_rel C E arg arg' ⇒
    OPTREL (λ(body_env,body) (body_env',body').
      ∀(t:'ffi semanticPrimitives$state) t'.
        t.clock < s.clock ∧ lift_state_rel (lift_value_rel C E) D t t' ⇒
        lift_eval_refinement (lift_value_rel C E) D (LIST_REL (lift_value_rel C E))
          (evaluate t body_env [body]) (evaluate t' body_env' [body']))
      (do_opapp [f;arg]) (do_opapp [f';arg'])) ⇒
  lift_eval_refinement (lift_value_rel C E) D (LIST_REL (lift_value_rel C E))
    (evaluate s env [App (ThunkOp ForceThunk) es]) (evaluate s' env' [App (ThunkOp ForceThunk) es'])
Proof
  strip_tac
  >> simp_tac (srw_ss()) [lift_eval_refinement_def]
  >> namedCases_on ‘evaluate s env (REVERSE es)’ ["source_state source_result"]
  >> ‘source_state.clock ≤ s.clock’ by metis_tac [cj 1 evaluate_clock]
  >> namedCases_on ‘evaluate s' env' (REVERSE es')’ ["target_state target_result"]
  >> namedCases_on ‘source_result’ ["source_values","source_error"]
  >> namedCases_on ‘target_result’ ["target_values","target_error"]
  >> gvs [evaluate_def,lift_eval_result_rel_def,lift_result_rel_def]
  >> have ‘lift_thunk_result_rel (lift_value_rel C E)
        (dest_thunk (REVERSE source_values) source_state.refs)
        (dest_thunk (REVERSE target_values) target_state.refs)’
  >- (irule lift_value_rel_dest_thunk >> fs [lift_state_rel_def,LIST_REL_REVERSE])
  >> namedCases_on ‘dest_thunk (REVERSE source_values) source_state.refs’
       ["","","source_mode source_thunk"]
  >> namedCases_on ‘dest_thunk (REVERSE target_values) target_state.refs’
       ["","","target_mode target_thunk"]
  >> gvs [lift_thunk_result_rel_def,lift_eval_result_rel_def,lift_result_rel_def]
  >> Cases_on ‘source_mode’ >> gvs [lift_eval_result_rel_def,lift_result_rel_def]
  >> have ‘LIST_REL (lift_value_rel C E)
        [source_thunk; Conv NONE []] [target_thunk; Conv NONE []]’
  >- simp [lift_value_rel_cases_l]
  >> drule_all lift_value_rel_opapp >> strip_tac
  >> namedCases_on ‘do_opapp [source_thunk; Conv NONE []]’ ["","source_body_pair"]
  >> namedCases_on ‘do_opapp [target_thunk; Conv NONE []]’ ["","target_body_pair"]
  >> gvs [lift_eval_result_rel_def,lift_result_rel_def]
  >> namedCases_on ‘source_body_pair’ ["source_body_env source_body"]
  >> namedCases_on ‘target_body_pair’ ["target_body_env target_body"] >> gvs []
  >> ‘source_state.clock = target_state.clock’ by fs [lift_state_rel_def]
  >> have ‘lift_state_rel (lift_value_rel C E) D
        (dec_clock source_state) (dec_clock target_state)’
  >- metis_tac [lift_state_rel_dec_clock]
  >> simp [] >> IF_CASES_TAC
  >- gvs [lift_eval_result_rel_def,lift_result_rel_def]
  >> ‘(dec_clock source_state).clock < s.clock’ by (simp [dec_clock_def] >> decide_tac)
  >> qpat_x_assum ‘∀t t'. t.clock < s.clock ∧ _ ⇒ _’
       (qspecl_then [‘dec_clock source_state’,‘dec_clock target_state’] mp_tac)
  >> simp [] >> strip_tac
  >> namedCases_on ‘evaluate (dec_clock source_state) source_body_env [source_body]’
       ["source_return_state source_return_result"]
  >> namedCases_on ‘evaluate (dec_clock target_state) target_body_env [target_body]’
       ["target_return_state target_return_result"]
  >> namedCases_on ‘source_return_result’ ["source_return_values","source_return_error"]
  >> namedCases_on ‘target_return_result’ ["target_return_values","target_return_error"]
  >> gvs [lift_eval_refinement_def,lift_eval_result_rel_def,lift_result_rel_def]
  >> have ‘OPTREL (LIST_REL (sv_rel (lift_value_rel C E)))
        (update_thunk (REVERSE source_values) source_return_state.refs source_return_values)
        (update_thunk (REVERSE target_values) target_return_state.refs target_return_values)’
  >- (irule lift_value_rel_update_thunk >> fs [lift_state_rel_def,LIST_REL_REVERSE])
  >> namedCases_on
       ‘update_thunk (REVERSE source_values) source_return_state.refs source_return_values’
       ["","source_return_refs"]
  >> namedCases_on
       ‘update_thunk (REVERSE target_values) target_return_state.refs target_return_values’
       ["","target_return_refs"]
  >> gvs [lift_eval_result_rel_def,lift_result_rel_def,lift_state_rel_def]
QED

(* ------------------------------------------------------------------------
   Closure bodies and calls
   ------------------------------------------------------------------------ *)

Definition lift_body_refinement_def:
  lift_body_refinement D (caller:'ffi semanticPrimitives$state) source body target body' ⇔
    ∀(s:'ffi semanticPrimitives$state) s'.
      s.clock < caller.clock ∧ lift_state_rel lift_runtime_rel D s s' ⇒
      lift_eval_refinement lift_runtime_rel D (LIST_REL lift_runtime_rel)
        (evaluate s source [body]) (evaluate s' target [body'])
End

Theorem lift_evaluate_runtime_call_refinement[local]:
  (op = Opapp ∨ op = ThunkOp ForceThunk) ∧
  lift_eval_result_rel lift_runtime_rel D (LIST_REL lift_runtime_rel)
    (evaluate (s:'ffi semanticPrimitives$state) env (REVERSE es))
    (evaluate s' env' (REVERSE es')) ∧
  (∀source arg body target body' value value'.
    lift_function_certificate lift_runtime_rel source arg body target body' ∧
    lift_runtime_rel value value' ⇒
    lift_body_refinement D s (source with v := nsBind arg value source.v) body
      (target with v := nsBind arg value' target.v) body') ∧
  (∀source funs target funs' ren name name' arg body body' value value'.
    lift_rec_certificate lift_runtime_rel source funs target funs' ren ∧
    rename_var ren (Short name) = (Short name':(mlstring,mlstring) id) ∧
    find_recfun name funs = SOME (arg,body) ∧
    find_recfun name' funs' = SOME (arg,body') ∧ lift_runtime_rel value value' ⇒
    lift_body_refinement D s
      (source with v := nsBind arg value (build_rec_env funs source source.v)) body
      (target with v := nsBind arg value' (build_rec_env funs' target target.v)) body') ∧
  (∀source target body. lift_runtime_env lift_runtime_rel source target ⇒
    lift_body_refinement D s source body target body) ⇒
  lift_eval_refinement lift_runtime_rel D (LIST_REL lift_runtime_rel)
    (evaluate s env [App op es]) (evaluate s' env' [App op es'])
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac)
  >> mp_tac (Q.INST [‘P’ |-> ‘lift_body_refinement D (s:'ffi semanticPrimitives$state)’]
       (SPEC_ALL lift_runtime_rel_opapp))
  >> simp [] >> impl_tac
  >- (
    qpat_x_assum ‘∀source funs target funs' ren name name' arg body body' value value'. _’
      ACCEPT_TAC)
  >> strip_tac >> qpat_x_assum ‘∀values values'. _’
       (assume_tac o REWRITE_RULE [lift_body_refinement_def])
  >> qpat_x_assum ‘op = Opapp ∨ op = ThunkOp ForceThunk’ strip_assume_tac >> gvs []
  >~ [‘evaluate _ _ [App Opapp _]’] >- (
    irule (runtime_inst lift_evaluate_app_refinement)
    >> simp [] >> rpt strip_tac >> qpat_x_assum ‘∀values values'. _’ irule
    >> simp [lift_closure_certificate_runtime_rel])
  >> irule (runtime_inst lift_evaluate_force_refinement)
  >> simp [] >> rpt strip_tac >> qpat_x_assum ‘∀values values'. _’ irule
  >> simp [lift_closure_certificate_runtime_rel]
QED

Theorem lift_function_certificate_body_refinement[local]:
  lift_app_sim (:'ffi) clock D ⇒
  ∀source arg body target body' value value' (caller:'ffi semanticPrimitives$state).
    caller.clock ≤ clock + 1 ∧
    lift_function_certificate lift_runtime_rel source arg body target body' ∧
    lift_runtime_rel value value' ⇒
    lift_body_refinement D caller (source with v := nsBind arg value source.v) body
      (target with v := nsBind arg value' target.v) body'
Proof
  strip_tac
  >> qx_genl_tac [‘source’,‘arg’,‘body’,‘target’,‘body'’,‘value’,‘value'’,‘caller’]
  >> strip_tac
  >> qpat_x_assum ‘lift_function_certificate lift_runtime_rel source arg body target body'’
       (mp_tac o REWRITE_RULE [lift_function_certificate_def])
  >> disch_then (qx_choosel_then
       [‘tree’,‘limit’,‘captures’,‘bound’,‘ren’,‘n’,‘ds’,‘used’,
        ‘n1’,‘ds1’,‘used1’,‘base’,‘initial’,‘final’,‘locals’] strip_assume_tac)
  >> have ‘∀name. name ∈ FDOM captures ∧ name ≠ arg ⇒
        rename_var ren (Short name) ≠ (Short arg:(mlstring,mlstring) id)’
  >- (
    qx_gen_tac ‘name’ >> strip_tac
    >> namedCases_on ‘FLOOKUP ren name’ ["","mapped"]
    >> simp [rename_var_def] >> strip_tac
    >> qpat_x_assum ‘∀name renamed. FLOOKUP ren name = SOME renamed ∧ renamed ≠ name ⇒ _’
         (qspecl_then [‘name’,‘arg’] mp_tac)
    >> simp [])
  >> have ‘lift_scope lift_runtime_rel captures (bound |+ (arg,())) (fdomsub ren arg)
        (n,ds,used) (source with v := nsBind arg value source.v) initial
        ((arg,value')::locals)’
  >- (irule lift_scope_bind >> simp [])
  >> drule lift_function_body_routes >> disch_tac
  >> have ‘∀name renamed. FLOOKUP (fdomsub ren arg) name = SOME renamed ∧ renamed ≠ name ⇒
        renamed ∉ exp_names body’
  >- (
    simp_tac (srw_ss()) [DOMSUB_FLOOKUP_THM] >> rpt strip_tac
    >> qpat_x_assum ‘∀name renamed. FLOOKUP ren name = SOME renamed ∧ renamed ≠ name ⇒ _’
         (qspecl_then [‘name’,‘renamed’] mp_tac)
    >> simp [])
  >> ‘source.c = initial.c’ by fs [lift_scope_def,lift_env_rel_def]
  >> qpat_assum ‘lift_global_decs _ base initial’
       (assume_tac o MATCH_MP lift_global_decs_constructors)
  >> ‘check_exp_constructors base.c body’ by gvs []
  >> qpat_assum ‘lift_app_sim _ _ _’ (drule_all o SRULE [] o MATCH_MP lift_exp_simulation)
  >> disch_then (qx_choose_then ‘actual_final’ strip_assume_tac)
  >> ‘actual_final = final’ by metis_tac [lift_global_decs_deterministic]
  >> qpat_x_assum ‘actual_final = final’ SUBST_ALL_TAC
  >> qpat_x_assum ‘∀source locals. lift_scope _ _ _ _ _ _ _ _ ⇒ _’ drule >> strip_tac
  >> rewrite_tac [lift_body_refinement_def] >> qx_genl_tac [‘s’,‘s'’] >> strip_tac
  >> ‘s.clock ≤ clock’ by decide_tac
  >> qpat_x_assum ‘∀s s' target. _ ⇒ lift_eval_refinement _ _ _
       (evaluate s (source with v := nsBind arg value source.v) [body]) _’
    (qspecl_then [‘s’,‘s'’,‘target with v := nsBind arg value' target.v’] match_mp_tac)
  >> simp [nsBindList_clauses]
  >> match_mp_tac (SRULE [nsBindList_clauses] (Q.INST
    [‘bindings’ |-> ‘[(arg,value')]’,‘names’ |-> ‘[arg]’,
     ‘fvs’ |-> ‘exp_free_names body'’,‘globals’ |-> ‘target.v’,
     ‘globals'’ |-> ‘nsBindList locals final.v’] (SPEC_ALL lift_bound_lookup)))
  >> simp [DELETE_DEF]
QED

Theorem lift_scope_renamed_local_bindings[local]:
  lift_scope R (delete_all names captures) bound ren (n,ds,used) source global locals ∧
  MAP FST bindings = names ∧ MAP FST bindings' = names' ∧
  lift_env_rel R captures ren (source with v := nsBindList bindings source.v)
    (global with v := nsBindList (bindings' ++ locals) global.v) ∧
  (∀mapped. MEM mapped names' ⇒
    ∃original. MEM original names ∧
      rename_var ren (Short original) = (Short mapped:(mlstring,mlstring) id)) ∧
  (∀name mapped. name ∈ FDOM captures ∧
    rename_var ren (Short name) = (Short mapped:(mlstring,mlstring) id) ⇒
    (MEM name names ⇔ MEM mapped names')) ∧
  (∀name k. MEM name names' ∧ n ≤ k ⇒ name ≠ make_name k) ⇒
  lift_scope R captures (bind_all names bound) ren (n,ds,used)
    (source with v := nsBindList bindings source.v) global (bindings' ++ locals)
Proof
  strip_tac
  >> fs [lift_scope_def,delete_all_domain,bind_all_domain,MEM_APPEND,ALOOKUP_APPEND]
  >> rpt conj_tac
  >- (
    qpat_x_assum ‘lift_env_rel R (DRESTRICT (delete_all names captures)
        (COMPL (FDOM bound))) ren source global’
      (strip_assume_tac o SRULE
        [lift_env_rel_def,delete_all_domain,FDOM_DRESTRICT])
    >> simp [lift_env_rel_def,FDOM_DRESTRICT,nsBindList_long_lookup]
    >> qx_gen_tac ‘lookup_name’ >> strip_tac
    >> ‘ALOOKUP bindings lookup_name = NONE’ by metis_tac [ALOOKUP_NONE]
    >> simp [nsBindList_short_lookup]
    >> qpat_x_assum ‘∀x. _ ⇒ OPTREL R _ _’ (qspec_then ‘lookup_name’ mp_tac)
    >> simp [])
  >- (rpt strip_tac >> metis_tac [MEM_MAP,FST])
  >- (
    qx_genl_tac [‘name’,‘renamed’] >> strip_tac
    >> namedCases_on ‘ALOOKUP bindings' renamed’ ["","local_value"] >> simp []
    >> metis_tac [ALOOKUP_NONE])
  >- (rpt strip_tac >> metis_tac [])
  >> qx_gen_tac ‘k’ >> strip_tac
  >> ‘ALOOKUP bindings' (make_name k) = NONE’ by metis_tac [ALOOKUP_NONE] >> simp []
QED

Theorem lift_scope_rec_bindings[local]:
  lift_rec_certificate lift_runtime_rel source funs target funs' ren ∧
  annotate_funs [] funs = (trees,limit,captures) ∧
  lift_scope lift_runtime_rel (delete_all (MAP FST funs) captures) bound ren
    (n,ds,used) source global locals ∧
  (∀name k. MEM name (MAP FST funs') ∧ n ≤ k ⇒ name ≠ make_name k) ⇒
  lift_scope lift_runtime_rel captures (bind_all (MAP FST funs) bound) ren
    (n,ds,used) (source with v := build_rec_env funs source source.v) global
    (MAP (λname. (name,Recclosure target funs' name)) (MAP FST funs') ++ locals)
Proof
  strip_tac
  >> drule lift_scope_env_rel >> disch_tac >> drule_all lift_rec_certificate_capture_env
  >> disch_tac
  >> qpat_assum ‘lift_env_rel _ captures ren
       (source with v := build_rec_env funs source source.v) _’
    (assume_tac o SRULE [build_rec_env_nsBindList_names])
  >> qpat_x_assum ‘lift_rec_certificate lift_runtime_rel source funs target funs' ren’
       (mp_tac o REWRITE_RULE [lift_rec_certificate_def])
  >> disch_then (qx_choosel_then [‘cert_trees’,‘cert_limit’,‘cert_captures’,
       ‘cert_bound’,‘cert_n’,‘cert_ds’,‘cert_used’,‘cert_n1’,‘cert_ds1’,‘cert_used1’,
       ‘cert_base’,‘cert_initial’,‘cert_final’,‘cert_locals’] strip_assume_tac)
  >> gvs [] >> rewrite_tac [build_rec_env_nsBindList_names]
  >> irule (Q.INST
       [‘names’ |-> ‘MAP FST (funs:(mlstring # mlstring # exp) list)’,
        ‘names'’ |-> ‘MAP FST (funs':(mlstring # mlstring # exp) list)’,
        ‘bindings’ |-> ‘MAP (λname. (name,Recclosure source funs name)) (MAP FST funs)’,
        ‘bindings'’ |-> ‘MAP (λname. (name,Recclosure target funs' name)) (MAP FST funs')’]
       (INST_TYPE [alpha |-> “:v”] (SPEC_ALL lift_scope_renamed_local_bindings)))
  >> simp [MAP_MAP_o,o_DEF,nsBindList_append] >> conj_tac
  >- (qx_gen_tac ‘mapped’ >> strip_tac >> drule_all LIST_REL_MEM_IMP_R >> simp [])
  >> simp [ETA_THM]
  >> qpat_x_assum ‘lift_env_rel _ captures ren
       (source with v := nsBindList (MAP _ _) source.v) _’
    (ACCEPT_TAC o SRULE [MAP_MAP_o,o_DEF])
QED

Theorem lift_renamed_names_fresh[local]:
  lift_renaming_wf ren used ∧ lift_state_fresh (n,ds,used) ∧
  EVERY (λname. bump name 0 ≤ n) names ∧
  LIST_REL (λname mapped.
    rename_var ren (Short name) = (Short mapped:(mlstring,mlstring) id)) names names' ⇒
  ∀mapped k. MEM mapped names' ∧ n ≤ k ⇒ mapped ≠ make_name k
Proof
  strip_tac
  >> qx_genl_tac [‘mapped’,‘k’] >> strip_tac >> drule_all LIST_REL_MEM_IMP_R
  >> disch_then (qx_choose_then ‘original’ strip_assume_tac o SRULE [])
  >> drule_all rename_var_used_or_original >> strip_tac >> fs [EVERY_MEM]
  >> metis_tac [bump_make_name,LESS_EQ_TRANS,lift_state_fresh_used]
QED

Theorem lift_rec_certificate_body_scope_trace[local]:
  lift_rec_certificate R source funs target funs' ren ∧ index < LENGTH funs ⇒
  ∃bound base tree limit captures before after before_env after_env final locals
    group_trees group_limit group_captures.
    annotate_exp [] (SND (SND (EL index funs))) = (tree,limit,captures) ∧
    limit ≤ FST before ∧ bump (FST (SND (EL index funs))) 0 ≤ FST before ∧
    lift_function_body (bind_all (MAP FST funs) bound) ren before
      (FST (SND (EL index funs))) tree = (SND (SND (EL index funs')),after) ∧
    lift_state_fresh before ∧ lift_state_fresh after ∧
    lift_state_decs_avoid before after ∧
    lift_global_decs (REVERSE (FST (SND before))) base before_env ∧
    lift_global_decs (REVERSE (FST (SND after))) base after_env ∧
    annotate_funs [] funs = (group_trees,group_limit,group_captures) ∧
    FDOM (fdomsub captures (FST (SND (EL index funs)))) ⊆ FDOM group_captures ∧
    lift_env_rel R (delete_all (MAP FST funs) group_captures) ren source
      (before_env with v := nsBindList locals before_env.v) ∧
    lift_env_rel R (delete_all (MAP FST funs) group_captures) ren source
      (after_env with v := nsBindList locals after_env.v) ∧
    target.c = final.c ∧
    (∀id. (∀name. id = Short name ⇒
        name ∈ exp_free_names_funs funs' DIFF set (MAP FST funs')) ⇒
      nsLookup target.v id = nsLookup (nsBindList locals final.v) id) ∧
    (∀bindings id. (∀name. id = Short name ⇒
        name ∈ FDOM (SND (SND after)) ∨ IS_SOME (ALOOKUP bindings name)) ⇒
      nsLookup (nsBindList bindings final.v) id =
        nsLookup (nsBindList bindings after_env.v) id) ∧
    lift_scope R (delete_all (MAP FST funs) group_captures) bound ren before
      source before_env locals ∧
    EVERY (λ(f,x,e). source_dce$no_Open e ∧ check_exp_constructors source.c e) funs ∧
    (∀name renamed. FLOOKUP ren name = SOME renamed ∧ renamed ≠ name ⇒
      renamed ∉ exp_names_funs funs) ∧
    (∀name k. MEM name (MAP FST funs') ∧ FST before ≤ k ⇒ name ≠ make_name k)
Proof
  strip_tac
  >> qpat_x_assum ‘lift_rec_certificate R source funs target funs' ren’
       (mp_tac o REWRITE_RULE [lift_rec_certificate_def])
  >> disch_then (qx_choosel_then
       [‘trees’,‘group_limit’,‘group_captures’,‘bound’,‘n’,‘ds’,‘used’,
        ‘n1’,‘ds1’,‘used1’,‘base’,‘initial’,‘final’,‘locals’] strip_assume_tac)
  >> imp_res_tac (cj 3 annotate_LENGTH) >> imp_res_tac LIST_REL_LENGTH
  >> ‘LENGTH funs' = LENGTH funs’ by fs []
  >> ‘LENGTH (ZIP (MAP FST funs',MAP (FST o SND) funs)) = LENGTH funs’ by simp []
  >> ‘LENGTH (ZIP (MAP FST funs',MAP (FST o SND) funs)) ≤ LENGTH trees ∧
        index < LENGTH (ZIP (MAP FST funs',MAP (FST o SND) funs))’ by fs []
  >> ‘EVERY (λ(f,x,e). source_dce$no_Open e) funs’ by fs [ELIM_UNCURRY,EVERY_CONJ]
  >> qpat_assum ‘lift_scope _ _ _ _ _ _ _ _’ (strip_assume_tac o REWRITE_RULE [lift_scope_def])
  >> have ‘EVERY (λname. bump name 0 ≤ n) (MAP FST funs)’
  >- (
    simp [EVERY_MEM]
    >> qx_gen_tac ‘name’ >> strip_tac
    >> ‘name ∈ exp_names_funs funs’ by metis_tac [recursive_names_all_names]
    >> drule_all (cj 4 annotate_all_name_bound)
    >> decide_tac)
  >> have ‘∀name k. MEM name (MAP FST funs') ∧ n ≤ k ⇒ name ≠ make_name k’
  >- (
    match_mp_tac (Q.INST
      [‘names’ |-> ‘MAP FST (funs:(mlstring # mlstring # exp) list)’,
       ‘names'’ |-> ‘MAP FST (funs':(mlstring # mlstring # exp) list)’]
      (SPEC_ALL lift_renamed_names_fresh))
    >> simp [])
  >> have ‘EVERY (tree_names_bounded group_limit) trees’
  >- metis_tac [cj 4 annotate_tree_names_bounded]
  >> ‘group_limit ≤ FST (n,ds,used)’ by simp [] >> drule_all lift_funs_body_trace_lookup
  >> disch_then (qx_choosel_then [‘before’,‘after’,‘before_env’,‘after_env’]
       strip_assume_tac)
  >> drule_all annotate_funs_body
  >> disch_then (qx_choosel_then [‘body_limit’,‘body_captures’] strip_assume_tac)
  >> ‘LENGTH (MAP FST funs') = LENGTH (MAP (FST o SND) funs)’ by simp []
  >> ‘index < LENGTH (MAP FST funs')’ by simp []
  >> have ‘n ≤ FST before’
  >- (
    qpat_assum ‘lift_state_extends (n,ds,used) before’
      (mp_tac o MATCH_MP lift_state_extends_counter)
    >> simp [])
  >> have ‘∀name renamed.
        name ∈ FDOM (delete_all (MAP FST funs) group_captures) ∧
        rename_var ren (Short name) = (Short renamed:(mlstring,mlstring) id) ⇒
        renamed ∈ FDOM used ∨ IS_SOME (ALOOKUP locals renamed)’
  >- (
    qx_genl_tac [‘name’,‘renamed’] >> strip_tac
    >> Cases_on ‘name ∈ FDOM bound’
    >- (
      qpat_assum ‘∀name renamed. _ ⇒ IS_SOME (ALOOKUP locals renamed)’
        (qspecl_then [‘name’,‘renamed’] mp_tac)
      >> simp [])
    >> qpat_x_assum ‘∀name. name ∈ FDOM (delete_all (MAP FST funs) group_captures) ∧
         name ∉ FDOM bound ⇒ _’ (qspec_then ‘name’ mp_tac)
    >> simp [])
  >> have ‘lift_state_decs_avoid (n,ds,used) after’
  >- (irule lift_state_decs_avoid_trans >> qexists_tac ‘before’ >> simp [])
  >> namedCases_on ‘before’ ["before_n before_ds before_used"]
  >> namedCases_on ‘after’ ["after_n after_ds after_used"]
  >> have ‘lift_env_rel R (delete_all (MAP FST funs) group_captures) ren source
        (after_env with v := nsBindList locals after_env.v)’
  >- (
    irule lift_state_decs_avoid_env_rel
    >> qexistsl_tac [‘base’,‘ds’,‘after_ds’,‘initial’,‘n’,‘after_n’,‘used’,‘after_used’]
    >> simp [] >> conj_tac
    >- (
      qpat_assum ‘∀name renamed. _ ⇒ renamed ∈ FDOM used ∨ IS_SOME (ALOOKUP locals renamed)’
        ACCEPT_TAC)
    >> qpat_assum ‘lift_global_decs (REVERSE (FST (SND (after_n,after_ds,after_used))))
         base after_env’ (ACCEPT_TAC o SRULE []))
  >> have ‘lift_scope R (delete_all (MAP FST funs) group_captures) bound ren
       (before_n,before_ds,before_used) source before_env locals’
  >- (
    qpat_assum ‘lift_global_decs (REVERSE (FST (SND (before_n,before_ds,before_used))))
         base before_env’ (assume_tac o SRULE [])
    >> irule lift_scope_decs_avoid >> qexistsl_tac [‘base’,‘ds’,‘initial’,‘n’,‘used’]
    >> simp [])
  >> drule lift_scope_env_rel >> disch_tac
  >> qexistsl_tac [‘bound’,‘base’,‘EL index trees’,‘body_limit’,‘body_captures’,
       ‘(before_n,before_ds,before_used)’,‘(after_n,after_ds,after_used)’,
       ‘before_env’,‘after_env’,‘final’,‘locals’,‘trees’,‘group_limit’,‘group_captures’]
  >> fs [EL_ZIP,EL_MAP,o_DEF] >> conj_tac
  >- first_assum ACCEPT_TAC
  >> metis_tac [LESS_EQ_TRANS]
QED

Theorem lift_rec_certificate_bind_body_scope[local]:
  lift_rec_certificate lift_runtime_rel source funs target funs' ren ∧
  annotate_funs [] funs = (trees,limit,group_captures) ∧
  lift_scope lift_runtime_rel (delete_all (MAP FST funs) group_captures) bound ren
    (n,ds,used) source global locals ∧
  FDOM (fdomsub captures arg) ⊆ FDOM group_captures ∧
  arg ∈ exp_names_funs funs ∧ bump arg 0 ≤ n ∧
  (∀name k. MEM name (MAP FST funs') ∧ n ≤ k ⇒ name ≠ make_name k) ∧
  lift_runtime_rel value value' ⇒
  lift_scope lift_runtime_rel captures ((bind_all (MAP FST funs) bound) |+ (arg,()))
    (fdomsub ren arg) (n,ds,used)
    (source with v := nsBind arg value (build_rec_env funs source source.v)) global
    ((arg,value')::
      (MAP (λname. (name,Recclosure target funs' name)) (MAP FST funs') ++ locals))
Proof
  strip_tac
  >> drule_all lift_scope_rec_bindings >> disch_tac
  >> have ‘lift_scope lift_runtime_rel (fdomsub captures arg)
       (bind_all (MAP FST funs) bound) ren (n,ds,used)
       (source with v := build_rec_env funs source source.v) global
       (MAP (λname. (name,Recclosure target funs' name)) (MAP FST funs') ++ locals)’
  >- (irule lift_scope_domain_subset >> qexists_tac ‘group_captures’ >> simp [])
  >> have ‘∀name. name ≠ arg ⇒
       rename_var ren (Short name) ≠ (Short arg:(mlstring,mlstring) id)’
  >- (
    match_mp_tac (Q.INST
      [‘R’ |-> ‘lift_runtime_rel’]
      (SPEC_ALL lift_rec_certificate_argument_shadow))
    >> simp [])
  >> irule (SRULE [] (Q.INST
       [‘source’ |-> ‘source with v := build_rec_env funs source source.v’]
       (SPEC_ALL lift_scope_bind)))
  >> simp []
QED

Theorem exp_free_names_funs_member[local]:
  ∀funs name arg body. MEM (name,arg,body) funs ⇒
    exp_free_names body DELETE arg ⊆ exp_free_names_funs funs
Proof
  Induct_on ‘funs’
  >- simp []
  >> qx_gen_tac ‘entry’
  >> namedCases_on ‘entry’ ["head_name head_arg head_body"] >> rpt gen_tac
  >> simp [Once exp_free_names_def] >> strip_tac
  >- (gvs [] >> simp [])
  >> qpat_x_assum ‘∀name arg body. _’ (qspecl_then [‘name’,‘arg’,‘body’] mp_tac)
  >> simp [] >> metis_tac [SUBSET_UNION,SUBSET_TRANS]
QED

Theorem lift_scope_free_names_protected[local]:
  lift_scope R captures bound ren (n,ds,used) source global locals ∧
  exp_free_names e ⊆ lift_renamed_names ren (FDOM captures) ∪ FDOM used ⇒
  ∀name. name ∈ exp_free_names e ⇒
    name ∈ FDOM used ∨ IS_SOME (ALOOKUP locals name)
Proof
  strip_tac
  >> drule lift_scope_captures_protected >> disch_tac
  >> fs [SUBSET_DEF,lift_renamed_names_def] >> metis_tac []
QED

Theorem lift_rec_certificate_body_refinement[local]:
  lift_app_sim (:'ffi) clock D ⇒
  ∀source funs target funs' ren name name' arg body body' value value'
    (caller:'ffi semanticPrimitives$state).
    caller.clock ≤ clock + 1 ∧
    lift_rec_certificate lift_runtime_rel source funs target funs' ren ∧
    rename_var ren (Short name) = (Short name':(mlstring,mlstring) id) ∧
    find_recfun name funs = SOME (arg,body) ∧
    find_recfun name' funs' = SOME (arg,body') ∧ lift_runtime_rel value value' ⇒
    lift_body_refinement D caller
      (source with v := nsBind arg value (build_rec_env funs source source.v)) body
      (target with v := nsBind arg value' (build_rec_env funs' target target.v)) body'
Proof
  strip_tac
  >> qx_genl_tac [‘source’,‘funs’,‘target’,‘funs'’,‘ren’,‘name’,‘name'’,
       ‘arg’,‘body’,‘body'’,‘value’,‘value'’,‘caller’]
  >> strip_tac >> drule_all lift_rec_certificate_find_recfun_index
  >> disch_then (qx_choosel_then [‘index’,‘compiled_body’] strip_assume_tac)
  >> gvs [] >> drule_all lift_rec_certificate_body_scope_trace
  >> disch_then (qx_choosel_then
       [‘bound’,‘base’,‘tree’,‘limit’,‘captures’,‘before’,‘after’,‘before_env’,
        ‘after_env’,‘final’,‘locals’,‘group_trees’,‘group_limit’,‘group_captures’]
       strip_assume_tac)
  >> namedCases_on ‘before’ ["before_n before_ds before_used"]
  >> namedCases_on ‘after’ ["after_n after_ds after_used"] >> fs []
  >> have ‘MEM (name,arg,body) funs’
  >- (
    qpat_assum ‘EL index funs = (name,arg,body)’ (fn th => rewrite_tac [GSYM th])
    >> simp [EL_MEM])
  >> drule_all exp_names_funs_member >> strip_tac
  >> have ‘source_dce$no_Open body ∧ check_exp_constructors source.c body’
  >- (
    qpat_assum ‘EVERY (λ(f,x,e). source_dce$no_Open e ∧ check_exp_constructors source.c e) funs’
      (mp_tac o REWRITE_RULE [EVERY_MEM])
    >> disch_then (qspec_then ‘(name,arg,body)’ mp_tac)
    >> simp [])
  >> have ‘lift_scope lift_runtime_rel captures
       ((bind_all (MAP FST funs) bound) |+ (arg,())) (fdomsub ren arg)
       (before_n,before_ds,before_used)
       (source with v := nsBind arg value (build_rec_env funs source source.v)) before_env
       ((arg,value')::
         (MAP (λname. (name,Recclosure target funs' name)) (MAP FST funs') ++ locals))’
  >- (
    match_mp_tac (Q.INST
      [‘trees’ |-> ‘group_trees’,‘limit’ |-> ‘group_limit’]
      (SPEC_ALL lift_rec_certificate_bind_body_scope))
    >> gvs [])
  >> gvs [] >> drule lift_function_body_routes >> disch_tac
  >> ‘check_exp_constructors base.c body’
    by (imp_res_tac lift_global_decs_constructors >> gvs [lift_scope_def,lift_env_rel_def])
  >> qpat_assum ‘lift_app_sim _ _ _’ (mp_tac o MATCH_MP lift_exp_simulation)
  >> disch_then (qspecl_then [‘body’,‘tree’,‘limit’,‘captures’,‘LiftValues’,
       ‘(bind_all (MAP FST funs) bound) |+ (arg,())’,‘fdomsub ren arg’,
       ‘before_n’,‘before_ds’,‘before_used’,‘body'’,‘after_n’,‘after_ds’,‘after_used’,
       ‘base’,‘before_env’] mp_tac)
  >> impl_tac
  >- (
    simp [] >> qx_genl_tac [‘original’,‘mapped’] >> strip_tac
    >> qpat_x_assum ‘FLOOKUP (fdomsub ren arg) original = SOME mapped’
      (strip_assume_tac o SRULE [DOMSUB_FLOOKUP_THM])
    >> qpat_x_assum ‘∀name renamed. FLOOKUP ren name = SOME renamed ∧ renamed ≠ name ⇒ _’
      (qspecl_then [‘original’,‘mapped’] mp_tac)
    >> simp [] >> strip_tac >> qpat_x_assum ‘exp_names body ⊆ exp_names_funs funs’
      (mp_tac o REWRITE_RULE [SUBSET_DEF])
    >> disch_then (qspec_then ‘mapped’ mp_tac) >> simp [])
  >> disch_then (qx_choose_then ‘actual_final’ strip_assume_tac)
  >> ‘actual_final = after_env’ by metis_tac [lift_global_decs_deterministic]
  >> qpat_x_assum ‘actual_final = after_env’ SUBST_ALL_TAC
  >> qpat_x_assum ‘∀source locals. lift_scope _ _ _ _ _ _ _ _ ⇒ _’ drule >> strip_tac
  >> qpat_assum ‘lift_rec_certificate lift_runtime_rel source funs target funs' ren’
    (assume_tac o CONJUNCT1 o MATCH_MP lift_rec_certificate_constructors)
  >> qpat_assum ‘lift_scope lift_runtime_rel captures _ _ (after_n,after_ds,after_used)
       _ after_env _’
    (assume_tac o SRULE [] o CONJUNCT1 o
      REWRITE_RULE [lift_env_rel_def] o MATCH_MP lift_scope_env_rel)
  >> ‘target.c = after_env.c’ by metis_tac [] >> rewrite_tac [lift_body_refinement_def]
  >> qx_genl_tac [‘s’,‘s'’] >> strip_tac >> ‘s.clock ≤ clock’ by decide_tac
  >> qpat_x_assum ‘∀s s' target. _ ⇒ lift_eval_refinement _ _ _
       (evaluate s (source with v := nsBind arg value (build_rec_env funs source source.v))
          [body]) _’
    (qspecl_then [‘s’,‘s'’,
       ‘target with v := nsBind arg value' (build_rec_env funs' target target.v)’]
      match_mp_tac)
  >> simp []
  >> have ‘exp_free_names body' ⊆
       lift_renamed_names (fdomsub ren arg) (exp_free_names body) ∪ FDOM after_used’
  >- (
    drule (cj 1 lift_annotated_free_names)
    >> disch_then (qspecl_then
         [‘(bind_all (MAP FST funs) bound) |+ (arg,())’,‘fdomsub ren arg’,
          ‘(before_n,before_ds,before_used)’,‘LiftValues’,‘body'’,
          ‘(after_n,after_ds,after_used)’] mp_tac)
    >> simp [])
  >> have ‘FDOM captures = exp_free_names body’
  >- (metis_tac [cj 1 annotate_free_names])
  >> have ‘∀lookup_name. lookup_name ∈ exp_free_names body' ⇒
       lookup_name ∈ FDOM after_used ∨
       IS_SOME (ALOOKUP ((arg,value')::
         (MAP (λname. (name,Recclosure target funs' name)) (MAP FST funs') ++ locals))
         lookup_name)’
  >- (
    match_mp_tac (Q.INST
      [‘R’ |-> ‘lift_runtime_rel’,
       ‘bound’ |-> ‘(bind_all (MAP FST (funs:(mlstring # mlstring # exp) list)) bound) |+ (arg,())’,
       ‘ren’ |-> ‘fdomsub ren arg’,‘n’ |-> ‘after_n’,‘ds’ |-> ‘after_ds’,
       ‘source’ |-> ‘source with v := nsBind arg value (build_rec_env funs source source.v)’,
       ‘global’ |-> ‘after_env’]
      (INST_TYPE [alpha |-> “:v”] (SPEC_ALL lift_scope_free_names_protected)))
    >> simp [])
  >> qx_gen_tac ‘id’ >> strip_tac >> irule EQ_TRANS
  >> qexists_tac ‘nsLookup (nsBindList ((arg,value')::
       (MAP (λname. (name,Recclosure target funs' name)) (MAP FST funs') ++ locals))
       final.v) id’
  >> conj_tac
  >- (
    drule lift_rec_certificate_function_names
    >> disch_then (assume_tac o MATCH_MP LIST_REL_LENGTH)
    >> ‘index < LENGTH funs'’ by simp []
    >> have ‘MEM (name',arg,body') funs'’
    >- (
      qpat_assum ‘EL index funs' = (name',arg,body')’ (fn th => rewrite_tac [GSYM th])
      >> simp [EL_MEM])
    >> drule exp_free_names_funs_member >> disch_tac
    >> rewrite_tac [build_rec_env_nsBindList_names,nsBindList_clauses,nsBindList_append]
    >> irule (SRULE [nsBindList_clauses] (Q.INST
         [‘bindings’ |->
            ‘(arg,value')::MAP (λname. (name,Recclosure target funs' name)) (MAP FST funs')’,
          ‘names’ |-> ‘arg::MAP FST (funs':(mlstring # mlstring # exp) list)’,
          ‘fvs’ |-> ‘exp_free_names body'’]
         (INST_TYPE [alpha |-> “:v”] (SPEC_ALL lift_bound_lookup))))
    >> simp [MAP_MAP_o,o_DEF] >> simp [ETA_THM] >> qexists_tac ‘body'’ >> simp []
    >> qx_gen_tac ‘lookup_id’ >> strip_tac
    >> qpat_x_assum ‘∀id. _ ⇒ nsLookup target.v id = nsLookup (nsBindList locals final.v) id’
      (qspec_then ‘lookup_id’ match_mp_tac)
    >> qx_gen_tac ‘lookup_name’ >> strip_tac
    >> qpat_x_assum ‘∀name. lookup_id = Short name ⇒ _’
      (qspec_then ‘lookup_name’ mp_tac)
    >> qpat_x_assum ‘exp_free_names body' DELETE arg ⊆ exp_free_names_funs funs'’
      (mp_tac o REWRITE_RULE [SUBSET_DEF])
    >> simp [])
  >> qpat_x_assum ‘∀bindings id. _ ⇒ nsLookup (nsBindList bindings final.v) id = _’
    (qspecl_then [‘(arg,value')::
       (MAP (λname. (name,Recclosure target funs' name)) (MAP FST funs') ++ locals)’,
       ‘id’] match_mp_tac)
  >> qx_gen_tac ‘lookup_name’ >> strip_tac
  >> qpat_x_assum ‘∀lookup_name. lookup_name ∈ exp_free_names body' ⇒ _’
    (qspec_then ‘lookup_name’ match_mp_tac)
  >> qpat_x_assum ‘∀name. id = Short name ⇒ name ∈ exp_free_names body'’
    (qspec_then ‘lookup_name’ mp_tac)
  >> simp []
QED

Theorem lift_evaluate_runtime_match_refinement[local]:
  (∀pattern body. MEM (pattern,body) pes ⇒
    ∀(t:'ffi semanticPrimitives$state) t' source target.
      t.clock ≤ clock ∧ lift_state_rel lift_runtime_rel D t t' ∧
      lift_runtime_env lift_runtime_rel source target ⇒
      lift_eval_refinement lift_runtime_rel D (LIST_REL lift_runtime_rel)
        (evaluate t source [body]) (evaluate t' target [body])) ∧
  (s:'ffi semanticPrimitives$state).clock ≤ clock ∧
  lift_state_rel lift_runtime_rel D s s' ∧
  lift_runtime_env lift_runtime_rel env env' ∧
  lift_runtime_rel value value' ∧ lift_runtime_rel err err' ⇒
  lift_eval_refinement lift_runtime_rel D (LIST_REL lift_runtime_rel)
    (evaluate_match s env value pes err) (evaluate_match s' env' value' pes err')
Proof
  strip_tac
  >> ‘env.c = env'.c’ by fs [lift_runtime_env_def]
  >> irule (runtime_inst lift_evaluate_match_list_refinement)
  >> simp [LIST_REL_EL_EQN,ELIM_UNCURRY] >> qx_gen_tac ‘index’ >> strip_tac
  >> qx_genl_tac [‘t’,‘t'’,‘bindings’,‘bindings'’] >> strip_tac
  >> qpat_x_assum ‘∀pattern body. _’
       (qspecl_then [‘FST (EL index pes)’,‘SND (EL index pes)’] mp_tac)
  >> simp [EL_MEM] >> disch_then irule >> simp [] >> irule lift_runtime_env_bindings
  >> simp [LIST_REL_EL_EQN]
QED

(* ------------------------------------------------------------------------
   Unchanged code and compiled declarations
   ------------------------------------------------------------------------ *)

Theorem lift_evaluate_runtime_same_refinement[local]:
  lift_app_sim (:'ffi) clock D ⇒
  ∀e (s:'ffi semanticPrimitives$state) s' env env'.
    s.clock ≤ clock ∧ lift_state_rel lift_runtime_rel D s s' ∧
    lift_runtime_env lift_runtime_rel env env' ⇒
    lift_eval_refinement lift_runtime_rel D (LIST_REL lift_runtime_rel)
      (evaluate s env [e]) (evaluate s' env' [e])
Proof
  strip_tac
  >> ho_match_mp_tac (SRULE []
       (Q.SPEC ‘λ(p:exp -> bool) (e:exp). P e’ every_exp_ind))
  >> rpt conj_tac
  >- (rpt strip_tac >> irule lift_evaluate_raise_refinement >> simp [])
  >- (
    rpt strip_tac
    >> ‘env.c = env'.c’ by fs [lift_runtime_env_def]
    >> irule (runtime_inst lift_evaluate_handle_refinement)
    >> simp [] >> rpt strip_tac >> irule lift_evaluate_runtime_match_refinement >> simp []
    >> qexists_tac ‘clock’ >> simp [] >> qpat_x_assum ‘∀pat e. _’ ACCEPT_TAC)
  >- (
    rpt strip_tac
    >> simp [evaluate_def,lift_eval_refinement_def,lift_eval_result_rel_def,
         lift_result_rel_def,lift_runtime_rel_refl])
  >- (
    qx_genl_tac [‘cn’,‘es’] >> strip_tac
    >> qx_genl_tac [‘s’,‘s'’,‘env’,‘env'’] >> strip_tac
    >> ‘env.c = env'.c’ by fs [lift_runtime_env_def]
    >> irule (runtime_inst lift_evaluate_con_refinement)
    >> simp []
    >> irule lift_evaluate_list_refinement
    >> simp [LIST_REL_EL_EQN] >> qexists_tac ‘clock’ >> simp []
    >> qx_gen_tac ‘position’ >> strip_tac >> qx_genl_tac [‘t’,‘t'’] >> strip_tac
    >> qpat_x_assum ‘∀e. MEM e es ⇒ _’ irule >> simp [EL_MEM])
  >- (
    qx_genl_tac [‘name’,‘s’,‘s'’,‘env’,‘env'’] >> strip_tac
    >> have ‘OPTREL lift_runtime_rel (nsLookup env.v name) (nsLookup env'.v name)’
    >- fs [lift_runtime_env_def]
    >> namedCases_on ‘nsLookup env.v name’ ["","source_value"]
    >> namedCases_on ‘nsLookup env'.v name’ ["","target_value"]
    >> gvs [evaluate_def,OPTREL_def,lift_eval_refinement_def,
         lift_eval_result_rel_def,lift_result_rel_def])
  >- (
    rpt strip_tac
    >> simp [evaluate_def,lift_eval_refinement_def,lift_eval_result_rel_def,
         lift_result_rel_def,lift_runtime_rel_cases_l,lift_closure_certificate_def])
  >- (
    qx_genl_tac [‘op’,‘es’] >> strip_tac
    >> qx_genl_tac [‘s’,‘s'’,‘env’,‘env'’] >> strip_tac
    >> have ‘lift_eval_refinement lift_runtime_rel D (LIST_REL lift_runtime_rel)
         (evaluate s env (REVERSE es)) (evaluate s' env' (REVERSE es))’
    >- (
      irule lift_evaluate_list_refinement
      >> simp [LIST_REL_EL_EQN] >> qexists_tac ‘clock’ >> simp []
      >> qx_gen_tac ‘position’ >> strip_tac >> qx_genl_tac [‘t’,‘t'’] >> strip_tac
      >> qpat_x_assum ‘∀e. MEM e es ⇒ _’ irule
      >> simp [EL_MEM])
    >> qpat_x_assum ‘lift_app_sim _ _ _’ (irule o REWRITE_RULE [lift_app_sim_def])
    >> simp [])
  >- (
    rpt strip_tac
    >> irule (runtime_inst lift_evaluate_log_refinement)
    >> simp [] >> metis_tac [LESS_EQ_TRANS])
  >- (
    rpt strip_tac
    >> irule (runtime_inst lift_evaluate_if_refinement)
    >> simp [] >> metis_tac [LESS_EQ_TRANS])
  >- (
    rpt strip_tac
    >> ‘env.c = env'.c’ by fs [lift_runtime_env_def]
    >> irule (runtime_inst lift_evaluate_mat_refinement)
    >> simp [lift_runtime_rel_refl] >> rpt strip_tac
    >> irule lift_evaluate_runtime_match_refinement >> simp [lift_runtime_rel_refl]
    >> qexists_tac ‘clock’ >> simp [lift_runtime_rel_refl]
    >> qpat_x_assum ‘∀pat e. _’ ACCEPT_TAC)
  >- (
    qx_genl_tac [‘binding’,‘rhs’,‘body’] >> strip_tac
    >> qx_genl_tac [‘s’,‘s'’,‘env’,‘env'’] >> strip_tac
    >> namedCases_on ‘binding’ ["","name"] >> irule lift_evaluate_let_refinement
    >> simp [namespaceTheory.nsOptBind_def]
    >> metis_tac [lift_runtime_env_bind,LESS_EQ_TRANS])
  >- (rpt strip_tac >> simp [evaluate_def])
  >- (rpt strip_tac >> simp [evaluate_def])
  >- (
    qx_genl_tac [‘funs’,‘body’] >> strip_tac
    >> qx_genl_tac [‘s’,‘s'’,‘env’,‘env'’] >> strip_tac
    >> Cases_on ‘ALL_DISTINCT (MAP FST funs)’ >> simp [cj 14 evaluate_def]
    >- (
      simp [ELIM_UNCURRY,ETA_THM]
      >> qpat_x_assum ‘∀s s' env env'. _ ⇒ _’ irule
      >> simp [lift_runtime_env_build_rec_env])
    >> simp [ELIM_UNCURRY,ETA_THM,lift_eval_refinement_def])
  >- (
    qx_genl_tac [‘path’,‘body’] >> strip_tac
    >> qx_genl_tac [‘s’,‘s'’,‘env’,‘env'’] >> strip_tac >> drule lift_runtime_env_open
    >> disch_then (qspec_then ‘path’ assume_tac)
    >> namedCases_on ‘open_dec_env path env’ ["","source_opened"]
    >- simp [cj 17 evaluate_def,lift_eval_refinement_def]
    >> namedCases_on ‘open_dec_env path env'’ ["","target_opened"]
    >> gvs [OPTREL_def,cj 17 evaluate_def]
    >> qpat_x_assum ‘∀s s' env env'. _ ⇒ _’ irule >> simp []
    >> irule lift_runtime_env_extend >> simp [])
QED

Theorem lift_evaluate_dlet_refinement[local]:
  env.c = env'.c ∧
  (check_exp_constructors env.c body ⇒ check_exp_constructors env'.c body') ∧
  lift_eval_refinement lift_runtime_rel D (LIST_REL lift_runtime_rel)
    (evaluate (s:'ffi semanticPrimitives$state) env [body])
    (evaluate s' env' [body']) ⇒
  lift_eval_refinement lift_runtime_rel D (lift_runtime_env lift_runtime_rel)
    (evaluate_decs s env [Dlet locs pattern body])
    (evaluate_decs s' env' [Dlet locs pattern body'])
Proof
  strip_tac >> drule lift_eval_refinement_single >> strip_tac
  >> Cases_on ‘ALL_DISTINCT (pat_bindings pattern) ∧ check_exp_constructors env.c body’
  >> gvs [evaluate_decs_def,lift_eval_refinement_def,lift_eval_result_rel_def,
          lift_result_rel_def]
  >> ‘lift_match_rel lift_runtime_rel (pmatch env'.c t.refs pattern v [])
        (pmatch env'.c t'.refs pattern v' [])’ by (
    irule (runtime_inst (CONJUNCT1 lift_value_rel_pmatch))
    >> simp []
    >> metis_tac [lift_state_rel_def,LIST_REL_OPTREL_store_lookup])
  >> gvs [lift_match_rel_cases,lift_result_rel_def,lift_runtime_rel_refl,
          lift_runtime_env_namespace]
  >> irule namespacePropsTheory.nsAll2_alist_to_ns >> fs [ELIM_UNCURRY]
QED

Theorem lift_evaluate_dmod_refinement[local]:
  lift_eval_refinement lift_runtime_rel D (lift_runtime_env lift_runtime_rel)
    (evaluate_decs (s:'ffi semanticPrimitives$state) env ds)
    (evaluate_decs s' env' ds') ⇒
  lift_eval_refinement lift_runtime_rel D (lift_runtime_env lift_runtime_rel)
    (evaluate_decs s env [Dmod name ds]) (evaluate_decs s' env' [Dmod name ds'])
Proof
  Cases_on ‘evaluate_decs s env ds’ >> Cases_on ‘evaluate_decs s' env' ds'’
  >> rw [evaluate_decs_def,lift_eval_refinement_def,lift_eval_result_rel_def,
       lift_result_rel_cases] >> gvs [lift_runtime_env_namespace]
QED

Theorem lift_evaluate_dlocal_refinement[local]:
  lift_runtime_env lift_runtime_rel env env' ∧
  lift_eval_refinement lift_runtime_rel D (lift_runtime_env lift_runtime_rel)
    (evaluate_decs (s:'ffi semanticPrimitives$state) env ds1)
    (evaluate_decs s' env' ds1') ∧
  (∀t delta (t':'ffi semanticPrimitives$state) e'.
    evaluate_decs s env ds1 = (t,Rval delta) ∧
    t.clock ≤ s.clock ∧ lift_state_rel lift_runtime_rel D t t' ∧
    lift_runtime_env lift_runtime_rel (delta +++ env) e' ⇒
    lift_eval_refinement lift_runtime_rel D (lift_runtime_env lift_runtime_rel)
      (evaluate_decs t (delta +++ env) ds2) (evaluate_decs t' e' ds2')) ⇒
  lift_eval_refinement lift_runtime_rel D (lift_runtime_env lift_runtime_rel)
    (evaluate_decs s env [Dlocal ds1 ds2]) (evaluate_decs s' env' [Dlocal ds1' ds2'])
Proof
  strip_tac
  >> Cases_on ‘evaluate_decs s env ds1’ >> Cases_on ‘evaluate_decs s' env' ds1'’
  >> imp_res_tac (cj 3 evaluate_clock)
  >> gvs [evaluate_decs_def,lift_eval_refinement_def,lift_eval_result_rel_def,
       lift_result_rel_cases]
  >> first_x_assum irule >> simp [lift_runtime_env_extend]
QED

Theorem lift_evaluate_decs_cons_refinement[local]:
  lift_runtime_env lift_runtime_rel env env' ∧
  lift_eval_refinement lift_runtime_rel D (lift_runtime_env lift_runtime_rel)
    (evaluate_decs (s:'ffi semanticPrimitives$state) env [d])
    (evaluate_decs s' env' [d']) ∧
  (∀t delta (t':'ffi semanticPrimitives$state) e'.
    evaluate_decs s env [d] = (t,Rval delta) ∧
    t.clock ≤ s.clock ∧ lift_state_rel lift_runtime_rel D t t' ∧
    lift_runtime_env lift_runtime_rel (delta +++ env) e' ⇒
    lift_eval_refinement lift_runtime_rel D (lift_runtime_env lift_runtime_rel)
      (evaluate_decs t (delta +++ env) ds) (evaluate_decs t' e' ds')) ⇒
  lift_eval_refinement lift_runtime_rel D (lift_runtime_env lift_runtime_rel)
    (evaluate_decs s env (d::ds)) (evaluate_decs s' env' (d'::ds'))
Proof
  strip_tac >> once_rewrite_tac [evaluate_decs_cons]
  >> Cases_on ‘evaluate_decs s env [d]’ >> Cases_on ‘evaluate_decs s' env' [d']’
  >> imp_res_tac (cj 3 evaluate_clock)
  >> gvs [lift_eval_refinement_def,lift_eval_result_rel_def,lift_result_rel_cases]
  >> rename1 ‘evaluate_decs s env [d] = (t,Rval delta)’
  >> rename1 ‘evaluate_decs s' env' [d'] = (t',Rval delta')’
  >> first_x_assum (qspecl_then [‘t'’,‘delta' +++ env'’] mp_tac)
  >> simp [lift_runtime_env_extend]
  >> Cases_on ‘evaluate_decs t (delta +++ env) ds’
  >> Cases_on ‘evaluate_decs t' (delta' +++ env') ds'’
  >> rw [lift_eval_result_rel_def,lift_result_rel_cases]
  >> gvs [combine_dec_result_def,lift_runtime_env_namespace]
  >> irule namespacePropsTheory.nsAll2_nsAppend >> simp []
QED

Definition lift_declare_env_rel_def:
  lift_declare_env_rel D ⇔
    ∀eval_state eval_state' env env'.
      D eval_state eval_state' ∧ lift_runtime_env lift_runtime_rel env env' ⇒
      OPTREL (λ(value,next_state) (value',next_state').
        lift_runtime_rel value value' ∧ D next_state next_state')
        (declare_env eval_state env) (declare_env eval_state' env')
End

Theorem lift_evaluate_denv_refinement[local]:
  lift_declare_env_rel D ∧ lift_state_rel lift_runtime_rel D s s' ∧
  lift_runtime_env lift_runtime_rel env env' ⇒
  lift_eval_refinement lift_runtime_rel D (lift_runtime_env lift_runtime_rel)
    (evaluate_decs (s:'ffi semanticPrimitives$state) env [Denv name])
    (evaluate_decs s' env' [Denv name])
Proof
  rw [lift_declare_env_rel_def] >> ‘D s.eval_state s'.eval_state’ by fs [lift_state_rel_def]
  >> first_x_assum drule_all
  >> Cases_on ‘declare_env s.eval_state env’ >> Cases_on ‘declare_env s'.eval_state env'’
  >> rw [OPTREL_def] >> rpt (pairarg_tac >> gvs [])
  >> gvs [evaluate_decs_def,lift_eval_refinement_def,lift_eval_result_rel_def,
          lift_result_rel_def,lift_state_rel_def,lift_runtime_env_namespace]
QED

Theorem lift_evaluate_dopen_refinement[local]:
  lift_state_rel lift_runtime_rel D s s' ∧ lift_runtime_env lift_runtime_rel env env' ⇒
  lift_eval_refinement lift_runtime_rel D (lift_runtime_env lift_runtime_rel)
    (evaluate_decs (s:'ffi semanticPrimitives$state) env [Dopen locs path])
    (evaluate_decs s' env' [Dopen locs path])
Proof
  strip_tac >> drule lift_runtime_env_open >> disch_then (qspec_then ‘path’ assume_tac)
  >> Cases_on ‘open_dec_env path env’ >> Cases_on ‘open_dec_env path env'’
  >> gvs [OPTREL_def,evaluate_decs_def,lift_eval_refinement_def,lift_eval_result_rel_def,
          lift_result_rel_def]
QED

Theorem lift_evaluate_decs_runtime_same_refinement[local]:
  (∀e (s:'ffi semanticPrimitives$state) s' env env'.
    s.clock ≤ clock ∧ lift_state_rel lift_runtime_rel D s s' ∧
    lift_runtime_env lift_runtime_rel env env' ⇒
    lift_eval_refinement lift_runtime_rel D (LIST_REL lift_runtime_rel)
      (evaluate s env [e]) (evaluate s' env' [e])) ∧
  lift_declare_env_rel D ⇒
  ∀(s:'ffi semanticPrimitives$state) env ds s' env'.
    s.clock ≤ clock ∧ lift_state_rel lift_runtime_rel D s s' ∧
    lift_runtime_env lift_runtime_rel env env' ⇒
    lift_eval_refinement lift_runtime_rel D (lift_runtime_env lift_runtime_rel)
      (evaluate_decs s env ds) (evaluate_decs s' env' ds)
Proof
  strip_tac
  >> ho_match_mp_tac evaluate_decs_ind >> rpt conj_tac >> rpt gen_tac
  >~ [‘evaluate_decs _ _ []’] >- (
    rpt strip_tac
    >> simp [evaluate_decs_def,lift_eval_refinement_def,lift_eval_result_rel_def,
             lift_result_rel_def,lift_runtime_env_namespace])
  >~ [‘d1::d2::ds’] >- (
    rpt strip_tac >> irule lift_evaluate_decs_cons_refinement >> simp []
    >> metis_tac [LESS_EQ_TRANS])
  >~ [‘Dlet locs p e’] >- (
    rpt strip_tac >> irule lift_evaluate_dlet_refinement
    >> fs [lift_runtime_env_def])
  >~ [‘Dletrec locs funs’] >- (
    rpt strip_tac
    >> ‘env.c = env'.c’ by fs [lift_runtime_env_def]
    >> have ‘∀name. lift_runtime_rel (Recclosure env funs name)
                 (Recclosure env' funs name)’
    >- simp [lift_runtime_rel_cases_l,lift_closure_certificate_def]
    >> simp [evaluate_decs_def] >> IF_CASES_TAC
    >> simp [lift_eval_refinement_def,lift_eval_result_rel_def,lift_result_rel_def,
             lift_runtime_env_namespace,build_rec_env_nsBindList]
    >> irule namespacePropsTheory.nsAll2_nsBindList
    >> simp [LIST_REL_EL_EQN,EL_MAP,ELIM_UNCURRY])
  >~ [‘Dtype locs tds’] >- (
    rpt strip_tac
    >> simp [evaluate_decs_def] >> IF_CASES_TAC
    >> fs [lift_eval_refinement_def,lift_eval_result_rel_def,lift_result_rel_def,
           lift_state_rel_def,lift_runtime_env_namespace])
  >~ [‘Dtabbrev locs tvs tn t’] >- (
    rpt strip_tac
    >> simp [evaluate_decs_def,lift_eval_refinement_def,lift_eval_result_rel_def,
             lift_result_rel_def,lift_runtime_env_namespace])
  >~ [‘Denv n’] >- (
    rpt strip_tac >> irule lift_evaluate_denv_refinement >> simp [])
  >~ [‘Dexn locs cn ts’] >- (
    rpt strip_tac
    >> fs [evaluate_decs_def,lift_eval_refinement_def,lift_eval_result_rel_def,
           lift_result_rel_def,lift_state_rel_def,lift_runtime_env_namespace])
  >~ [‘Dmod mn ds’] >- (
    rpt strip_tac >> irule lift_evaluate_dmod_refinement
    >> first_x_assum irule >> simp [])
  >~ [‘Dlocal lds ds’] >- (
    rpt strip_tac >> irule lift_evaluate_dlocal_refinement >> simp []
    >> metis_tac [LESS_EQ_TRANS])
  >> rpt strip_tac >> irule lift_evaluate_dopen_refinement >> simp []
QED

Theorem lift_eval_refinement_mono[local]:
  (∀value value'. success_rel value value' ⇒ success_rel' value value') ∧
  lift_eval_refinement R D success_rel
    (source_eval:'ffi semanticPrimitives$state # ('a,v) result) target_eval ⇒
  lift_eval_refinement R D success_rel' source_eval target_eval
Proof
  rw [lift_eval_refinement_def] >> simp []
  >> disj2_tac >> irule lift_eval_result_rel_mono
  >> qexists_tac ‘success_rel’ >> simp []
QED

Theorem compile_dlet_refinement[local]:
  lift_app_sim (:'ffi) clock D ⇒
  ∀locs pattern body source target (s:'ffi semanticPrimitives$state) s'.
    s.clock ≤ clock ∧ lift_state_rel lift_runtime_rel D s s' ∧
    lift_runtime_env lift_runtime_rel source target ⇒
    lift_eval_refinement lift_runtime_rel D (lift_runtime_env lift_runtime_rel)
      (evaluate_decs s source [Dlet locs pattern body])
      (evaluate_decs s' target [compile_dec (Dlet locs pattern body)])
Proof
  strip_tac
  >> qx_genl_tac [‘locs’,‘pattern’,‘body’,‘source’,‘target’,‘s’,‘s'’] >> strip_tac
  >> Cases_on ‘ALL_DISTINCT (pat_bindings pattern) ∧ check_exp_constructors source.c body’
  >- (
    fs []
    >> Cases_on ‘source_dce$no_Open body’
    >- (
      namedCases_on ‘annotate_exp [] body’ ["tree n captures"]
      >> namedCases_on ‘lower_exp KeepValue str_empty FEMPTY
           (bump_pat n pattern,[],bind_all (pat_bindings pattern) captures) tree’
           ["compiled out_n ds used"]
      >> simp [compile_dec_def]
      >> qpat_assum ‘lift_app_sim _ _ _’ (drule_all o MATCH_MP lower_let_simulation)
      >> simp [] >> disch_then (qx_choose_then ‘final’ strip_assume_tac)
      >> have ‘lift_decs_env s' (REVERSE ds) target final’
      >- metis_tac [lift_global_decs_evaluates]
      >> drule make_local_evaluates
      >> disch_then (qspec_then ‘Dlet locs pattern compiled’ assume_tac) >> simp []
      >> have ‘source.c = final.c’
      >- metis_tac [lift_global_decs_constructors,lift_runtime_env_def]
      >> have ‘tree_constructors source.c tree’
      >- metis_tac [CONJUNCT1 annotate_constructors]
      >> have ‘check_exp_constructors source.c compiled’
      >- metis_tac [cj 2 lift_exp_constructors]
      >> irule lift_evaluate_dlet_refinement >> simp []
      >> qpat_x_assum ‘source.c = final.c’ (fn th => simp [GSYM th]))
    >> simp [compile_dec_def] >> irule lift_evaluate_dlet_refinement >> conj_tac
    >- fs [lift_runtime_env_def] >> conj_tac
    >- (
      fs [lift_runtime_env_def]
      >> qpat_x_assum ‘source.c = target.c’ (fn th => simp [GSYM th]))
    >> qpat_assum ‘lift_app_sim _ _ _’
         (mp_tac o MATCH_MP lift_evaluate_runtime_same_refinement)
    >> disch_then (qspecl_then [‘body’,‘s’,‘s'’,‘source’,‘target’] mp_tac)
    >> simp [])
  >> simp [evaluate_decs_def,lift_eval_refinement_def]
QED

Theorem lower_letrec_certificate[local]:
  lift_app_sim (:'ffi) clock D ⇒
  ∀funs trees n captures compiled out_n ds used source target.
    annotate_funs [] funs = (trees,n,captures) ∧
    EVERY (λ(f,x,e). source_dce$no_Open e ∧ check_exp_constructors source.c e) funs ∧
    ALL_DISTINCT (MAP FST funs) ∧ lift_runtime_env lift_runtime_rel source target ∧
    lift_funs (bind_all (MAP FST funs) str_empty) FEMPTY
      (n,[],bind_all (MAP FST funs) captures)
      (MAP (λ(f,x,e). (f,x)) funs) trees = (compiled,out_n,ds,used) ⇒
    ∃final.
      lift_global_decs (REVERSE ds) target final ∧
      lift_rec_certificate lift_runtime_rel source funs final compiled FEMPTY
Proof
  strip_tac
  >> qx_genl_tac [‘funs’,‘trees’,‘n’,‘captures’,‘compiled’,‘out_n’,‘ds’,‘used’,
       ‘source’,‘target’]
  >> strip_tac >> have ‘EVERY (λ(f,x,e). source_dce$no_Open e) funs’
  >- fs [ELIM_UNCURRY,EVERY_CONJ]
  >> have ‘lift_state_fresh (n,[],bind_all (MAP FST funs) captures)’
  >- metis_tac [initial_letrec_state_fresh]
  >> have ‘EVERY (λname. bump name 0 ≤ n) (MAP FST funs)’
  >- (
    simp [EVERY_MEM]
    >> metis_tac [cj 4 annotate_all_name_bound,recursive_names_all_names])
  >> have ‘lift_scope lift_runtime_rel captures FEMPTY FEMPTY
       (n,[],bind_all (MAP FST funs) captures) source target []’
  >- metis_tac [initial_letrec_scope]
  >> have ‘lift_scope lift_runtime_rel (delete_all (MAP FST funs) captures) FEMPTY FEMPTY
       (n,[],bind_all (MAP FST funs) captures) source target []’
  >- (
    irule lift_scope_domain_subset
    >> qexists_tac ‘captures’
    >> simp [delete_all_domain,SUBSET_DEF])
  >> ‘∀f x e. MEM (f,x,e) funs ⇒ lift_exp_sim (:'ffi) clock D e’
    by metis_tac [lift_exp_sim_thm]
  >> qspecl_then [‘funs’,‘trees’,‘n’,‘captures’,‘MAP (λ(f,x,e). (f,x)) funs’,
       ‘bind_all (MAP FST funs) str_empty’,‘FEMPTY:mlstring |-> mlstring’,‘n’,
       ‘[]:dec list’,‘bind_all (MAP FST funs) captures’,‘compiled’,‘out_n’,‘ds’,‘used’,
       ‘target’,‘target’] mp_tac lift_funs_global_decs
  >> impl_tac
  >- (
    conj_tac >- first_assum ACCEPT_TAC
    >> gvs [lift_global_decs_rules,lift_runtime_env_def,MAP_MAP_o,o_DEF,ELIM_UNCURRY])
  >> disch_then (qx_choose_then ‘final’ assume_tac)
  >> drule (cj 3 annotate_LENGTH) >> disch_tac
  >> ‘MAP FST compiled = MAP FST funs’ by (
    drule lift_funs_names_prefix
    >> simp [TAKE_LENGTH_TOO_LONG,MAP_MAP_o,o_DEF,ELIM_UNCURRY,ETA_AX])
  >> fs [MAP_MAP_o,o_DEF,ELIM_UNCURRY,ETA_AX]
  >> qexists_tac ‘final’ >> conj_tac
  >- first_assum ACCEPT_TAC
  >> mp_tac (Q.INST [‘R’ |-> ‘lift_runtime_rel’,‘limit’ |-> ‘n’,
       ‘bound’ |-> ‘FEMPTY:mlstring |-> unit’,‘ren’ |-> ‘FEMPTY:mlstring |-> mlstring’,
       ‘ds’ |-> ‘[]:dec list’,‘used’ |-> ‘bind_all (MAP FST funs) captures’,
       ‘n1’ |-> ‘out_n’,‘ds1’ |-> ‘ds’,‘used1’ |-> ‘used’,‘funs'’ |-> ‘compiled’,
       ‘base’ |-> ‘target’,‘initial’ |-> ‘target’,
       ‘locals’ |-> ‘[]:(mlstring # v) list’] (SPEC_ALL lift_scope_rec_certificate))
  >> simp [nsBindList_clauses] >> impl_tac
  >- (
    gvs [str_empty_def,lift_global_decs_rules,rich_listTheory.ZIP_MAP_MAP,
         o_DEF,ELIM_UNCURRY,rename_var_empty,namespaceTheory.id_11,LIST_REL_EL_EQN]
    >> qx_gen_tac ‘counter’ >> CCONTR_TAC >> fs [EVERY_MEM]
    >> metis_tac [bump_make_name,LESS_EQ_TRANS])
  >> simp []
QED

Theorem lift_evaluate_dletrec_refinement[local]:
  lift_state_rel lift_runtime_rel D (s:'ffi semanticPrimitives$state) s' ∧
  lift_rec_certificate lift_runtime_rel source funs target funs' FEMPTY ⇒
  lift_eval_refinement lift_runtime_rel D (lift_runtime_env lift_runtime_rel)
    (evaluate_decs s source [Dletrec locs funs])
    (evaluate_decs s' target [Dletrec locs funs'])
Proof
  strip_tac
  >> have ‘MAP FST funs = MAP FST funs' ∧
       ALL_DISTINCT (MAP FST funs) ∧ ALL_DISTINCT (MAP FST funs')’
  >- (
    fs [lift_rec_certificate_def,rename_var_empty,namespaceTheory.id_11,LIST_REL_eq]
    >> fs [LIST_REL_EL_EQN]
    >> simp [LIST_EQ_REWRITE])
  >> drule lift_rec_certificate_constructors >> strip_tac
  >> simp [evaluate_decs_def,ELIM_UNCURRY,ETA_AX,lift_eval_refinement_def,
       lift_eval_result_rel_def,lift_result_rel_def,lift_runtime_env_namespace,
       build_rec_env_nsBindList_names]
  >> irule namespacePropsTheory.nsAll2_nsBindList >> simp [LIST_REL_EL_EQN,EL_MAP]
  >> qx_gen_tac ‘index’ >> strip_tac
  >> irule (Q.INST [‘ren’ |-> ‘FEMPTY:mlstring |-> mlstring’]
       (SPEC_ALL lift_rec_certificate_runtime_rel))
  >> simp [rename_var_empty]
  >> qpat_x_assum ‘MAP FST funs = MAP FST funs'’ (fn th => simp [th,MEM_MAP])
  >> qexists_tac ‘EL index funs'’ >> simp [EL_MEM]
QED

Theorem compile_dletrec_refinement[local]:
  lift_app_sim (:'ffi) clock D ⇒
  ∀locs funs source target (s:'ffi semanticPrimitives$state) s'.
    s.clock ≤ clock ∧ lift_state_rel lift_runtime_rel D s s' ∧
    lift_runtime_env lift_runtime_rel source target ⇒
    lift_eval_refinement lift_runtime_rel D (lift_runtime_env lift_runtime_rel)
      (evaluate_decs s source [Dletrec locs funs])
      (evaluate_decs s' target [compile_dec (Dletrec locs funs)])
Proof
  strip_tac
  >> qx_genl_tac [‘locs’,‘funs’,‘source’,‘target’,‘s’,‘s'’] >> strip_tac
  >> Cases_on ‘ALL_DISTINCT (MAP FST funs) ∧
       EVERY (λ(f,x,e). check_exp_constructors source.c e) funs’
  >- (
    fs []
    >> Cases_on ‘EVERY (λ(f,x,e). source_dce$no_Open e) funs’
    >- (
      namedCases_on ‘annotate_funs [] funs’ ["trees n captures"]
      >> namedCases_on ‘lift_funs (bind_all (MAP FST funs) str_empty) FEMPTY
           (n,[],bind_all (MAP FST funs) captures)
           (MAP (λ(f,x,e). (f,x)) funs) trees’ ["compiled out_n ds used"]
      >> simp [compile_dec_def]
      >> qpat_assum ‘lift_app_sim _ _ _’ (mp_tac o MATCH_MP lower_letrec_certificate)
      >> disch_then (qspecl_then [‘funs’,‘trees’,‘n’,‘captures’,‘compiled’,‘out_n’,
           ‘ds’,‘used’,‘source’,‘target’] mp_tac)
      >> impl_tac
      >- fs [ELIM_UNCURRY,EVERY_CONJ]
      >> disch_then (qx_choose_then ‘final’ strip_assume_tac)
      >> have ‘lift_decs_env s' (REVERSE ds) target final’
      >- metis_tac [lift_global_decs_evaluates]
      >> drule make_local_evaluates
      >> disch_then (qspec_then ‘Dletrec locs compiled’ assume_tac)
      >> have ‘¬EXISTS ($¬ ∘ (λ(f,x,e). source_dce$no_Open e)) funs’
      >- fs [EVERY_MEM,EXISTS_MEM,o_DEF,ELIM_UNCURRY]
      >> simp [] >> irule lift_evaluate_dletrec_refinement
      >> simp [])
    >> simp [compile_dec_def] >> ‘source.c = target.c’ by fs [lift_runtime_env_def]
    >> have ‘∀name. lift_runtime_rel (Recclosure source funs name)
         (Recclosure target funs name)’
    >- simp [lift_runtime_rel_cases_l,lift_closure_certificate_def]
    >> qpat_assum ‘source.c = target.c’ (fn th =>
         simp [GSYM th,evaluate_decs_def])
    >> IF_CASES_TAC
    >- (
      have ‘EXISTS ($¬ ∘ (λ(f,x,e). source_dce$no_Open e)) funs’
      >- (fs [EVERY_MEM,EXISTS_MEM,o_DEF,ELIM_UNCURRY] >> metis_tac [])
      >> qpat_assum ‘EXISTS _ funs’ (fn th =>
           simp_tac pure_ss [th,evaluate_decs_def])
      >> qpat_x_assum ‘source.c = target.c’ (fn th =>
           simp_tac pure_ss [GSYM th])
      >> simp [lift_eval_refinement_def,lift_eval_result_rel_def,lift_result_rel_def,
           lift_runtime_env_namespace,build_rec_env_nsBindList]
      >> simp_tac pure_ss [evaluate_decs_def]
      >> ‘source.c = target.c’ by fs [lift_runtime_env_def]
      >> qpat_x_assum ‘source.c = target.c’ (fn th => once_rewrite_tac [GSYM th])
      >> simp [lift_eval_result_rel_def,lift_result_rel_def,
           lift_runtime_env_namespace,build_rec_env_nsBindList]
      >> irule namespacePropsTheory.nsAll2_nsBindList
      >> simp [LIST_REL_EL_EQN,EL_MAP,ELIM_UNCURRY])
    >> simp [lift_eval_refinement_def])
  >> rewrite_tac [lift_eval_refinement_def] >> disj1_tac
  >> simp [evaluate_decs_def,ELIM_UNCURRY,ETA_AX] >> IF_CASES_TAC
  >- (gvs [EVERY_MEM,EXISTS_MEM,o_DEF] >> gvs [ELIM_UNCURRY]) >> simp []
QED

Theorem compile_decs_sing[local]:
  compile_decs [d] = [compile_dec d]
Proof
  simp [compile_dec_def]
QED

Theorem compile_decs_refinement[local]:
  lift_app_sim (:'ffi) clock D ∧ lift_declare_env_rel D ⇒
  ∀(s:'ffi semanticPrimitives$state) env ds s' env'.
    s.clock ≤ clock ∧ lift_state_rel lift_runtime_rel D s s' ∧
    lift_runtime_env lift_runtime_rel env env' ⇒
    lift_eval_refinement lift_runtime_rel D (lift_runtime_env lift_runtime_rel)
      (evaluate_decs s env ds) (evaluate_decs s' env' (compile_decs ds))
Proof
  strip_tac
  >> ho_match_mp_tac evaluate_decs_ind >> rpt conj_tac >> rpt gen_tac
  >~ [‘evaluate_decs _ _ []’] >- (
    rpt strip_tac
    >> simp [compile_dec_def,evaluate_decs_def,lift_eval_refinement_def,
             lift_eval_result_rel_def,lift_result_rel_def,lift_runtime_env_namespace])
  >~ [‘d1::d2::ds’] >- (
    simp [compile_dec_def] >> rpt strip_tac
    >> irule lift_evaluate_decs_cons_refinement
    >> simp [] >> metis_tac [LESS_EQ_TRANS])
  >~ [‘Dlet locs p e’] >- (
    rpt strip_tac >> simp [compile_decs_sing]
    >> qpat_assum ‘lift_app_sim _ _ _’ (irule o MATCH_MP compile_dlet_refinement)
    >> simp [])
  >~ [‘Dletrec locs funs’] >- (
    rpt strip_tac >> simp [compile_decs_sing]
    >> qpat_assum ‘lift_app_sim _ _ _’ (irule o MATCH_MP compile_dletrec_refinement)
    >> simp [])
  >~ [‘Dtype locs tds’] >- (
    rpt strip_tac
    >> simp [compile_dec_def,evaluate_decs_def] >> IF_CASES_TAC
    >> fs [lift_eval_refinement_def,lift_eval_result_rel_def,lift_result_rel_def,
           lift_state_rel_def,lift_runtime_env_namespace])
  >~ [‘Dtabbrev locs tvs tn t’] >- (
    rpt strip_tac
    >> simp [compile_dec_def,evaluate_decs_def,lift_eval_refinement_def,
             lift_eval_result_rel_def,lift_result_rel_def,lift_runtime_env_namespace])
  >~ [‘Denv n’] >- (
    rpt strip_tac >> simp [compile_dec_def] >> irule lift_evaluate_denv_refinement
    >> simp [])
  >~ [‘Dexn locs cn ts’] >- (
    rpt strip_tac
    >> fs [compile_dec_def,evaluate_decs_def,lift_eval_refinement_def,
           lift_eval_result_rel_def,lift_result_rel_def,lift_state_rel_def,
           lift_runtime_env_namespace])
  >~ [‘Dmod mn ds’] >- (
    rpt strip_tac >> simp [compile_dec_def] >> irule lift_evaluate_dmod_refinement
    >> first_x_assum irule >> simp [])
  >~ [‘Dlocal lds ds’] >- (
    rpt strip_tac >> simp [compile_dec_def] >> irule lift_evaluate_dlocal_refinement
    >> simp [] >> metis_tac [LESS_EQ_TRANS])
  >> rpt strip_tac >> simp [compile_dec_def] >> irule lift_evaluate_dopen_refinement
  >> simp []
QED

Theorem lift_evaluate_eval_decs_refinement[local]:
  lift_eval_result_rel R D (LIST_REL R)
    (evaluate (s:'ffi semanticPrimitives$state) env (REVERSE es))
    (evaluate s' env' (REVERSE es')) ∧
  (∀(t:'ffi semanticPrimitives$state) t' vs vs'.
    lift_state_rel R D t t' ∧ LIST_REL R vs vs' ⇒
    lift_eval_result_rel R D
      (λ(env1,decs) (env1',decs'). E env1 env1' ∧ P decs decs')
      (do_eval_res vs t) (do_eval_res vs' t')) ∧
  (∀(t:'ffi semanticPrimitives$state) t' env1 env1' decs decs'.
    t.clock < s.clock ∧ lift_state_rel R D t t' ∧ E env1 env1' ∧ P decs decs' ⇒
    lift_eval_refinement R D
      (λdelta delta'.
        E (extend_dec_env delta env1) (extend_dec_env delta' env1'))
      (evaluate_decs t env1 decs) (evaluate_decs t' env1' decs')) ∧
  (∀eval_state eval_state' env1 env1'.
    D eval_state eval_state' ∧ E env1 env1' ⇒
    OPTREL (λ(v,next_state) (v',next_state').
      R v v' ∧ D next_state next_state')
      (declare_env eval_state env1) (declare_env eval_state' env1')) ∧
  (∀prior prior' current current'.
    D prior prior' ∧ D current current' ⇒
    D (reset_env_generation prior current)
      (reset_env_generation prior' current')) ⇒
  lift_eval_refinement R D (LIST_REL R)
    (evaluate s env [App Eval es]) (evaluate s' env' [App Eval es'])
Proof
  strip_tac
  >> rewrite_tac [lift_eval_refinement_def]
  >> namedCases_on ‘evaluate s env (REVERSE es)’ ["source_state source_result"]
  >> ‘source_state.clock ≤ s.clock’ by metis_tac [cj 1 evaluate_clock]
  >> namedCases_on ‘evaluate s' env' (REVERSE es')’ ["target_state target_result"]
  >> namedCases_on ‘source_result’ ["source_values","source_error"]
  >> namedCases_on ‘target_result’ ["target_values","target_error"]
  >> gvs [evaluate_def,getOpClass_def,lift_eval_result_rel_def,lift_result_rel_def]
  >> have ‘lift_eval_result_rel R D
        (λ(env1,decs) (env1',decs'). E env1 env1' ∧ P decs decs')
        (do_eval_res (REVERSE source_values) source_state)
        (do_eval_res (REVERSE target_values) target_state)’
  >- (qpat_x_assum ‘∀t t' vs vs'. _’ irule >> simp [LIST_REL_REVERSE])
  >> namedCases_on ‘(do_eval_res (REVERSE source_values) source_state :
         'ffi semanticPrimitives$state # (v sem_env # dec list,v) result)’
       ["source_eval_state source_eval_result"]
  >> have ‘source_eval_state.clock = source_state.clock’
  >- (
    qpat_assum ‘do_eval_res _ source_state = _’
      (mp_tac o Q.AP_TERM ‘λresult. (FST result).clock’)
    >> simp [do_eval_res_clock])
  >> namedCases_on ‘(do_eval_res (REVERSE target_values) target_state :
         'ffi semanticPrimitives$state # (v sem_env # dec list,v) result)’
       ["target_eval_state target_eval_result"]
  >> namedCases_on ‘source_eval_result’ ["source_eval_payload","source_eval_error"]
  >> namedCases_on ‘target_eval_result’ ["target_eval_payload","target_eval_error"]
  >> gvs [lift_eval_result_rel_def,lift_result_rel_def]
  >- (
    namedCases_on ‘source_eval_payload’ ["source_eval_env source_decs"]
    >> namedCases_on ‘target_eval_payload’ ["target_eval_env target_decs"] >> gvs []
    >> ‘source_eval_state.clock = target_eval_state.clock’ by fs [lift_state_rel_def]
    >> Cases_on ‘source_eval_state.clock = 0’
    >> gvs [lift_eval_result_rel_def,lift_result_rel_def]
    >> have ‘lift_eval_refinement R D
          (λdelta delta'. E (extend_dec_env delta source_eval_env)
                             (extend_dec_env delta' target_eval_env))
          (evaluate_decs (dec_clock source_eval_state) source_eval_env source_decs)
          (evaluate_decs (dec_clock target_eval_state) target_eval_env target_decs)’
    >- (
      qpat_x_assum ‘∀t t' env1 env1' decs decs'. _’ irule
      >> simp [lift_state_rel_dec_clock,dec_clock_def]
      >> decide_tac)
    >> namedCases_on
         ‘evaluate_decs (dec_clock source_eval_state) source_eval_env source_decs’
         ["source_decs_state source_decs_result"]
    >> namedCases_on
         ‘evaluate_decs (dec_clock target_eval_state) target_eval_env target_decs’
         ["target_decs_state target_decs_result"]
    >> namedCases_on ‘source_decs_result’ ["source_delta","source_decs_error"]
    >> namedCases_on ‘target_decs_result’ ["target_delta","target_decs_error"]
    >> gvs [lift_eval_refinement_def,lift_eval_result_rel_def,lift_result_rel_def]
    >- (
      have ‘OPTREL (λ(v,next_state) (v',next_state'). R v v' ∧ D next_state next_state')
          (declare_env source_decs_state.eval_state
            (extend_dec_env source_delta source_eval_env))
          (declare_env target_decs_state.eval_state
            (extend_dec_env target_delta target_eval_env))’
      >- (
        qpat_x_assum ‘∀eval_state eval_state' env1 env1'. _’ irule
        >> fs [lift_state_rel_def])
      >> namedCases_on
           ‘declare_env source_decs_state.eval_state
              (extend_dec_env source_delta source_eval_env)’
           ["","source_return"]
      >> namedCases_on
           ‘declare_env target_decs_state.eval_state
              (extend_dec_env target_delta target_eval_env)’
           ["","target_return"]
      >> gvs [lift_eval_refinement_def,lift_eval_result_rel_def,lift_result_rel_def]
      >> namedCases_on ‘source_return’ ["source_return_value source_return_state"]
      >> namedCases_on ‘target_return’ ["target_return_value target_return_state"]
      >> gvs [lift_eval_refinement_def,lift_eval_result_rel_def,lift_result_rel_def,
              lift_state_rel_def])
    >> namedCases_on ‘source_decs_error’ ["source_raised","source_abort"]
    >> namedCases_on ‘target_decs_error’ ["target_raised","target_abort"]
    >> gvs [lift_eval_refinement_def,lift_eval_result_rel_def,lift_result_rel_def,
            lift_state_rel_def]
    >> qpat_x_assum ‘∀prior prior' current current'. _’ irule
    >> simp [])
  >> namedCases_on ‘source_eval_error’ ["source_raised","source_abort"]
  >> namedCases_on ‘target_eval_error’ ["target_raised","target_abort"]
  >> gvs [lift_result_rel_def]
QED

Theorem lift_evaluate_decs_compiled_refinement[local]:
  lift_app_sim (:'ffi) clock D ∧ lift_declare_env_rel D ⇒
  ∀decs decs' (s:'ffi semanticPrimitives$state) s' env env'.
    s.clock ≤ clock ∧ lift_state_rel lift_runtime_rel D s s' ∧
    lift_runtime_env lift_runtime_rel env env' ∧
    (decs' = decs ∨ decs' = compile_decs decs) ⇒
    lift_eval_refinement lift_runtime_rel D (lift_runtime_env lift_runtime_rel)
      (evaluate_decs s env decs) (evaluate_decs s' env' decs')
Proof
  strip_tac
  >> qx_genl_tac [‘decs’,‘decs'’,‘s’,‘s'’,‘env’,‘env'’] >> strip_tac >> gvs []
  >- (
    qpat_assum ‘lift_app_sim _ _ _’
      (assume_tac o MATCH_MP lift_evaluate_runtime_same_refinement)
    >> drule_all lift_evaluate_decs_runtime_same_refinement >> simp [])
  >> drule_all compile_decs_refinement >> simp []
QED

(* ------------------------------------------------------------------------
   Top level
   ------------------------------------------------------------------------ *)

Theorem lift_evaluate_runtime_compiled_app_refinement[local]:
  (∀decs decs'. P decs decs' ⇒ decs' = decs ∨ decs' = compile_decs decs) ∧
  (∀(t:'ffi semanticPrimitives$state) t' vs vs'.
    lift_state_rel lift_runtime_rel D t t' ∧ LIST_REL lift_runtime_rel vs vs' ⇒
    lift_eval_result_rel lift_runtime_rel D
      (λ(env,decs) (env',decs').
        lift_runtime_env lift_runtime_rel env env' ∧ P decs decs')
      (do_eval_res vs t) (do_eval_res vs' t')) ∧
  lift_declare_env_rel D ∧
  (∀prior prior' current current'.
    D prior prior' ∧ D current current' ⇒
    D (reset_env_generation prior current)
      (reset_env_generation prior' current')) ⇒
  ∀clock. lift_app_sim (:'ffi) clock D
Proof
  strip_tac
  >> completeInduct_on ‘clock’ >> rewrite_tac [lift_app_sim_def]
  >> qx_genl_tac [‘op’,‘es’,‘es'’,‘s’,‘s'’,‘env’,‘env'’] >> strip_tac
  >> Cases_on ‘SND (evaluate s env (REVERSE es)) = Rerr (Rabort Rtype_error)’
  >- (
    namedCases_on ‘evaluate s env (REVERSE es)’ ["argument_state argument_result"]
    >> gvs [] >> simp [cj 9 evaluate_def,lift_eval_refinement_def])
  >> drule_all lift_eval_refinement_nonfailure >> disch_tac
  >> Cases_on ‘op = Opapp ∨ op = ThunkOp ForceThunk’
  >- (
    Cases_on ‘clock = 0’
    >- (irule lift_evaluate_runtime_call_refinement >> fs [lift_body_refinement_def])
    >> qpat_assum ‘∀m. m < clock ⇒ _’ (qspec_then ‘clock - 1’ mp_tac) >> impl_tac
    >- decide_tac >> strip_tac
    >> ‘s.clock ≤ clock - 1 + 1’ by decide_tac
    >> qpat_assum ‘lift_app_sim _ _ _’
         (assume_tac o MATCH_MP lift_function_certificate_body_refinement)
    >> qpat_assum ‘lift_app_sim _ _ _’
         (assume_tac o MATCH_MP lift_rec_certificate_body_refinement)
    >> irule lift_evaluate_runtime_call_refinement >> simp [] >> conj_tac
    >- (
      rpt strip_tac
      >> qpat_x_assum
           ‘∀source funs target funs' ren name name' arg body body' value value' caller. _’
           drule_all
      >> simp [])
    >> qpat_assum ‘lift_app_sim _ _ _’
         (assume_tac o MATCH_MP lift_evaluate_runtime_same_refinement)
    >> qx_genl_tac [‘source’,‘target’,‘body’] >> strip_tac
    >> rewrite_tac [lift_body_refinement_def] >> qx_genl_tac [‘t’,‘t'’] >> strip_tac
    >> ‘t.clock ≤ clock - 1’ by decide_tac
    >> qpat_x_assum ‘∀e s s' env env'. _’ irule >> simp [])
  >> Cases_on ‘op = Eval’
  >- (
    gvs []
    >> irule (Q.INST [‘E’ |-> ‘lift_runtime_env lift_runtime_rel’]
         (SPEC_ALL lift_evaluate_eval_decs_refinement))
    >> fs [lift_declare_env_rel_def] >> qexists_tac ‘P’ >> simp []
    >> qx_genl_tac [‘t’,‘t'’,‘source’,‘target’,‘decs’,‘decs'’] >> strip_tac
    >> ‘t.clock < clock’ by decide_tac
    >> qpat_x_assum ‘∀m. m < clock ⇒ _’ (qspec_then ‘t.clock’ mp_tac) >> simp []
    >> strip_tac >> irule lift_eval_refinement_mono
    >> qexists_tac ‘lift_runtime_env lift_runtime_rel’ >> simp [lift_runtime_env_extend]
    >> mp_tac (Q.INST [‘clock’ |-> ‘(t:'ffi semanticPrimitives$state).clock’]
         (SPEC_ALL lift_evaluate_decs_compiled_refinement))
    >> impl_tac
    >- simp [lift_declare_env_rel_def]
    >> disch_then (qspecl_then [‘decs’,‘decs'’,‘t’,‘t'’,‘source’,‘target’] mp_tac)
    >> impl_tac
    >- (
      simp []
      >> qpat_x_assum ‘∀decs decs'. P decs decs' ⇒ _’
           (qspecl_then [‘decs’,‘decs'’] mp_tac)
      >> simp [])
    >> simp [])
  >> Cases_on ‘op = PtrEq’
  >- (gvs [] >> irule (runtime_inst lift_evaluate_ptr_eq) >> simp [])
  >- (
    have ‘getOpClass op = Simple’
    >- (
      Cases_on ‘op’
      >> gvs [getOpClass_def] >> qmatch_asmsub_rename_tac ‘thunk_operation ≠ ForceThunk’
      >> Cases_on ‘thunk_operation’
      >> gvs [])
    >> irule (runtime_inst lift_evaluate_simple)
    >> simp [])
QED

Definition lift_eval_decs_state_rel_def:
  lift_eval_decs_state_rel es es' ⇔
    es = es' ∧ (∀x. es = SOME x ⇒ ∃ev. x = EvalDecs ev)
End

Theorem lift_eval_decs_state_rel_reset[local]:
  lift_eval_decs_state_rel prior prior' ∧
  lift_eval_decs_state_rel current current' ⇒
  lift_eval_decs_state_rel (reset_env_generation prior current)
    (reset_env_generation prior' current')
Proof
  rw [lift_eval_decs_state_rel_def]
  >> namedCases_on ‘current’ ["","current_mode"] >> gvs []
  >> gvs [reset_env_generation_def,AllCaseEqs()]
QED

Theorem lift_eval_decs_state_rel_declare_env[local]:
  lift_declare_env_rel lift_eval_decs_state_rel
Proof
  rewrite_tac [lift_declare_env_rel_def] >> qx_genl_tac [‘es’,‘es'’,‘env’,‘env'’]
  >> rw [lift_eval_decs_state_rel_def] >> namedCases_on ‘es’ ["","eval_mode"]
  >> gvs [declare_env_def,lift_eval_decs_state_rel_def,
       lift_runtime_rel_cases_l,AllCaseEqs()]
  >> qmatch_goalsub_rename_tac ‘eval_decs.env_id_counter’
  >> namedCases_on ‘eval_decs.env_id_counter’ ["generation next_id next_generation"]
  >> simp [lift_runtime_rel_cases_l]
QED

Theorem lift_eval_decs_state_rel_do_eval_state[local]:
  lift_eval_decs_state_rel es es ∧
  do_eval vs es = SOME (env,decs,next_state) ⇒
  lift_eval_decs_state_rel next_state next_state
Proof
  rw [lift_eval_decs_state_rel_def]
  >> namedCases_on ‘es’ ["","eval_mode"] >> gvs [do_eval_def,AllCaseEqs()]
QED

Theorem lift_eval_decs_state_rel_do_eval[local]:
  lift_eval_decs_state_rel es es' ∧ LIST_REL lift_runtime_rel vs vs' ⇒
  OPTREL (λ(env,decs,next_state) (env',decs',next_state').
    lift_runtime_env lift_runtime_rel env env' ∧ decs = decs' ∧
    lift_eval_decs_state_rel next_state next_state')
    (do_eval vs es) (do_eval vs' es')
Proof
  rw [lift_eval_decs_state_rel_def]
  >> namedCases_on ‘es’ ["","eval_mode"] >> gvs []
  >- simp [do_eval_def]
  >> qmatch_goalsub_rename_tac ‘EvalDecs eval_decs’
  >> mp_tac (runtime_inst lift_value_rel_do_eval_decs) >> simp [] >> strip_tac
  >> namedCases_on ‘do_eval vs (SOME (EvalDecs eval_decs))’ ["","source_payload"]
  >> namedCases_on ‘do_eval vs' (SOME (EvalDecs eval_decs))’ ["","target_payload"]
  >> gvs [OPTREL_def]
  >> namedCases_on ‘source_payload’ ["source_env source_decs source_eval_state"]
  >> namedCases_on ‘target_payload’ ["target_env target_decs target_eval_state"]
  >> gvs []
  >> ‘lift_eval_decs_state_rel (SOME (EvalDecs eval_decs))
       (SOME (EvalDecs eval_decs))’ by simp [lift_eval_decs_state_rel_def]
  >> drule_all lift_eval_decs_state_rel_do_eval_state
  >> simp [lift_eval_decs_state_rel_def]
QED

Theorem lift_eval_decs_state_rel_do_eval_res[local]:
  lift_state_rel lift_runtime_rel lift_eval_decs_state_rel
    (s:'ffi semanticPrimitives$state) s' ∧ LIST_REL lift_runtime_rel vs vs' ⇒
  lift_eval_result_rel lift_runtime_rel lift_eval_decs_state_rel
    (λ(env,decs) (env',decs').
      lift_runtime_env lift_runtime_rel env env' ∧ decs = decs')
    (do_eval_res vs s) (do_eval_res vs' s')
Proof
  strip_tac
  >> irule lift_do_eval_res >> simp [] >> irule lift_eval_decs_state_rel_do_eval
  >> fs [lift_state_rel_def]
QED

Theorem lift_evaluate_app_decs_state_refinement[local]:
  ∀clock. lift_app_sim (:'ffi) clock lift_eval_decs_state_rel
Proof
  match_mp_tac (Q.INST [‘P’ |-> ‘λd d'. d = d'’]
    lift_evaluate_runtime_compiled_app_refinement)
  >> simp [lift_eval_decs_state_rel_do_eval_res,
       lift_eval_decs_state_rel_declare_env,lift_eval_decs_state_rel_reset]
QED

Theorem lift_semantics_determ_refinement[local]:
  (∀clock. lift_eval_result_rel R D E
    (evaluate_decs ((s:'ffi semanticPrimitives$state) with clock := clock) env prog)
    (evaluate_decs (s' with clock := clock) env' prog')) ⇒
  semantics_determ s env prog outcome ⇒ semantics_determ s' env' prog' outcome
Proof
  strip_tac
  >> ‘∀clock. ∃ffi r r'.
        evaluate_prog_with_clock s env clock prog = (ffi,r) ∧
        evaluate_prog_with_clock s' env' clock prog' = (ffi,r') ∧
        lift_result_rel E R r r'’ by (
    qx_gen_tac ‘clock’
    >> qpat_x_assum ‘∀clock. lift_eval_result_rel _ _ _ _ _’ (qspec_then ‘clock’ mp_tac)
    >> Cases_on ‘evaluate_decs (s with clock := clock) env prog’
    >> Cases_on ‘evaluate_decs (s' with clock := clock) env' prog'’
    >> simp [evaluate_prog_with_clock_def,lift_eval_result_rel_def,lift_state_rel_def])
  >> Cases_on ‘outcome’ >> rewrite_tac [semantics_determ_def] >> strip_tac
  >- (
    conj_tac
    >- (
      qx_gen_tac ‘k’
      >> qpat_x_assum ‘∀k. ∃ffi. _’ (qspec_then ‘k’ strip_assume_tac)
      >> qpat_x_assum ‘∀clock. ∃ffi r r'. _’
           (qspec_then ‘k’ (strip_assume_tac o REWRITE_RULE [lift_result_rel_cases]))
      >> gvs [])
    >> ‘∀k. FST (evaluate_prog_with_clock s' env' k prog') =
          FST (evaluate_prog_with_clock s env k prog)’ by (
      qx_gen_tac ‘k’
      >> qpat_x_assum ‘∀clock. ∃ffi r r'. _’ (qspec_then ‘k’ strip_assume_tac)
      >> simp [])
    >> qpat_x_assum ‘lprefix_lub _ _’ mp_tac >> asm_rewrite_tac [])
  >> qpat_x_assum ‘∀clock. ∃ffi r r'. _’
       (qspec_then ‘k’ (strip_assume_tac o REWRITE_RULE [lift_result_rel_cases]))
  >> qexists_tac ‘k’ >> gvs []
QED

Theorem lift_semantics_compiled[local]:
  (∀clock. lift_app_sim (:'ffi) clock D) ∧ lift_declare_env_rel D ∧
  lift_state_rel lift_runtime_rel D (s:'ffi semanticPrimitives$state) s' ∧
  lift_runtime_env lift_runtime_rel env env' ∧
  (prog' = prog ∨ prog' = compile_decs prog) ∧
  ¬semantics_determ s env prog Fail ∧ semantics_determ s env prog outcome ⇒
  semantics_determ s' env' prog' outcome
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th))
  >> mp_tac (Q.INST [‘R’ |-> ‘lift_runtime_rel’,‘E’ |-> ‘lift_runtime_env lift_runtime_rel’]
       (SPEC_ALL lift_semantics_determ_refinement))
  >> impl_tac
  >- (
    qx_gen_tac ‘clock’ >> irule lift_eval_refinement_nonfailure >> conj_tac
    >- (
      qpat_x_assum ‘¬semantics_determ s env prog Fail’ mp_tac
      >> simp [semantics_determ_def,evaluate_prog_with_clock_def,ELIM_UNCURRY])
    >> irule lift_evaluate_decs_compiled_refinement >> gvs [lift_state_rel_def]
    >> qexists_tac ‘clock’ >> simp [])
  >> simp []
QED

Theorem compile_semantics:
  (∀x. (s:'ffi semanticPrimitives$state).eval_state = SOME x ⇒ ∃ev. x = EvalDecs ev) ∧
  ¬semantics_determ s env prog Fail ∧ semantics_determ s env prog outcome ⇒
  semantics_determ s env (compile_decs prog) outcome
Proof
  strip_tac >> irule lift_semantics_compiled
  >> qexistsl_tac [‘lift_eval_decs_state_rel’,‘env’,‘prog’,‘s’]
  >> simp [lift_evaluate_app_decs_state_refinement,lift_eval_decs_state_rel_declare_env,
       lift_runtime_env_refl]
  >> irule lift_runtime_state_refl >> simp [lift_eval_decs_state_rel_def]
QED

(* ------------------------------------------------------------------------
   Eval oracle
   ------------------------------------------------------------------------ *)

Definition lift_oracle_state_rel_def:
  lift_oracle_state_rel source_callback target_callback es es' ⇔
    case (es,es') of
      (NONE,NONE) => T
    | (SOME (EvalDecs ed),SOME (EvalDecs ed')) => ed = ed'
    | (SOME (EvalOracle os),SOME (EvalOracle os')) =>
        os.oracle = os'.oracle ∧ os.generation = os'.generation ∧
        os.custom_do_eval = source_callback ∧
        os'.custom_do_eval = target_callback ∧
        LIST_REL (LIST_REL (lift_runtime_env lift_runtime_rel)) os.envs os'.envs
    | _ => F
End

Theorem lift_oracle_state_rel_reset[local]:
  lift_oracle_state_rel source_callback target_callback prior prior' ∧
  lift_oracle_state_rel source_callback target_callback current current' ⇒
  lift_oracle_state_rel source_callback target_callback (reset_env_generation prior current)
    (reset_env_generation prior' current')
Proof
  namedCases_on ‘prior’ ["","source_prior"]
  >> namedCases_on ‘prior'’ ["","target_prior"]
  >> namedCases_on ‘current’ ["","source_current"]
  >> namedCases_on ‘current'’ ["","target_current"]
  >> gvs [lift_oracle_state_rel_def,reset_env_generation_def,AllCaseEqs()]
  >> namedCases_on ‘source_prior’ ["source_prior_decs","source_prior_oracle"]
  >> namedCases_on ‘target_prior’ ["target_prior_decs","target_prior_oracle"]
  >> namedCases_on ‘source_current’ ["source_current_decs","source_current_oracle"]
  >> namedCases_on ‘target_current’ ["target_current_decs","target_current_oracle"]
  >> gvs [AllCaseEqs()] >> namedCases_on ‘target_prior_decs.env_id_counter’
       ["prior_generation prior_id prior_next"]
  >> namedCases_on ‘target_current_decs.env_id_counter’
       ["current_generation current_id current_next"]
  >> simp []
QED

Theorem lift_lookup_env_refinement[local]:
  LIST_REL (LIST_REL E) source.envs target.envs ⇒
  OPTREL E (lookup_env source env_id) (lookup_env target env_id)
Proof
  strip_tac
  >> namedCases_on ‘env_id’ ["generation index"] >> drule LIST_REL_oEL
  >> disch_then (qspec_then ‘generation’ mp_tac)
  >> namedCases_on ‘oEL generation source.envs’ ["","source_envs"]
  >> namedCases_on ‘oEL generation target.envs’ ["","target_envs"]
  >> gvs [lookup_env_def] >> strip_tac >> irule LIST_REL_oEL >> simp []
QED

Theorem lift_oracle_state_rel_add_generation[local]:
  lift_oracle_state_rel source_callback target_callback
    (SOME (EvalOracle source)) (SOME (EvalOracle target)) ⇒
  lift_oracle_state_rel source_callback target_callback
    (SOME (EvalOracle (add_env_generation (source with oracle := next_oracle))))
    (SOME (EvalOracle (add_env_generation (target with oracle := next_oracle))))
Proof
  rw [lift_oracle_state_rel_def,add_env_generation_def]
  >> imp_res_tac LIST_REL_LENGTH >> simp [LIST_REL_APPEND]
QED

Theorem lift_oracle_state_rel_declare_oracle[local]:
  lift_oracle_state_rel source_callback target_callback
    (SOME (EvalOracle source)) (SOME (EvalOracle target)) ∧
  lift_runtime_env lift_runtime_rel env env' ⇒
  OPTREL (λ(value,next_state) (value',next_state').
    lift_runtime_rel value value' ∧
    lift_oracle_state_rel source_callback target_callback next_state next_state')
    (declare_env (SOME (EvalOracle source)) env)
    (declare_env (SOME (EvalOracle target)) env')
Proof
  strip_tac
  >> gvs [lift_oracle_state_rel_def,declare_env_def] >> drule LIST_REL_oEL
  >> disch_then (qspec_then ‘target.generation’ mp_tac)
  >> namedCases_on ‘oEL target.generation source.envs’ ["","source_envs"]
  >> namedCases_on ‘oEL target.generation target.envs’ ["","target_envs"] >> gvs []
  >> strip_tac >> imp_res_tac LIST_REL_LENGTH >> simp [lift_runtime_rel_refl]
  >> irule LIST_REL_LUPDATE_same >> simp [LIST_REL_APPEND]
QED

Theorem lift_oracle_state_rel_declare_env[local]:
  lift_declare_env_rel (lift_oracle_state_rel source_callback target_callback)
Proof
  rewrite_tac [lift_declare_env_rel_def] >> qx_genl_tac [‘es’,‘es'’,‘env’,‘env'’]
  >> strip_tac >> namedCases_on ‘es’ ["","source_mode"] >> namedCases_on ‘es'’ ["","target_mode"]
  >> gvs [lift_oracle_state_rel_def,declare_env_def]
  >> namedCases_on ‘source_mode’ ["source_decs","source_oracle"]
  >> namedCases_on ‘target_mode’ ["target_decs","target_oracle"] >> gvs []
  >- (
    namedCases_on ‘source_decs.env_id_counter’ ["generation next_id next_generation"]
    >> simp [lift_runtime_rel_cases_l])
  >> irule (SRULE
       [lift_oracle_state_rel_def,declare_env_def]
       lift_oracle_state_rel_declare_oracle)
  >> simp []
QED

Theorem lift_oracle_state_rel_do_eval_oracle[local]:
  (∀vs vs' oracle.
    LIST_REL lift_runtime_rel vs vs' ⇒
    OPTREL (λ(env_id,oracle,decs) (env_id',oracle',decs').
      env_id = env_id' ∧ oracle = oracle' ∧ P decs decs')
      (source_callback vs oracle) (target_callback vs' oracle)) ∧
  lift_oracle_state_rel source_callback target_callback
    (SOME (EvalOracle source)) (SOME (EvalOracle target)) ∧
  LIST_REL lift_runtime_rel vs vs' ⇒
  OPTREL (λ(env,decs,next_state) (env',decs',next_state').
    lift_runtime_env lift_runtime_rel env env' ∧ P decs decs' ∧
    lift_oracle_state_rel source_callback target_callback next_state next_state')
    (do_eval vs (SOME (EvalOracle source)))
    (do_eval vs' (SOME (EvalOracle target)))
Proof
  strip_tac
  >> qpat_assum ‘lift_oracle_state_rel _ _ _ _’
       (mp_tac o SRULE [lift_oracle_state_rel_def])
  >> strip_tac >> qpat_x_assum ‘∀vs vs' oracle. _’
       (qspecl_then [‘vs’,‘vs'’,‘target.oracle’] mp_tac)
  >> simp [] >> namedCases_on ‘source_callback vs target.oracle’ ["","source_result"]
  >> namedCases_on ‘target_callback vs' target.oracle’ ["","target_result"]
  >> gvs [do_eval_def] >> PairCases_on ‘source_result’
  >> PairCases_on ‘target_result’ >> gvs [] >> strip_tac >> gvs []
  >> qmatch_goalsub_rename_tac ‘lookup_env source (generation,index)’
  >> qmatch_goalsub_rename_tac ‘source with oracle := next_oracle’
  >> drule lift_lookup_env_refinement
  >> disch_then (qspec_then ‘(generation,index)’ mp_tac)
  >> namedCases_on ‘lookup_env source (generation,index)’ ["","source_env"]
  >> namedCases_on ‘lookup_env target (generation,index)’ ["","target_env"] >> gvs []
  >> strip_tac >> simp [] >> irule lift_oracle_state_rel_add_generation >> simp []
QED

Theorem lift_eval_decs_oracle_state_rel[local]:
  lift_eval_decs_state_rel es es' ⇒
  lift_oracle_state_rel source_callback target_callback es es'
Proof
  rw [lift_eval_decs_state_rel_def]
  >> namedCases_on ‘es’ ["","eval_mode"] >> gvs [lift_oracle_state_rel_def]
QED

Theorem lift_oracle_state_rel_do_eval[local]:
  (∀decs. P decs decs) ∧
  (∀vs vs' oracle.
    LIST_REL lift_runtime_rel vs vs' ⇒
    OPTREL (λ(env_id,oracle,decs) (env_id',oracle',decs').
      env_id = env_id' ∧ oracle = oracle' ∧ P decs decs')
      (source_callback vs oracle) (target_callback vs' oracle)) ∧
  lift_oracle_state_rel source_callback target_callback es es' ∧
  LIST_REL lift_runtime_rel vs vs' ⇒
  OPTREL (λ(env,decs,next_state) (env',decs',next_state').
    lift_runtime_env lift_runtime_rel env env' ∧ P decs decs' ∧
    lift_oracle_state_rel source_callback target_callback next_state next_state')
    (do_eval vs es) (do_eval vs' es')
Proof
  strip_tac
  >> namedCases_on ‘es’ ["","source_mode"] >> namedCases_on ‘es'’ ["","target_mode"]
  >> gvs [lift_oracle_state_rel_def]
  >- simp [do_eval_def]
  >> namedCases_on ‘source_mode’ ["source_decs","source_oracle"]
  >> namedCases_on ‘target_mode’ ["target_decs","target_oracle"] >> gvs []
  >- (
    ‘lift_eval_decs_state_rel (SOME (EvalDecs source_decs))
       (SOME (EvalDecs source_decs))’ by simp [lift_eval_decs_state_rel_def]
    >> drule_all lift_eval_decs_state_rel_do_eval
    >> namedCases_on ‘do_eval vs (SOME (EvalDecs source_decs))’ ["","source_payload"]
    >> namedCases_on ‘do_eval vs' (SOME (EvalDecs source_decs))’ ["","target_payload"]
    >> gvs [OPTREL_def]
    >> namedCases_on ‘source_payload’ ["source_env source_declarations source_state"]
    >> namedCases_on ‘target_payload’ ["target_env target_declarations target_state"]
    >> gvs [] >> strip_tac >> simp []
    >> irule (SRULE [lift_oracle_state_rel_def]
         lift_eval_decs_oracle_state_rel)
    >> simp [])
  >> irule (SRULE [lift_oracle_state_rel_def]
    lift_oracle_state_rel_do_eval_oracle)
  >> simp []
QED

Theorem lift_oracle_state_rel_do_eval_res[local]:
  (∀decs. P decs decs) ∧
  (∀vs vs' oracle.
    LIST_REL lift_runtime_rel vs vs' ⇒
    OPTREL (λ(env_id,oracle,decs) (env_id',oracle',decs').
      env_id = env_id' ∧ oracle = oracle' ∧ P decs decs')
      (source_callback vs oracle) (target_callback vs' oracle)) ∧
  lift_state_rel lift_runtime_rel
    (lift_oracle_state_rel source_callback target_callback)
    (s:'ffi semanticPrimitives$state) s' ∧
  LIST_REL lift_runtime_rel vs vs' ⇒
  lift_eval_result_rel lift_runtime_rel
    (lift_oracle_state_rel source_callback target_callback)
    (λ(env,decs) (env',decs').
      lift_runtime_env lift_runtime_rel env env' ∧ P decs decs')
    (do_eval_res vs s) (do_eval_res vs' s')
Proof
  strip_tac
  >> irule lift_do_eval_res >> simp [] >> irule lift_oracle_state_rel_do_eval
  >> gvs [lift_state_rel_def]
QED

Theorem lift_oracle_compiler_arguments[local]:
  lift_runtime_rel value value' ⇒
  v_to_mlstring value = v_to_mlstring value' ∧
  v_to_word64_list value = v_to_word64_list value'
Proof
  rw [lift_runtime_rel_unfold]
  >> metis_tac [lift_value_rel_compiler_literals,lift_value_rel_compiler_words]
QED

Theorem do_eval_oracle_shape[local]:
  do_eval_oracle compiler g vs orac = SOME r ⇒
  ∃a b c d e h. vs = [a; b; c; d; e; h]
Proof
  rw [do_eval_oracle_def,AllCaseEqs()] >> simp []
QED

Theorem lift_do_eval_oracle[local]:
  LIST_REL lift_runtime_rel vs vs' ⇒
  OPTREL (λ(env_id,orac,decs) (env_id',orac',decs').
    env_id = env_id' ∧ orac = orac' ∧ decs' = compile_decs decs)
    (do_eval_oracle compiler f vs orac)
    (do_eval_oracle compiler (compile_decs ∘ f) vs' orac)
Proof
  strip_tac
  >> Cases_on ‘∃a b c d e h. vs = [a; b; c; d; e; h]’
  >- (
    gvs [LIST_REL_CONS1] >> imp_res_tac lift_oracle_compiler_arguments
    >> simp [do_eval_oracle_def] >> pairarg_tac >> simp []
    >> rpt CASE_TAC >> simp [])
  >> Cases_on ‘do_eval_oracle compiler f vs orac’
  >- (
    Cases_on ‘do_eval_oracle compiler (compile_decs ∘ f) vs' orac’ >> simp []
    >> drule do_eval_oracle_shape >> strip_tac >> gvs [LIST_REL_CONS2])
  >> drule do_eval_oracle_shape >> metis_tac []
QED

Theorem lift_adjust_oracle_state_rel[local]:
  is_insert_oracle ci f es ⇒
  lift_oracle_state_rel
    (do_eval_oracle (mk_compiler_fun_from_ci ci) f)
    (do_eval_oracle (mk_compiler_fun_from_ci ci) (compile_decs ∘ f))
    es (adjust_oracle ci (compile_decs ∘ f) es)
Proof
  rewrite_tac [is_insert_oracle_def]
  >> disch_then (qx_choosel_then [‘initial_state’,‘shift’,‘orac’] strip_assume_tac)
  >> namedCases_on ‘initial_state’ ["","initial_mode"]
  >> gvs [insert_gen_oracle_def,adjust_oracle_def,lift_oracle_state_rel_def]
  >> Cases_on ‘initial_mode’ >> gvs [LIST_REL_refl,lift_runtime_env_refl]
QED

Theorem compile_semantics_oracle:
  ∀f.
  is_insert_oracle ci f s.eval_state ∧
  ¬ semantics_determ s env prog Fail ∧
  semantics_determ s env prog outcome ⇒
  semantics_determ (s with eval_state updated_by
            adjust_oracle ci (compile_decs ∘ f))
        env prog outcome
Proof
  rpt strip_tac >> irule lift_semantics_compiled
  >> qexistsl_tac [‘lift_oracle_state_rel (do_eval_oracle (mk_compiler_fun_from_ci ci) f)
       (do_eval_oracle (mk_compiler_fun_from_ci ci) (compile_decs ∘ f))’,‘env’,‘prog’,‘s’]
  >> simp [lift_state_rel_def,lift_adjust_oracle_state_rel,LIST_REL_refl,
       lift_runtime_store_refl,lift_runtime_env_refl,lift_oracle_state_rel_declare_env]
  >> gen_tac >> irule lift_evaluate_runtime_compiled_app_refinement
  >> simp [lift_oracle_state_rel_declare_env,lift_oracle_state_rel_reset]
  >> qexists_tac ‘λdecs decs'. decs' = decs ∨ decs' = compile_decs decs’
  >> conj_tac >- simp [] >> rpt strip_tac
  >> irule (Q.INST [‘P’ |-> ‘λdecs decs'. decs' = decs ∨ decs' = compile_decs decs’]
       lift_oracle_state_rel_do_eval_res)
  >> simp [] >> rpt strip_tac >> irule OPTREL_MONO
  >> irule_at Any lift_do_eval_oracle >> simp [FORALL_PROD]
QED
