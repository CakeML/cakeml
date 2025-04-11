(*
  Semantics of Scheme
*)
open preamble;
open mlstringTheory;
open scheme_astTheory;
open finite_mapTheory;

val _ = new_theory "scheme_semantics";

Datatype:
  e_or_v = Exp exp | Val val | Exception mlstring
End

Definition sadd_def:
  sadd [] n = Val $ SNum n ∧
  sadd (SNum m :: xs) n = sadd xs (m + n) ∧
  sadd (_ :: xs) _ = Exception $ strlit "Arith-op applied to non-number"
End

Definition smul_def:
  smul [] n = Val $ SNum n ∧
  smul (SNum m :: xs) n = smul xs (m * n) ∧
  smul (_ :: xs) _ = Exception $ strlit "Arith-op applied to non-number"
End

Definition sminus_def:
  sminus [] = Exception $ strlit "Arity mismatch" ∧
  sminus (SNum n :: xs) = (case sadd xs 0 of
  | Val (SNum m) => Val (SNum (n - m))
  | e => e) ∧
  sminus _ = Exception $ strlit "Arith-op applied to non-number"
End

Definition seqv_def:
  seqv [v1; v2] = (if v1 = v2 then Val $ SBool T else Val $ SBool F) ∧
  seqv _ = Exception $ strlit "Arity mismatch"
End

(*
Definition strict_def:
  strict (Prim SAdd) xs = sadd xs 0 ∧
  strict (Prim SMul) xs = smul xs 1
End

Definition semantics_def:
  semantics (Val v) = v ∧
  semantics (Apply fn args) = strict (semantics fn) (MAP semantics args)
Termination
  WF_REL_TAC ‘measure exp_size’
End
*)

Definition fresh_loc_def:
  fresh_loc store ov = (LENGTH store, SNOC ov store)
End

Definition parameterize_def:
  parameterize store env [] NONE e [] = (store, env, Exp e) ∧
  parameterize store env [] (SOME (l:mlstring)) e xs = (let (n, store') = fresh_loc store (SOME $ SList xs)
    in (store', (env |+ (l, n)), Exp e)) ∧
  parameterize store env (p::ps) lp e (x::xs) = (let (n, store') = fresh_loc store (SOME x)
    in parameterize store' (env |+ (p, n)) ps lp e xs) ∧
  parameterize store _ _ _ _ _ = (store, FEMPTY, Exception $ strlit "Wrong number of arguments")
End

Definition application_def:
  application store ks (Prim p) xs = (case p of
  | SAdd => (store, ks, FEMPTY, sadd xs 0)
  | SMul => (store, ks, FEMPTY, smul xs 1)
  | SMinus => (store, ks, FEMPTY, sminus xs)
  | SEqv => (store, ks, FEMPTY, seqv xs)
  | CallCC => case xs of
    | [v] => (store, (FEMPTY, ApplyK (SOME (v, [])) []) :: ks, FEMPTY, Val $ Throw ks)
    | _ => (store, ks, FEMPTY, Exception $ strlit "Arity mismatch")) ∧
  application store ks (Proc env ps lp e) xs = (let (store', env', e') =
    parameterize store env ps lp e xs in (store', ks, env', e')) ∧
  application store ks (Throw ks') xs = (case xs of
    | [v] => (store, ks', FEMPTY, Val v)
    | _ => (store, ks, FEMPTY, Exception $ strlit "Arity mismatch")) ∧
  application store ks _ _ = (store, ks, FEMPTY, Exception $ strlit "Not a procedure")
End

Definition return_def:
  return store [] v = (store, [], FEMPTY, Val v) ∧

  return store ((env, ApplyK NONE eargs) :: ks) v = (case eargs of
  | [] => application store ks v []
  | e::es => (store, (env, ApplyK (SOME (v, [])) es) :: ks, env, Exp e)) ∧
  return store ((env, ApplyK (SOME (vfn, vargs)) eargs) :: ks) v = (case eargs of
  | [] => application store ks vfn (REVERSE $ v::vargs)
  | e::es => (store, (env, ApplyK (SOME (vfn, v::vargs)) es) :: ks, env, Exp e)) ∧

  return store ((env, CondK t f) :: ks) v = (if v = (SBool F)
    then (store, ks, env, Exp f) else (store, ks, env, Exp t)) ∧

  return store ((env, BeginK es e) :: ks) v = (case es of
  | [] => (store, ks, env, Exp e)
  | e'::es' => (store, (env, BeginK es' e) :: ks, env, Exp e')) ∧
  return store ((env, SetK x) :: ks) v = (LUPDATE (SOME v) (env ' x) store, ks, env, Val $ Wrong "Unspecified")
End

Definition letrec_init_def:
  letrec_init store env [] = (store, env) ∧
  letrec_init store env (x::xs) = (let (n, store') = fresh_loc store NONE
    in letrec_init store' (env |+ (x, n)) xs)
End

Definition step_def:
  step (store, ks, env, Val v) = return store ks v ∧
  step (store, ks, env, Exp $ Lit lit) = (store, ks, env, Val $ lit_to_val lit) ∧
  step (store, ks, env, Exp $ Apply fn args) = (store, (env, ApplyK NONE args) :: ks, env, Exp fn) ∧
  step (store, ks, env, Exp $ Cond c t f) = (store, (env, CondK t f) :: ks, env, Exp c) ∧
  (*This is undefined if the program doesn't typecheck*)
  step (store, ks, env, Exp $ Ident s) = (let ev = case EL (env ' s) store of
    | NONE => Exception $ strlit "letrec variable touched"
    | SOME v => Val v
    in (store, ks, env, ev)) ∧
  step (store, ks, env, Exp $ Lambda ps lp e) = (store, ks, env, Val $ Proc env ps lp e) ∧
  step (store, ks, env, Exp $ Begin es e) = (case es of
  | [] => (store, ks, env, Exp e)
  | e'::es' => (store, (env, BeginK es' e) :: ks, env, Exp e')) ∧
  step (store, ks, env, Exp $ Set x e) = (store, (env, SetK x) :: ks, env, Exp e) ∧
  (*There is a missing reinit check, though the spec says it is optional*)
  step (store, ks, env, Exp $ Letrec bs e) = (let
    (store', env') = letrec_init store env (MAP FST bs)
      in (store', ks, env', Exp $ Begin (MAP (UNCURRY Set) bs) e)) ∧

  step (store, ks, env, Exception ex) = (store, [], env, Exception ex)
End

Definition steps_def:
  steps (n:num) t = if n = 0 then t
    else steps (n - 1) $ step t
End

Definition option_to_set_def:
  option_to_set NONE = ∅ ∧
  option_to_set (SOME x) = {x}
End

Inductive can_lookup:
  FEVERY (λ (x, n). n < LENGTH store) env
  ⇒
  can_lookup env store
End

Inductive valid_val:
[~val_SNum:]
  valid_val store (SNum n)
[~val_SBool:]
  valid_val store (SBool b)
[~val_Prim:]
  valid_val store (Prim p)
[~val_Wrong:]
  valid_val store (Wrong w)
[~val_SList:]
  EVERY (valid_val store) vs
  ⇒
  valid_val store (SList vs)
[~val_Proc_NONE:]
  static_scope (FDOM env ∪ set xs) e ∧
  can_lookup env store
  ⇒
  valid_val store (Proc env xs NONE e)
[~val_Proc_SOME:]
  static_scope (FDOM env ∪ set (x::xs)) e ∧
  can_lookup env store
  ⇒
  valid_val store (Proc env xs (SOME x) e)
[~val_Throw:]
  valid_cont store ks
  ⇒
  valid_val store (Throw ks)

[~cont_Id:]
  valid_cont store []
[~cont_CondK:]
  static_scope (FDOM env) t ∧
  static_scope (FDOM env) f ∧
  valid_cont store ks ∧
  can_lookup env store
  ⇒
  valid_cont store ((env, CondK t f)::ks)
[~cont_ApplyK_NONE:]
  EVERY (static_scope (FDOM env)) es ∧
  valid_cont store ks ∧
  can_lookup env store
  ⇒
  valid_cont store ((env, ApplyK NONE es)::ks)
[~cont_ApplyK_SOME:]
  valid_val store fn ∧
  EVERY (valid_val store) vs ∧
  EVERY (static_scope (FDOM env)) es ∧
  valid_cont store ks ∧
  can_lookup env store
  ⇒
  valid_cont store ((env, ApplyK (SOME (fn, vs)) es)::ks)
[~cont_BeginK:]
  EVERY (static_scope (FDOM env)) es ∧
  static_scope (FDOM env) e ∧
  valid_cont store ks ∧
  can_lookup env store
  ⇒
  valid_cont store ((env, BeginK es e)::ks)
[~cont_SetK:]
  (FDOM env) x ∧
  valid_cont store ks ∧
  can_lookup env store
  ⇒
  valid_cont store ((env, SetK x)::ks)
End

Inductive valid_state:
[~Val:]
  valid_val store v ∧
  valid_cont store ks ∧
  can_lookup env store ∧
  EVERY (OPTION_ALL (valid_val store)) store
  ⇒
  valid_state store ks env (Val v)
[~Exp:]
  static_scope (FDOM env) e ∧
  valid_cont store ks ∧
  can_lookup env store ∧
  EVERY (OPTION_ALL (valid_val store)) store
  ⇒
  valid_state store ks env (Exp e)
[~Exception:]
  valid_state store ks env (Exception s)
End

Theorem FEVERY_MONO:
  ∀ P Q f .
    (∀ x . P x ⇒ Q x) ∧ FEVERY P f
    ⇒
    FEVERY Q f
Proof
  Induct_on ‘f’
  >> rpt strip_tac >- simp[FEVERY_FEMPTY]
  >> last_x_assum $ drule_then assume_tac
  >> gvs[FEVERY_FUPDATE]
  >> qsuff_tac ‘DRESTRICT f (COMPL {x}) = f’ >- (strip_tac >> gvs[])
  >> simp[EQ_FDOM_SUBMAP, DRESTRICT_DEF, EXTENSION]
  >> strip_tac
  >> iff_tac
  >> rpt strip_tac
  >> gvs[]
QED

Theorem EVERY_OPTION_ALL_MAP_SOME:
  ∀ f xs . EVERY f xs ⇒ EVERY (OPTION_ALL f) (MAP SOME xs)
Proof
  strip_tac
  >> Induct
  >> simp[]
QED

Theorem EVERY_TAKE:
  ∀ f n xs . EVERY f xs ⇒ EVERY f (TAKE n xs)
Proof
  gen_tac
  >> Induct_on ‘xs’
  >> Cases_on ‘n’
  >> simp[]
QED

Theorem valid_larger_store:
  ∀ (store :'a list) (store' :'a list) .
    LENGTH store ≤ LENGTH store'
    ⇒
    (∀ v .
      valid_val store v
      ⇒
      valid_val store' v) ∧
    ∀ ks .
      valid_cont store ks
      ⇒
      valid_cont store' ks
Proof
  rpt gen_tac >> strip_tac
  >> ho_match_mp_tac valid_val_ind
  >> rpt strip_tac
  >> simp[Once valid_val_cases]
  >> gvs[can_lookup_cases]
  >> gvs[SF ETA_ss]
  >> irule FEVERY_MONO
  >> pop_assum $ irule_at (Pos last)
  >> PairCases
  >> rpt strip_tac
  >> gvs[]
QED

Theorem valid_val_larger_store = SRULE [PULL_FORALL, AND_IMP_INTRO] $
  cj 1 valid_larger_store;
Theorem valid_cont_larger_store = SRULE [PULL_FORALL, AND_IMP_INTRO] $
  cj 2 valid_larger_store;

Theorem letrec_init_mono:
  ∀ bs store env store' env' .
    letrec_init store env bs = (store', env')
    ⇒
    FDOM env ⊆ FDOM env'
Proof
  Induct
  >> simp[letrec_init_def]
  >> rpt strip_tac
  >> rpt (pairarg_tac >> gvs[])
  >> last_x_assum drule
  >> simp[]
QED

Theorem letrec_init_dom:
  ∀ xs store env store' env' .
    letrec_init store env xs = (store', env')
    ⇒
    FDOM env ∪ set xs = FDOM env' ∧
    store ++ GENLIST (λ x. NONE) (LENGTH xs) = store'
Proof
  Induct
  >> simp[letrec_init_def, fresh_loc_def]
  >> rpt strip_tac
  >> rpt (pairarg_tac >> gvs[])
  >> last_x_assum $ drule_then assume_tac
  >> gvs[GENLIST] >- (
    rpt strip_tac
    >> qpat_x_assum ‘_ ∪ _ = _’ $ simp o single o GSYM
    >> simp[EXTENSION]
    >> simp[UNION_DEF, INSERT_DEF, SPECIFICATION, GSYM DISJ_ASSOC]
    >> strip_tac
    >> iff_tac
    >> rw[] >> rw[]
  )
  >> rpt $ pop_assum kall_tac
  >> ‘∃ n . LENGTH xs = n’ by simp[]
  >> simp[]
  >> pop_assum kall_tac
  >> Induct_on ‘n’
  >> simp[GENLIST]
QED

Theorem letrec_init_lookup:
  ∀ xs store env store' env' .
    can_lookup env store ∧
    letrec_init store env xs = (store', env')
    ⇒
    can_lookup env' store'
Proof
  Induct
  >> simp[letrec_init_def, fresh_loc_def]
  >> rpt strip_tac
  >> rpt (pairarg_tac >> gvs[])
  >> qsuff_tac ‘can_lookup (env |+ (h,LENGTH store)) (SNOC NONE store)’ >- (
    strip_tac
    >> last_x_assum drule_all
    >> simp[]
  )
  >> gvs[can_lookup_cases]
  >> qsuff_tac ‘FEVERY (λ(x,n). n < SUC (LENGTH store)) env’ >- (
    strip_tac
    >> irule $ cj 2 FEVERY_STRENGTHEN_THM
    >> simp[]
  )
  >> irule FEVERY_MONO
  >> qpat_assum ‘FEVERY _ _’ $ irule_at (Pos last)
  >> PairCases
  >> simp[]
QED

Theorem parameterize_NONE_dom:
  ∀ xs store env vs store' env' e e' .
    LENGTH xs = LENGTH vs ∧
    parameterize store env xs NONE e vs = (store', env', e')
    ⇒
    Exp e = e' ∧
    FDOM env ∪ set xs = FDOM env' ∧
    store ++ MAP SOME vs = store'
Proof
  Induct
  >> simp[parameterize_def]
  >> Cases_on ‘vs’
  >> simp[parameterize_def]
  >> rpt strip_tac
  >> rpt (pairarg_tac >> gvs[])
  >> last_x_assum $ drule_at (Pos $ el 2)
  >> rpt strip_tac
  >> gvs[] >- (
    pop_assum $ simp o single o GSYM
    >> simp[Once INSERT_SING_UNION, EXTENSION]
    >> strip_tac
    >> iff_tac
    >> strip_tac
    >> simp[]
  )
  >> gvs[fresh_loc_def]
QED

Theorem parameterize_NONE_lookup:
  ∀ xs store env vs store' env' e e' .
    LENGTH xs = LENGTH vs ∧
    can_lookup env store ∧
    parameterize store env xs NONE e vs = (store', env', e')
    ⇒
    can_lookup env' store'
Proof
  Induct
  >> simp[parameterize_def]
  >> Cases_on ‘vs’
  >> simp[parameterize_def]
  >> rpt strip_tac
  >> rpt (pairarg_tac >> gvs[])
  >> last_x_assum $ drule_at (Pos $ el 3)
  >> rpt strip_tac
  >> gvs[]
  >> pop_assum irule
  >> gvs[can_lookup_cases, fresh_loc_def]
  >> irule $ cj 2 FEVERY_STRENGTHEN_THM
  >> simp[]
  >> irule $ FEVERY_MONO
  >> qpat_assum ‘FEVERY _ _’ $ irule_at (Pos last)
  >> PairCases
  >> simp[]
QED

Theorem parameterize_NONE_exception:
  ∀ xs store env vs store' env' e e' .
    LENGTH xs ≠ LENGTH vs ∧
    parameterize store env xs NONE e vs = (store', env', e')
    ⇒
    ∃ s . Exception s = e'
Proof
  Induct
  >> Cases_on ‘vs’
  >> simp[parameterize_def]
  >> rpt strip_tac
  >> rpt (pairarg_tac >> gvs[])
  >> last_x_assum drule_all
  >> simp[]
QED

Theorem parameterize_SOME_dom:
  ∀ xs vs store env x store' env' e e' .
    LENGTH xs ≤ LENGTH vs ∧
    parameterize store env xs (SOME x) e vs = (store', env', e')
    ⇒
    Exp e = e' ∧
    FDOM env ∪ set (x::xs) = FDOM env' ∧
    store ++ MAP SOME (TAKE (LENGTH xs) vs)
      ++ [SOME (SList (REVERSE (TAKE (LENGTH vs - LENGTH xs) (REVERSE vs))))]
      = store'
Proof
  gen_tac >> gen_tac
  >> ‘∃ n . n = LENGTH vs - LENGTH xs’ by simp[]
  >> pop_assum mp_tac
  >> qid_spec_tac ‘vs’
  >> Induct_on ‘xs’
  >> simp[parameterize_def, fresh_loc_def] >- (
    strip_tac >> strip_tac
    >> simp_tac bool_ss [Once $ GSYM LENGTH_REVERSE]
    >> simp[TAKE_LENGTH_ID]
    >> simp[Once UNION_COMM]
    >> simp[Once $ GSYM INSERT_SING_UNION]
  )
  >> Cases_on ‘vs’
  >> simp[parameterize_def]
  >> rpt strip_tac
  >> rpt (pairarg_tac >> gvs[])
  >> last_x_assum $ drule_at (Pos $ el 3)
  >> rpt strip_tac
  >> gvs[fresh_loc_def] >- (
    pop_assum $ simp o single o GSYM
    >> simp[EXTENSION]
    >> strip_tac
    >> iff_tac
    >> strip_tac
    >> simp[]
  )
  >> simp[TAKE_APPEND1]
QED

Theorem parameterize_SOME_lookup:
  ∀ xs vs store env x store' env' e e' .
    LENGTH xs ≤ LENGTH vs ∧
    can_lookup env store ∧
    parameterize store env xs (SOME x) e vs = (store', env', e')
    ⇒
    can_lookup env' store'
Proof
  gen_tac >> gen_tac
  >> ‘∃ n . n = LENGTH vs - LENGTH xs’ by simp[]
  >> pop_assum mp_tac
  >> qid_spec_tac ‘vs’
  >> Induct_on ‘xs’
  >> simp[parameterize_def, fresh_loc_def] >- (
    simp[can_lookup_cases]
    >> rpt strip_tac
    >> irule $ cj 2 FEVERY_STRENGTHEN_THM
    >> simp[]
    >> irule $ FEVERY_MONO
    >> qpat_assum ‘FEVERY _ _’ $ irule_at (Pos last)
    >> PairCases
    >> simp[]
  )
  >> Cases_on ‘vs’
  >> simp[parameterize_def]
  >> rpt strip_tac
  >> rpt (pairarg_tac >> gvs[])
  >> last_x_assum $ drule_at (Pos $ el 4)
  >> rpt strip_tac
  >> gvs[]
  >> pop_assum irule
  >> gvs[fresh_loc_def, can_lookup_cases]
  >> irule $ cj 2 FEVERY_STRENGTHEN_THM
  >> simp[]
  >> irule $ FEVERY_MONO
  >> qpat_assum ‘FEVERY _ _’ $ irule_at (Pos last)
  >> PairCases
  >> simp[]
QED

Theorem parameterize_SOME_exception:
  ∀ xs store env x vs store' env' e e' .
    LENGTH vs < LENGTH xs ∧
    parameterize store env xs (SOME x) e vs = (store', env', e')
    ⇒
    ∃ s . Exception s = e'
Proof
  Induct
  >> Cases_on ‘vs’
  >> simp[parameterize_def]
  >> rpt strip_tac
  >> rpt (pairarg_tac >> gvs[])
  >> last_x_assum drule_all
  >> simp[]
QED

Theorem sadd_num_or_exception:
  ∀ vs n .
    (∃ m . sadd vs n = Val (SNum m)) ∨
    (∃ s . sadd vs n = Exception s)
Proof
  Induct
  >> simp[sadd_def]
  >> Cases
  >> simp[sadd_def]
QED

Theorem smul_num_or_exception:
  ∀ vs n .
    (∃ m . smul vs n = Val (SNum m)) ∨
    (∃ s . smul vs n = Exception s)
Proof
  Induct
  >> simp[smul_def]
  >> Cases
  >> simp[smul_def]
QED

Theorem sminus_num_or_exception:
  ∀ vs .
    (∃ m . sminus vs = Val (SNum m)) ∨
    (∃ s . sminus vs = Exception s)
Proof
  Cases
  >> simp[sminus_def]
  >> Cases_on ‘h’
  >> simp[sminus_def]
  >> qspecl_then [‘t’, ‘0’] assume_tac sadd_num_or_exception
  >> EVERY_CASE_TAC
  >> gvs[]
QED

Theorem seqv_bool_or_exception:
  ∀ vs .
    (∃ b . seqv vs = Val (SBool b)) ∨
    (∃ s . seqv vs = Exception s)
Proof
  Cases
  >> simp[seqv_def]
  >> Cases_on ‘t’
  >> simp[seqv_def]
  >> Cases_on ‘t'’
  >> simp[seqv_def]
  >> IF_CASES_TAC
  >> simp[]
QED

Theorem valid_state_progress:
  ∀ store ks env state .
    valid_state store ks env state
    ⇒
    ∃ store' ks' env' state' .
      step (store, ks, env, state) = (store', ks', env', state') ∧
      valid_state store' ks' env' state'
Proof
  Cases_on ‘state’
  >> rpt strip_tac
  >~ [‘Exp e’] >- (
    Cases_on ‘e’
    >~ [‘Lit l’] >- (
      Cases_on ‘l’
      >> simp[step_def, lit_to_val_def]
      >> simp[Once valid_state_cases, Once valid_val_cases]
      >> gvs[Once valid_state_cases]
    )
    >~ [‘Begin es e’] >- (
      Cases_on ‘es’ >- (
        simp[step_def, Once valid_state_cases]
        >> gvs[Once valid_state_cases, Once static_scope_cases]
      )
      >> simp[step_def, Once valid_state_cases]
      >> simp[Once valid_val_cases]
      >> gvs[Once valid_state_cases, Once static_scope_cases]
    )
    >~ [‘Ident x’] >- (
      simp[step_def]
      >> gvs[Once valid_state_cases, Once static_scope_cases, can_lookup_cases]
      >> ‘∀ x . FDOM env x ⇒ ∃ a. FLOOKUP env x = SOME a’
        by simp[FLOOKUP_DEF, SPECIFICATION]
      >> pop_assum drule >> strip_tac
      >> drule_all_then assume_tac FEVERY_FLOOKUP
      >> qpat_assum ‘EVERY _ _’ $ assume_tac o SRULE [EVERY_EL]
      >> gvs[]
      >> pop_assum $ drule_then assume_tac
      >> ‘∀ x a . FLOOKUP env x = SOME a ⇒ env ' x = a’ by simp[FLOOKUP_DEF]
      >> pop_assum $ drule_then assume_tac
      >> simp[]
      >> Cases_on ‘EL a store’ >- simp[Once valid_state_cases]
      >> gvs[Once valid_state_cases, can_lookup_cases]
    )
    >~ [‘Letrec bs e’] >- (
      simp[step_def]
      >> rpt (pairarg_tac >> gvs[])
      >> simp[Once valid_state_cases, Once static_scope_cases]
      >> gvs[Once valid_state_cases, Once static_scope_cases]
      >> drule_then assume_tac letrec_init_dom
      >> drule_all_then assume_tac letrec_init_lookup
      >> gvs[]
      >> irule_at (Pos $ el 2) valid_cont_larger_store
      >> qpat_assum ‘valid_cont _ _’ $ irule_at (Pos $ el 2)
      >> simp[]
      >> irule_at (Pos $ el 2) EVERY_MONOTONIC
      >> qpat_assum ‘EVERY (OPTION_ALL _) _’ $ irule_at (Pos $ el 2)
      >> strip_tac >- (
        rpt strip_tac
        >> irule_at (Pos hd) OPTION_ALL_MONO
        >> pop_assum $ irule_at (Pos last)
        >> rpt strip_tac
        >> irule valid_val_larger_store
        >> pop_assum $ irule_at (Pos last)
        >> simp[]
      )
      >> simp[EVERY_GENLIST]
      >> qpat_assum ‘EVERY _ (MAP SND bs)’ mp_tac
      >> qpat_assum ‘FDOM _ ∪ _ = FDOM _’ mp_tac
      >> rpt (pop_assum kall_tac)
      >> qid_spec_tac ‘env’
      >> Induct_on ‘bs’ >- simp[]
      >> rpt strip_tac
      >> PairCases_on ‘h’
      >> simp[Once static_scope_cases]
      >> gvs[]
      >> last_x_assum $ qspec_then ‘env |+ (h0, 0)’ assume_tac
      >> gvs[]
      >> qsuff_tac ‘FDOM env ∪ (h0 INSERT set (MAP FST bs))
        = (h0 INSERT FDOM env) ∪ set (MAP FST bs)’ >- (
        strip_tac
        >> pop_assum $ gvs o single
        >> last_x_assum $ simp o single o GSYM
      )
      >> rpt $ pop_assum kall_tac
      >> simp[EXTENSION, UNION_DEF]
      >> strip_tac
      >> iff_tac
      >> strip_tac
      >> simp[]
    )
    >> simp[step_def, Once valid_state_cases]
    >> simp[Once valid_val_cases]
    >> gvs[Once valid_state_cases, Once static_scope_cases, can_lookup_cases]
  )
  >~ [‘Val v’] >- (
    Cases_on ‘ks’ >- (
      simp[step_def, return_def, Once valid_state_cases,
        can_lookup_cases, FEVERY_FEMPTY]
      >> gvs[Once valid_state_cases]
    )
    >> PairCases_on ‘h’
    >> Cases_on ‘h1’
    >~ [‘CondK t f’] >- (
      simp[step_def, return_def]
      >> IF_CASES_TAC >- (
        gvs[Once valid_state_cases, Once valid_val_cases]
        >> gvs[Once valid_val_cases]
        >> simp[Once valid_state_cases]
      )
      >> gvs[Once valid_state_cases]
      >> qpat_x_assum ‘valid_cont _ _’ $ mp_tac o SRULE [Once valid_val_cases]
      >> rpt strip_tac
      >> simp[Once valid_state_cases]
    )
    >~ [‘BeginK es e’] >- (
      simp[step_def, return_def]
      >> CASE_TAC
      >> gvs[Once valid_state_cases]
      >> qpat_x_assum ‘valid_cont _ _’ $ mp_tac o SRULE [Once valid_val_cases]
      >> rpt strip_tac
      >> simp[Once valid_state_cases]
      >> simp[Once valid_val_cases]
    )
    >~ [‘SetK x’] >- (
      simp[step_def, return_def]
      >> gvs[Once valid_state_cases]
      >> qpat_x_assum ‘valid_cont _ _’ $ mp_tac o SRULE [Once valid_val_cases]
      >> rpt strip_tac
      >> simp[Once valid_state_cases]
      >> simp[Once valid_val_cases]
      >> irule_at (Pos hd) valid_cont_larger_store
      >> qpat_assum ‘valid_cont _ _’ $ irule_at (Pos $ el 2)
      >> simp[]
      >> gvs[can_lookup_cases]
      >> irule IMP_EVERY_LUPDATE
      >> simp[OPTION_ALL_def]
      >> irule_at (Pos hd) valid_val_larger_store
      >> last_assum $ irule_at (Pos $ el 2)
      >> simp[]
      >> irule EVERY_MONOTONIC
      >> qpat_assum ‘EVERY _ _’ $ irule_at (Pos last)
      >> rpt strip_tac
      >> irule OPTION_ALL_MONO
      >> pop_assum $ irule_at (Pos last)
      >> rpt strip_tac
      >> irule_at (Pos hd) valid_val_larger_store
      >> pop_assum $ irule_at (Pos last)
      >> simp[]
    )
    >~ [‘ApplyK fnp es’] >- (
      simp[step_def]
      >> Cases_on ‘∃ e es' . es = e::es'’ >-(
        gvs[]
        >> Cases_on ‘∃ fn vs . fnp = SOME (fn,vs)’
        >> Cases_on ‘fnp = NONE’
        >> gvs[]
        >> simp[return_def]
        >> simp[Once valid_state_cases]
        >> gvs[Once valid_state_cases]
        >> simp[Once valid_val_cases]
        >> qpat_x_assum ‘valid_cont _ _’ $ mp_tac o SRULE [Once valid_val_cases]
        >> rpt strip_tac
        >> simp[]
        >> Cases_on ‘fnp’ >> gvs[] >> PairCases_on ‘x’ >> gvs[]
      )
      >> Cases_on ‘es’ >> gvs[]
      >> Cases_on ‘fnp’ >- (
        simp[return_def]
        >> Cases_on ‘v’
        >> simp[application_def]
        >~ [‘Prim p’] >- (
          CASE_TAC
          >> simp[Once valid_state_cases, sadd_def, smul_def,
            sminus_def, seqv_def, can_lookup_cases, FEVERY_FEMPTY]
          >> simp[Once valid_val_cases]
          >> gvs[Once valid_state_cases]
          >> qpat_x_assum ‘valid_cont _ _’ $ mp_tac o SRULE [Once valid_val_cases]
          >> simp[]
        )
        >~ [‘Proc env' xs xp e’] >- (
          Cases_on ‘xp’
          >> Cases_on ‘xs’
          >> simp[parameterize_def] >- (
            simp[Once valid_state_cases]
            >> gvs[Once valid_state_cases]
            >> gvs[Once valid_val_cases]
            >> gvs[Once valid_val_cases]
          )
          >- simp[Once valid_state_cases]
          >- (
            rpt (pairarg_tac >> gvs[])
            >> simp[Once valid_state_cases]
            >> gvs[Once valid_state_cases, fresh_loc_def]
            >> gvs[Once valid_val_cases]
            >> gvs[Once valid_val_cases]
            >> simp[Once INSERT_SING_UNION, Once UNION_COMM]
            >> irule_at (Pos hd) valid_cont_larger_store
            >> qpat_assum ‘valid_cont _ _’ $ irule_at (Pos $ el 2)
            >> simp[Once valid_val_cases]
            >> irule_at (Pos $ el 2) $ EVERY_MONOTONIC
            >> pop_assum $ irule_at (Pos $ el 2)
            >> gvs[can_lookup_cases]
            >> irule_at (Pos $ el 2) $ cj 2 FEVERY_STRENGTHEN_THM
            >> simp[]
            >> irule_at (Pos hd) FEVERY_MONO
            >> qpat_assum ‘FEVERY _ env'’ $ irule_at (Pos $ el 2)
            >> rpt strip_tac >- (PairCases_on ‘x'’ >> gvs[])
            >> irule OPTION_ALL_MONO
            >> pop_assum $ irule_at (Pos last)
            >> rpt strip_tac
            >> irule valid_val_larger_store
            >> pop_assum $ irule_at (Pos last)
            >> simp[]
          )
          >> simp[Once valid_state_cases]
          >> gvs[Once valid_state_cases]
          >> gvs[Once valid_val_cases]
          >> gvs[Once valid_val_cases]
        )
        >> simp[Once valid_state_cases]
        >> gvs[Once valid_state_cases]
        >> gvs[Once valid_val_cases]
        >> gvs[Once valid_val_cases]
      )
      >> PairCases_on ‘x’
      >> simp[return_def]
      >> Cases_on ‘x0’
      >> simp[application_def]
      >~ [‘Prim p’] >- (
        TOP_CASE_TAC >- (
          qspecl_then [‘REVERSE x1 ++ [v]’, ‘0’] assume_tac sadd_num_or_exception
          >> simp[Once valid_state_cases]
          >> gvs[]
          >> simp[Once valid_val_cases, can_lookup_cases, FEVERY_FEMPTY]
          >> gvs[Once valid_state_cases]
          >> qpat_x_assum ‘valid_cont _ _’ $ mp_tac o SRULE [Once valid_val_cases]
          >> simp[]
        )
        >- (
          qspecl_then [‘REVERSE x1 ++ [v]’, ‘1’] assume_tac smul_num_or_exception
          >> simp[Once valid_state_cases]
          >> gvs[]
          >> simp[Once valid_val_cases, can_lookup_cases, FEVERY_FEMPTY]
          >> gvs[Once valid_state_cases]
          >> qpat_x_assum ‘valid_cont _ _’ $ mp_tac o SRULE [Once valid_val_cases]
          >> simp[]
        )
        >- (
          qspec_then ‘REVERSE x1 ++ [v]’ assume_tac sminus_num_or_exception
          >> simp[Once valid_state_cases]
          >> gvs[]
          >> simp[Once valid_val_cases, can_lookup_cases, FEVERY_FEMPTY]
          >> gvs[Once valid_state_cases]
          >> qpat_x_assum ‘valid_cont _ _’ $ mp_tac o SRULE [Once valid_val_cases]
          >> simp[]
        )
        >- (
          qspec_then ‘REVERSE x1 ++ [v]’ assume_tac seqv_bool_or_exception
          >> simp[Once valid_state_cases]
          >> gvs[]
          >> simp[Once valid_val_cases, can_lookup_cases, FEVERY_FEMPTY]
          >> gvs[Once valid_state_cases]
          >> qpat_x_assum ‘valid_cont _ _’ $ mp_tac o SRULE [Once valid_val_cases]
          >> simp[]
        )
        >> CASE_TAC
        >> gvs[]
        >> Cases_on ‘t'’ >- (
          gvs[]
          >> simp[Once valid_state_cases]
          >> gvs[Once valid_state_cases]
          >> qpat_x_assum ‘valid_cont _ _’ $ mp_tac o SRULE [Once valid_val_cases]
          >> rpt strip_tac
          >> simp[Once valid_val_cases, can_lookup_cases, FEVERY_FEMPTY]
        )
        >> gvs[]
        >> simp[Once valid_state_cases]
        >> gvs[Once valid_state_cases]
        >> gvs[Once valid_val_cases]
        >> gvs[Once valid_val_cases]
      )
      >~ [‘Proc env' xs xp e’] >- (
        rpt (pairarg_tac >> gvs[])
        >> gvs[Once valid_state_cases]
        >> qpat_x_assum ‘valid_cont _ _’ $ mp_tac o SRULE [Once valid_val_cases]
        >> rpt strip_tac
        >> qpat_x_assum ‘valid_val _ (Proc _ _ _ _)’ $ mp_tac o SRULE [Once valid_val_cases]
        >> rpt strip_tac
        >> gvs[] >- (
          Cases_on ‘LENGTH xs = LENGTH (REVERSE x1 ++ [v])’ >- (
            drule_all_then mp_tac parameterize_NONE_dom
            >> drule_all_then mp_tac parameterize_NONE_lookup
            >> rpt strip_tac
            >> qpat_x_assum ‘Exp _ = _’ $ simp o single o GSYM
            >> simp[Once valid_state_cases]
            >> qpat_x_assum ‘_ ∪ _ = _’ $ simp o single o GSYM
            >> qpat_x_assum ‘_ ++ _ = _’ $ simp o single o GSYM
            >> irule_at (Pos hd) $ valid_cont_larger_store
            >> qpat_assum ‘valid_cont _ _’ $ irule_at (Pos $ el 2)
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
            >> strip_tac >- (
              irule EVERY_OPTION_ALL_MAP_SOME
              >> irule EVERY_MONOTONIC
              >> qexists ‘valid_val store’
              >> simp[]
              >> rpt strip_tac
              >> irule valid_val_larger_store
              >> pop_assum $ irule_at (Pos last)
              >> simp[]
            )
            >> irule valid_val_larger_store
            >> last_assum $ irule_at (Pos last)
            >> simp[]
          )
          >> drule_all_then mp_tac parameterize_NONE_exception
          >> rpt strip_tac
          >> simp[Once valid_state_cases]
          >> gvs[]
        )
        >> Cases_on ‘LENGTH xs ≤ LENGTH (REVERSE x1 ++ [v])’ >- (
          drule_all_then mp_tac parameterize_SOME_dom
          >> drule_all_then mp_tac parameterize_SOME_lookup
          >> rpt strip_tac
          >> simp[Once valid_state_cases]
          >> gvs[]
          >> irule_at (Pos hd) $ valid_cont_larger_store
          >> qpat_assum ‘valid_cont _ _’ $ irule_at (Pos $ el 2)
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
          >> strip_tac >- (
            irule EVERY_OPTION_ALL_MAP_SOME
            >> irule EVERY_TAKE
            >> simp[]
            >> strip_tac >- (
              irule EVERY_MONOTONIC
              >> qpat_assum ‘EVERY _ x1’ $ irule_at (Pos last)
              >> rpt strip_tac
              >> irule valid_val_larger_store
              >> pop_assum $ irule_at (Pos last)
              >> simp[]
            )
            >> irule valid_val_larger_store
            >> last_assum $ irule_at (Pos last)
            >> simp[]
          )
          >> simp[Once valid_val_cases]
          >> irule EVERY_TAKE
          >> simp[]
          >> strip_tac >- (
            irule valid_val_larger_store
            >> last_assum $ irule_at (Pos last)
            >> simp[]
          )
          >> irule EVERY_MONOTONIC
          >> qpat_assum ‘EVERY _ x1’ $ irule_at (Pos last)
          >> rpt strip_tac
          >> irule valid_val_larger_store
          >> pop_assum $ irule_at (Pos last)
          >> simp[]
        )
        >> ‘LENGTH (REVERSE x1 ++ [v]) < LENGTH xs’ by gvs[]
        >> drule_all_then mp_tac parameterize_SOME_exception
        >> rpt strip_tac
        >> simp[Once valid_state_cases]
        >> gvs[]
      )
      >~ [‘Throw ks’] >- (
        CASE_TAC >- simp[Once valid_state_cases]
        >> CASE_TAC >- (
          gvs[]
          >> simp[Once valid_state_cases, can_lookup_cases, FEVERY_FEMPTY]
          >> gvs[Once valid_state_cases]
          >> qpat_x_assum ‘valid_cont _ _’ $ mp_tac o SRULE [Once valid_val_cases]
          >> rpt strip_tac
          >> qpat_x_assum ‘valid_val _ _’ $ mp_tac o SRULE [Once valid_val_cases]
          >> simp[]
        )
        >> simp[Once valid_state_cases]
      )
      >> simp[Once valid_state_cases]
      >> gvs[Once valid_state_cases]
      >> gvs[Once valid_val_cases]
      >> gvs[Once valid_val_cases]
    )
  )
  >> simp[step_def, Once valid_state_cases]
QED

Theorem statically_scoped_program_valid:
  ∀ p . static_scope ∅ p ⇒ valid_state [] [] FEMPTY (Exp p)
Proof
  simp[Once valid_state_cases,
    can_lookup_cases, FEVERY_FEMPTY]
  >> simp[Once valid_val_cases]
QED

(*
  open scheme_semanticsTheory;

  EVAL “steps 4 ([], [], Apply (Val (Prim SMinus)) [Val (SNum 2); Val (SNum 4)])”
  EVAL “steps 4 ([], [], Apply (Val (SNum 7)) [Val (SNum 2); Val (SNum 4)])”
  EVAL “steps 6 ([], [InLetK []], Apply (Val (Prim SMul)) [Val (SNum 2); Val (Prim SAdd)])”
  EVAL “steps 2 ([], [], Cond (Val (SBool F)) (Val (SNum 2)) (Val (SNum 4)))”
  EVAL “steps 4 ([], [], SLet [(strlit "x", Val $ SNum 42)] (Ident $ strlit "x"))”
  EVAL “steps 6 ([], [], Apply (Lambda [] (SOME $ strlit "x") (Ident $ strlit "y")) [Val $ SNum 4])”
  EVAL “steps 3 ([], [], Begin (Val $ SNum 1) [Val $ SNum 2])”

  EVAL “steps 16 ([], [], FEMPTY,
    Apply (
      Lambda [strlit "f"; strlit "x"] NONE (
        Apply (Ident $ strlit "f") [Val $ SNum 1]
      )
    ) [
      Lambda [strlit "y"] NONE (
        Apply (Val $ Prim SAdd) [
          Ident $ strlit "y";
          Ident $ strlit "x"
        ]
      );
      Val $ SNum 4
    ]
  )”

  EVAL “steps 99 ([], [], FEMPTY,Exp $
    Apply (
      Lambda [strlit "x"] NONE (
        Apply (
          Lambda [strlit "y"] NONE (
            Apply (Lit $ LitPrim SAdd) [
              Ident $ strlit "y";
              Ident $ strlit "x"
            ]
          )
        ) [Lit $ LitNum 1]
      )
    ) [Lit $ LitNum 4]
  )”

  EVAL “steps 16 ([], [], FEMPTY,
    Apply (
      Lambda [strlit "x"] NONE (
        Apply (
          Lambda [strlit "x"] NONE (
            Apply (Val $ Prim SAdd) [
              Ident $ strlit "x"
            ]
          )
        ) [Val $ SNum 1]
      )
    ) [Val $ SNum 4]
  )”

  EVAL “steps 22 ([], [], FEMPTY,
    Apply (
      Lambda [strlit "x"] NONE (Begin (
        Apply (
          Lambda [strlit "y"] NONE (Begin (
            Set (strlit "x") (Val $ SNum 5)
          ) [
            Apply (Val $ Prim SAdd) [
              Ident $ strlit "y";
              Ident $ strlit "x"
            ]
          ])
        ) [Val $ SNum 1]
      ) [
        Ident $ strlit "x"
      ])
    ) [Val $ SNum 4]
  )”

  EVAL “steps 100 ([], [], FEMPTY,
    Letrec [
      (strlit $ "to", Lambda [strlit "x"] NONE (
        Apply (Ident $ strlit "fro") [
          Apply (Val $ Prim SAdd) [Val $ SNum 1; Ident $ strlit "x"]
        ]
      ));
      (strlit $ "fro", Lambda [strlit "x"] NONE (
        Apply (Ident $ strlit "to") [
          Apply (Val $ Prim SMul) [Val $ SNum 2; Ident $ strlit "x"]
        ]
      ))
    ] (Apply (Ident $ strlit "to") [Val $ SNum 0])
  )”

  EVAL “steps 3 ([], [], FEMPTY,
    Letrec [(strlit $ "fail", Ident $ strlit "fail")] (Val $ SBool F)
  )”

  EVAL “steps 20 ([], [], FEMPTY,
    Apply (Val $ Prim SMul) [
      Val $ SNum 2;
      Apply (Val $ Prim CallCC) [ Lambda [strlit "x"] NONE (
        Apply (Val $ Prim SAdd) [
          Val $ SNum 4;
          Cond (Val $ SBool F) (
            Val $ SNum 3
          ) (
            Apply (Ident $ strlit "x") [Val $ SNum 5]
          )
        ]
      )]
    ]
  )”

  EVAL “steps 102 ([], [], FEMPTY,
    Letrec [
      (strlit $ "double", Val $ SNum 0);
      (strlit $ "x", Val $ SNum 1)
    ] (Begin (
      Apply (Val $ Prim CallCC) [ Lambda [strlit "x"] NONE (
        Set (strlit "double") (Ident $ strlit "x")
      )]
    ) [
      Set (strlit "x") (Apply (Val $ Prim SMul) [
        Val $ SNum 2;
        Ident $ strlit "x"
      ]);
      Apply (Ident $ strlit "double") [Val $ SNum 0]
    ])
  )”

  EVAL “steps 10 ([], [], FEMPTY, Apply (Val $ Prim SMinus) [Val $ SNum 3; Val $ SNum 2])”

  EVAL “steps 1000 ([], [], FEMPTY, Letrec [(strlit "fac", Lambda [strlit "x"] NONE (
    Cond (Apply (Val $ Prim SEqv) [Ident $ strlit "x"; Val $ SNum 0]) (
      Val $ SNum 1
    ) (
      Apply (Val $ Prim SMul) [Ident $ strlit "x"; Apply (Ident $ strlit "fac") [
        Apply (Val $ Prim SMinus) [Ident $ strlit "x"; Val $ SNum 1]
      ]]
    )
  ))] (Apply (Ident $ strlit "fac") [Val $ SNum 6]))”

  EVAL “steps 500 ([], [], FEMPTY, Exp $ Letrec [(strlit "fac", Lambda [strlit "x"] NONE (
    Letrec [(strlit "st", Lit $ LitNum 0); (strlit "acc", Lit $ LitNum 1)] (
      Begin [ Apply (Lit $ LitPrim CallCC) [ Lambda [strlit "k"] NONE (
        Set (strlit "st") (Ident $ strlit "k")
      )]] (
        Cond (Apply (Lit $ LitPrim SEqv) [Ident $ strlit "x"; Lit $ LitNum 0])
          (Ident $ strlit "acc")
          (Apply (Ident $ strlit "st") [ Begin [
            Set (strlit "acc") (Apply (Lit $ LitPrim SMul) [
              Ident $ strlit "acc";
              Ident $ strlit "x"
            ])
          ] (
            Set (strlit "x") (Apply (Lit $ LitPrim SMinus) [
              Ident $ strlit "x";
              Lit $ LitNum 1
            ])
          )])
      )
    )
  ))] (Apply (Ident $ strlit "fac") [Lit $ LitNum 6]))”
*)

val _ = export_theory();