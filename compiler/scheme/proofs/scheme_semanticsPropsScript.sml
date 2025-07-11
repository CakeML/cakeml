(*
  Proofs of Scheme semantics properties
*)
open preamble;
open mlstringTheory;
open scheme_astTheory;
open scheme_semanticsTheory;
open finite_mapTheory;

val _ = new_theory "scheme_semanticsProps";

Inductive can_lookup:
  FEVERY (λ (x, l). ? v . l < LENGTH store /\ EL l store = Mut v) env
  ⇒
  can_lookup env store
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

Theorem FEVERY_LIST_STRENGTHEN_THM:
  ! l P f .
    FEVERY P f /\ EVERY P l ==> FEVERY P (f |++ l)
Proof
  Induct
  >> simp[FUPDATE_LIST]
  >> simp[GSYM FUPDATE_LIST]
  >> rpt strip_tac
  >> last_x_assum irule
  >> simp[]
  >> rename1 `P p`
  >> PairCases_on `p`
  >> irule $ cj 2 FEVERY_STRENGTHEN_THM
  >> simp[]
QED

Theorem can_lookup_LUPDATE_same:
  ! env store l v1 v2 .
    EL l store = Mut v1 /\
    can_lookup env store
    ==>
    can_lookup env (LUPDATE (Mut v2) l store)
Proof
  rpt strip_tac
  >> gvs[can_lookup_cases]
  >> irule FEVERY_MONO
  >> pop_assum $ irule_at $ Pos last
  >> PairCases
  >> rpt strip_tac
  >> gvs[EL_LUPDATE]
  >> IF_CASES_TAC
  >> gvs[]
QED

Inductive valid_val_cont:
[~SNum:]
  valid_val store (SNum n)
[~SBool:]
  valid_val store (SBool b)
[~Prim:]
  valid_val store (Prim p)
[~Wrong:]
  valid_val store (Wrong w)
[~SList:]
  EVERY (valid_val store) vs
  ⇒
  valid_val store (SList vs)
[~Proc_NONE:]
  static_scope (FDOM env ∪ set xs) e ∧
  can_lookup env store
  ⇒
  valid_val store (Proc env xs NONE e)
[~Proc_SOME:]
  static_scope (FDOM env ∪ set (x::xs)) e ∧
  can_lookup env store
  ⇒
  valid_val store (Proc env xs (SOME x) e)
[~Throw:]
  valid_cont store ks
  ⇒
  valid_val store (Throw ks)
[~PairP:]
  l < LENGTH store /\ EL l store = Pair (v1, v2)
  ⇒
  valid_val store (PairP l)
[~Null:]
  valid_val store Null

[~Id:]
  valid_cont store []
[~CondK:]
  static_scope (FDOM env) t ∧
  static_scope (FDOM env) f ∧
  valid_cont store ks ∧
  can_lookup env store
  ⇒
  valid_cont store ((env, CondK t f)::ks)
[~ApplyK_NONE:]
  EVERY (static_scope (FDOM env)) es ∧
  valid_cont store ks ∧
  can_lookup env store
  ⇒
  valid_cont store ((env, ApplyK NONE es)::ks)
[~ApplyK_SOME:]
  valid_val store fn ∧
  EVERY (valid_val store) vs ∧
  EVERY (static_scope (FDOM env)) es ∧
  valid_cont store ks ∧
  can_lookup env store
  ⇒
  valid_cont store ((env, ApplyK (SOME (fn, vs)) es)::ks)
[~BeginK:]
  EVERY (static_scope (FDOM env)) es ∧
  static_scope (FDOM env) e ∧
  valid_cont store ks ∧
  can_lookup env store
  ⇒
  valid_cont store ((env, BeginK es e)::ks)
[~SetK:]
  (FDOM env) x ∧
  valid_cont store ks ∧
  can_lookup env store
  ⇒
  valid_cont store ((env, SetK x)::ks)
[~LetinitK:]
  EVERY (FDOM env) (MAP FST xvs) ∧
  EVERY (valid_val store) (MAP SND xvs) ∧
  (FDOM env) x ∧
  EVERY (FDOM env) (MAP FST bs) ∧
  EVERY (static_scope (FDOM env)) (MAP SND bs) ∧
  static_scope (FDOM env) e ∧
  valid_cont store ks ∧
  can_lookup env store
  ⇒
  valid_cont store ((env, LetinitK xvs x bs e)::ks)
End

Theorem valid_val_cases = cj 1 valid_val_cont_cases;
Theorem valid_cont_cases = cj 2 valid_val_cont_cases;

Inductive valid_store_entry:
[~Mut_NONE:]
  valid_store_entry store (Mut NONE)
[~Mut_SOME:]
  valid_val store v
  ==>
  valid_store_entry store (Mut (SOME v))
[~Pair:]
  valid_val store v1 /\
  valid_val store v2
  ==>
  valid_store_entry store (Pair (v1, v2))
End

Inductive valid_state:
[~Val:]
  valid_val store v ∧
  valid_cont store ks ∧
  EVERY (valid_store_entry store) store
  ⇒
  valid_state store ks (Val v)
[~Exp:]
  static_scope (FDOM env) e ∧
  valid_cont store ks ∧
  can_lookup env store ∧
  EVERY (valid_store_entry store) store
  ⇒
  valid_state store ks (Exp env e)
[~Exception:]
  valid_state store ks (Exception s)
End

Definition terminating_state_def:
  terminating_state (st, ks, e)
    ⇔ (ks = [] ∧ ∃ v . e = Val v) ∨ (∃ ex . e = Exception ex)
End

Theorem SET_MEM:
  ∀ l x . set l x ⇔ MEM x l
Proof
  Induct
  >> simp[]
QED

Theorem EVERY_SET:
  ∀ l . EVERY (set l) l
Proof
  simp[EVERY_MEM, SET_MEM]
QED

Theorem valid_LUPDATE_same:
  ∀ store l v1 v2 .
    EL l store = Mut v1
    ⇒
    (∀ v .
      valid_val store v
      ⇒
      valid_val (LUPDATE (Mut v2) l store) v) ∧
    ∀ ks .
      valid_cont store ks
      ⇒
      valid_cont (LUPDATE (Mut v2) l store) ks
Proof
  rpt gen_tac >> strip_tac
  >> ho_match_mp_tac valid_val_cont_ind
  >> rpt strip_tac
  >> simp[Once valid_val_cases]
  >> simp[Once valid_cont_cases]
  >> gvs[SF ETA_ss, can_lookup_LUPDATE_same]
  >> simp[EL_LUPDATE]
  >> IF_CASES_TAC
  >> gvs[]
QED

Theorem valid_val_LUPDATE_same = SRULE [PULL_FORALL] $
  cj 1 valid_LUPDATE_same;
Theorem valid_cont_LUPDATE_same = SRULE [PULL_FORALL] $
  cj 2 valid_LUPDATE_same;

Theorem valid_alloc:
  ∀ store svs .
    (∀ v .
      valid_val store v
      ⇒
      valid_val (store ++ svs) v) ∧
    ∀ ks .
      valid_cont store ks
      ⇒
      valid_cont (store ++ svs) ks
Proof
  rpt gen_tac
  >> ho_match_mp_tac valid_val_cont_ind
  >> rpt strip_tac
  >> simp[Once valid_val_cases]
  >> simp[Once valid_cont_cases]
  >> gvs[SF ETA_ss, can_lookup_cases, EL_APPEND_EQN]
  >> irule FEVERY_MONO
  >> pop_assum $ irule_at $ Pos last
  >> PairCases
  >> rpt strip_tac
  >> gvs[]
QED

Theorem valid_val_alloc = SRULE [PULL_FORALL] $
  cj 1 valid_alloc;
Theorem valid_cont_alloc = SRULE [PULL_FORALL] $
  cj 2 valid_alloc;

Definition letrec_preinit_env_def:
  letrec_preinit_env env xs l
  =
  env |++ MAP (\ p. (FST p, l + SND p)) (ZIP (xs, GENLIST I $ LENGTH xs))
End

Theorem letrec_preinit_APPEND:
  ! xs store env .
    letrec_preinit store env xs
    =
    (store ++ (GENLIST (K $ Mut NONE) $ LENGTH xs),
    letrec_preinit_env env xs $ LENGTH store)
Proof
  simp[letrec_preinit_env_def]
  >> Induct
  >> simp[letrec_preinit_env_def, letrec_preinit_def, FUPDATE_LIST,
    fresh_loc_def, GENLIST_CONS]
  >> gvs[letrec_preinit_env_def]
  >> `! l . GENLIST SUC l = MAP SUC $ GENLIST I l` by simp[MAP_GENLIST]
  >> pop_assum $ simp o single
  >> simp[cj 2 ZIP_MAP, MAP_MAP_o, o_DEF]
  >> `! x y . x + SUC y = SUC x + y` by simp[]
  >> pop_assum $ simp o single o Once
QED

Theorem letinit_valid:
  ∀ store env xvs ks .
    EVERY (valid_store_entry store) store ∧
    EVERY (FDOM env) (MAP FST xvs) ∧
    EVERY (valid_val store) (MAP SND xvs) ∧
    valid_cont store ks ∧
    can_lookup env store
    ⇒
      valid_cont (letinit store env xvs) ks ∧
      can_lookup env (letinit store env xvs) ∧
      EVERY (valid_store_entry (letinit store env xvs))
        (letinit store env xvs)
Proof
  Induct_on ‘xvs’
  >> simp[letinit_def]
  >> PairCases
  >> simp[letinit_def]
  >> rpt gen_tac
  >> strip_tac
  >> last_x_assum irule
  >> simp[]
  >> qpat_assum `can_lookup _ _` $ assume_tac
    o SRULE [can_lookup_cases, FEVERY_DEF, SPECIFICATION]
  >> first_x_assum drule >> strip_tac
  >> simp[can_lookup_LUPDATE_same, valid_cont_LUPDATE_same]
  >> irule_at (Pos hd) IMP_EVERY_LUPDATE
  >> simp[Once valid_store_entry_cases, valid_val_LUPDATE_same]
  >> irule_at (Pos hd) EVERY_MONOTONIC
  >> last_assum $ irule_at $ Pat `EVERY _ _`
  >> strip_tac >- (
    rpt strip_tac
    >> gvs[Once valid_store_entry_cases]
    >> simp[Once valid_store_entry_cases, valid_val_LUPDATE_same]
  )
  >> irule_at (Pos hd) EVERY_MONOTONIC
  >> last_assum $ irule_at $ Pat `EVERY _ _`
  >> simp[valid_val_LUPDATE_same]
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
QED

Theorem valid_application_progress:
  ∀ store ks fn vs .
    valid_val store fn ∧
    EVERY (valid_val store) vs ∧
    valid_cont store ks ∧
    EVERY (valid_store_entry store) store
    ⇒
    ∃ store' ks' state' .
      application store ks fn vs  = (store', ks', state') ∧
      valid_state store' ks' state'
Proof
  rpt strip_tac
  >> simp[oneline application_def]
  >> TOP_CASE_TAC
  >~ [`Prim p`] >- (
    TOP_CASE_TAC
    >~ [`Prim SAdd`] >- (
      qspecl_then [`vs`, `0`] assume_tac sadd_num_or_exception
      >> gvs[]
      >> simp[Once valid_state_cases]
      >> simp[Once valid_val_cases]
    )
    >~ [`Prim SMul`] >- (
      qspecl_then [`vs`, `1`] assume_tac smul_num_or_exception
      >> gvs[]
      >> simp[Once valid_state_cases]
      >> simp[Once valid_val_cases]
    )
    >~ [`Prim SMinus`] >- (
      qspecl_then [`vs`] assume_tac sminus_num_or_exception
      >> gvs[]
      >> simp[Once valid_state_cases]
      >> simp[Once valid_val_cases]
    )
    >~ [`Prim SEqv`] >- (
      qspecl_then [`vs`] assume_tac seqv_bool_or_exception
      >> gvs[]
      >> simp[Once valid_state_cases]
      >> simp[Once valid_val_cases]
    )
    >~ [`Prim CallCC`] >- (
      TOP_CASE_TAC >- simp[Once valid_state_cases]
      >> TOP_CASE_TAC
      >> simp[Once valid_state_cases]
      >> simp[Once valid_val_cases]
      >> simp[Once valid_cont_cases]
      >> simp[can_lookup_cases, FEVERY_FEMPTY]
      >> gvs[]
    )
    >~ [`Prim Cons`] >- (
      rpt (TOP_CASE_TAC >- simp[Once valid_state_cases])
      >> TOP_CASE_TAC
      >> simp[Once valid_state_cases]
      >> gvs[fresh_loc_def]
      >> simp[Once valid_val_cases, EL_LENGTH_SNOC]
      >> simp[SNOC_APPEND, valid_cont_alloc]
      >> simp[Once valid_store_entry_cases, valid_val_alloc]
      >> irule EVERY_MONOTONIC
      >> first_assum $ irule_at $ Pos last
      >> rpt strip_tac
      >> gvs[Once valid_store_entry_cases]
      >> simp[Once valid_store_entry_cases, valid_val_alloc]
    )
    >~ [`Prim Car`] >- (
      rpt (TOP_CASE_TAC >- simp[Once valid_state_cases])
      >> TOP_CASE_TAC >>> LASTGOAL (simp[Once valid_state_cases])
      >> CASE_TAC
      >~ [`PairP l`] >- (
        simp[Once valid_state_cases]
        >> gvs[Ntimes valid_val_cases 2]
        >> gvs[EVERY_EL]
        >> last_x_assum $ drule_then assume_tac
        >> gvs[Once valid_store_entry_cases]
      )
      >> simp[Once valid_state_cases]
    )
    >~ [`Prim Cdr`] >- (
      rpt (TOP_CASE_TAC >- simp[Once valid_state_cases])
      >> TOP_CASE_TAC >>> LASTGOAL (simp[Once valid_state_cases])
      >> CASE_TAC
      >~ [`PairP l`] >- (
        simp[Once valid_state_cases]
        >> gvs[Ntimes valid_val_cases 2]
        >> gvs[EVERY_EL]
        >> last_x_assum $ drule_then assume_tac
        >> gvs[Once valid_store_entry_cases]
      )
      >> simp[Once valid_state_cases]
    )
  )
  >~ [`Proc env xs xp e`] >- (
    rpt (pairarg_tac >> gvs[])
    >> Cases_on `xp`
    >~ [`SOME x`] >- cheat
    >> rpt $ pop_assum mp_tac
    >> qid_spec_tac `store`
    >> qid_spec_tac `env`
    >> qid_spec_tac `vs`
    >> Induct_on `xs`
    >> rpt strip_tac
    >> Cases_on `vs`
    >> gvs[parameterize_def]
    >>> LASTGOAL (last_x_assum irule)
    >> simp[Once valid_state_cases] >- gvs[Once valid_val_cases]
    >> gvs[parameterize_def, fresh_loc_def]
    >> pop_assum $ irule_at $ Pos hd
    >> simp[SNOC_APPEND, valid_store_entry_cases, valid_cont_alloc, valid_val_alloc]
    >> strip_tac >- (
      irule EVERY_MONOTONIC
      >> qpat_assum `EVERY (valid_store_entry _) _` $ irule_at Any
      >> rpt strip_tac
      >> gvs[Once valid_store_entry_cases]
      >> simp[Once valid_store_entry_cases, valid_val_alloc]
    )
    >> strip_tac >- (
      irule EVERY_MONOTONIC
      >> qpat_assum `EVERY (valid_val _) _` $ irule_at Any
      >> rpt strip_tac
      >> simp[valid_val_alloc]
    )
    >> last_x_assum kall_tac
    >> gvs[Once valid_val_cases]
    >> simp[Once valid_val_cases]
    >> qmatch_goalsub_abbrev_tac `static_scope left_sub _`
    >> qmatch_asmsub_abbrev_tac `static_scope right_sub _`
    >> qsuff_tac `left_sub = right_sub` >- (
      strip_tac
      >> gvs[can_lookup_cases]
      >> irule $ cj 2 FEVERY_STRENGTHEN_THM
      >> simp[EL_APPEND_EQN]
      >> irule FEVERY_MONO
      >> first_assum $ irule_at $ Pos last
      >> PairCases
      >> rpt strip_tac
      >> gvs[]
    )
    >> unabbrev_all_tac
    >> simp[EXTENSION]
    >> strip_tac
    >> iff_tac
    >> rpt strip_tac
    >> simp[]
  )
  >~ [`Throw ks`] >- (
    TOP_CASE_TAC >- simp[Once valid_state_cases]
    >> TOP_CASE_TAC
    >> simp[Once valid_state_cases]
    >> gvs[Once valid_val_cases]
  )
  >> simp[Once valid_state_cases]
QED

Theorem valid_state_progress:
  ∀ state store ks .
    valid_state store ks state
    ⇒
    ∃ store' ks' state' .
      step (store, ks, state) = (store', ks', state') ∧
      valid_state store' ks' state'
Proof
  Cases
  >> rpt strip_tac
  >~ [‘Exp env e’] >- (
    Cases_on ‘e’
    >~ [‘Ident x’] >- (
      simp[step_def]
      >> gvs[Once valid_state_cases, Once static_scope_def, can_lookup_cases]
      >> gvs[FEVERY_DEF, SPECIFICATION]
      >> first_x_assum drule >> strip_tac
      >> simp[]
      >> CASE_TAC >- simp[Once valid_state_cases]
      >> gvs[Once valid_state_cases, can_lookup_cases]
      >> gvs[EVERY_EL]
      >> first_x_assum drule >> strip_tac
      >> gvs[Once valid_store_entry_cases]
    )
    >~ [‘Letrec bs e’] >- (
      Cases_on ‘bs’ >- (
        simp[step_def, Once valid_state_cases]
        >> gvs[Once valid_state_cases, Once static_scope_def]
      )
      >> simp[step_def]
      >> PairCases_on ‘h’
      >> rpt (pairarg_tac >> gvs[])
      >> gvs[Once valid_state_cases, Once static_scope_def]
      >> simp[Once valid_state_cases]
      >> simp[Once valid_cont_cases]
      >> gvs[letrec_preinit_APPEND, letrec_preinit_env_def]
      >> simp[FDOM_FUPDATE_LIST, MAP_MAP_o, o_DEF, SF ETA_ss, MAP_ZIP]
      >> simp[valid_cont_alloc]
      >> irule_at (Pos hd) EVERY_MONOTONIC
      >> irule_at Any EVERY_SET
      >> simp[SET_MEM]
      >> gvs[can_lookup_cases]
      >> irule_at (Pos hd) FEVERY_LIST_STRENGTHEN_THM
      >> irule_at (Pos hd) FEVERY_MONO
      >> first_assum $ irule_at $ Pat `FEVERY _ _`
      >> strip_tac >- (
        PairCases
        >> rpt strip_tac
        >> gvs[EL_APPEND_EQN]
      )
      >> strip_tac >- (
        simp[EVERY_MAP, EVERY_EL]
        >> rpt strip_tac
        >> simp[EL_ZIP]
        >> simp_tac bool_ss [Once ADD_COMM, EL_APPEND_EQN]
        >> simp[]
      )
      >> irule_at (Pos hd) EVERY_MONOTONIC
      >> first_assum $ irule_at $ Pat `EVERY _ _`
      >> strip_tac >- (
        rpt strip_tac
        >> gvs[valid_store_entry_cases, valid_val_alloc]
      )
      >> simp[EVERY_GENLIST, valid_store_entry_cases]
    )
    >~ [‘Letrecstar bs e’] >- (
      simp[step_def]
      >> rpt (pairarg_tac >> gvs[])
      >> gvs[Once valid_state_cases, Once static_scope_def]
      >> simp[Once valid_state_cases]
      >> simp[Once static_scope_def]
      >> gvs[letrec_preinit_APPEND, letrec_preinit_env_def]
      >> simp[FDOM_FUPDATE_LIST, MAP_MAP_o, o_DEF, SF ETA_ss, MAP_ZIP]
      >> simp[valid_cont_alloc]
      >> simp[EVERY_MAP, UNCURRY, Once static_scope_def, EVERY_CONJ]
      >> simp[GSYM EVERY_MAP]
      >> simp[Once EVERY_EL]
      >> strip_tac >- (
        rpt strip_tac
        >> disj2_tac
        >> simp[MEM_EL]
        >> first_assum $ irule_at $ Pos hd
        >> simp[EL_MAP]
      )
      >> gvs[can_lookup_cases]
      >> irule_at (Pos hd) FEVERY_LIST_STRENGTHEN_THM
      >> irule_at (Pos hd) FEVERY_MONO
      >> first_assum $ irule_at $ Pat `FEVERY _ _`
      >> strip_tac >- (
        PairCases
        >> rpt strip_tac
        >> gvs[EL_APPEND_EQN]
      )
      >> strip_tac >- (
        simp[EVERY_MAP, EVERY_EL]
        >> rpt strip_tac
        >> simp[EL_ZIP]
        >> simp_tac bool_ss [Once ADD_COMM, EL_APPEND_EQN]
        >> simp[]
      )
      >> irule_at (Pos hd) EVERY_MONOTONIC
      >> first_assum $ irule_at $ Pat `EVERY _ _`
      >> strip_tac >- (
        rpt strip_tac
        >> gvs[valid_store_entry_cases, valid_val_alloc]
      )
      >> simp[EVERY_GENLIST, valid_store_entry_cases]
    )
    >~ [`Lambda xs xp e`]
    >> simp[step_def, oneline lit_to_val_def]
    >> rpt CASE_TAC
    >> simp[Once valid_state_cases, Once valid_val_cases]
    >> gvs[Once valid_state_cases, Once static_scope_def]
    >> simp[Once valid_cont_cases]
    >> gvs[Once static_scope_def]
    >> Cases_on `xp`
    >> gvs[Once static_scope_def]
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
        >> gvs[Once valid_cont_cases]
        >> simp[Once valid_state_cases]
      )
      >> gvs[Once valid_state_cases]
      >> gvs[Once valid_cont_cases]
      >> simp[Once valid_state_cases]
    )
    >~ [‘BeginK es e’] >- (
      simp[step_def, return_def]
      >> CASE_TAC
      >> gvs[Once valid_state_cases]
      >> gvs[Once valid_cont_cases]
      >> simp[Once valid_state_cases]
      >> simp[Once valid_cont_cases]
    )
    >~ [‘SetK x’] >- (
      simp[step_def, return_def]
      >> gvs[Once valid_state_cases]
      >> gvs[Once valid_cont_cases, can_lookup_cases]
      >> simp[Once valid_state_cases]
      >> gvs[FEVERY_DEF, SPECIFICATION]
      >> first_x_assum drule >> strip_tac
      >> irule_at (Pos last) IMP_EVERY_LUPDATE
      >> simp[Once valid_store_entry_cases]
      >> simp[valid_cont_LUPDATE_same, valid_val_LUPDATE_same]
      >> irule_at (Pat `valid_val _ _`) valid_val_LUPDATE_same
      >> first_assum $ irule_at $ Pos hd
      >> simp[valid_val_cases]
      >> irule EVERY_MONOTONIC
      >> first_assum $ irule_at $ Pos last
      >> rpt strip_tac
      >> gvs[Once valid_store_entry_cases]
      >> simp[Once valid_store_entry_cases, valid_val_LUPDATE_same]
    )
    >~ [‘LetinitK xvs x bs e’] >- (
      simp[step_def, return_def]
      >> CASE_TAC
      >> gvs[Once valid_state_cases]
      >> gvs[Once valid_cont_cases] >- (
        simp[Once valid_state_cases]
        >> irule letinit_valid
        >> simp[]
      )
      >> PairCases_on ‘h’
      >> simp[Once valid_state_cases]
      >> simp[Once valid_cont_cases]
      >> gvs[]
    )
    >~ [‘ApplyK fnp es’] >- (
      simp[step_def]
      >> Cases_on ‘∃ e es' . es = e::es'’ >-(
        gvs[]
        >> Cases_on ‘∃ fnvs . fnp = SOME fnvs’
        >> gvs[]
        >>> HEADGOAL $ PairCases_on ‘fnvs’
        >>> LASTGOAL $ Cases_on ‘fnp’
        >> gvs[]
        >> simp[return_def]
        >> simp[Once valid_state_cases]
        >> simp[Once valid_cont_cases]
        >> gvs[Once valid_state_cases]
        >> gvs[Once valid_cont_cases]
      )
      >> Cases_on ‘es’ >> gvs[]
      >> Cases_on ‘∃ fnvs . fnp = SOME fnvs’
      >> gvs[]
      >>> HEADGOAL $ PairCases_on ‘fnvs’
      >>> LASTGOAL $ Cases_on ‘fnp’
      >> gvs[]
      >> simp[return_def]
      >> irule valid_application_progress
      >> gvs[Once valid_state_cases]
      >> gvs[Once valid_cont_cases]
    )
  )
  >> simp[step_def, Once valid_state_cases]
QED

Theorem terminating_direction:
  ∀ st ks e st' ks' e' .
    step (st, ks, e) = (st', ks', e') ∧
    ¬ terminating_state (st', ks', e')
    ⇒
    ¬ terminating_state (st, ks, e)
Proof
  simp[terminating_state_def]
  >> rpt strip_tac
  >> gvs[step_def, return_def]
QED

Theorem terminating_direction_n:
  ∀ n st ks e st' ks' e' .
    FUNPOW step n (st, ks, e) = (st', ks', e') ∧
    ¬ terminating_state (st', ks', e')
    ⇒
    ¬ terminating_state (st, ks, e)
Proof
  Induct
  >> simp[FUNPOW_SUC]
  >> rpt gen_tac
  >> strip_tac
  >> last_x_assum irule
  >> Cases_on ‘FUNPOW step n (st,ks,e)’
  >> PairCases_on ‘r’
  >> drule_all_then assume_tac terminating_direction
  >> simp[]
QED

Theorem scheme_divergence:
  ∀ state st ks st' ks' state' .
    step (st, ks, state) = (st', ks', state') ∧
    ¬ terminating_state (st, ks, state)
    ⇒
    (st, ks, state) ≠ (st', ks', state')
Proof
  Cases
  >> simp[terminating_state_def]
  >~ [‘Exp env e’] >- (
    Cases_on ‘e’
    >> simp[step_def] >- (
      rpt strip_tac
      >> Cases_on ‘mut_entry $ EL (env ' m) st’
      >> gvs[]
    )
    >- (
      CASE_TAC
      >> simp[]
      >> rpt strip_tac
      >> Cases_on `e'`
      >> ‘∀ (e:scheme_ast$exp) e' . e = e' ⇒ exp_size e = exp_size e'’ by simp[]
      >> pop_assum drule
      >> simp[exp_size_def]
    )
    >- (
      CASE_TAC
      >> simp[]
      >> rpt strip_tac
      >- (
        ‘∀ (e:scheme_ast$exp) e' . e = e' ⇒ exp_size e = exp_size e'’ by simp[]
        >> pop_assum drule
        >> simp[exp_size_def]
      )
      >> rpt (pairarg_tac >> gvs[])
      >> PairCases_on ‘h’
      >> gvs[]
    )
    >> rpt strip_tac
    >> rpt (pairarg_tac >> gvs[])
  )
  >> Cases_on ‘ks’
  >> simp[step_def]
  >> PairCases_on ‘h’
  >> simp[oneline return_def, oneline application_def, AllCaseEqs()]
  >> rpt strip_tac
  >> rpt (pairarg_tac >> gvs[])
  >> qpat_x_assum ‘_ = Throw _’ mp_tac
  >> rpt $ pop_assum kall_tac
  >> strip_tac
  >> ‘∀ v v' . v = v' ⇒ val_size v = val_size v'’ by simp[]
  >> pop_assum drule
  >> simp[cont_size_def]
QED

Theorem statically_scoped_program_valid:
  ∀ p . static_scope ∅ p ⇒ valid_state [] [] (Exp FEMPTY p)
Proof
  simp[Once valid_state_cases,
    can_lookup_cases, FEVERY_FEMPTY]
  >> simp[Once valid_cont_cases]
QED

val _ = export_theory();
