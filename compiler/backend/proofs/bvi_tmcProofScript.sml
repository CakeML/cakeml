(*
  Correctness proof for bvi_tailrec
*)
Theory bvi_tmcProof
Ancestors
  bvi_tmc bviProps bviSem bvlSem[qualified] backend_common[qualified] semanticPrimitivesProps[qualified]
Libs
  preamble

val s = “s : (num # γ, 'ffi) bviSem$state”;

Overload in_ns_2[local] = ``λn. n MOD bvl_to_bvi_namespaces = 2``

Inductive v_rel:
[~Number:]
  ∀f i. v_rel f (Number i) (Number i)
[~Word64:]
  ∀f w. v_rel f (Word64 w) (Word64 w)
[~Block:]
  ∀f n xs ys.
    LIST_REL (v_rel f) xs ys ⇒
    v_rel f (Block n xs) (Block n ys)
[~CodePtr:]
  ∀f n. v_rel f (CodePtr n) (CodePtr n)
[~RefPtr:]
  ∀f n m b.
    FLOOKUP f n = SOME m ⇒
    v_rel f (RefPtr b n) (RefPtr b m)
End

Inductive ref_rel:
[~ByteArray:]
  ref_rel f (ByteArray b bs) (ByteArray b bs)
[~ValueArray:]
  LIST_REL (v_rel f) xs ys ⇒
  ref_rel f (ValueArray xs) (ValueArray ys)
[~Thunk:]
  v_rel f x y ⇒
  ref_rel f (Thunk tm x) (Thunk tm y)
End

Definition env_rel_def:
  env_rel opt f env1 env2 <=>
  ∃xs ys.
    env2 = xs ++ ys ∧
    LIST_REL (v_rel f) env1 xs ∧
    (opt ⇒
      LENGTH ys = 2 ∧
      ∃hole_ptr hole_idx.
        EL 0 ys = RefPtr F hole_ptr ∧
        EL 1 ys = Number hole_idx ∧
        backend_common$small_enough_int hole_idx)
End

Definition no_mutcons_op_def:
  no_mutcons_op op ⇔ ∀tag i. op ≠ MemOp (MutCons tag i)
End

Definition no_mutcons_def[simp]:
  (no_mutcons (Var n) ⇔ T) ∧
  (no_mutcons (If x1 x2 x3) ⇔ no_mutcons x1 ∧ no_mutcons x2 ∧ no_mutcons x3) ∧
  (no_mutcons (Let xs x) ⇔ EVERY no_mutcons xs ∧ no_mutcons x) ∧
  (no_mutcons (Raise x) ⇔ no_mutcons x) ∧
  (no_mutcons (Tick x) ⇔ no_mutcons x) ∧
  (no_mutcons (Call ticks dest xs handler) ⇔
     EVERY no_mutcons xs ∧ (case handler of NONE => T | SOME x => no_mutcons x)) ∧
  (no_mutcons (Force loc n) ⇔ T) ∧
  (no_mutcons (Op op xs) ⇔ no_mutcons_op op ∧ EVERY no_mutcons xs)
Termination
  WF_REL_TAC ‘measure exp_size’
End

Definition code_rel_def:
  code_rel c1 c2 ⇔
    ∀loc arity exp.
      lookup loc c1 = SOME (arity, exp) ⇒
      no_mutcons exp ∧
      ∃n.
        (compile_exp loc n arity exp = NONE ⇒
         lookup loc c2 = SOME (arity, exp)) ∧
        ∀wrap work.
          compile_exp loc n arity exp = SOME (wrap,work) ⇒
          lookup loc c2 = SOME (arity, wrap) ∧
          lookup n c2 = SOME (arity + 2, work)
End

Theorem code_rel_domain:
   ∀c1 c2.
     code_rel c1 c2 ⇒ domain c1 ⊆ domain c2
Proof
  rw [code_rel_def, SUBSET_DEF]
  >> CCONTR_TAC >> fs []
  >> Cases_on `lookup x c1`
  >- fs [lookup_NONE_domain]
  >> fs [GSYM lookup_NONE_domain]
  >> rename1 `SOME z`
  >> PairCases_on `z`
  >> rename [‘lookup x c1 = SOME (arity,exp)’]
  >> first_x_assum drule
  >> strip_tac >> pop_assum mp_tac
  >> fs [compile_exp_def]
  >> rpt strip_tac
  >> CASE_TAC >> fs []
QED

Definition free_names_def:
  free_names n (name: num) ⇔ ∀k. n + bvl_to_bvi_namespaces*k ≠ name
End

Definition namespace_rel_def:
  namespace_rel (c1:'a spt) (c2:'a spt) ⇔
    (∀n. n ∈ domain c2 ∧ bvl_num_stubs ≤ n ⇒ if in_ns_2 n then n ∉ domain c1 else n ∈ domain c1) ∧
    (∀n. n ∈ domain c1 ∧ bvl_num_stubs ≤ n ⇒ ¬(in_ns_2 n)) ∧
    (∀n. n ∈ domain c2 ∧ n < bvl_num_stubs ⇒ n ∈ domain c1)
End

(* This should say: expression in prog satisfies no-mutblock property *)
Definition input_condition_def:
  input_condition next prog ⇔
    EVERY (free_names next o FST) prog ∧
    EVERY (no_mutcons o SND o SND) prog ∧
    ALL_DISTINCT (MAP FST prog) ∧
    EVERY ($~ o in_ns_2 o FST) (FILTER ((<=) bvl_num_stubs o FST) prog) ∧
    bvl_num_stubs ≤ next ∧ in_ns_2 next
End

Definition state_ref_rel_def:
  state_ref_rel f (s_refs : num |-> bvlSem$v ref) (t_refs : num |-> bvlSem$v ref) ⇔
    FDOM f = FDOM s_refs ∧
    ∀i v.
      FLOOKUP s_refs i = SOME v ⇒
       ∃j w. FLOOKUP f i = SOME j ∧
             ref_rel f v w ∧
             FLOOKUP t_refs j = SOME w
End

Definition fmap_inj_def:
  fmap_inj (f : num |-> num) ⇔
    ∀p1 p2 q. FLOOKUP f p1 = SOME q ∧ FLOOKUP f p2 = SOME q ⇒ p1 = p2
End

Theorem fmap_inj_FEMPTY[simp]:
  fmap_inj FEMPTY
Proof
  rw [fmap_inj_def]
QED

Theorem fmap_inj_update:
  ∀f k v.
    fmap_inj f ∧ v ∉ FRANGE f ⇒
    fmap_inj (f⟨k ↦ v⟩)
Proof
  rw [fmap_inj_def, FLOOKUP_SIMP]
  >> gvs [AllCaseEqs ()]
  >> gvs [FRANGE_FLOOKUP]
QED

Definition state_rel_def:
  state_rel f s (t:('a,'ffi) bviSem$state) ⇔
    state_ref_rel f s.refs t.refs ∧
    t.clock = s.clock ∧
    OPTREL (λp p'. FLOOKUP f p = SOME p') s.global t.global ∧
    t.ffi = s.ffi ∧
    t.compile_oracle = state_co compile_prog s.compile_oracle ∧
    s.compile = state_cc compile_prog t.compile ∧
    code_rel s.code t.code ∧
    namespace_rel s.code t.code ∧
    (∀n. let ((next,cfg),prog) = s.compile_oracle n in
            input_condition next prog) ∧
    (∀n. n ∈ domain t.code ∧ in_ns_2 n ⇒ n < FST(FST(s.compile_oracle 0))) ∧
    fmap_inj f
End

(* Copied - not used currently *)
Theorem compile_prog_code_rel:
   compile_prog next prog = (next1, prog2) ∧
   ALL_DISTINCT (MAP FST prog) ∧
   EVERY (free_names next o FST) prog ⇒
     code_rel (fromAList prog) (fromAList prog2)
Proof
  cheat
QED

Definition opt_res_rel_def:
  opt_res_rel f (r1 : (v list, v) result) (r2 : (v list, v) result) =
  case (r1,r2) of
  | (Rval v1,Rval [Block 0 []]) => T
  | (Rerr e1,Rerr e2) => exc_rel (v_rel f) e1 e2
  | _ => F
End

Theorem v_rel_submap:
  ∀f v1 v2 f'. v_rel f v1 v2 ∧ f SUBMAP f' ⇒ v_rel f' v1 v2
Proof
  Induct_on ‘v_rel’
  >> rpt strip_tac
  >> simp [Once v_rel_cases]
  >- gvs [LIST_REL_EL_EQN]
  >> drule_all FLOOKUP_SUBMAP
  >> fs []
QED

Theorem list_rel_submap:
  LIST_REL (v_rel f) env1 env2 ∧ f SUBMAP f' ⇒ LIST_REL (v_rel f') env1 env2
Proof
  Induct_on ‘LIST_REL (v_rel f) env1 env2’ using LIST_REL_ind
  >> rpt strip_tac
  >> gvs [LIST_REL_def]
  >> irule v_rel_submap
  >> first_x_assum $ irule_at Any
  >> gvs []
QED

Theorem env_rel_submap:
  env_rel opt f env1 env2 ∧ f SUBMAP f' ⇒ env_rel opt f' env1 env2
Proof
  strip_tac
  >> gvs [env_rel_def]
  >> qexistsl [‘xs’, ‘ys’]
  >> gvs []
  >> irule list_rel_submap
  >> first_x_assum $ irule_at Any
  >> gvs []
QED

Theorem env_rel_relax_opt:
  ∀opt f env1 env2.
    env_rel opt f env1 env2 ⇒
    env_rel F f env1 env2
Proof
  rw [env_rel_def]
  >> qexists ‘xs’
  >> gvs []
QED

Theorem env_rel_cons:
  env_rel opt f env1 env2 ∧
  v_rel f a b ⇒
  env_rel opt f (a::env1) (b::env2)
Proof
  rw [env_rel_def]
  >> qexistsl [‘b::xs’, ‘ys’]
  >> gvs []
QED

Theorem env_rel_append:
  env_rel opt f env1 env2 ∧
  LIST_REL (v_rel f) a b ⇒
  env_rel opt f (a ++ env1) (b ++ env2)
Proof
  rw []
  >> gvs [env_rel_def]
  >> qexistsl [‘b ++ xs’, ‘ys’]
  >> gvs [LIST_REL_APPEND_suff]
QED

Theorem env_rel_length_opt:
  ∀f env1 env2.
    env_rel T f env1 env2 ⇒
    LENGTH env2 = LENGTH env1 + 2
Proof
  rw [env_rel_def]
  >> drule LIST_REL_LENGTH
  >> gvs [APPEND_LENGTH_EQ]
QED

(* not a strict equality anymore! *)
Theorem env_rel_length_non_opt:
  ∀f env1 env2.
    env_rel F f env1 env2 ⇒
    LENGTH env2 >= LENGTH env1
Proof
  rw [env_rel_def]
  >> drule LIST_REL_LENGTH
  >> gvs []
QED

Theorem env_rel_length:
  ∀opt f env1 env2.
    env_rel opt f env1 env2 ⇒
    LENGTH env2 >= LENGTH env1
Proof
  rw []
  >> Cases_on ‘opt’
  >- (drule env_rel_length_opt >> gvs [])
  >> drule env_rel_length_non_opt >> gvs []
QED

Theorem env_rel_extras_opt:
  ∀f env env'.
    env_rel T f env env' ⇒
    ∃hole_ptr hole_idx.
      env'❲LENGTH env❳ = RefPtr F hole_ptr ∧
      env'❲LENGTH env + 1❳ = Number hole_idx
Proof
  rw [env_rel_def]
  >> drule LIST_REL_LENGTH
  >> strip_tac
  >> gvs [EL_APPEND_EQN]
QED

Theorem env_rel_el_v_rel:
  ∀opt f env1 env2 n.
    env_rel opt f env1 env2 ∧
    n < LENGTH env1 ⇒
    v_rel f env1❲n❳ env2❲n❳
Proof
  rw []
  >> gvs [env_rel_def]
  >> drule LIST_REL_LENGTH
  >> strip_tac
  >> ‘n < LENGTH xs’ by gvs []
  >> gvs [EL_APPEND_EQN, LIST_REL_EL_EQN]
QED

Theorem env_rel_strip_extras:
  ∀f env1 env2.
    env_rel T f env1 env2 ⇒
    ∃env2' hole_ptr hole_idx.
      env_rel F f env1 env2' ∧
      env2 = env2' ++ [RefPtr F hole_ptr; Number hole_idx] ∧
      backend_common$small_enough_int hole_idx
Proof
  rw []
  >> gvs [env_rel_def]
  >> qexistsl [‘xs’, ‘hole_ptr’, ‘hole_idx’]
  >> gvs []
  >> conj_tac
  >- (qexistsl [‘xs’, ‘[]’] >> gvs [])
  >> gvs []
  >> gvs [LENGTH_EQ_NUM_compute]
QED

Theorem state_rel_dec:
  ∀n t f s s'.
    state_rel f s s' ∧
    s.clock = SUC n ∧
    s'.clock = SUC n ∧
    SUC n >= t ⇒
    state_rel f (dec_clock t s) (dec_clock t s')
Proof
  rw [] >> gvs [state_rel_def, dec_clock_def]
QED

Theorem state_rel_with_clock:
  ∀n f s s'.
    state_rel f s s' ⇒
    state_rel f (s with clock := n) (s' with clock := n)
Proof
  rw [state_rel_def]
QED

Theorem state_ref_rel_filled:
  ∀f refs refs' k v.
    state_ref_rel f refs refs' ∧
    k ∉ FRANGE f ⇒
    state_ref_rel f refs refs'⟨k ↦ v⟩
Proof
  rw [state_ref_rel_def]
  >> gvs [FLOOKUP_SIMP]
  >> first_x_assum drule
  >> strip_tac
  >> gvs []
  >> first_assum $ irule_at Any
  >> IF_CASES_TAC >> gvs []
  >> gvs [FLOOKUP_DEF, FRANGE_DEF]
QED

Theorem state_rel_filled:
  ∀f s s' k v.
    state_rel f s s' ∧
    k ∉ FRANGE f ⇒
    state_rel f s (s' with refs := s'.refs⟨k ↦ v⟩)
Proof
  rw [state_rel_def]
  >> irule state_ref_rel_filled
  >> gvs []
QED

Definition hole_has_val_def:
  hole_has_val (f : num |-> num) (env1 : v list) (env2 : v list) (refs : num |-> v ref) c ⇔
  LENGTH env2 = LENGTH env1 + 2 ∧
  ∃hole_ptr tag left right.
    env2❲LENGTH env1❳ = RefPtr F hole_ptr ∧
    env2❲LENGTH env1 + 1❳ = Number (&LENGTH left) ∧
    backend_common$small_enough_int (&LENGTH left) ∧
    hole_ptr ∉ FRANGE f ∧
    FLOOKUP refs hole_ptr = SOME (MutBlock tag left c right)
End

Definition holes_unchanged_except_def:
  holes_unchanged_except f refs refs' changed ⇔
    (∀ptr val.
       ptr ∉ FRANGE f ∧
       ptr ∉ changed ∧
       FLOOKUP refs ptr = SOME val ⇒
       FLOOKUP refs' ptr = SOME val) ∧
    (∀ptr tag left child right.
       ptr ∉ FRANGE f ∧
       ptr ∈ changed ∧
       FLOOKUP refs ptr = SOME (MutBlock tag left child right) ⇒
       ∃child'.
         FLOOKUP refs' ptr = SOME (MutBlock tag left child' right))
End

Definition only_fresh_def:
  only_fresh (f : num |-> num) (f' : num |-> num) (refs_old : num |-> v ref) =
  ∀n. n ∈ FRANGE f' ∧ ~(n ∈ FRANGE f) ⇒ ~(n ∈ FDOM refs_old)
End

Theorem holes_unchanged_except_refl:
  ∀f refs changed. holes_unchanged_except f refs refs changed
Proof
  rw [holes_unchanged_except_def]
QED

Theorem holes_unchanged_except_submap:
  ∀f f' refs refs' changed.
    holes_unchanged_except f refs refs' changed ∧
    f ⊑ f' ⇒
    holes_unchanged_except f' refs refs' changed
Proof
  rw [holes_unchanged_except_def]
  >-
   (first_x_assum $ qspecl_then [‘ptr’, ‘val’] mp_tac
    >> strip_tac
    >> gvs []
    >> pop_assum irule
    >> spose_not_then assume_tac
    >> drule SUBMAP_FRANGE
    >> strip_tac
    >> gvs [SUBSET_DEF])
  >> first_x_assum irule
  >> gvs []
  >> spose_not_then assume_tac
  >> drule SUBMAP_FRANGE
  >> strip_tac
  >> gvs [SUBSET_DEF]
QED

Theorem holes_unchanged_except_trans:
  ∀f f' refs refs' refs'' changed.
    holes_unchanged_except f refs refs' changed ∧
    holes_unchanged_except f' refs' refs'' changed ∧
    only_fresh f f' refs ∧
    f ⊑ f' ⇒
    holes_unchanged_except f refs refs'' changed
Proof
  rw [holes_unchanged_except_def]
  >-
   (rpt $ first_x_assum $ qspecl_then [‘ptr’, ‘val’] mp_tac
    >> rpt strip_tac
    >> gvs []
    >> first_x_assum irule
    >> spose_not_then assume_tac
    >> gvs [only_fresh_def]
    >> first_x_assum drule_all
    >> strip_tac
    >> gvs [FLOOKUP_DEF])
  >> first_x_assum irule
  >> first_x_assum drule_all
  >> strip_tac
  >> rpt $ first_assum $ irule_at Any
  >> spose_not_then assume_tac
  >> gvs [only_fresh_def]
  >> first_x_assum drule_all
  >> strip_tac
  >> gvs [FLOOKUP_DEF]
QED

Theorem holes_unchanged_except_subset:
  ∀f refs refs' changed changed'.
    holes_unchanged_except f refs refs' changed ∧
    changed SUBSET changed' ⇒
    holes_unchanged_except f refs refs' changed'
Proof
  rw [holes_unchanged_except_def]
  >-
   (first_x_assum irule
    >> gvs [SUBSET_DEF]
    >> first_x_assum $ drule_at Concl
    >> gvs [])
  >> Cases_on ‘ptr ∈ changed’
  >-
   (first_x_assum $ irule_at Any
    >> gvs []
    >> first_assum $ irule_at Any)
  >> last_x_assum drule
  >> gvs []
QED

Theorem holes_unchanged_except_del:
  ∀f refs_old refs_new changed ptr v.
    holes_unchanged_except f refs_old⟨ptr ↦ v⟩ refs_new changed ∧
    ptr ∉ FDOM refs_old ⇒
    holes_unchanged_except f refs_old refs_new (changed DIFF {ptr})
Proof
  rw [holes_unchanged_except_def]
  >-
   (first_x_assum irule
    >> gvs [FLOOKUP_SIMP, FLOOKUP_DEF]
    >> IF_CASES_TAC
    >- gvs []
    >> gvs [])
  >> rpt $ first_x_assum $ irule_at Any
  >> Cases_on ‘ptr = ptr'’
  >- gvs [FLOOKUP_SIMP, FLOOKUP_DEF]
  >> gvs [FLOOKUP_SIMP, FLOOKUP_DEF]
QED

Theorem holes_unchanged_except_del_SING:
  ∀f refs_old refs_new changed ptr v.
    holes_unchanged_except f refs_old⟨ptr ↦ v⟩ refs_new {ptr} ∧
    ptr ∉ FDOM refs_old ⇒
    holes_unchanged_except f refs_old refs_new EMPTY
Proof
  rw []
  >> drule_all holes_unchanged_except_del
  >> strip_tac
  >> gvs []
QED

Theorem holes_unchanged_except_changed:
  ∀f refs_old refs_new changed ptr tag l c r.
    holes_unchanged_except f refs_old⟨ptr ↦ MutBlock tag l c r⟩ refs_new EMPTY ∧
    FLOOKUP refs_old ptr = SOME (MutBlock tag l c' r) ⇒
    holes_unchanged_except f refs_old refs_new {ptr}
Proof
  rw [holes_unchanged_except_def]
  >-
   (gvs []
    >> rw []
    >> first_x_assum irule
    >> gvs [FLOOKUP_SIMP, FLOOKUP_DEF])
  >> first_x_assum $ irule_at Any
  >> gvs [FLOOKUP_SIMP, FLOOKUP_DEF]
QED

Theorem holes_unchanged_except_filled:
  ∀f refs_old refs_new changed ptr tag l c r.
    holes_unchanged_except f refs_old refs_new EMPTY ∧
    FLOOKUP refs_old ptr = SOME (MutBlock tag l c' r) ⇒
    holes_unchanged_except f refs_old refs_new⟨ptr ↦ MutBlock tag l c r⟩ {ptr}
Proof
  rw []
  >> irule holes_unchanged_except_changed
  >> first_assum $ irule_at Any
  >> qexists ‘c’
  >> gvs [holes_unchanged_except_def]
  >> rw []
  >> gvs [FLOOKUP_SIMP]
  >> IF_CASES_TAC
  >- gvs []
  >> gvs []
QED

Theorem unchanged_hole_has_val:
  ∀f f' env env' hole_ptr hole_idx refs refs' c changed.
    hole_has_val f env (env' ++ [RefPtr F hole_ptr; Number hole_idx]) refs c ∧
    only_fresh f f' refs ∧
    holes_unchanged_except f refs refs' changed ∧
    hole_ptr ∉ changed ⇒
    hole_has_val f' env (env' ++ [RefPtr F hole_ptr; Number hole_idx]) refs' c
Proof
  rw [hole_has_val_def]
  >> gvs [EL_APPEND_EQN, holes_unchanged_except_def]
  >> first_x_assum drule_all
  >> strip_tac
  >> gvs []
  >> spose_not_then assume_tac
  >> gvs [only_fresh_def]
  >> first_x_assum drule_all
  >> strip_tac
  >> gvs [FLOOKUP_DEF]
QED

Theorem hole_has_val_submap:
  ∀f f' env1 env2 refs c.
    hole_has_val f' env1 env2 refs c ∧
    f ⊑ f' ⇒
    hole_has_val f env1 env2 refs c
Proof
  rw [hole_has_val_def]
  >> qexistsl [‘hole_ptr’, ‘tag’, ‘left’, ‘right’]
  >> gvs []
  >> drule SUBMAP_FRANGE
  >> strip_tac
  >> spose_not_then assume_tac
  >> gvs [SUBSET_DEF]
QED

Theorem hole_has_val_append:
  ∀f env env' refs c vs vs'.
    hole_has_val f env env' refs c ∧
    LIST_REL (v_rel f) vs vs' ⇒
    hole_has_val f (vs ++ env) (vs' ++ env') refs c
Proof
  rw [hole_has_val_def]
  >> drule LIST_REL_LENGTH
  >> strip_tac
  >> gvs [EL_APPEND_EQN]
QED

Theorem hole_has_val_unappend:
  ∀f.
    hole_has_val f (vs ++ env) (vs' ++ env') refs c ∧
    LIST_REL (v_rel f) vs vs' ⇒
    hole_has_val f env env' refs c
Proof
  rw [hole_has_val_def]
  >> drule LIST_REL_LENGTH
  >> strip_tac
  >> gvs [EL_APPEND_EQN]
QED

Theorem hole_has_val_dec:
  ∀f env env' s c n.
    hole_has_val f env env' s.refs c ∧
    s.clock = SUC n ⇒
    hole_has_val f env env' (dec_clock 1 s).refs c
Proof
  rw [hole_has_val_def]
QED

Theorem only_fresh_refl:
  ∀f refs. only_fresh f f refs
Proof
  rw [only_fresh_def]
QED

Theorem only_fresh_trans:
  ∀f f' f'' refs refs'.
    only_fresh f f' refs ∧
    only_fresh f' f'' refs' ∧
    FDOM refs SUBSET FDOM refs' ⇒
    only_fresh f f'' refs
Proof
  rw [only_fresh_def]
  >> rpt $ first_x_assum $ qspec_then ‘n’ mp_tac
  >> rpt strip_tac
  >> gvs [SUBSET_DEF]
QED

Theorem only_fresh_submap:
  ∀f f' f'' refs.
    only_fresh f f'' refs ∧
    f' ⊑ f'' ⇒
    only_fresh f f' refs
Proof
  rw [only_fresh_def]
  >> first_assum $ irule_at Any
  >> gvs []
  >> drule SUBMAP_FRANGE
  >> strip_tac
  >> gvs [SUBSET_DEF]
QED

Theorem non_fresh_not_in_frange:
  ptr ∈ FDOM refs_old ∧
  ptr ∉ FRANGE f ∧
  only_fresh f f' refs_old ⇒
  ptr ∉ FRANGE f'
Proof
  rw [only_fresh_def]
  >> first_x_assum $ drule_at Concl
  >> strip_tac
  >> gvs []
QED

Theorem fresh_ptr_fresh:
  ∀refs.
    (LEAST ptr. ptr ∉ FDOM refs) ∉ FDOM refs
Proof
  rw []
  >> numLib.LEAST_ELIM_TAC
  >> conj_tac
  >-
   (qexists ‘SUC (MAX_SET (FDOM refs))’
    >> spose_not_then assume_tac
    >> imp_res_tac X_LE_MAX_SET
    >> qspec_then ‘FDOM refs’ mp_tac X_LE_MAX_SET
    >> impl_tac
    >- gvs []
    >> disch_then drule
    >> strip_tac
    >> gvs [])
  >> rw []
QED

Theorem fresh_not_in_range_f:
  ∀f s_refs t_refs.
    state_ref_rel f s_refs t_refs ⇒
    (LEAST ptr. ptr ∉ FDOM t_refs) ∉ FRANGE f
Proof
  rw []
  >> spose_not_then assume_tac
  >> qspec_then ‘t_refs’ mp_tac fresh_ptr_fresh
  >> strip_tac
  >> gvs [state_ref_rel_def, FRANGE_DEF]
  >> Cases_on ‘FLOOKUP s_refs x’
  >- gvs [FLOOKUP_DEF]
  >> first_x_assum drule
  >> strip_tac
  >> gvs [FLOOKUP_DEF]
QED

Theorem only_fresh_del:
  ∀f f' refs ptr v.
    only_fresh f f' refs⟨ptr ↦ v⟩ ∧
    ptr ∉ FRANGE f ⇒
    only_fresh f f' refs
Proof
  rw []
  >> gvs [only_fresh_def]
QED

Theorem flookup_com_neq:
  ∀m k1 v1 k2 v2.
    k1 ≠ k2 ⇒
    m⟨k1 ↦ v1; k2 ↦ v2⟩ = m⟨k2 ↦ v2; k1 ↦ v1⟩
Proof
  rw []
  >> irule $ iffRL fmap_eq_flookup
  >> rw []
  >> gvs [FLOOKUP_SIMP, FLOOKUP_DEF]
  >> IF_CASES_TAC
  >- gvs []
  >> gvs []
QED

Definition mb_rel_def:
  (mb_rel f refs (Block tag xs) (RefPtr b ptr) =
   (b = F ∧
    ptr ∉ FRANGE f ∧
    ∃left child right left' child' right'.
      xs = left ++ [child] ++ right ∧
      FLOOKUP refs ptr = SOME (MutBlock tag left' child' right') ∧
      LIST_REL (v_rel f) left left' ∧
      mb_rel f (refs \\ ptr) child child' ∧
      LIST_REL (v_rel f) right right')) ∧
  (mb_rel f refs v1 v2 = v_rel f v1 v2)
Termination
  (* There is something similar for definition of finalise_cons in bviSem *)
  cheat
End

Theorem mb_rel_cons:
  ∀refs ptr f tag left left' v v' right right'.
    mb_rel f (refs \\ ptr) v v' ∧
    LIST_REL (v_rel f) left left' ∧
    LIST_REL (v_rel f) right right' ∧
    FLOOKUP refs ptr = SOME (MutBlock tag left' v' right') ∧
    ptr ∉ FRANGE f ⇒
    mb_rel f refs (Block tag (left ++ [v] ++ right)) (RefPtr F ptr)
Proof
  rw []
  >> simp [mb_rel_def]
  >> qexistsl [‘left’, ‘v’, ‘right’]
  >> gvs []
QED

Theorem mb_rel_del:
  ∀f refs v1 v2 ptr tag left ptr' right.
    mb_rel f refs v1 v2 ∧
    FLOOKUP refs ptr = SOME (MutBlock tag left (RefPtr F ptr') right) ∧
    ptr' ∉ FDOM refs ∧
    ptr' ∉ FRANGE f ⇒
    mb_rel f (refs \\ ptr) v1 v2
Proof
  recInduct mb_rel_ind
  >> rw [mb_rel_def]
  >> Cases_on ‘ptr = ptr'’
  >-
   (gvs []
    >> Cases_on ‘child’ >> gvs [mb_rel_def, v_rel_cases]
    >- gvs [DOMSUB_FLOOKUP_THM, FLOOKUP_DEF]
    >> gvs [FRANGE_DEF, FLOOKUP_DEF])
  >> first_x_assum drule
  >> disch_then $ qspec_then ‘ptr'’ mp_tac
  >> gvs [DOMSUB_FLOOKUP_THM]
  >> strip_tac
  >> simp [DOMSUB_COMMUTES]
  >> rpt $ first_assum $ irule_at Any
  >> gvs []
QED

Theorem state_ref_rel_update:
  ∀f s_refs t_refs ptr ptr' v w.
    state_ref_rel f s_refs t_refs ∧ fmap_inj f ∧
    FLOOKUP f ptr = SOME ptr' ∧ ref_rel f v w ⇒
    state_ref_rel f (s_refs⟨ptr ↦ v⟩) (t_refs⟨ptr' ↦ w⟩)
Proof
  rw [state_ref_rel_def]
  >- (gvs [FLOOKUP_DEF, EXTENSION] >> metis_tac [])
  >> Cases_on ‘i = ptr’ >> gvs [FLOOKUP_SIMP]
  >> first_x_assum drule >> strip_tac
  >> first_assum $ irule_at Any >> first_assum $ irule_at Any
  >> ‘ptr' ≠ j’ by (gvs [fmap_inj_def] >> metis_tac [])
  >> gvs []
QED

Theorem bvl_to_bvi_refs:
  bvl_to_bvi (bvi_to_bvl s with refs := r) s = s with refs := r
Proof
  simp [bvl_to_bvi_def, bvi_to_bvl_def, bviSemTheory.state_component_equality]
QED

Theorem holes_unchanged_except_frange_update:
  ∀f p k v refs.
    FLOOKUP f p = SOME k ⇒
    holes_unchanged_except f refs (refs⟨k ↦ v⟩) ∅
Proof
  rw [holes_unchanged_except_def, FLOOKUP_SIMP]
  >> ‘k ≠ ptr’ by (CCONTR_TAC >> gvs [IN_FRANGE_FLOOKUP] >> metis_tac [])
  >> gvs []
QED

Theorem ref_rel_submap:
  ∀f f' v w. ref_rel f v w ∧ f ⊑ f' ⇒ ref_rel f' v w
Proof
  rw [ref_rel_cases]
  >> gvs [LIST_REL_EL_EQN]
  >> rw []
  >> metis_tac [v_rel_submap, list_rel_submap]
QED

Theorem state_ref_rel_alloc:
  ∀f s_refs t_refs src tgt rv rw.
    state_ref_rel f s_refs t_refs ∧
    src ∉ FDOM s_refs ∧ tgt ∉ FDOM t_refs ∧ tgt ∉ FRANGE f ∧
    ref_rel (f⟨src ↦ tgt⟩) rv rw ⇒
    state_ref_rel (f⟨src ↦ tgt⟩) (s_refs⟨src ↦ rv⟩) (t_refs⟨tgt ↦ rw⟩)
Proof
  rw [state_ref_rel_def]
  >> ‘f ⊑ f⟨src ↦ tgt⟩’ by gvs [SUBMAP_FUPDATE_FLOOKUP, FLOOKUP_DEF]
  >> gvs [FLOOKUP_SIMP]
  >> Cases_on ‘i = src’ >> gvs []
  >> first_x_assum drule >> strip_tac
  >> qexistsl [‘j’, ‘w’] >> gvs []
  >> conj_tac
  >- (irule ref_rel_submap >> first_assum $ irule_at Any
      >> gvs [SUBMAP_FUPDATE_FLOOKUP, FLOOKUP_DEF])
  >> ‘j ≠ tgt’ by (gvs [IN_FRANGE_FLOOKUP] >> metis_tac [])
  >> gvs []
QED

Theorem state_rel_alloc:
  ∀f s s' src tgt rv rw.
    state_rel f s s' ∧
    src ∉ FDOM s.refs ∧ tgt ∉ FDOM s'.refs ∧ tgt ∉ FRANGE f ∧
    ref_rel (f⟨src ↦ tgt⟩) rv rw ⇒
    FLOOKUP (f⟨src ↦ tgt⟩) src = SOME tgt ∧
    state_rel (f⟨src ↦ tgt⟩)
      (s with refs := s.refs⟨src ↦ rv⟩) (s' with refs := s'.refs⟨tgt ↦ rw⟩) ∧
    f ⊑ f⟨src ↦ tgt⟩ ∧
    only_fresh f (f⟨src ↦ tgt⟩) s'.refs ∧
    holes_unchanged_except f s'.refs (s'.refs⟨tgt ↦ rw⟩) ∅
Proof
  rpt gen_tac >> strip_tac
  >> ‘src ∉ FDOM f’ by gvs [state_rel_def, state_ref_rel_def]
  >> ‘f ⊑ f⟨src ↦ tgt⟩’ by gvs [SUBMAP_FUPDATE_FLOOKUP, FLOOKUP_DEF]
  >> simp [FLOOKUP_SIMP]
  >> rpt conj_tac
  >- (gvs [state_rel_def]
      >> rpt conj_tac
      >- (irule state_ref_rel_alloc >> gvs [])
      >- (Cases_on ‘s.global’ >> gvs [OPTREL_def]
          >> irule FLOOKUP_SUBMAP >> first_assum $ irule_at Any >> gvs [])
      >> irule fmap_inj_update >> gvs [])
  >- (gvs [only_fresh_def] >> rw [] >> gvs [FRANGE_FUPDATE, DOMSUB_NOT_IN_DOM])
  >> gvs [holes_unchanged_except_def, FLOOKUP_SIMP] >> rw [] >> gvs [FLOOKUP_DEF]
QED

Theorem state_ref_rel_lookup:
  ∀f n m refs t_refs.
    FLOOKUP f n = SOME m ∧ state_ref_rel f refs t_refs ⇒
    ∃v w. FLOOKUP refs n = SOME v ∧ FLOOKUP t_refs m = SOME w ∧ ref_rel f v w
Proof
  rw []
  >> ‘n ∈ FDOM refs’ by (gvs [state_ref_rel_def] >> gvs [FLOOKUP_DEF])
  >> Cases_on ‘FLOOKUP refs n’ >- gvs [FLOOKUP_DEF]
  >> gvs [state_ref_rel_def] >> first_x_assum drule >> rw [] >> gvs []
QED

Theorem fmap_inj_flookup_eq:
  ∀f n m n' m'.
    fmap_inj f ∧ FLOOKUP f n = SOME m ∧ FLOOKUP f n' = SOME m' ⇒
    ((m = m') ⇔ (n = n'))
Proof
  rw [] >> eq_tac >> rw [] >> gvs [fmap_inj_def] >> metis_tac []
QED

Theorem v_to_list_v_rel:
  ∀lv xs lw f.
    bvlSem$v_to_list lv = SOME xs ∧ v_rel f lv lw ⇒
    ∃ys. bvlSem$v_to_list lw = SOME ys ∧ LIST_REL (v_rel f) xs ys
Proof
  recInduct bvlSemTheory.v_to_list_ind
  >> rw [bvlSemTheory.v_to_list_def]
  >> qpat_x_assum ‘v_rel f _ _’ mp_tac
  >> simp [Once v_rel_cases] >> strip_tac >> gvs []
  >> gvs [bvlSemTheory.v_to_list_def, AllCaseEqs ()]
  >> first_x_assum drule >> strip_tac >> gvs []
QED

Theorem list_to_v_v_rel:
  ∀xs ys f.
    LIST_REL (v_rel f) xs ys ⇒
    v_rel f (list_to_v xs) (list_to_v ys)
Proof
  Induct >> Cases_on ‘ys’ >> rw [bvlSemTheory.list_to_v_def]
  >> simp [Once v_rel_cases]
QED

Theorem do_eq_v_rel:
  (∀refs x1 x2 t_refs y1 y2.
     v_rel f x1 y1 ∧ v_rel f x2 y2 ∧ state_ref_rel f refs t_refs ∧ fmap_inj f ⇒
     do_eq refs x1 x2 = do_eq t_refs y1 y2) ∧
  (∀refs x1s x2s t_refs y1s y2s.
     LIST_REL (v_rel f) x1s y1s ∧ LIST_REL (v_rel f) x2s y2s ∧
     state_ref_rel f refs t_refs ∧ fmap_inj f ⇒
     do_eq_list refs x1s x2s = do_eq_list t_refs y1s y2s)
Proof
  ho_match_mp_tac bvlSemTheory.do_eq_ind >> rw []
  >> gvs [v_rel_cases, bvlSemTheory.isClos_def]
  >> imp_res_tac LIST_REL_LENGTH >> gvs []
  >> imp_res_tac state_ref_rel_lookup >> gvs [ref_rel_cases]
  >> rw [] >> gvs []
  >> TRY (qspecl_then [‘f’,‘n1’,‘m’,‘n2’,‘m'’] mp_tac fmap_inj_flookup_eq
          >> impl_tac >- gvs [] >> strip_tac >> gvs [])
  >> TRY (qspecl_then [‘f’,‘n’,‘m’,‘n'’,‘m'’] mp_tac fmap_inj_flookup_eq
          >> impl_tac >- gvs [] >> strip_tac >> gvs [])
  >> rw [] >> gvs []
  >> TRY (first_x_assum irule >> gvs [])
  >> qmatch_goalsub_abbrev_tac ‘do_eq_list t_refs aa bb’
  >> ‘do_eq_list refs xs xs' = do_eq_list t_refs aa bb’ by
       (last_x_assum (qspecl_then [‘t_refs’, ‘Block n aa’, ‘Block n bb’] mp_tac)
        >> impl_tac >- gvs [Abbr ‘aa’, Abbr ‘bb’]
        >> simp [bvlSemTheory.do_eq_def, bvlSemTheory.isClos_def])
  >> gvs []
  >> Cases_on ‘do_eq_list t_refs aa bb’ >> gvs []
  >> Cases_on ‘b’ >> gvs []
  >> first_x_assum irule >> gvs []
QED

Theorem do_word_app_v_rel:
  ∀w vs res vs' f.
    bvlSem$do_word_app w vs = SOME res ∧ LIST_REL (v_rel f) vs vs' ⇒
    vs' = vs
Proof
  recInduct bvlSemTheory.do_word_app_ind
  >> rw [bvlSemTheory.do_word_app_def]
  >> gvs [AllCaseEqs (), v_rel_cases]
QED

Theorem do_word_app_v_rel_refl:
  ∀w vs res f.
    bvlSem$do_word_app w vs = SOME res ⇒ v_rel f res res
Proof
  recInduct bvlSemTheory.do_word_app_ind
  >> rw [bvlSemTheory.do_word_app_def]
  >> gvs [AllCaseEqs (), v_rel_cases, bvlSemTheory.Boolv_def]
QED

Theorem no_mutblock:
  ∀f refs t_refs ptr tag l c r.
    state_ref_rel f refs t_refs ∧ FLOOKUP refs ptr = SOME (MutBlock tag l c r) ⇒ F
Proof
  rw [] >> fs [state_ref_rel_def] >> rw []
  >> qexistsl [‘ptr’, ‘MutBlock tag l c r’] >> gvs [ref_rel_cases]
QED

Theorem do_app_op_rel:
  ∀f op vs vs' s s' t v.
    do_app op vs s = Rval (v,t) ∧
    no_mutcons_op op ∧
    LIST_REL (v_rel f) vs vs' ∧
    state_rel f s s' ⇒
    ∃f' v' t'.
      do_app op vs' s' = Rval (v',t') ∧
      v_rel f' v v' ∧
      state_rel f' t t' ∧
      f SUBMAP f' ∧
      only_fresh f f' s'.refs ∧
      holes_unchanged_except f s'.refs t'.refs ∅
Proof
  rw []
  >> Cases_on ‘op’
  >~ [‘Label n’] >- suspend "Label"
  >~ [‘FFI m’] >- suspend "FFI"
  >~ [‘IntOp i’] >- suspend "IntOp"
  >~ [‘WordOp w’] >- suspend "WordOp"
  >~ [‘BlockOp b’] >- suspend "BlockOp"
  >~ [‘GlobOp g’] >- suspend "GlobOp"
  >~ [‘MemOp m’] >- suspend "MemOp"
  >~ [‘Install’] >- suspend "Install"
  >~ [‘ThunkOp t’] >- suspend "ThunkOp"
QED

Resume do_app_op_rel[IntOp]:
  Cases_on ‘i’
  >~ [‘Const i’] >-
   (gvs [do_app_def, do_app_aux_def, CaseEq "option"]
    >> imp_res_tac LIST_REL_LENGTH
    >> first_assum $ irule_at Any
    >> gvs [v_rel_cases, only_fresh_refl, holes_unchanged_except_refl, NULL_LENGTH])
  >~ [‘LessConstSmall n’] >-
   (gvs [AllCaseEqs (), v_rel_cases, do_app_def, do_app_aux_def, bvlSemTheory.do_app_def]
    >> Cases_on ‘vs’ >> gvs [v_rel_cases, bvlSemTheory.do_int_app_def]
    >> reverse $ Cases_on ‘t’ >> gvs [v_rel_cases, bvlSemTheory.do_int_app_def]
    >- (Cases_on ‘t'’ >> gvs [v_rel_cases, bvlSemTheory.do_int_app_def, bvl_to_bvi_id, bvlSemTheory.Boolv_def])
    >> gvs [bvlSemTheory.Boolv_def, bvl_to_bvi_id]
    >> first_assum $ irule_at Any
    >> gvs [only_fresh_refl, holes_unchanged_except_refl])
  >> gvs [AllCaseEqs (), v_rel_cases, do_app_def, do_app_aux_def, bvlSemTheory.do_app_def]
  >> reverse $ Cases_on ‘vs’ >> gvs [v_rel_cases, bvlSemTheory.do_int_app_def]
  >> Cases_on ‘t’ >> gvs [v_rel_cases, bvlSemTheory.do_int_app_def]
  >> Cases_on ‘t'’ >> gvs [v_rel_cases, bvlSemTheory.do_int_app_def, bvl_to_bvi_id, bvlSemTheory.Boolv_def]
  >> first_assum $ irule_at Any
  >> gvs [only_fresh_refl, holes_unchanged_except_refl]
QED

Resume do_app_op_rel[WordOp]:
  gvs [do_app_def, do_app_aux_def, AllCaseEqs (), bvlSemTheory.do_app_def]
  >> drule_all do_word_app_v_rel >> strip_tac >> gvs []
  >> qexists ‘f’
  >> gvs [bvl_to_bvi_id, only_fresh_refl, holes_unchanged_except_refl]
  >> drule do_word_app_v_rel_refl >> simp []
QED

Resume do_app_op_rel[Label]:
  gvs [AllCaseEqs (), v_rel_cases, do_app_def, do_app_aux_def]
  >> first_assum $ irule_at Any
  >> gvs [only_fresh_refl, holes_unchanged_except_refl, state_rel_def, code_rel_def, domain_lookup]
  >> Cases_on ‘v’
  >> last_x_assum $ drule
  >> strip_tac
  >> Cases_on ‘compile_exp n n' q r’
  >- gvs []
  >> gvs []
  >> Cases_on ‘x’
  >> gvs []
QED

Resume do_app_op_rel[GlobOp]:
  Cases_on ‘g’
  >~ [‘do_app (GlobOp AllocGlobal)’] >-
   gvs [do_app_def, do_app_aux_def, AllCaseEqs ()]
  >~ [‘do_app (GlobOp GlobalsPtr)’] >-
   (gvs [do_app_def, do_app_aux_def, AllCaseEqs (), v_rel_cases]
    >> ‘OPTREL (λp p'. FLOOKUP f p = SOME p') s.global s'.global’ by gvs [state_rel_def]
    >> gvs [OPTREL_def]
    >> qexists ‘f’ >> gvs [only_fresh_refl, holes_unchanged_except_refl])
  >~ [‘do_app (GlobOp SetGlobalsPtr)’] >-
   (gvs [do_app_def, do_app_aux_def, AllCaseEqs (), v_rel_cases]
    >> qexists ‘f’
    >> simp [only_fresh_refl, holes_unchanged_except_refl]
    >> rpt conj_tac
    >- simp [bvlSemTheory.Unit_def]
    >> gvs [state_rel_def, OPTREL_def])
  >~ [‘do_app (GlobOp (Global _))’] >-
   (gvs [do_app_def, do_app_aux_def, AllCaseEqs (), v_rel_cases]
    >> ‘OPTREL (λp p'. FLOOKUP f p = SOME p') s.global s'.global’ by gvs [state_rel_def]
    >> ‘state_ref_rel f s.refs s'.refs’ by gvs [state_rel_def]
    >> gvs [OPTREL_def]
    >> qpat_assum ‘state_ref_rel f s.refs s'.refs’
         (strip_assume_tac o REWRITE_RULE [state_ref_rel_def])
    >> first_x_assum drule >> strip_tac >> gvs [ref_rel_cases]
    >> ‘n < LENGTH ys’ by (imp_res_tac LIST_REL_LENGTH >> gvs [])
    >> ‘v_rel f (EL n xs) (EL n ys)’ by gvs [LIST_REL_EL_EQN]
    >> qexists ‘f’ >> simp [only_fresh_refl, holes_unchanged_except_refl]
    >> qpat_x_assum ‘v_rel f (EL n xs) _’ mp_tac
    >> simp [Once v_rel_cases])
  (* SetGlobal *)
  >> gvs [do_app_def, do_app_aux_def, AllCaseEqs (), v_rel_cases]
  >> ‘OPTREL (λp p'. FLOOKUP f p = SOME p') s.global s'.global’ by gvs [state_rel_def]
  >> ‘state_ref_rel f s.refs s'.refs’ by gvs [state_rel_def]
  >> ‘fmap_inj f’ by gvs [state_rel_def]
  >> gvs [OPTREL_def]
  >> qpat_assum ‘state_ref_rel f s.refs s'.refs’
       (strip_assume_tac o REWRITE_RULE [state_ref_rel_def])
  >> first_x_assum drule >> strip_tac >> gvs [ref_rel_cases]
  >> rename1 ‘LIST_REL (v_rel f) xs ws’
  >> ‘n < LENGTH ws’ by (imp_res_tac LIST_REL_LENGTH >> gvs [])
  >> qexists ‘f’ >> simp [only_fresh_refl]
  >> rpt conj_tac
  >> (
    (gvs [state_rel_def] >> irule state_ref_rel_update >> simp [ref_rel_cases]
     >> irule EVERY2_LUPDATE_same >> simp [Once v_rel_cases] >> gvs [])
    ORELSE
    (irule holes_unchanged_except_frange_update >> first_assum $ irule_at Any)
    ORELSE
    simp [bvlSemTheory.Unit_def])
QED

(*
val memop_create_tac =
  simp [bvl_to_bvi_refs]
  >> ‘state_ref_rel f s.refs s'.refs’ by gvs [state_rel_def]
  >> qmatch_goalsub_abbrev_tac ‘s.refs⟨_ ↦ rv⟩’
  >> qmatch_goalsub_abbrev_tac ‘s'.refs⟨_ ↦ rw⟩’
  >> drule state_rel_alloc
  >> disch_then $ qspecl_then
       [‘LEAST ptr. ptr ∉ FDOM s.refs’, ‘LEAST ptr. ptr ∉ FDOM s'.refs’,
        ‘rv’, ‘rw’] mp_tac
  >> impl_tac
  >- (simp [fresh_ptr_fresh]
      >> conj_tac >- (irule fresh_not_in_range_f >> first_assum $ irule_at Any)
      >> ‘f ⊑ f⟨(LEAST ptr. ptr ∉ FDOM s.refs) ↦ (LEAST ptr. ptr ∉ FDOM s'.refs)⟩’
           by (simp [SUBMAP_FUPDATE_FLOOKUP, FLOOKUP_DEF]
               >> gvs [state_ref_rel_def, fresh_ptr_fresh])
      >> irule ref_rel_submap
      >> first_assum $ irule_at Any
      >> unabbrev_all_tac >> simp [ref_rel_cases]
      >> TRY (simp [LIST_REL_REPLICATE_same] >> rw [] >> simp [Once v_rel_cases]))
  >> strip_tac
  >> qexists ‘f⟨(LEAST ptr. ptr ∉ FDOM s.refs) ↦ (LEAST ptr. ptr ∉ FDOM s'.refs)⟩’
  >> gvs [];

val memop_read_tac =
  qexists ‘f’
  >> ‘state_ref_rel f s.refs s'.refs’ by gvs [state_rel_def]
  >> drule_all state_ref_rel_lookup >> strip_tac
  >> gvs [ref_rel_cases, bvl_to_bvi_id, only_fresh_refl, holes_unchanged_except_refl]
  >> imp_res_tac LIST_REL_LENGTH >> gvs []
  >> simp [Once v_rel_cases, bvlSemTheory.Boolv_def];

val memop_el_tac =
  qexists ‘f’
  >> ‘state_ref_rel f s.refs s'.refs’ by gvs [state_rel_def]
  >> TRY (drule_all state_ref_rel_lookup >> strip_tac >> gvs [ref_rel_cases])
  >> gvs [bvl_to_bvi_id, only_fresh_refl, holes_unchanged_except_refl, LIST_REL_EL_EQN]
  >> qpat_x_assum ‘∀n. n < _ ⇒ v_rel _ _ _’ (qspec_then ‘Num i''’ mp_tac)
  >> (impl_tac >- (gvs [] >> intLib.ARITH_TAC))
  >> simp [Once v_rel_cases];

val memop_update_tac =
  qexists ‘f’
  >> ‘state_ref_rel f s.refs s'.refs’ by gvs [state_rel_def]
  >> ‘fmap_inj f’ by gvs [state_rel_def]
  >> imp_res_tac state_ref_rel_lookup
  >> gvs [ref_rel_cases]
  >> imp_res_tac LIST_REL_LENGTH
  >> simp [bvl_to_bvi_refs, only_fresh_refl, bvlSemTheory.Unit_def]
  >> rpt conj_tac
  >> TRY (irule holes_unchanged_except_frange_update >> first_assum $ irule_at Any >> NO_TAC)
  >> TRY intLib.ARITH_TAC
  >> gvs [state_rel_def]
  >> TRY (irule state_ref_rel_update >> simp [ref_rel_cases])
  >> TRY (irule EVERY2_LUPDATE_same)
  >> simp [Once v_rel_cases]
  >> gvs [];

val memop_finalise_tac =
  qexists ‘f’
  >> simp [only_fresh_refl, holes_unchanged_except_refl]
  >> ‘state_ref_rel f s.refs s'.refs’ by gvs [state_rel_def]
  >> gvs [bviSemTheory.finalise_cons_def, AllCaseEqs ()]
  >> imp_res_tac state_ref_rel_lookup
  >> gvs [ref_rel_cases, bviSemTheory.finalise_cons_def]
  >> simp [Once v_rel_cases];

val memop_mutblock_tac =
  ‘state_ref_rel f s.refs s'.refs’ by gvs [state_rel_def]
  >> drule_all no_mutblock >> simp [];

val memop_configgc_tac =
  qexists ‘f’
  >> gvs [bvl_to_bvi_id, only_fresh_refl, holes_unchanged_except_refl,
          bvlSemTheory.Unit_def];
*)

Resume do_app_op_rel[MemOp]:
  Cases_on ‘m’
  >> gvs [do_app_def, do_app_aux_def, AllCaseEqs (), bvlSemTheory.do_app_def,
          no_mutcons_op_def, v_rel_cases]
  >> cheat
QED

Resume do_app_op_rel[ThunkOp]:
  Cases_on ‘t’
  >> gvs [do_app_def, do_app_aux_def, bvlSemTheory.do_app_def, AllCaseEqs ()]
  >~ [‘Thunk NotEvaluated’] >-
   (* UpdateThunk *)
   (qpat_x_assum ‘v_rel f (RefPtr _ _) _’ mp_tac
    >> simp [Once v_rel_cases] >> strip_tac
    >> ‘state_ref_rel f s.refs s'.refs’ by gvs [state_rel_def]
    >> ‘fmap_inj f’ by gvs [state_rel_def]
    >> qpat_assum ‘state_ref_rel f s.refs s'.refs’
         (strip_assume_tac o REWRITE_RULE [state_ref_rel_def])
    >> first_x_assum drule >> strip_tac
    >> gvs [ref_rel_cases]
    >> simp [bvl_to_bvi_refs] >> qexists ‘f’
    >> simp [only_fresh_refl, bvlSemTheory.Unit_def]
    >> rpt conj_tac
    >- simp [Once v_rel_cases]
    >- (gvs [state_rel_def] >> irule state_ref_rel_update >> simp [ref_rel_cases])
    >> gvs [holes_unchanged_except_def, FLOOKUP_SIMP]
    >> rw [] >> gvs [IN_FRANGE_FLOOKUP] >> metis_tac [])
  (* AllocThunk *)
  >> qmatch_goalsub_rename_tac ‘Thunk mode v'’
  >> simp [bvl_to_bvi_refs]
  >> qexists ‘f⟨(LEAST ptr. ptr ∉ FDOM s.refs) ↦ (LEAST ptr. ptr ∉ FDOM s'.refs)⟩’
  >> ‘state_ref_rel f s.refs s'.refs’ by gvs [state_rel_def]
  >> ‘(LEAST ptr. ptr ∉ FDOM s'.refs) ∉ FRANGE f’
       by (irule fresh_not_in_range_f >> first_assum $ irule_at Any)
  >> drule state_rel_alloc
  >> disch_then $ qspecl_then
       [‘LEAST ptr. ptr ∉ FDOM s.refs’, ‘LEAST ptr. ptr ∉ FDOM s'.refs’,
        ‘Thunk mode v'’, ‘Thunk mode y’] mp_tac
  >> impl_tac
  >- (simp [fresh_ptr_fresh, ref_rel_cases]
      >> irule v_rel_submap >> first_assum $ irule_at Any
      >> simp [SUBMAP_FUPDATE_FLOOKUP, FLOOKUP_DEF]
      >> gvs [state_ref_rel_def, fresh_ptr_fresh])
  >> strip_tac >> simp [Once v_rel_cases]
QED

Resume do_app_op_rel[FFI]:
  gvs [do_app_def, do_app_aux_def, bvlSemTheory.do_app_def, AllCaseEqs (), v_rel_cases]
  >> ‘state_ref_rel f s.refs s'.refs’ by gvs [state_rel_def]
  >> ‘s'.ffi = s.ffi’ by gvs [state_rel_def]
  >> fs [state_ref_rel_def]
  >> res_tac
  >> gvs [ref_rel_cases]
  >> qexists ‘f’
  >> ‘fmap_inj f’ by gvs [state_rel_def]
  >> simp [bvl_to_bvi_def, bvi_to_bvl_def, only_fresh_refl, bvlSemTheory.Unit_def]
  >> conj_tac
  >- (‘state_ref_rel f s.refs s'.refs’ by gvs [state_rel_def]
      >> gvs [state_rel_def]
      >> irule state_ref_rel_update
      >> simp [ref_rel_cases]
      >> first_assum $ irule_at Any)
  >> gvs [holes_unchanged_except_def, FLOOKUP_SIMP]
  >> rw [] >> gvs [IN_FRANGE_FLOOKUP]
  >> metis_tac []
QED

Resume do_app_op_rel[BlockOp]:
  cheat
QED

Resume do_app_op_rel[Install]:
  cheat
QED

Finalise do_app_op_rel;

Theorem do_app_op_err_rel:
  do_app (FFI i) vs u = Rerr (Rabort (Rffi_error e)) ∧
  state_rel f u u' ∧
  LIST_REL (v_rel f) vs vs' ⇒
  do_app (FFI i) vs' u' = Rerr (Rabort (Rffi_error e))
Proof
  rw []
  >> gvs [do_app_def, do_app_aux_def, bvlSemTheory.do_app_def, v_rel_cases,
          CaseEq "option", CaseEq "prod", CaseEq "result", CaseEq "list", CaseEq "v", CaseEq "ref"]
  >> ‘state_ref_rel f u.refs u'.refs’ by gvs [state_rel_def]
  >> imp_res_tac state_ref_rel_def
  >> gvs [ref_rel_cases]
  >> IF_CASES_TAC
  >- gvs []
  >> gvs []
  >> reverse IF_CASES_TAC
  >- gvs []
  >> gvs [CaseEq "ffi_result", ffiTheory.call_FFI_def]
  >> reverse IF_CASES_TAC
  >- gvs []
  >> gvs []
  >> ‘u.ffi = u'.ffi’ by gvs [state_rel_def]
  >> gvs [CaseEq "oracle_result"]
QED

Theorem wrapper_strip_if_then:
  rewrite_wrapper loc loc_opt n (If x1 x2 x3) = SOME w ⇒
  ∃w2 w3.
    w = If x1 w2 w3 ∧
    (rewrite_wrapper loc loc_opt n x2 = SOME w2 ∨
     w2 = x2)
Proof
  rw []
  >> gvs [rewrite_wrapper_def]
  >> Cases_on ‘rewrite_wrapper loc loc_opt n x2’
  >> Cases_on ‘rewrite_wrapper loc loc_opt n x3’
  >> gvs []
QED

Theorem wrapper_strip_if_else:
  rewrite_wrapper loc loc_opt n (If x1 x2 x3) = SOME w ⇒
  ∃w2 w3.
    w = If x1 w2 w3 ∧
    (rewrite_wrapper loc loc_opt n x3 = SOME w3 ∨
     w3 = x3)
Proof
  rw []
  >> gvs [rewrite_wrapper_def]
  >> Cases_on ‘rewrite_wrapper loc loc_opt n x2’
  >> Cases_on ‘rewrite_wrapper loc loc_opt n x3’
  >> gvs []
QED

Theorem wrapper_strip_let:
  ∀n loc loc_opt xs x w.
    rewrite_wrapper loc loc_opt n (Let xs x) = SOME w ⇒
    ∃w'.
      w = Let xs w' ∧
      rewrite_wrapper loc loc_opt (n + LENGTH xs) x = SOME w'
Proof
  rw []
  >> gvs [rewrite_wrapper_def, CaseEq "option"]
QED

Theorem wrapper_strip_tick:
  ∀n loc loc_opt x w.
    rewrite_wrapper loc loc_opt n (Tick x) = SOME w ⇒
    ∃w'.
      w = Tick w' ∧
      rewrite_wrapper loc loc_opt n x = SOME w'
Proof
  rw [] >> gvs [rewrite_wrapper_def]
QED

Definition is_block_op_cons_def:
  is_block_op_cons op ⇔
    ∃block_tag.
      op = BlockOp (Cons block_tag)
End

(*
  This was copied from bvlPropsScript but I don't see it for bviPropsScript.
  Consider putting it there.
  Look for it elsewhere.
*)
Theorem evaluate_refs_SUBSET:
  (evaluate (xs,env,s) = (res,t)) ==> FDOM s.refs SUBSET FDOM t.refs
Proof
  cheat
QED

Theorem list_rel_reverse:
  ∀r l1 l2. LIST_REL r l1 l2 ⇔ LIST_REL r (REVERSE l1) (REVERSE l2)
Proof
  rw []
QED

Theorem list_rel_last:
  ∀r l1 l2.
    LIST_REL r l1 l2 ∧
    l1 ≠ [] ⇒
    r (LAST l1) (LAST l2)
Proof
  rw []
  >> Cases_on ‘l1’ using SNOC_CASES >> gvs []
  >> Cases_on ‘l2’ using SNOC_CASES >> gvs []
  >> gvs [LIST_REL_SNOC]
QED

Theorem list_rel_front:
  ∀r l1 l2.
    LIST_REL r l1 l2 ⇒
    LIST_REL r (FRONT l1) (FRONT l2)
Proof
  rw []
  >> Cases_on ‘l1’ using SNOC_CASES >> gvs []
  >> Cases_on ‘l2’ using SNOC_CASES >> gvs []
  >> gvs [LIST_REL_SNOC]
QED

Theorem list_rel_env_rel:
  ∀f env1 env2.
    LIST_REL (v_rel f) env1 env2 ⇒
    env_rel F f env1 env2
Proof
  rw [LIST_REL_def, env_rel_def]
  >> qexistsl [‘env2’, ‘[]’]
  >> gvs []
QED

Theorem evaluate_fill_hole:
  ∀exp f f' env1 env2 s t s' t' r r' c.
    evaluate ([exp],env1,s) = (r,t) ∧
    evaluate ([exp],env2,s') = (r',t') ∧
    env_rel T f env1 env2 ∧
    state_rel f s s' ∧
    f ⊑ f' ∧
    result_rel (LIST_REL (v_rel f')) (v_rel f') r r' ∧
    hole_has_val f env1 env2 s'.refs c ∧
    holes_unchanged_except f s'.refs t'.refs ∅ ∧
    only_fresh f f' s'.refs ∧
    state_rel f' t t' ∧
    env2❲LENGTH env1❳ = RefPtr F hole_ptr ⇒
    ∃r_fill f_fill t_fill.
      evaluate ([fill_hole (LENGTH env1) (LENGTH env1 + 1) exp],env2,s') = (r_fill,t_fill) ∧
      opt_res_rel f_fill r r_fill ∧
      state_rel f_fill t t_fill ∧
      f SUBMAP f_fill ∧
      only_fresh f f_fill s'.refs ∧
      holes_unchanged_except f s'.refs t_fill.refs {hole_ptr} ∧
      ∀v.
        r = Rval [v] ⇒
        ∃v_fill.
          mb_rel f_fill (t_fill.refs \\ hole_ptr) v v_fill ∧
          hole_has_val f env1 env2 t_fill.refs v_fill
Proof
  rw []
  >> imp_res_tac env_rel_length_opt
  >> imp_res_tac env_rel_extras_opt
  >> imp_res_tac hole_has_val_def
  >> imp_res_tac holes_unchanged_except_def
  >> simp [evaluate_def, fill_hole_def, do_app_def, do_app_aux_def,
           case_eq_thms, PULL_EXISTS, FLOOKUP_SIMP, bvlSemTheory.Unit_def, backend_commonTheory.tuple_tag_def]
  >> gvs []
  >> reverse $ Cases_on ‘r’
  >-
   (gvs []
    >> first_assum $ irule_at Any
    >> gvs [opt_res_rel_def]
    >> irule holes_unchanged_except_subset
    >> first_assum $ irule_at Any
    >> gvs [])
  >> gvs []
  >> imp_res_tac evaluate_SING_IMP
  >> gvs []
  >> first_x_assum $ drule_all
  >> strip_tac
  >> first_x_assum drule
  >> disch_then drule
  >> impl_tac
  >- gvs []
  >> strip_tac
  >> gvs []
  >> qexists ‘f'’
  >> gvs [opt_res_rel_def, GSYM PULL_EXISTS]
  >> conj_tac
  >-
   (irule state_rel_filled
    >> gvs []
    >> irule non_fresh_not_in_frange
    >> rpt $ first_assum $ irule_at Any
    >> gvs [FLOOKUP_DEF])
  >> conj_tac
  >-
   (irule holes_unchanged_except_filled
    >> rpt $ first_assum $ irule_at Any)
  >> gvs [hole_has_val_def, FLOOKUP_SIMP]
  >> Cases_on ‘w'’ >> gvs [mb_rel_def]
  >> Cases_on ‘w’ >> gvs [mb_rel_def, v_rel_cases]
QED

Theorem evaluate_fill_hole_val:
  ∀exp f f' env1 env2 s t s' t' v v' c.
    evaluate ([exp],env1,s) = (Rval [v],t) ∧
    evaluate ([exp],env2,s') = (Rval [v'],t') ∧
    env_rel T f env1 env2 ∧
    state_rel f s s' ∧
    f ⊑ f' ∧
    v_rel f' v v' ∧
    hole_has_val f env1 env2 s'.refs c ∧
    holes_unchanged_except f s'.refs t'.refs ∅ ∧
    only_fresh f f' s'.refs ∧
    state_rel f' t t' ∧
    env2❲LENGTH env1❳ = RefPtr F hole_ptr ⇒
    ∃r_fill f_fill t_fill.
      evaluate ([fill_hole (LENGTH env1) (LENGTH env1 + 1) exp],env2,s') = (r_fill,t_fill) ∧
      opt_res_rel f_fill (Rval [v]) r_fill ∧
      state_rel f_fill t t_fill ∧
      f SUBMAP f_fill ∧
      only_fresh f f_fill s'.refs ∧
      holes_unchanged_except f s'.refs t_fill.refs {hole_ptr} ∧
      ∃v_fill.
        mb_rel f_fill (t_fill.refs \\ hole_ptr) v v_fill ∧
        hole_has_val f env1 env2 t_fill.refs v_fill
Proof
  rw []
  >> drule evaluate_fill_hole
  >> rpt $ disch_then drule
  >> gvs []
  >> disch_then drule
  >> strip_tac
  >> rpt $ first_assum $ irule_at Any
QED

Theorem evaluate_vars_source:
  ∀vs env (s : (num # γ, 'ffi) state).
    wf_vars (LENGTH env) vs ⇒
    evaluate (MAP (λn. Var n) vs,env,s) = (Rval (MAP (λn. env❲n❳) vs),s)
Proof
  Induct
  >- gvs [evaluate_def]
  >> rw []
  >> gvs [wf_vars_def, evaluate_def, Once evaluate_CONS]
QED

Theorem evaluate_vars_target:
  ∀vs n env (s : (γ, 'ffi) state).
    wf_vars n vs ∧
    LENGTH env >= n ⇒
    evaluate (MAP (λn. Var n) vs,env,s) = (Rval (MAP (λn. env❲n❳) vs),s)
Proof
  Induct
  >- gvs [evaluate_def]
  >> rw []
  >> gvs [wf_vars_def, evaluate_def, Once evaluate_CONS]
  >> first_x_assum drule_all
  >> strip_tac
  >> gvs []
QED

Theorem evaluate_vars_expand_env:
  ∀vs env s v extras.
    evaluate (MAP (λn. Var n) vs,env,s) = (Rval v,s) ⇒
    evaluate (MAP (λn. Var n) vs,env ++ extras,s) = (Rval v,s)
Proof
  Induct
  >- rw [evaluate_def]
  >> rw []
  >> gvs [Once evaluate_CONS, evaluate_def]
  >> simp [Once evaluate_CONS, evaluate_def]
  >> reverse $ Cases_on ‘h < LENGTH env’
  >- gvs [CaseEq "prod", CaseEq "result"]
  >> gvs [CaseEq "prod", CaseEq "result", EL_APPEND_EQN]
QED

Theorem evaluate_var_list:
  ∀ns env s t r.
    evaluate (MAP (λn. Var n) ns,env,s) = (r,t) ∧
    r ≠ Rerr (Rabort Rtype_error) ⇒
    (r,t) = (Rval (MAP (λn. env❲n❳) ns),s)
Proof
  Induct_on ‘ns’
  >- gvs [evaluate_def]
  >> rpt gen_tac
  >> strip_tac
  >> gvs [Once evaluate_CONS, evaluate_def]
  >> Cases_on ‘h < LENGTH env’ >> gvs []
  >> gvs [CaseEq "prod"]
  >> first_x_assum drule
  >> strip_tac
  >> Cases_on ‘v3’ >> gvs []
QED

Theorem evaluate_var_list_binders:
  ∀ns extras env s r t.
    evaluate (MAP (λn. Var n) ns,env,s) = (r,t) ∧
    r ≠ Rerr (Rabort Rtype_error) ⇒
    evaluate (MAP (λn. Var (n + LENGTH extras)) ns,extras ++ env,s) = (r,t)
Proof
  Induct_on ‘ns’
  >- gvs [evaluate_def]
  >> rw []
  >> gvs [evaluate_CONS, evaluate_def]
  >> reverse IF_CASES_TAC >> gvs []
  >> gvs [CaseEq "prod", CaseEq "result", EL_APPEND_EQN]
QED

Theorem evaluate_binders:
  ∀args env s t vs as next next'.
    evaluate (args,env,s) = (Rval as,t) ∧
    bind next args = (vs,next') ⇒
    ∀ys.
      LENGTH ys = next ⇒
      evaluate (MAP (λn. Var n) vs,ys ++ as,t) = (Rval as,t)
Proof
  Induct
  >- gvs [evaluate_def, bind_def]
  >> rw []
  >> gvs [bind_def, CaseEq "prod"]
  >> first_x_assum $ drule_at Any
  >> gvs [Once evaluate_CONS, evaluate_def]
  >> gvs [CaseEq "prod", CaseEq "result"]
  >> disch_then drule
  >> imp_res_tac evaluate_SING_IMP >> gvs []
  >> disch_then $ qspec_then ‘ys ++ [w]’ mp_tac
  >> gvs []
  >> strip_tac
  >> simp [Once evaluate_CONS, evaluate_def]
  >> gvs [CaseEq "prod", CaseEq "result"]
  >> gvs [EL_APPEND_EQN]
  >> ‘ys ++ [w] ++ vs = ys ++ w::vs’ by gvs []
  >> gvs []
QED

Theorem evaluate_shift_vars:
  ∀vs env s bs.
    evaluate (MAP (λn. Var n) (shift_vars (LENGTH bs) vs),bs ++ env,s) =
    evaluate (MAP (λn. Var n) vs,env,s)
Proof
  Induct
  >- gvs [evaluate_def, shift_vars_def]
  >> rw []
  >> gvs [Once evaluate_CONS, evaluate_def]
  >> reverse IF_CASES_TAC
  >- (gvs [Once evaluate_CONS, evaluate_def, shift_vars_def])
  >> CASE_TAC
  >> CASE_TAC
  >> Cases_on ‘q' = Rerr (Rabort Rtype_error)’
  >- gvs [Once evaluate_CONS, evaluate_def, shift_vars_def]
  >> drule evaluate_var_list
  >> impl_tac >- gvs []
  >> strip_tac
  >> gvs []
  >> first_x_assum $ qspecl_then [‘env’, ‘r’, ‘bs’] assume_tac
  >> gvs [shift_vars_def, Once evaluate_CONS, evaluate_def, EL_APPEND_EQN]
QED

Theorem evaluate_shift_vars_sing:
  ∀vs env s b.
    evaluate (MAP (λn. Var n) (shift_vars 1 vs),b::env,s) =
    evaluate (MAP (λn. Var n) vs,env,s)
Proof
  rw []
  >> qspecl_then [‘vs’, ‘env’, ‘s’, ‘[b]’] assume_tac evaluate_shift_vars
  >> gvs []
QED

Theorem evaluate_shift_cb:
  ∀cb loc env s bs.
    evaluate ([cb_to_bvi loc (shift_cb (LENGTH bs) cb)],bs ++ env,s) = evaluate ([cb_to_bvi loc cb],env,s)
Proof
  reverse Induct
  >-
   (rpt gen_tac
    >> gvs [shift_cb_def, cb_to_bvi_def, evaluate_def]
    >> CASE_TAC
    >> rw []
    >> gvs [evaluate_shift_vars])
  >> rw []
  >> gvs [shift_cb_def, cb_to_bvi_def, evaluate_def]
  >> gvs [evaluate_APPEND, evaluate_def]
  >> gvs [evaluate_shift_vars]
  >> CASE_TAC >> gvs []
  >> Cases_on ‘q’ >> gvs []
  >> Cases_on ‘evaluate ([cb_to_bvi loc cb],env,r')’
  >> first_x_assum drule
  >> disch_then $ qspec_then ‘bs’ mp_tac
  >> strip_tac >> gvs []
QED

Theorem evaluate_shift_cb_sing:
  ∀cb loc env s b.
    evaluate ([cb_to_bvi loc (shift_cb 1 cb)],b::env,s) = evaluate ([cb_to_bvi loc cb],env,s)
Proof
  rw []
  >> qspecl_then [‘cb’, ‘loc’, ‘env’, ‘s’, ‘[b]’] mp_tac evaluate_shift_cb
  >> strip_tac
  >> gvs []
QED

Theorem evaluate_pure_exps:
  ∀n xs.
    pure_exps n xs ⇒
    ∀env.
      n ≤ LENGTH env ⇒
      ∃v.
        ∀s.
          evaluate (xs,env,s) = (Rval v,s)
Proof
  recInduct pure_exps_ind
  >> rw []
  >> gvs [pure_exps_def, evaluate_def]
  >-
   (last_x_assum drule
    >> strip_tac
    >> gvs [])
  >-
   (last_x_assum drule
    >> strip_tac
    >> gvs []
    >> Cases_on ‘op’ >> gvs [pure_op_def, do_app_def, do_app_aux_def]
    >- (* IntOp *)
     (Cases_on ‘i’ >> Cases_on ‘args’ >> gvs [pure_op_def, evaluate_def])
    (* BlockOp *)
    >> Cases_on ‘b’ >> gvs [pure_op_def, do_app_def, do_app_aux_def, bvl_to_bvi_id])
  >> last_x_assum drule
  >> strip_tac
  >> gvs []
  >> first_x_assum drule
  >> strip_tac
  >> gvs []
QED

Theorem evaluate_bvi_to_cb_aux_inl:
  ∀n loc tag args bs vs.
    bvi_to_cb_aux n loc tag args = SOME (bs,INL vs) ⇒
    bs = args ∧
    ∀env.
      n ≤ LENGTH env ⇒
      ∃v.
        ∀s.
          evaluate (args,env,s) = (Rval v,s) ∧
          evaluate (MAP (λn. Var n) vs,v,s) = (Rval v,s)
Proof
  recInduct bvi_to_cb_aux_ind >> rw [bvi_to_cb_aux_def, call_to_cb_def] >> gvs [evaluate_def]
  >- gvs [CaseEq "prod", CaseEq "option", CaseEq "sum"]
  >- gvs [CaseEq "prod", CaseEq "option", CaseEq "sum"]
  >- gvs [CaseEq "option", CaseEq "prod", CaseEq "sum", evaluate_def]
  >-
   (imp_res_tac evaluate_pure_exps
    >> qexists ‘v’
    >> gen_tac
    >> first_x_assum $ qspec_then ‘s’ assume_tac
    >> gvs [CaseEq "option", CaseEq "prod", CaseEq "sum", CaseEq "result", evaluate_def])
  >- gvs [CaseEq "option", CaseEq "prod", CaseEq "sum"]
  >- gvs [CaseEq "option", CaseEq "prod", CaseEq "sum"]
  >- (gvs [pure_exps_def] >> qexists ‘[env❲v30❳]’ >> gvs [])
  >- gvs [pure_exps_def]
  >-
   (gvs [pure_exps_def]
    >> imp_res_tac evaluate_pure_exps
    >> pop_assum kall_tac
    >> gvs []
    >> ‘n ≤ LENGTH (v ++ env)’ by gvs []
    >> imp_res_tac evaluate_pure_exps
    >> pop_assum kall_tac
    >> gvs []
    >> qexists ‘v'³'’
    >> gen_tac
    >> gvs []
    >> pop_assum $ qspec_then ‘s’ assume_tac
    >> imp_res_tac evaluate_SING_IMP
    >> gvs [])
  >- gvs [pure_exps_def]
  >- gvs [pure_exps_def]
  >- gvs [pure_exps_def]
  >-
   (gvs [CaseEq "option"]
    >> gvs [CaseEq "prod"]
    >> reverse $ gvs [CaseEq "sum"]
    >- (Cases_on ‘cb’ >> gvs [shift_cb_def])
    >> gvs [CaseEq "option"]
    >> gvs [CaseEq "prod"]
    >> gvs [CaseEq "sum"]
    >> gvs [CaseEq "call_block"]
    >> gvs [CaseEq "list"])
  >> gvs [CaseEq "option"]
  >> gvs [CaseEq "prod"]
  >> reverse $ gvs [CaseEq "sum"]
  >- (Cases_on ‘cb’ >> gvs [shift_cb_def])
  >> gvs [CaseEq "option"]
  >> gvs [CaseEq "prod"]
  >> gvs [CaseEq "sum"]
  >> gvs [CaseEq "call_block"]
  >> gvs [CaseEq "list"]
  >> last_x_assum drule
  >> strip_tac
  >> gvs []
  >> first_x_assum drule
  >> strip_tac
  >> qexists ‘v ++ v'’
  >> gen_tac
  >> rpt $ first_x_assum $ qspec_then ‘s’ assume_tac
  >> gvs []
  >> imp_res_tac evaluate_SING_IMP
  >> gvs [evaluate_APPEND, evaluate_shift_vars_sing]
  >> imp_res_tac evaluate_vars_expand_env
  >> pop_assum $ qspec_then ‘v'’ mp_tac
  >> strip_tac
  >> gvs [APPEND]
QED

Theorem evaluate_bvi_to_cb_aux_inr:
  ∀n loc tag args env s t r bs cb.
    bvi_to_cb_aux n loc tag args = SOME (bs,INR cb) ∧
    evaluate ([Op (BlockOp (Cons tag)) args],env,s) = (r,t) ∧
    n ≤ LENGTH env ⇒
    ∃as u.
      evaluate (bs,env,s) = (as,u) ∧
      (∀vs.
         as = Rval vs ⇒
         evaluate ([cb_to_bvi loc cb],vs,u) = (r,t) ∧
         ∀extras.
           evaluate ([cb_to_bvi loc cb],vs ++ extras,u) = (r,t)) ∧
      (∀e.
         as = Rerr e ⇒
         (as,u) = (r,t))
Proof
  recInduct bvi_to_cb_aux_ind
  >> rw []
  >> imp_res_tac bvi_to_cb_aux_wf_inr
  >> gvs []
  >- gvs [bvi_to_cb_aux_def]
  >- (* call *)
   (gvs [bvi_to_cb_aux_def, call_to_cb_def, CaseEq "prod", CaseEq "option"]
    >> rename [‘bind 0 args = (vs,n')’]
    >> gvs [evaluate_def, cb_to_bvi_def, evaluate_def]
    >> gvs [CaseEq "prod"]
    >> Cases_on ‘v5'’ >> gvs []
    >> drule evaluate_binders
    >> disch_then drule
    >> disch_then $ qspec_then ‘[]’ mp_tac
    >> strip_tac
    >> gvs []
    >> rw []
    >> drule evaluate_vars_expand_env
    >> disch_then $ qspec_then ‘extras’ mp_tac
    >> strip_tac
    >> gvs [])
  >- (* op *)
   (gvs [bvi_to_cb_aux_def, evaluate_def, cb_to_bvi_def, CaseEq "option"]
    >> Cases_on ‘op’ >> gvs [dest_Cons_def]
    >> Cases_on ‘b’ >> gvs [dest_Cons_def]
    >> gvs [CaseEq "prod", CaseEq "sum", PULL_EXISTS]
    >> first_x_assum drule
    >> gvs []
    >> strip_tac
    >> first_assum $ irule_at Any
    >> conj_tac
    >-
     (rw []
      >> gvs [cb_to_bvi_def, evaluate_def])
    >> rw []
    >- gvs [CaseEq "result", CaseEq "error_result"]
    >> gvs [CaseEq "result", CaseEq "error_result"])
  >- gvs [bvi_to_cb_aux_def]
  >- gvs [bvi_to_cb_aux_def]
  >- gvs [bvi_to_cb_aux_def]
  >- gvs [bvi_to_cb_aux_def]
  >- gvs [bvi_to_cb_aux_def]
  >- gvs [bvi_to_cb_aux_def]
  (* Cons *)
  >> rename [‘CallBlock _ left child right’, ‘evaluate ([Op _ (x1::x2::xs)],_,_) = _’]
  >> gvs [bvi_to_cb_aux_def, CaseEq "prod", CaseEq "option", CaseEq "sum", CaseEq "call_block", CaseEq "list"]
  >- (* INL *)
   (first_x_assum $ qspecl_then [‘env’, ‘s’] mp_tac
    >> gvs [evaluate_def, CaseEq "prod"]
    >> CASE_TAC >> gvs []
    >-
     (gvs [CaseEq "call_block", CaseEq "list"]
      >> gvs [do_app_def, do_app_aux_def]
      >> gvs [CaseEq "prod"]
      >> strip_tac
      >> gvs [evaluate_APPEND]
      >> Cases_on ‘as’ >> gvs []
      >> imp_res_tac evaluate_bvi_to_cb_aux_inl
      >> gvs []
      >> gvs [cb_to_bvi_def, evaluate_def]
      >> simp [Once evaluate_CONS, evaluate_def]
      >> first_assum $ qspec_then ‘v’ mp_tac
      >> strip_tac
      >> gvs [CaseEq "prod", CaseEq "result", do_app_def, do_app_aux_def, bvl_to_bvi_id]
      >> gvs [PULL_EXISTS]
      >> gvs [GSYM PULL_FORALL]
      >> first_assum $ qspec_then ‘s'’ mp_tac
      >> strip_tac
      >> imp_res_tac evaluate_IMP_LENGTH
      >> gvs [evaluate_shift_vars]
      >> gen_tac
      >> imp_res_tac evaluate_SING_IMP
      >> gvs []
      >> simp [Once evaluate_CONS]
      >> first_x_assum $ qspec_then ‘v ++ extras’ mp_tac
      >> strip_tac
      >> gvs []
      >> qspecl_then [‘vs2’, ‘v ++ extras’, ‘s'’, ‘a'’] mp_tac evaluate_shift_vars
      >> strip_tac
      >> gvs []
      >> first_x_assum $ qspec_then ‘s'’ mp_tac
      >> strip_tac
      >> drule evaluate_vars_expand_env
      >> disch_then $ qspec_then ‘extras’ mp_tac
      >> strip_tac
      >> gvs [])
    >> strip_tac
    >> gvs [CaseEq "call_block", CaseEq "list"]
    >> gvs [evaluate_APPEND]
    >> Cases_on ‘as’ >> gvs []
    >> imp_res_tac evaluate_bvi_to_cb_aux_inl
    >> gvs []
    >> gvs [cb_to_bvi_def, evaluate_def]
    >> simp [Once evaluate_CONS, evaluate_def]
    >> gvs [CaseEq "prod"]
    >> first_assum $ qspec_then ‘v’ mp_tac
    >> strip_tac
    >> gvs [CaseEq "prod", CaseEq "result", do_app_def, do_app_aux_def, bvl_to_bvi_id]
    >> rw []
    >> simp [Once evaluate_CONS]
    >> first_assum $ qspec_then ‘v ++ extras’ mp_tac
    >> strip_tac
    >> fs [])
  (* INR *)
  >> Cases_on ‘cb’ >> gvs [shift_cb_def]
  >> rename [‘CallBlock tag (0::shift_vars 1 left) (shift_cb 1 child) (shift_vars 1 right)’]
  >> simp [Once evaluate_CONS]
  >> gvs [evaluate_def, CaseEq "prod"]
  >> Cases_on ‘v4’ >> gvs []
  >> gvs [CaseEq "prod"]
  >> gvs [PULL_EXISTS]
  >> first_x_assum drule
  >> CASE_TAC >> gvs []
  >-
   (gvs [do_app_def, do_app_aux_def]
    >> strip_tac
    >> gvs []
    >> CASE_TAC >> gvs []
    >> gvs [cb_to_bvi_def, evaluate_def]
    >> simp [Once evaluate_CONS, evaluate_def]
    >> gvs [evaluate_APPEND]
    >> gvs [evaluate_shift_vars_sing]
    >> CASE_TAC
    >> gvs [CaseEq "prod", CaseEq "result", evaluate_shift_cb_sing]
    >> gvs [do_app_def, do_app_aux_def]
    >> rw []
    >> simp [Once evaluate_CONS, evaluate_def, evaluate_APPEND]
    >> imp_res_tac evaluate_SING_IMP
    >> gvs [bvl_to_bvi_id, evaluate_shift_vars_sing]
    >> first_assum $ qspec_then ‘extras’ mp_tac
    >> strip_tac
    >> gvs [evaluate_shift_cb_sing])
  >> strip_tac
  >> gvs []
  >> reverse CASE_TAC >> gvs []
  >> gvs [cb_to_bvi_def, evaluate_def]
  >> simp [Once evaluate_CONS, evaluate_def]
  >> gvs [evaluate_APPEND, evaluate_def]
  >> gvs [evaluate_shift_vars_sing]
  >> gvs [CaseEq "prod", evaluate_shift_cb_sing]
  >> conj_tac
  >- gvs [CaseEq "prod", CaseEq "result", do_app_def, do_app_aux_def]
  >> rw []
  >> simp [Once evaluate_CONS, evaluate_def, evaluate_APPEND, evaluate_shift_vars_sing]
  >> first_assum $ qspec_then ‘extras’ mp_tac
  >> strip_tac
  >> gvs [CaseEq "prod", CaseEq "result", do_app_def, do_app_aux_def, evaluate_shift_cb_sing]
QED

Theorem evaluate_bvi_to_cb:
  ∀cb n loc x env s t r bs.
    evaluate ([x],env,s) = (r,t) ∧
    bvi_to_cb n loc x = SOME (bs,cb) ∧
    n ≤ LENGTH env ⇒
    evaluate ([Let bs (cb_to_bvi loc cb)],env,s) = (r,t)
Proof
  rw []
  >> Cases_on ‘x’ >> gvs [bvi_to_cb_def, call_to_cb_def, CaseEq "option", CaseEq "prod", CaseEq "sum", CaseEq "exp"]
  >-
   (gvs [evaluate_def, bvi_to_cb_def, cb_to_bvi_def, CaseEq "prod"]
    >> gvs [CaseEq "result"]
    >> drule_then drule evaluate_binders
    >> disch_then $ qspec_then ‘[]’ mp_tac
    >> impl_tac >- gvs []
    >> strip_tac
    >> gvs []
    >> drule evaluate_vars_expand_env
    >> disch_then $ qspec_then ‘env’ mp_tac
    >> strip_tac
    >> gvs [])
  >> rename [‘Op op args’]
  >> Cases_on ‘op’ >> gvs [dest_Cons_def]
  >> Cases_on ‘b’ >> gvs [dest_Cons_def]
  >> drule_all evaluate_bvi_to_cb_aux_inr
  >> strip_tac
  >> simp [evaluate_def]
  >> CASE_TAC >> gvs []
QED

Theorem WF_I_I[local]:
  WF (measure I LEX measure I)
Proof
  irule WF_LEX >> simp [prim_recTheory.WF_measure]
QED

Definition optimised_code_def:
  optimised_code loc loc_opt c1 c2 ⇔
    ∃arity body body_wrap body_work.
      lookup loc c1 = SOME (arity,body) ∧
      lookup loc c2 = SOME (arity,body_wrap) ∧
      lookup loc_opt c2 = SOME (arity + 2,body_work) ∧
      rewrite_wrapper loc loc_opt arity body = SOME body_wrap ∧
      rewrite_worker loc loc_opt arity (arity + 1) arity body = body_work
End

Theorem evaluate_rewrite_tmc:
  ∀n xs ^s env1 r t opt f s' env2 loc.
    evaluate (xs,env1,s) = (r,t) ∧
    n = (s.clock, list_size exp_size xs) ∧
    env_rel opt f env1 env2 ∧ EVERY (λx. no_mutcons x) xs ∧
    state_rel f s s' ∧
    (opt ⇒ LENGTH xs = 1) ∧
    r ≠ Rerr (Rabort Rtype_error) ⇒
    ∃t' f' r'.
      evaluate (xs,env2,s') = (r',t') ∧
      result_rel (LIST_REL (v_rel f')) (v_rel f') r r' ∧
      state_rel f' t t' ∧
      f SUBMAP f' ∧
      only_fresh f f' s'.refs ∧
      holes_unchanged_except f s'.refs t'.refs ∅ ∧
      (∀loc_opt.
         optimised_code loc loc_opt s.code s'.code ⇒
         (∀wrap.
            LENGTH xs = 1 ∧
            rewrite_wrapper loc loc_opt (LENGTH env1) (HD xs) = SOME wrap ⇒
            ∃t_wrap f_wrap r_wrap.
              evaluate ([wrap], env2, s') = (r_wrap,t_wrap) ∧
              result_rel (LIST_REL (v_rel f_wrap)) (v_rel f_wrap) r r_wrap ∧
              state_rel f_wrap t t_wrap ∧
              f SUBMAP f_wrap ∧
              only_fresh f f_wrap s'.refs ∧
              holes_unchanged_except f s'.refs t_wrap.refs ∅) ∧
         (opt ⇒
          (∀i j hole_ptr work.
             i = LENGTH env1 ∧
             j = LENGTH env1 + 1 ∧
             (∃c. hole_has_val f env1 env2 s'.refs c) ∧
             rewrite_worker loc loc_opt i j (LENGTH env1) (HD xs) = work ∧
             env2❲i❳ = RefPtr F hole_ptr ⇒
             ∃r_work f_work t_work.
               evaluate ([work], env2, s') = (r_work,t_work) ∧
               opt_res_rel f_work r r_work ∧
               state_rel f_work t t_work ∧
               f SUBMAP f_work ∧
               only_fresh f f_work s'.refs ∧
               holes_unchanged_except f s'.refs t_work.refs {hole_ptr} ∧
               ∀res_v.
                 r = Rval [res_v] ⇒
                 ∃res_v'.
                   mb_rel f_work (t_work.refs \\ hole_ptr) res_v res_v' ∧
                   hole_has_val f env1 env2 t_work.refs res_v')))
Proof
  ho_match_mp_tac $ MATCH_MP WF_INDUCTION_THM WF_I_I
  >> simp [FORALL_PROD]
  >> rpt gen_tac >> disch_tac
  >> rpt gen_tac >> disch_tac
  >> gvs [LEX_DEF,PULL_FORALL]
  >> ‘∀n0 n1 b. n1 < n0 ∨ n1 = n0 ∧ b ⇔ n1 < n0 ∨ n1 ≤ n0:num ∧ b’ by
    (rw [] >> eq_tac >> rw [] >> fs [])
  >> pop_assum $ fs o single
  (* -- at this point the indfuction is set up -- *)
  >> Cases_on ‘xs’
  >~ [‘evaluate ([],_,_)’] >-
   (gvs [evaluate_def] >> first_x_assum $ irule_at Any >> fs [only_fresh_def, holes_unchanged_except_def])
  >> reverse $ Cases_on ‘t'’
  >~ [‘evaluate (x::y::xs,_,_)’] >- suspend "list"
  >> reverse $ Cases_on ‘bvi_to_cb (LENGTH env1) loc h’
  >-
   (Cases_on ‘x’
    >> gvs []
    >> rename [‘bvi_to_cb _ _ x = SOME (bs,cb)’]
    >> suspend "call_block")
  >> Cases_on ‘h’
  >~ [‘Var n’] >- suspend "var"
  >~ [‘If x1 x2 x3’] >- suspend "if"
  >~ [‘Let xs x2’] >- suspend "lett"
  >~ [‘Raise x’] >- suspend "raise"
  >~ [‘Op op xs’] >- suspend "op_non_opt"
  >~ [‘Tick x’] >- suspend "tick"
  >~ [‘Force force_loc n’] >- suspend "force"
  >~ [‘Call ticks dest xs handler’] >- suspend "call_non_opt"
QED

Resume evaluate_rewrite_tmc[op_non_opt]:
  gvs [evaluate_def]
  >> gvs [CaseEq "prod", PULL_EXISTS]
  >> rename [‘evaluate (xs,env,s) = (rs,u)’]
  >> first_assum $ qspecl_then [‘xs’, ‘s’, ‘env’] mp_tac
  >> impl_tac >- gvs []
  >> disch_then drule
  >> drule_all env_rel_relax_opt
  >> strip_tac
  >> rpt $ disch_then drule
  >> impl_tac >- gvs [CaseEq "prod", CaseEq "result"]
  >> disch_then $ qspec_then ‘loc’ mp_tac
  >> strip_tac
  >> gvs [GSYM PULL_FORALL]
  >> rename [‘evaluate (xs,env2,s') = (rs',u')’]
  >> reverse $ Cases_on ‘rs’ >> gvs []
  >- (* Error evaluating args *)
   (rename [‘evaluate (xs,env2,s') = (Rerr e',t')’]
    >> qexists‘f''’
    >> gvs []
    >> strip_tac >> gvs []
    >> rw []
    >- gvs [rewrite_wrapper_def]
    >> gvs [rewrite_worker_def]
    >> gvs [evaluate_def, fill_hole_def, opt_res_rel_def]
    >> rpt $ first_assum $ irule_at Any
    >> irule holes_unchanged_except_subset
    >> first_assum $ irule_at Any
    >> gvs [])
  >> rename [‘LIST_REL (v_rel f'') vs vs'’]
  >> reverse $ Cases_on ‘do_app op (REVERSE vs) u’ >> gvs []
  >- (* FFI *)
   (qrefinel [‘_’, ‘f''’, ‘_’]
    >> drule do_app_err
    >> strip_tac >> gvs []
    >> rename [‘do_app (FFI i) (REVERSE vs) u = Rerr (Rabort (Rffi_error e))’]
    >> drule do_app_op_err_rel
    >> disch_then $ qspecl_then [‘REVERSE vs'’, ‘u'’, ‘f''’] mp_tac
    >> disch_then drule
    >> drule $ iffLR list_rel_reverse
    >> gvs []
    >> rw []
    >- gvs [rewrite_wrapper_def]
    >> gvs [rewrite_worker_def, evaluate_def, fill_hole_def, opt_res_rel_def]
    >> rpt $ first_assum $ irule_at Any
    >> irule holes_unchanged_except_subset
    >> first_assum $ irule_at Any
    >> gvs [])
  >> rename [‘do_app _ (REVERSE vs) u = Rval v’]
  >> gvs [CaseEq "prod"]
  >> rename [‘do_app op _ _ = Rval (v,r)’]
  >> drule $ iffLR list_rel_reverse
  >> strip_tac
  >> drule_all do_app_op_rel
  >> strip_tac
  >> gvs []
  >> first_assum $ irule_at Any
  >> gvs []
  >> conj_asm1_tac
  >- imp_res_tac SUBMAP_TRANS
  >> conj_asm1_tac
  >-
   (irule only_fresh_trans
    >> rpt $ first_assum $ irule_at Any
    >> imp_res_tac evaluate_refs_SUBSET)
  >> conj_asm1_tac
  >- imp_res_tac holes_unchanged_except_trans
  >> rw []
  >- gvs [rewrite_wrapper_def]
  >> gvs [rewrite_worker_def]
  >> ho_match_mp_tac evaluate_fill_hole_val
  >> rpt $ first_assum $ irule_at Any
  >> gvs [evaluate_def]
QED

Definition hypothesis_def:
  hypothesis xs' (s'' : (num # γ, 'ffi) bviSem$state) clock ⇔
  s''.clock < clock ⇒
  ∀env1' r' t' opt' f' s'³' env2' loc'.
            evaluate (xs',env1',s'') = (r',t') ∧
            env_rel opt' f' env1' env2' ∧ EVERY (λx. no_mutcons x) xs' ∧
            state_rel f' s'' s'³' ∧
            (opt' ⇒ LENGTH xs' = 1) ∧
            r' ≠ Rerr (Rabort Rtype_error) ⇒
            ∃t'' f'' r''.
              evaluate (xs',env2',s'³') = (r'',t'') ∧
              result_rel (LIST_REL (v_rel f'')) (v_rel f'') r' r'' ∧
              state_rel f'' t' t'' ∧ f' ⊑ f'' ∧ only_fresh f' f'' s'³'.refs ∧
              holes_unchanged_except f' s'³'.refs t''.refs ∅ ∧
              ∀loc_opt.
                optimised_code loc' loc_opt s''.code s'³'.code ⇒
                (∀wrap.
                   LENGTH xs' = 1 ∧
                   rewrite_wrapper loc' loc_opt (LENGTH env1') (HD xs') = SOME wrap ⇒
                   ∃t_wrap f_wrap r_wrap.
                     evaluate ([wrap],env2',s'³') = (r_wrap,t_wrap) ∧
                     result_rel (LIST_REL (v_rel f_wrap)) (v_rel f_wrap) r'
                       r_wrap ∧ state_rel f_wrap t' t_wrap ∧ f' ⊑ f_wrap ∧
                     only_fresh f' f_wrap s'³'.refs ∧
                     holes_unchanged_except f' s'³'.refs t_wrap.refs ∅) ∧
                (opt' ⇒
                 ∀hole_ptr.
                   (∃c. hole_has_val f' env1' env2' s'³'.refs c) ∧
                   env2'❲LENGTH env1'❳ = RefPtr F hole_ptr ⇒
                   ∃r_work f_work t_work.
                     evaluate
                       ([rewrite_worker loc' loc_opt (LENGTH env1')
                           (LENGTH env1' + 1) (LENGTH env1') (HD xs')],env2',s'³') =
                     (r_work,t_work) ∧ opt_res_rel f_work r' r_work ∧
                     state_rel f_work t' t_work ∧ f' ⊑ f_work ∧
                     only_fresh f' f_work s'³'.refs ∧
                     holes_unchanged_except f' s'³'.refs t_work.refs
                       {hole_ptr} ∧
                     ∀res_v.
                       r' = Rval [res_v] ⇒
                       ∃res_v'.
                         mb_rel f_work (t_work.refs \\ hole_ptr) res_v res_v' ∧
                         hole_has_val f' env1' env2' t_work.refs res_v')
End

Definition alloc_hole_has_val_def:
  alloc_hole_has_val f refs extras i_ptr c_idx c ⇔
    ∃hole_ptr tag left right.
      i_ptr < LENGTH extras ∧
      extras❲i_ptr❳ = RefPtr F hole_ptr ∧
      c_idx = LENGTH left ∧
      backend_common$small_enough_int (&LENGTH left) ∧
      hole_ptr ∉ FRANGE f ∧
      FLOOKUP refs hole_ptr = SOME (MutBlock tag left c right)
End

Theorem wf_vars_list_rel:
  ∀vars opt f env1 env2.
    env_rel opt f env1 env2 ∧
    wf_vars (LENGTH env1) vars ⇒
    LIST_REL (v_rel f) (MAP (λn. EL n env1) vars) (MAP (λn. EL n env2) vars)
Proof
  Induct
  >- rw []
  >> rw []
  >- gvs [wf_vars_def, env_rel_def, EL_APPEND_EQN, LIST_REL_EL_EQN]
  >> first_x_assum $ irule
  >> first_assum $ irule_at Any
  >> gvs [wf_vars_def]
QED

Theorem wf_vars_env_rel:
  ∀vars opt f env1 env2.
    env_rel opt f env1 env2 ∧
    wf_vars (LENGTH env1) vars ⇒
    env_rel F f (MAP (λn. env1❲n❳) vars) (MAP (λn. env2❲n❳) vars)
Proof
  rw []
  >> imp_res_tac wf_vars_list_rel
  >> gvs [env_rel_def]
  >> first_assum $ irule_at Any
  >> imp_res_tac LIST_REL_LENGTH
  >> gvs [EL_APPEND_EQN]
QED

Theorem wf_vars_env_rel_opt:
  ∀vars opt f env1 env2 ptr idx.
    env_rel opt f env1 env2 ∧
    wf_vars (LENGTH env1) vars ∧
    backend_common$small_enough_int idx ⇒
    env_rel T f (MAP (λn. env1❲n❳) vars) (MAP (λn. env2❲n❳) vars ++ [RefPtr F ptr; Number idx])
Proof
  rw []
  >> imp_res_tac wf_vars_env_rel
  >> simp [env_rel_def]
  >> qexistsl [‘MAP (λn. env2❲n❳) vars’, ‘[RefPtr F ptr; Number idx]’]
  >> gvs []
  >> irule wf_vars_list_rel
  >> rpt $ first_assum $ irule_at Any
QED

Theorem state_ref_rel_sub:
  ∀ptr f s_refs t_refs.
    ptr ∉ FRANGE f ∧
    state_ref_rel f s_refs t_refs ⇒
    state_ref_rel f s_refs (t_refs \\ ptr)
Proof
  rw []
  >> gvs [state_ref_rel_def]
  >> rw []
  >> first_x_assum drule
  >> strip_tac
  >> gvs []
  >> first_assum $ irule_at Any
  >> gvs [DOMSUB_FLOOKUP_THM]
  >> spose_not_then assume_tac
  >> gvs []
  >> ‘j ∈ FRANGE f’ by gvs [FRANGE_FLOOKUP]
QED

Theorem evaluate_finalise_cons:
  ∀v2 t_refs f s_refs v1.
    state_ref_rel f s_refs t_refs ∧
    mb_rel f t_refs v1 v2 ⇒
    ∃v3.
      finalise_cons v2 t_refs = SOME v3 ∧
      v_rel f v1 v3
Proof
  recInduct finalise_cons_ind
  >> rw []
  >~ [‘RefPtr _ _’] >-
   (reverse $ Cases_on ‘v1’ >> gvs [mb_rel_def, v_rel_cases, finalise_cons_def]
    >-
     (CASE_TAC
      >-
       (gvs [state_ref_rel_def]
        >> ‘n ∈ FDOM s_refs’ by gvs [FLOOKUP_DEF]
        >> Cases_on ‘FLOOKUP s_refs n’
        >- gvs [FLOOKUP_DEF]
        >> first_x_assum drule
        >> strip_tac
        >> gvs [])
      >> CASE_TAC
      >> gvs [state_ref_rel_def]
      >> Cases_on ‘FLOOKUP s_refs n’
      >- gvs [FLOOKUP_DEF]
      >> last_x_assum drule
      >> strip_tac
      >> gvs [ref_rel_cases, v_rel_cases])
    >> drule_all state_ref_rel_sub
    >> strip_tac
    >> CASE_TAC
    >-
     (first_x_assum drule_all
      >> strip_tac
      >> gvs [])
    >> irule LIST_REL_APPEND_suff
    >> gvs []
    >> first_x_assum drule_all
    >> strip_tac >> gvs [v_rel_cases])
  >~ [‘Number i’] >-
   (Cases_on ‘v1’ >> gvs [mb_rel_def, v_rel_cases, finalise_cons_def])
  >~ [‘Word64 w’] >-
   (Cases_on ‘v1’ >> gvs [mb_rel_def, v_rel_cases, finalise_cons_def])
  >~ [‘Block xs ys’] >-
   (Cases_on ‘v1’ >> gvs [mb_rel_def, v_rel_cases, finalise_cons_def])
  >~ [‘CodePtr p’] >-
   (Cases_on ‘v1’ >> gvs [mb_rel_def, v_rel_cases, finalise_cons_def])
QED

Theorem code_rel_cases:
  ∀loc arity body1 c1 c2.
    lookup loc c1 = SOME (arity,body1) ∧
    code_rel c1 c2 ⇒
    no_mutcons body1 ∧
    ∃loc_opt body2.
      lookup loc c2 = SOME (arity,body2) ∧
      (body1 ≠ body2 ⇒
       optimised_code loc loc_opt c1 c2 ∧
       rewrite_wrapper loc loc_opt arity body1 = SOME body2)
Proof
  rw []
  >> gvs [code_rel_def]
  >> first_x_assum drule
  >> strip_tac
  >> Cases_on ‘compile_exp loc n arity body1’
  >- gvs []
  >> gvs []
  >> Cases_on ‘x’
  >> gvs []
  >> qexists ‘n’
  >> strip_tac
  >> gvs [optimised_code_def, compile_exp_def, CaseEq "option"]
QED

Theorem cons_append:
  ∀v l.
    v::l = [v] ++ l
Proof
  rw []
QED

Theorem rw_block_args:
  ∀left child right f.
    REVERSE (MAP f left ++ [child] ++ MAP f right) = MAP f (REVERSE right) ++ [child] ++ MAP f (REVERSE left)
Proof
  rw []
  >> gvs [GSYM MAP_REVERSE, REVERSE_APPEND]
QED

Theorem shift_cb_suc:
  ∀n cb.
    shift_cb (SUC (SUC n)) cb = shift_cb (n + 2) cb
Proof
  rw []
  >> ‘SUC (SUC n) = n + 2’ by gvs []
  >> simp []
QED

Theorem evaluate_cb:
  ∀cb loc f opt env env2 ^s s' t r clock.
    evaluate ([cb_to_bvi loc cb],env,s) = (r,t) ∧
    wf_cb (LENGTH env) cb ∧
    env_rel opt f env env2 ∧
    state_rel f s s' ∧
    s.clock ≤ clock ∧
    r ≠ Rerr (Rabort Rtype_error) ∧
    (∀xs' (s'' :(num # γ, 'ffi) state).
       hypothesis xs' s'' clock) ⇒
    (∃r' t' f'.
       evaluate ([cb_to_bvi loc cb],env2,s') = (r',t') ∧
       result_rel (LIST_REL (v_rel f')) (v_rel f') r r' ∧
       state_rel f' t t' ∧
       f ⊑ f' ∧
       only_fresh f f' s'.refs ∧
       holes_unchanged_except f s'.refs t'.refs ∅) ∧
    ∀loc_opt.
      optimised_code loc loc_opt s.code s'.code ⇒
      (∀tag left child right.
         cb = CallBlock tag left child right ⇒
         ∃t_wrap f_wrap r_wrap.
           evaluate ([cb_to_bvi_wrapper tag left child right loc_opt], env2, s') = (r_wrap,t_wrap) ∧
           result_rel (LIST_REL (v_rel f_wrap)) (v_rel f_wrap) r r_wrap ∧
           state_rel f_wrap t t_wrap ∧
           f SUBMAP f_wrap ∧
           only_fresh f f_wrap s'.refs ∧
           holes_unchanged_except f s'.refs t_wrap.refs ∅) ∧
      (∀refs extras ptr idx hole_ptr.
         state_ref_rel f s.refs refs ∧
         (∃c. alloc_hole_has_val f refs extras ptr idx c) ∧
         EL ptr extras = RefPtr F hole_ptr ⇒
         ∃r_aux t_aux f_aux.
           evaluate ([cb_to_bvi_worker_aux (shift_cb (LENGTH extras) cb) loc_opt ptr idx],extras ++ env2,s' with refs := refs) = (r_aux,t_aux) ∧
           opt_res_rel f_aux r r_aux ∧
           state_rel f_aux t t_aux ∧
           f ⊑ f_aux ∧
           only_fresh f f_aux refs ∧
           holes_unchanged_except f refs t_aux.refs {hole_ptr} ∧
           ∀res_v.
             r = Rval [res_v] ⇒
             ∃res_v'.
               mb_rel f_aux (t_aux.refs \\ hole_ptr) res_v res_v' ∧
               alloc_hole_has_val f t_aux.refs extras ptr idx res_v') ∧
      (opt ⇒
       (∀ptr idx work hole_ptr.
          ptr = LENGTH env ∧
          idx = LENGTH env + 1 ∧
          (∃c. hole_has_val f env env2 s'.refs c) ∧
          EL ptr env2 = RefPtr F hole_ptr ⇒
          ∃r_work f_work t_work.
            evaluate ([cb_to_bvi_worker cb loc_opt ptr idx], env2, s') = (r_work,t_work) ∧
            opt_res_rel f_work r r_work ∧
            state_rel f_work t t_work ∧
            f SUBMAP f_work ∧
            only_fresh f f_work s'.refs ∧
            holes_unchanged_except f s'.refs t_work.refs {hole_ptr} ∧
            ∀res_v.
              r = Rval [res_v] ⇒
              ∃res_v'.
                mb_rel f_work (t_work.refs \\ hole_ptr) res_v res_v' ∧
                hole_has_val f env env2 t_work.refs res_v'))
Proof
  reverse $ Induct
  >-
   (rpt gen_tac
    >> strip_tac
    >> rename [‘RCall ts args’]
    >> gvs [wf_cb_def, cb_to_bvi_def, evaluate_def, CaseEq "prod"]
    >> imp_res_tac evaluate_vars_source
    >> gvs []
    >> imp_res_tac env_rel_length
    >> imp_res_tac evaluate_vars_target
    >> gvs [bvlSemTheory.find_code_def, CaseEq "prod", CaseEq "option"]
    >> drule code_rel_cases
    >> ‘code_rel s.code s'.code’ by gvs [state_rel_def]
    >> disch_then drule
    >> strip_tac
    >> ‘s.clock = s'.clock’ by gvs [state_rel_def]
    >> gvs []
    >> Cases_on ‘s'.clock < ts + 1’
    >-
     (gvs [optimised_code_def]
      >> conj_tac
      >-
       (qexists ‘f’
        >> gvs [state_rel_def, only_fresh_refl, holes_unchanged_except_refl])
      >> rw []
      >-
       (gvs [cb_to_bvi_worker_aux_def, shift_cb_def, optimise_call_def, evaluate_def, evaluate_APPEND, evaluate_shift_vars]
        >> gvs [alloc_hole_has_val_def, do_app_def, do_app_aux_def]
        >> gvs [bvlSemTheory.find_code_def, EL_APPEND_EQN]
        >> qexists ‘f’
        >> gvs [state_rel_def, only_fresh_refl, holes_unchanged_except_refl, opt_res_rel_def])
      >> gvs [cb_to_bvi_worker_def, optimise_call_def, evaluate_def, evaluate_APPEND]
      >> imp_res_tac env_rel_length_opt
      >> gvs [bvlSemTheory.find_code_def, EL_APPEND_EQN]
      >> qexists ‘f’
      >> gvs [state_rel_def, only_fresh_refl, holes_unchanged_except_refl, opt_res_rel_def])
    >> gvs [CaseEq "prod"]
    >> ‘(v3,s'') = (r,t)’ by gvs [CaseEq "result", CaseEq "error_result"]
    >> rw []
    (* Untransformed *)
    >-
     (gvs [hypothesis_def]
      >> first_x_assum $ qspecl_then [‘[exp]’, ‘dec_clock (ts + 1) s’] mp_tac
      >> impl_tac >- gvs [dec_clock_def]
      >> imp_res_tac wf_vars_env_rel
      >> simp []
      >> rpt $ disch_then drule
      >> ‘state_rel f (dec_clock (ts + 1) s) (dec_clock (ts + 1) s')’ by
        (irule state_rel_dec
         >> Cases_on ‘s'.clock’
         >- gvs []
         >> gvs [])
      >> disch_then drule
      >> gvs [GSYM PULL_FORALL]
      >> disch_then $ qspec_then ‘loc’ mp_tac
      >> strip_tac
      >> rename [‘state_rel _ t _’]
      >> Cases_on ‘exp = body2’
      >-
       (gvs []
        >> rename [‘state_rel f' _ t'’]
        >> rename [‘result_rel _ _ _ r'’]
        >> qexistsl [‘r'’, ‘t'’, ‘f'’]
        >> conj_tac
        >-
         (gvs []
          >> CASE_TAC >> gvs []
          >> CASE_TAC >> gvs [])
        >> rpt $ first_assum $ irule_at Any)
      >> gvs []
      >> first_x_assum drule
      >> disch_then drule
      >> strip_tac
      >> gvs []
      >> qexistsl [‘r_wrap’, ‘t_wrap’, ‘f_wrap’]
      >> conj_tac
      >-
       (gvs []
        >> CASE_TAC >> gvs []
        >> CASE_TAC >> gvs [])
      >> rpt $ first_assum $ irule_at Any)
    (* Aux *)
    >-
     (qpat_x_assum ‘_ ≠ _ ⇒ _’ kall_tac
      >> rename [‘optimised_code _ loc_opt _ _’]
      >> gvs [shift_cb_def, cb_to_bvi_worker_def, cb_to_bvi_worker_aux_def, optimise_call_def, evaluate_def, evaluate_APPEND, evaluate_shift_vars]
      >> gvs [alloc_hole_has_val_def, do_app_def, do_app_aux_def]
      >> gvs [bvlSemTheory.find_code_def, EL_APPEND_EQN]
      >> gvs [hypothesis_def]
      >> first_x_assum $ qspecl_then [‘[exp]’, ‘dec_clock (ts + 1) s’] mp_tac
      >> impl_tac >- gvs [dec_clock_def]
      >> disch_then drule
      >> drule_then drule wf_vars_env_rel_opt
      >> disch_then $ qspecl_then [‘hole_ptr’, ‘&LENGTH left’] mp_tac
      >> impl_tac >- gvs []
      >> strip_tac
      >> disch_then drule
      >> disch_then $ qspecl_then [‘dec_clock (ts + 1) (s' with refs := refs)’, ‘loc’] mp_tac
      >> impl_tac
      >- gvs [state_rel_def, dec_clock_def]
      >> gvs [GSYM PULL_FORALL]
      >> strip_tac
      >> rename [‘state_rel f' t t'’, ‘result_rel _ _ _ r'’]
      >> CASE_TAC
      >- gvs [optimised_code_def]
      >> gvs []
      >> first_x_assum drule
      >> strip_tac
      >> gvs [optimised_code_def]
      >> pop_assum $ qspec_then ‘hole_ptr’ mp_tac
      >> impl_tac
      >-
       (gvs [hole_has_val_def]
        >> gvs [EL_APPEND_EQN, LENGTH_MAP])
      >> strip_tac
      >> gvs []
      >> qexistsl [‘r_work’, ‘t_work’, ‘f_work’]
      >> conj_tac
      >-
       (CASE_TAC >> gvs []
        >> CASE_TAC >> gvs [])
      >> conj_tac
      >- gvs [opt_res_rel_def]
      >> gvs []
      >> rw []
      >> gvs []
      >> first_assum $ irule_at Any
      >> gvs [hole_has_val_def, EL_APPEND_EQN, LENGTH_MAP])
    (* Work *)
    >> qpat_x_assum ‘_ ≠ _ ⇒ _’ kall_tac
    >> rename [‘optimised_code _ loc_opt _ _’]
    >> gvs [cb_to_bvi_worker_def, evaluate_def]
    >> gvs [optimise_call_def, evaluate_def, evaluate_APPEND]
    >> imp_res_tac env_rel_length_opt
    >> gvs [bvlSemTheory.find_code_def, EL_APPEND_EQN]
    >> gvs [hypothesis_def]
    >> first_x_assum $ qspecl_then [‘[exp]’, ‘dec_clock (ts + 1) s’] mp_tac
    >> impl_tac >- gvs [dec_clock_def]
    >> disch_then drule
    >> drule_then drule wf_vars_env_rel_opt
    >> imp_res_tac env_rel_strip_extras
    >> imp_res_tac env_rel_length_opt
    >> ‘hole_ptr = hole_ptr'’ by gvs [EL_APPEND_EQN]
    >> disch_then $ qspecl_then [‘hole_ptr’, ‘hole_idx’] mp_tac
    >> impl_tac >- gvs []
    >> strip_tac
    >> disch_then drule
    >> disch_then $ qspecl_then [‘dec_clock (ts + 1) s'’, ‘loc’] mp_tac
    >> impl_tac
    >-
     (gvs []
      >> gvs [state_rel_def, dec_clock_def])
    >> gvs [GSYM PULL_FORALL]
    >> strip_tac
    >> rename [‘state_rel f' t t'’, ‘result_rel _ _ _ r'’]
    >> first_x_assum drule
    >> gvs []
    >> strip_tac
    >> pop_assum $ qspec_then ‘hole_ptr’ mp_tac
    >> impl_tac
    >-
     (gvs [hole_has_val_def]
      >> gvs [EL_APPEND_EQN, LENGTH_MAP])
    >> strip_tac
    >> gvs []
    >> qexistsl [‘r_work’, ‘f_work’, ‘t_work’]
    >> ‘(env2' ++ [RefPtr F hole_ptr; Number hole_idx])❲LENGTH env❳ = RefPtr F hole_ptr’ by gvs [EL_APPEND_EQN]
    >> ‘(env2' ++ [RefPtr F hole_ptr; Number hole_idx])❲LENGTH env + 1❳ = Number hole_idx’ by gvs [EL_APPEND_EQN]
    >> gvs [optimised_code_def]
    >> conj_tac
    >-
     (CASE_TAC >> gvs []
      >> CASE_TAC >> gvs [])
    >> rw []
    >> gvs []
    >> first_assum $ irule_at Any
    >> gvs [hole_has_val_def, EL_APPEND_EQN, LENGTH_MAP])
  >> rpt gen_tac
  >> strip_tac
  >> rename [‘CallBlock tag left child right’]
  >> gvs [wf_cb_def, cb_to_bvi_def, evaluate_def, evaluate_APPEND, CaseEq "prod"]
  >> imp_res_tac evaluate_vars_source
  >> imp_res_tac env_rel_length
  >> imp_res_tac evaluate_vars_target
  >> gvs [CaseEq "prod"]
  >> last_x_assum drule
  >> rpt $ disch_then drule
  >> impl_tac >- gvs [CaseEq "prod", CaseEq "result"]
  >> strip_tac >> gvs []
  >> rename [‘state_rel f' u u'’, ‘result_rel _ _ r r'’]
  >> conj_tac
  >-
   (reverse $ Cases_on ‘r’
    >-
     (gvs [CaseEq "prod"]
      >> rename [‘state_rel f' u u'’]
      >> qexists ‘f'’
      >> gvs [only_fresh_refl])
    >> gvs [CaseEq "prod"]
    >> rename [‘state_rel f' u u'’]
    >> gvs [do_app_def, do_app_aux_def, bvl_to_bvi_id]
    >> first_assum $ irule_at Any
    >> imp_res_tac evaluate_SING_IMP
    >> gvs [REVERSE_APPEND]
    >> simp [Once v_rel_cases]
    >> irule LIST_REL_APPEND_suff
    >> irule_at Any LIST_REL_APPEND_suff
    >> simp [LIST_REL_REVERSE]
    >> imp_res_tac env_rel_submap
    >> imp_res_tac wf_vars_list_rel
    >> gvs [])
  >> rw []
  (* Wrap *)
  >-
   (first_x_assum drule
    >> strip_tac
    >> gvs [cb_to_bvi_wrapper_def, evaluate_def, mut_cons_def, evaluate_APPEND]
    >> gvs [do_app_def, do_app_aux_def, backend_commonTheory.small_enough_int_def]
    >> imp_res_tac env_rel_length
    >> drule_all evaluate_vars_source
    >> disch_then $ qspec_then ‘s2’ assume_tac
    >> drule_all evaluate_vars_target
    >> disch_then $ qspec_then ‘s'’ assume_tac
    >> gvs [LENGTH_MAP, REVERSE_APPEND, TAKE_APPEND, DROP_APPEND, GSYM MAP_REVERSE, GSYM MAP_TAKE, GSYM MAP_DROP, DROP_LENGTH_TOO_LONG]
    >> ‘TAKE (LENGTH right) (REVERSE right) = REVERSE right’ by gvs [LENGTH_REVERSE, TAKE_LENGTH_ID]
    >> simp []
    >> gvs [EL_APPEND_EQN, LENGTH_MAP, LENGTH_REVERSE]
    >> first_x_assum $ qspecl_then [‘s'.refs⟨
                                     (LEAST ptr. ptr ∉ FDOM s'.refs) ↦
                                     MutBlock tag (MAP (λn. env2❲n❳) (REVERSE right)) (Number 0) (MAP (λn. env2❲n❳) (REVERSE left))⟩’,
                                    ‘[RefPtr F (LEAST ptr. ptr ∉ FDOM s'.refs)]’, ‘0’, ‘LENGTH right’] mp_tac
    >> disch_then $ qspec_then ‘LEAST ptr. ptr ∉ FDOM s'.refs’ mp_tac
    >> impl_tac
    >-
     (conj_tac
      >-
       (irule state_ref_rel_filled
        >> gvs [state_rel_def]
        >> imp_res_tac fresh_not_in_range_f)
      >> gvs [alloc_hole_has_val_def, FLOOKUP_SIMP, backend_commonTheory.small_enough_int_def, state_rel_def]
      >> imp_res_tac fresh_not_in_range_f)
    >> strip_tac
    >> gvs []
    >> imp_res_tac evaluate_SING_IMP
    >> gvs []
    >> reverse $ Cases_on ‘r’
    >-
     (CASE_TAC >- gvs [opt_res_rel_def]
      >> gvs []
      >> rpt $ first_assum $ irule_at Any
      >> conj_tac
      >- gvs [opt_res_rel_def]
      >> conj_tac
      >-
       (irule only_fresh_del
        >> first_assum $ irule_at $ Pos $ el 2
        >> irule fresh_not_in_range_f
        >> gvs [state_rel_def]
        >> first_assum $ irule_at Any)
      >> irule holes_unchanged_except_del_SING
      >> first_assum $ irule_at $ Pos $ el 2
      >> irule_at Any fresh_ptr_fresh)
    >> reverse CASE_TAC >- gvs [opt_res_rel_def]
    >> gvs []
    >> imp_res_tac evaluate_SING_IMP
    >> gvs []
    >> rename [‘opt_res_rel _ (Rval [v]) (Rval [v'])’]
    >> gvs [bvi_tmcTheory.finalise_cons_def, evaluate_def]
    >> gvs [do_app_def, do_app_aux_def]
    >> gvs [alloc_hole_has_val_def]
    >> drule mb_rel_cons
    >> rpt $ disch_then $ drule_at Any
    >> disch_then $ qspecl_then [‘MAP (λn. env❲n❳) (REVERSE right)’, ‘MAP (λn. env❲n❳) (REVERSE left)’] mp_tac
    >> impl_tac
    >-
     (gvs [holes_unchanged_except_def, FLOOKUP_SIMP]
      >> drule_all env_rel_submap
      >> strip_tac
      >> imp_res_tac wf_vars_list_rel
      >> gvs [MAP_REVERSE]
      >> irule non_fresh_not_in_frange
      >> rpt $ first_assum $ irule_at Any
      >> gvs [FDOM_DEF])
    >> strip_tac
    >> rename [‘state_rel _ u t_aux’]
    >> ‘state_ref_rel f_aux u.refs t_aux.refs’ by gvs [state_rel_def]
    >> drule_all evaluate_finalise_cons
    >> strip_tac
    >> gvs []
    >> qexists ‘f_aux’
    >> gvs [bvl_to_bvi_id]
    >> conj_tac
    >- gvs [holes_unchanged_except_def, FLOOKUP_SIMP, REVERSE_APPEND, GSYM MAP_REVERSE, rw_block_args]
    >> conj_tac
    >-
     (irule only_fresh_del
      >> first_assum $ irule_at $ Pos $ el 2
      >> irule fresh_not_in_range_f
      >> gvs [state_rel_def]
      >> first_assum $ irule_at Any)
    >> irule holes_unchanged_except_del_SING
    >> first_assum $ irule_at $ Pos $ el 2
    >> irule_at Any fresh_ptr_fresh)
  (* Aux *)
  >-
   (first_x_assum drule
    >> strip_tac
    >> gvs [cb_to_bvi_worker_aux_def, evaluate_def, shift_cb_def]
    >> gvs [mut_cons_def, evaluate_def, evaluate_APPEND]
    >> gvs [evaluate_shift_vars]
    >> gvs [do_app_def, do_app_aux_def, backend_commonTheory.small_enough_int_def]
    >> imp_res_tac env_rel_length
    >> drule_all evaluate_vars_source
    >> disch_then $ qspec_then ‘s2’ assume_tac
    >> drule_all evaluate_vars_target
    >> disch_then $ qspec_then ‘s' with refs := refs’ assume_tac
    >> gvs [length_shift_vars]
    >> gvs [LENGTH_MAP, REVERSE_APPEND, TAKE_APPEND, DROP_APPEND, GSYM MAP_REVERSE, GSYM MAP_TAKE, GSYM MAP_DROP, DROP_LENGTH_TOO_LONG]
    >> gvs [update_cons_def, evaluate_def]
    >> gvs [do_app_def, do_app_aux_def]
    >> gvs [alloc_hole_has_val_def]
    >> Cases_on ‘ptr + 1’
    >- gvs []
    >> ‘n = ptr’ by gvs []
    >> gvs [FLOOKUP_SIMP, EL_APPEND_EQN]
    >> IF_CASES_TAC
    >-
     (qspec_then ‘refs’ mp_tac fresh_ptr_fresh
      >> strip_tac
      >> gvs [FDOM_DEF, FLOOKUP_DEF])
    >> gvs []
    >> first_x_assum $ qspecl_then [‘refs⟨
                                     hole_ptr ↦ MutBlock tag' left' (RefPtr F (LEAST ptr. ptr ∉ FDOM refs)) right';
                                     (LEAST ptr. ptr ∉ FDOM refs) ↦ MutBlock tag
                                                                  (MAP (λn. env2❲n❳) (TAKE (LENGTH right) (REVERSE right)))
                                                                  (Number 0)
                                                                  (MAP (λn. env2❲n❳) (REVERSE left))⟩’,
                                    ‘Unit::RefPtr F (LEAST ptr. ptr ∉ FDOM refs)::extras’, ‘1’, ‘LENGTH right’] mp_tac
    >> disch_then $ qspec_then ‘LEAST ptr. ptr ∉ FDOM refs’ mp_tac
    >> impl_tac
    >-
     (gvs []
      >> conj_tac
      >-
       (gvs [state_ref_rel_def]
        >> rw []
        >> first_x_assum drule
        >> strip_tac
        >> gvs []
        >> first_assum $ irule_at Any
        >> gvs [FLOOKUP_SIMP]
        >> IF_CASES_TAC
        >- gvs [IN_FRANGE_FLOOKUP]
        >> IF_CASES_TAC
        >-
         (gvs [IN_FRANGE_FLOOKUP]
          >> qspec_then ‘refs’ assume_tac fresh_ptr_fresh
          >> gvs [FLOOKUP_DEF])
        >> gvs [])
      >> qexistsl [‘Number 0’, ‘tag’, ‘(MAP (λn. env2❲n❳) (TAKE (LENGTH right) (REVERSE right)))’, ‘(MAP (λn. env2❲n❳) (REVERSE left))’]
      >> gvs [LENGTH_MAP, backend_commonTheory.small_enough_int_def]
      >> conj_tac
      >- imp_res_tac fresh_not_in_range_f
      >> gvs [FLOOKUP_SIMP])
    >> strip_tac
    >> reverse $ Cases_on ‘r’
    >-
     (gvs [shift_cb_dist, shift_cb_suc]
      >> rpt $ first_assum $ irule_at Any
    >> conj_tac
    >-
     (irule only_fresh_del
      >> irule_at Any only_fresh_del
      >> first_assum $ irule_at $ Pos hd
      >> imp_res_tac fresh_not_in_range_f
      >> gvs [])
      >> irule holes_unchanged_except_changed
      >> first_assum $ irule_at Any
      >> irule_at Any holes_unchanged_except_del_SING
      >> gvs [flookup_com_neq]
      >> first_assum $ irule_at Any
      >> qspec_then ‘refs’ assume_tac fresh_ptr_fresh
      >> gvs [])
    >> gvs []
    >> qexistsl [‘r_aux’, ‘t_aux’, ‘f_aux’]
    >> conj_tac
    >-
     (gvs [shift_cb_dist]
      >> ‘SUC (SUC (LENGTH extras)) = LENGTH extras + 2’ by gvs []
      >> gvs [])
    >> conj_tac
    >- gvs [opt_res_rel_def]
    >> conj_tac
    >- gvs [bvl_to_bvi_id]
    >> gvs []
    >> conj_tac
    >-
     (irule only_fresh_del
      >> irule_at Any only_fresh_del
      >> first_assum $ irule_at $ Pos hd
      >> imp_res_tac fresh_not_in_range_f
      >> gvs [])
    >> conj_tac
    >-
     (irule holes_unchanged_except_changed
      >> first_assum $ irule_at Any
      >> irule_at Any holes_unchanged_except_del_SING
      >> gvs [flookup_com_neq]
      >> first_assum $ irule_at Any
      >> qspec_then ‘refs’ assume_tac fresh_ptr_fresh
      >> gvs [])
    >> imp_res_tac evaluate_SING_IMP
    >> gvs [rw_block_args]
    >> irule_at Any mb_rel_cons
    >> drule mb_rel_del
    >> disch_then $ qspecl_then [‘hole_ptr’, ‘tag'’, ‘left'’, ‘LEAST ptr. ptr ∉ FDOM refs’, ‘right'’] mp_tac
    >> impl_tac
    >-
     (conj_tac
      >-
       (gvs [DOMSUB_FLOOKUP_THM]
        >> gvs [holes_unchanged_except_def]
        >> first_x_assum irule
        >> gvs [FLOOKUP_SIMP])
      >> gvs []
      >> irule non_fresh_not_in_frange
      >> rpt $ first_assum $ irule_at Any
      >> gvs [FLOOKUP_SIMP])
    >> strip_tac
    >> gvs [DOMSUB_COMMUTES]
    >> pop_assum $ irule_at Any
    >> gvs [DOMSUB_FLOOKUP_THM, holes_unchanged_except_def, FLOOKUP_SIMP]
    >> first_assum $ irule_at $ Pos last
    >> drule_all env_rel_submap
    >> strip_tac
    >> gvs []
    >> imp_res_tac wf_vars_list_rel
    >> ‘TAKE (LENGTH left'') (REVERSE right) = REVERSE right’ by gvs [LENGTH_REVERSE, TAKE_LENGTH_ID]
    >> gvs [MAP_REVERSE]
    >> irule non_fresh_not_in_frange
    >> rpt $ first_assum $ irule_at Any
    >> gvs [])
  (* Work *)
  >> first_x_assum drule
  >> strip_tac
  >> gvs [evaluate_def, cb_to_bvi_worker_def, mut_cons_def, evaluate_APPEND]
  >> gvs [do_app_def, do_app_aux_def, backend_commonTheory.small_enough_int_def]
  >> imp_res_tac env_rel_length
  >> drule_all evaluate_vars_source
  >> disch_then $ qspec_then ‘s2’ assume_tac
  >> drule_all evaluate_vars_target
  >> disch_then $ qspec_then ‘s'’ assume_tac
  >> gvs [LENGTH_MAP, REVERSE_APPEND, TAKE_APPEND, DROP_APPEND, GSYM MAP_REVERSE, GSYM MAP_TAKE, GSYM MAP_DROP, DROP_LENGTH_TOO_LONG]
  >> gvs [evaluate_def, update_cons_def]
  >> imp_res_tac env_rel_length_opt
  >> gvs []
  >> gvs [do_app_def, do_app_aux_def]
  >> imp_res_tac env_rel_strip_extras
  >> ‘LENGTH env + 1 = SUC (LENGTH env)’ by gvs []
  >> simp [EL_def, Once EL_APPEND_EQN]
  >> gvs []
  >> ‘LENGTH env + 2 = SUC (LENGTH env + 1)’ by gvs []
  >> simp [Once EL_def, Once EL_APPEND_EQN]
  >> gvs [FLOOKUP_SIMP]
  >> qspec_then ‘s'.refs’ mp_tac fresh_ptr_fresh
  >> strip_tac
  >> IF_CASES_TAC
  >- gvs [FDOM_DEF, FLOOKUP_DEF, hole_has_val_def, EL_APPEND_EQN]
  >> gvs [hole_has_val_def]
  >> ‘hole_ptr = hole_ptr'’ by gvs [EL_APPEND_EQN]
  >> ‘hole_idx = &LENGTH left'’ by gvs [EL_APPEND_EQN]
  >> ‘TAKE (LENGTH right) (REVERSE right) = REVERSE right’ by gvs [LENGTH_REVERSE, TAKE_LENGTH_ID]
  >> simp []
  >> first_x_assum $ qspecl_then [‘s'.refs⟨
                                   hole_ptr ↦ MutBlock tag' left' (RefPtr F (LEAST ptr. ptr ∉ FDOM s'.refs)) right';
                                   (LEAST ptr. ptr ∉ FDOM s'.refs) ↦ MutBlock tag
                                                                   (MAP (λn. (env2' ++ [RefPtr F hole_ptr; Number (&LENGTH left')])❲n❳) (REVERSE right))
                                                                   (MAP (λn. (env2' ++ [RefPtr F hole_ptr; Number (&LENGTH left')])❲n❳) (REVERSE right) ++
                                                                    Number 0::MAP (λn. (env2' ++ [RefPtr F hole_ptr; Number (&LENGTH left')])❲n❳) (REVERSE left))❲LENGTH right❳
                                                                   (MAP (λn. (env2' ++ [RefPtr F hole_ptr; Number (&LENGTH left')])❲n❳) (REVERSE left))⟩’,
                                  ‘[Unit; RefPtr F (LEAST ptr. ptr ∉ FDOM s'.refs)]’, ‘1’, ‘LENGTH right’] mp_tac
  >> disch_then $ qspec_then ‘LEAST ptr. ptr ∉ FDOM s'.refs’ mp_tac
  >> impl_tac
  >-
   (conj_tac
    >-
     (gvs [state_rel_def, state_ref_rel_def]
      >> rw []
      >> first_x_assum drule
      >> strip_tac
      >> gvs []
      >> first_assum $ irule_at Any
      >> gvs [FLOOKUP_SIMP]
      >> IF_CASES_TAC
      >- gvs [IN_FRANGE_FLOOKUP]
      >> IF_CASES_TAC
      >-
       (gvs [IN_FRANGE_FLOOKUP]
        >> qspec_then ‘s'.refs’ assume_tac fresh_ptr_fresh
        >> gvs [FLOOKUP_DEF])
      >> gvs [])
    >> gvs [alloc_hole_has_val_def, backend_commonTheory.small_enough_int_def]
    >> gvs [FLOOKUP_SIMP, LENGTH_MAP]
    >> irule fresh_not_in_range_f
    >> qexists ‘s.refs’
    >> gvs [state_rel_def])
  >> strip_tac
  >> gvs []
  >> reverse $ Cases_on ‘r’
  >-
   (gvs []
    >> rpt $ first_assum $ irule_at Any
    >> conj_tac
    >-
     (irule only_fresh_del
      >> irule_at Any only_fresh_del
      >> first_assum $ irule_at $ Pos hd
      >> gvs [state_rel_def]
      >> imp_res_tac fresh_not_in_range_f)
    >> irule holes_unchanged_except_changed
    >> first_assum $ irule_at Any
    >> irule_at Any holes_unchanged_except_del_SING
    >> gvs [flookup_com_neq]
    >> first_assum $ irule_at Any
    >> qspec_then ‘refs’ assume_tac fresh_ptr_fresh
    >> gvs [])
  >> qexists ‘f_aux’
  >> imp_res_tac evaluate_SING_IMP
  >> gvs []
  >> conj_tac
  >- gvs [opt_res_rel_def]
  >> conj_tac
  >- gvs [bvl_to_bvi_id]
  >> conj_tac
  >-
   (irule only_fresh_del
    >> irule_at Any only_fresh_del
    >> first_assum $ irule_at $ Pos hd
    >> gvs [state_rel_def]
    >> imp_res_tac fresh_not_in_range_f)
  >> conj_tac
  >-
   (irule holes_unchanged_except_changed
    >> first_assum $ irule_at Any
    >> irule_at Any holes_unchanged_except_del_SING
    >> gvs [flookup_com_neq]
    >> first_assum $ irule_at Any
    >> qspec_then ‘refs’ assume_tac fresh_ptr_fresh
    >> gvs [])
  >> imp_res_tac evaluate_SING_IMP
  >> gvs []
  >> gvs [alloc_hole_has_val_def]
  >> qexists ‘RefPtr F (LEAST ptr. ptr ∉ FDOM s'.refs)’
  >> conj_tac
  >-
   (gvs [rw_block_args]
    >> irule mb_rel_cons
    >> conj_tac
    >-
     (irule non_fresh_not_in_frange
      >> rpt $ first_assum $ irule_at Any
      >> gvs [FLOOKUP_SIMP, FDOM_DEF])
    >> gvs [FLOOKUP_SIMP, DOMSUB_FLOOKUP_THM, holes_unchanged_except_def]
    >> imp_res_tac env_rel_submap
    >> imp_res_tac wf_vars_list_rel
    >> gvs [MAP_REVERSE]
    >> drule mb_rel_del
    >> disch_then $ qspecl_then [‘hole_ptr’, ‘tag'’, ‘left'’, ‘LEAST ptr. ptr ∉ FDOM s'.refs’, ‘right'’] mp_tac
    >> impl_tac
    >-
     (conj_tac
      >-
       (gvs [DOMSUB_FLOOKUP_THM]
        >> gvs [holes_unchanged_except_def]
        >> first_x_assum irule
        >> gvs [FLOOKUP_SIMP])
      >> gvs []
      >> irule non_fresh_not_in_frange
      >> rpt $ first_assum $ irule_at Any
      >> gvs [FLOOKUP_SIMP])
    >> strip_tac
    >> gvs [DOMSUB_COMMUTES])
  >> gvs [holes_unchanged_except_def, backend_commonTheory.small_enough_int_def]
  >> first_x_assum $ irule_at Any
  >> gvs [FLOOKUP_SIMP]
QED

Theorem evaluate_pres_opt_code:
  ∀loc loc_opt s1 s2 xs env1 env2 r1 u1 r2 u2.
    optimised_code loc loc_opt s1.code s2.code ∧
    evaluate(xs,env1,s1) = (r1,u1) ∧
    evaluate(xs,env2,s2) = (r2,u2) ⇒
    optimised_code loc loc_opt u1.code u2.code
Proof
  rw []
  >> imp_res_tac evaluate_code_mono
  >> gvs [optimised_code_def]
  >> gvs [subspt_def]
  >> first_x_assum $ qspec_then ‘loc’ mp_tac
  >> impl_tac
  >- gvs [domain_lookup]
  >> strip_tac
  >> gvs []
  >> first_assum $ qspec_then ‘loc’ mp_tac
  >> impl_tac
  >- gvs [domain_lookup]
  >> strip_tac
  >> gvs []
  >> first_x_assum $ qspec_then ‘loc_opt’ mp_tac
  >> impl_tac
  >- gvs [domain_lookup]
  >> strip_tac
  >> gvs []
QED

Resume evaluate_rewrite_tmc[call_block]:
  (* Phase 1 theorem in s *)
  drule_then drule evaluate_bvi_to_cb
  >> impl_tac >- gvs []
  >> simp [Once evaluate_def]
  >> strip_tac
  >> gvs [CaseEq "prod"]
  >> rename [‘evaluate (bs,env,s) = (as,u)’]
  (* Hypothesis on bs *)
  >> first_assum $ qspecl_then [‘bs’, ‘s’] mp_tac
  >> impl_tac
  >- (imp_res_tac bvi_to_cb_size >> gvs [])
  >> imp_res_tac env_rel_relax_opt
  >> ‘EVERY (λx. no_mutcons x) bs’ by cheat
  >> rpt $ disch_then drule
  >> impl_tac
  >- (gvs [] >> spose_not_then assume_tac >> gvs [])
  >> gvs [GSYM PULL_FORALL]
  >> disch_then $ qspec_then ‘loc’ mp_tac
  >> strip_tac
  >> pop_assum kall_tac
  >> rename [‘evaluate (bs,env2,s') = (as',u')’]
  >> rename [‘f ⊑ f'’]
  (* Phase 1 theorem in s' *)
  >> Cases_on ‘evaluate ([x],env2,s')’
  >> rename [‘evaluate ([x],env2,s') = (r',t')’]
  >> drule_then drule evaluate_bvi_to_cb
  >> impl_tac >- (imp_res_tac env_rel_length >> gvs [])
  >> simp [Once evaluate_def]
  >> strip_tac
  >> reverse $ gvs [CaseEq "result"]
  >- (* bs fails *)
   (rename [‘exc_rel (v_rel f') e e'’]
    >> rpt $ first_assum $ irule_at Any
    >> rpt gen_tac
    >> strip_tac
    >> gvs [optimised_code_def]
    >> rw []
    >-
     (reverse $ imp_res_tac bvi_to_cb_cases
      >- gvs [rewrite_wrapper_def, bvi_to_cb_def]
      >> gvs [rewrite_wrapper_def, evaluate_def]
      >> rpt $ first_assum $ irule_at Any)
    >> reverse $ imp_res_tac bvi_to_cb_cases
    >-
     (gvs [rewrite_worker_def, evaluate_def, opt_res_rel_def]
      >> rpt $ first_assum $ irule_at Any
      >> irule holes_unchanged_except_subset
      >> first_assum $ irule_at Any
      >> gvs [])
    >> gvs [rewrite_worker_def, evaluate_def, opt_res_rel_def]
    >> rpt $ first_assum $ irule_at Any
    >> irule holes_unchanged_except_subset
    >> first_assum $ irule_at Any
    >> gvs [])
  (* Phase 2 theorem *)
  >> rename [‘LIST_REL (v_rel f') vs vs'’]
  >> qpat_x_assum ‘env_rel _ _ _ _’ kall_tac
  >> drule evaluate_cb
  >> drule_all env_rel_submap
  >> strip_tac
  >> drule_all env_rel_append
  >> strip_tac
  >> ntac 2 $ disch_then $ drule_at Any
  >> disch_then $ qspec_then ‘s.clock’ mp_tac
  >> impl_tac

  >-
   (irule_at Any wf_cb_expand
    >> imp_res_tac bvi_to_cb_wf
    >> first_assum $ irule_at Any
    >> imp_res_tac evaluate_IMP_LENGTH
    >> imp_res_tac evaluate_clock
    >> gvs [LENGTH_APPEND]
    >> gvs [hypothesis_def, LENGTH_APPEND])
  >> strip_tac
  >> gvs []
  >> rpt $ first_assum $ irule_at Any
  >> conj_tac
  >- imp_res_tac SUBMAP_TRANS
  >> conj_tac
  >-
   (irule only_fresh_trans
    >> rpt $ first_assum $ irule_at Any
    >> imp_res_tac evaluate_refs_SUBSET)
  >> conj_tac
  >- imp_res_tac holes_unchanged_except_trans
  >> gen_tac
  >> strip_tac
  >> drule_all evaluate_pres_opt_code
  >> strip_tac
  >> first_x_assum $ drule
  >> gvs []
  >> rw []
  >-
   (reverse $ imp_res_tac bvi_to_cb_cases
    >- gvs [rewrite_wrapper_def]
    >> rename [‘CallBlock _ left _ right’]
    >> gvs [rewrite_wrapper_def, evaluate_def]
    >> rpt $ first_assum $ irule_at Any
    >> conj_tac
    >- imp_res_tac SUBMAP_TRANS
    >> conj_tac
    >-
     (irule only_fresh_trans
      >> rpt $ first_assum $ irule_at Any
      >> imp_res_tac evaluate_refs_SUBSET)
    >> imp_res_tac holes_unchanged_except_trans)
  >> reverse $ imp_res_tac bvi_to_cb_cases
  >-
   (gvs [rewrite_worker_def, evaluate_def]
    >> imp_res_tac evaluate_IMP_LENGTH
    >> gvs []
    >> first_x_assum $ qspec_then ‘hole_ptr’ mp_tac
    >> impl_tac
    >-
     (conj_tac
      >-
       (irule_at Any hole_has_val_append
        >> imp_res_tac env_rel_strip_extras
        >> gvs []
        >> irule_at Any unchanged_hole_has_val
        >> rpt $ first_assum $ irule_at Any
        >> gvs [])
      >> gvs [EL_APPEND_EQN])
    >> strip_tac
    >> gvs []
    >> rpt $ first_assum $ irule_at Any
    >> conj_tac
    >- imp_res_tac SUBMAP_TRANS
    >> conj_tac
    >-
     (irule only_fresh_trans
      >> rpt $ first_assum $ irule_at Any
      >> imp_res_tac evaluate_refs_SUBSET)
    >> conj_tac
    >-
     (irule holes_unchanged_except_trans
      >> rpt $ first_assum $ irule_at Any
      >> irule holes_unchanged_except_subset
      >> first_assum $ irule_at Any
      >> gvs [])
    >> rw []
    >> first_assum $ irule_at Any
    >> irule hole_has_val_submap
    >> drule_all hole_has_val_unappend
    >> strip_tac
    >> first_assum $ irule_at Any
    >> gvs [])
  >> gvs [rewrite_worker_def, evaluate_def]
  >> imp_res_tac evaluate_IMP_LENGTH
  >> gvs []
  >> first_x_assum $ qspec_then ‘hole_ptr’ mp_tac
  >> impl_tac
  >-
   (conj_tac
    >-
     (irule_at Any hole_has_val_append
      >> imp_res_tac env_rel_strip_extras
      >> gvs []
      >> irule_at Any unchanged_hole_has_val
      >> rpt $ first_assum $ irule_at Any
      >> gvs [])
    >> gvs [EL_APPEND_EQN])
  >> strip_tac
  >> gvs []
  >> rpt $ first_assum $ irule_at Any
  >> conj_tac
  >- imp_res_tac SUBMAP_TRANS
  >> conj_tac
  >-
   (irule only_fresh_trans
    >> rpt $ first_assum $ irule_at Any
    >> imp_res_tac evaluate_refs_SUBSET)
  >> conj_tac
  >-
   (irule holes_unchanged_except_trans
    >> rpt $ first_assum $ irule_at Any
    >> irule holes_unchanged_except_subset
    >> first_assum $ irule_at Any
    >> gvs [])
  >> rw []
  >> first_assum $ irule_at Any
  >> irule hole_has_val_submap
  >> drule_all hole_has_val_unappend
  >> strip_tac
  >> first_assum $ irule_at Any
  >> gvs []
QED

Resume evaluate_rewrite_tmc[list]:
  gvs [evaluate_def]
  (* First inductive hypothesis *)
  >> gvs [CaseEq "prod", PULL_EXISTS]
  >> rename[‘evaluate ([x],env,s) = (rx,u)’]
  >> first_assum $ qspecl_then [‘[x]’, ‘s’, ‘env’] mp_tac
  >> impl_tac
  >- gvs []
  >> asm_simp_tac std_ss [EVERY_DEF]
  >> rpt $ disch_then drule
  >> impl_tac
  >- (spose_not_then assume_tac >> fs [])
  >> disch_then $ qspec_then ‘loc’ mp_tac
  >> gvs [GSYM PULL_FORALL]
  >> strip_tac
  >> gvs []
  >> pop_assum kall_tac
  >> rename [‘evaluate ([x],env2,s') = (rx',u')’]
  >> reverse $ Cases_on ‘rx’ >> gvs []
  >- (first_x_assum $ irule_at Any >> fs [])
  (* Second inductive hypothesis *)
  >> gvs [CaseEq "prod", PULL_EXISTS]
  >> qpat_x_assum ‘_ = _’ mp_tac
  >> rename [‘evaluate (y::xs,env,u) = (ry,w)’]
  >> strip_tac
  >> rename [‘LIST_REL (v_rel f'') vx vx'’]
  >> first_x_assum $ qspecl_then [‘y::xs’, ‘u’] mp_tac
  >> impl_tac
  >- (imp_res_tac evaluate_clock >> gvs [])
  >> imp_res_tac env_rel_submap
  >> asm_simp_tac std_ss [EVERY_DEF]
  >> rpt $ disch_then drule
  >> impl_tac
  >- gvs [CaseEq "result"]
  >> disch_then $ qspec_then ‘loc’ mp_tac
  >> strip_tac >> fs []
  >> rename [‘evaluate (y::xs,env2,u') = (ry',w')’]
  >> Cases_on ‘ry’ >> gvs []
  >-
   (rename [‘state_rel f3 t t'’]
    >> rename [‘LIST_REL (v_rel f3) vy vy'’]
    >> qexists ‘f3’ >> fs []
    >> imp_res_tac evaluate_SING_IMP >> gvs []
    >> rename [‘v_rel f'' vx vx'’]
    >> drule_all v_rel_submap >> rw []
    >- imp_res_tac SUBMAP_TRANS
    >-
     (irule only_fresh_trans
      >> rpt $ goal_assum $ drule_at Any
      >> irule evaluate_refs_SUBSET
      >> goal_assum $ drule_at Any)
    >> irule holes_unchanged_except_trans
    >> rpt $ goal_assum $ drule_at Any)
  >> rename [‘state_rel f3 t t'’]
  >> qexists ‘f3’ >> fs []
  >> rw []
  >- imp_res_tac SUBMAP_TRANS
  >-
   (irule only_fresh_trans
    >> rpt $ goal_assum $ drule_at Any
    >> irule evaluate_refs_SUBSET
    >> goal_assum $ drule_at Any)
  >> irule holes_unchanged_except_trans
  >> rpt $ goal_assum $ drule_at Any
QED

Resume evaluate_rewrite_tmc[var]:
  gvs [evaluate_def]
  >> Cases_on ‘n < LENGTH env1’ >> gvs []
  >> ‘n < LENGTH env2’ by (drule_all env_rel_length >> gvs [])
  >> gvs [GSYM PULL_FORALL]
  >> drule_all env_rel_el_v_rel
  >> strip_tac
  >> first_assum $ irule_at Any
  >> gvs []
  >> conj_asm1_tac
  >- irule only_fresh_refl
  >> conj_asm1_tac
  >- irule holes_unchanged_except_refl
  >> strip_tac
  >> gvs [rewrite_wrapper_def]
  >> rw []
  >> gvs [rewrite_worker_def]
  >> ho_match_mp_tac evaluate_fill_hole_val
  >> gvs [evaluate_def]
  >> rpt $ first_assum $ irule_at Any
  >> gvs []
QED

Resume evaluate_rewrite_tmc[if]:
  gvs [evaluate_def]
  >> gvs [CaseEq "prod", PULL_EXISTS]
  >> rename [‘evaluate ([x1],env,s) = (r1,u)’]
  (* First inductive hypothesis *)
  >> first_assum $ qspecl_then [‘[x1]’, ‘s’] mp_tac
  >> impl_tac >- gvs []
  >> imp_res_tac env_rel_relax_opt
  >> asm_simp_tac std_ss [EVERY_DEF]
  >> rpt $ disch_then drule
  >> impl_tac >- gvs [CaseEq "result"]
  >> disch_then $ qspec_then ‘loc’ mp_tac
  >> gvs [GSYM PULL_FORALL]
  >> strip_tac
  >> pop_assum kall_tac
  >> gvs []
  >> Cases_on ‘r1’ >> gvs []
  >-
   (imp_res_tac evaluate_SING_IMP
    >> gvs []
    >> rename [‘state_rel f' u u'’]
    >> rename [‘v_rel f' v1 v1'’]
    >> Cases_on ‘v1 = Boolv T’ >> gvs []
    >- (* Then inductive hypothesis *)
     (‘v1' = Boolv T’ by (drule $ iffLR v_rel_cases >> gvs [bvlSemTheory.Boolv_def])
      >> gvs []
      >> first_x_assum $ qspecl_then [‘[x2]’, ‘u’] mp_tac
      >> impl_tac >- (imp_res_tac evaluate_clock >> gvs [])
      >> qpat_x_assum ‘env_rel F _ _ _’ kall_tac
      >> imp_res_tac env_rel_submap
      >> asm_simp_tac std_ss [EVERY_DEF]
      >> rpt $ disch_then drule
      >> disch_then $ qspec_then ‘loc’ mp_tac
      >> impl_tac >- gvs []
      >> strip_tac
      >> qexistsl [‘t''’, ‘f''’, ‘r''’]
      >> gvs [GSYM PULL_FORALL]
      >> conj_tac
      >- imp_res_tac SUBMAP_TRANS
      >> conj_tac
      >-
       (irule only_fresh_trans
        >> goal_assum $ drule_at $ Pos $ el 2
        >> goal_assum $ drule_at Any
        >> irule evaluate_refs_SUBSET
        >> qexistsl [‘env2’, ‘Rval [Boolv T]’, ‘[x1]’]
        >> gvs [])
      >> conj_tac
      >-
       (irule holes_unchanged_except_trans
        >> first_assum $ irule_at Any
        >> gvs [])
      >> gen_tac
      >> strip_tac
      >> gvs []
      >> drule_all evaluate_pres_opt_code
      >> strip_tac
      >> first_x_assum drule
      >> strip_tac
      >> gvs []
      >> rw []
      >-
       (drule wrapper_strip_if_then
        >> strip_tac
        >-
         (gvs [evaluate_def]
          >> rpt $ first_assum $ irule_at Any
          >> conj_tac
          >- imp_res_tac SUBMAP_TRANS
          >> conj_tac
          >-
           (irule only_fresh_trans
            >> rpt $ first_assum $ irule_at Any
            >> imp_res_tac evaluate_refs_SUBSET)
          >> imp_res_tac holes_unchanged_except_trans)
        >> gvs [evaluate_def]
        >> rpt $ first_assum $ irule_at Any
        >> conj_tac
        >- imp_res_tac SUBMAP_TRANS
        >> conj_tac
        >-
         (irule only_fresh_trans
          >> rpt $ first_assum $ irule_at Any
          >> imp_res_tac evaluate_refs_SUBSET)
        >> imp_res_tac holes_unchanged_except_trans)
      >> gvs []
      >> first_x_assum $ qspecl_then [‘c’] mp_tac
      >> impl_tac
      >-
       (drule env_rel_strip_extras
        >> strip_tac
        >> gvs []
        >> irule unchanged_hole_has_val
        >> qexists ‘EMPTY’
        >> gvs []
        >> first_assum $ irule_at $ Pos hd
        >> gvs [])
      >> strip_tac
      >> gvs [rewrite_worker_def, evaluate_def]
      >> imp_res_tac env_rel_length_opt
      >> gvs [EL_APPEND_EQN]
      >> first_assum $ irule_at Any
      >> gvs []
      >> conj_tac
      >- imp_res_tac SUBMAP_TRANS
      >> conj_tac
      >-
       (irule only_fresh_trans
        >> rpt $ first_assum $ irule_at Any
        >> imp_res_tac evaluate_refs_SUBSET)
      >> conj_tac
      >-
       (irule holes_unchanged_except_trans
        >> first_assum $ irule_at Any
        >> gvs []
        >> irule holes_unchanged_except_subset
        >> first_assum $ irule_at Any
        >> gvs [])
      >> rw []
      >> rpt $ first_assum $ irule_at Any
      >> irule hole_has_val_submap
      >> first_assum $ irule_at Any
      >> gvs [])
    (* Else inductive hypothesis *)
    >> Cases_on ‘v1 = Boolv F’ >> gvs []
    >> ‘v1' = Boolv F’ by (drule $ iffLR v_rel_cases >> gvs [bvlSemTheory.Boolv_def])
    >> gvs []
    >> first_x_assum $ qspecl_then [‘[x3]’, ‘u’] mp_tac
    >> impl_tac >- (imp_res_tac evaluate_clock >> gvs [])
    >> qpat_x_assum ‘env_rel F _ _ _’ kall_tac
    >> imp_res_tac env_rel_submap
    >> asm_simp_tac std_ss [EVERY_DEF]
    >> rpt $ disch_then drule
    >> disch_then $ qspec_then ‘loc’ mp_tac
    >> impl_tac >- gvs []
    >> strip_tac
    >> qexistsl [‘t''’, ‘f''’, ‘r''’]
    >> gvs [GSYM PULL_FORALL]
    >> conj_tac
    >- imp_res_tac SUBMAP_TRANS
    >> conj_tac
    >-
     (irule only_fresh_trans
      >> goal_assum $ drule_at $ Pos $ el 2
      >> goal_assum $ drule_at Any
      >> irule evaluate_refs_SUBSET
      >> qexistsl [‘env2’, ‘Rval [Boolv F]’, ‘[x1]’]
      >> gvs [])
    >> conj_tac
    >-
     (irule holes_unchanged_except_trans
      >> first_assum $ irule_at Any
      >> gvs [])
    >> gen_tac
    >> strip_tac
    >> gvs []
    >> drule_all evaluate_pres_opt_code
    >> strip_tac
    >> first_x_assum drule
    >> strip_tac
    >> gvs []
    >> rw []
      >-
       (drule wrapper_strip_if_else
        >> strip_tac
        >-
         (gvs [evaluate_def]
          >> rpt $ first_assum $ irule_at Any
          >> conj_tac
          >- imp_res_tac SUBMAP_TRANS
          >> conj_tac
          >-
           (irule only_fresh_trans
            >> rpt $ first_assum $ irule_at Any
            >> imp_res_tac evaluate_refs_SUBSET)
          >> imp_res_tac holes_unchanged_except_trans)
        >> gvs [evaluate_def]
        >> rpt $ first_assum $ irule_at Any
        >> conj_tac
        >- imp_res_tac SUBMAP_TRANS
        >> conj_tac
        >-
         (irule only_fresh_trans
          >> rpt $ first_assum $ irule_at Any
          >> imp_res_tac evaluate_refs_SUBSET)
        >> imp_res_tac holes_unchanged_except_trans)
    >> gvs []
    >> first_x_assum $ qspecl_then [‘c’] mp_tac
    >> impl_tac
    >-
     (drule env_rel_strip_extras
      >> strip_tac
      >> gvs []
      >> irule unchanged_hole_has_val
      >> qexists ‘EMPTY’
      >> gvs []
      >> first_assum $ irule_at $ Pos hd
      >> gvs [])
    >> strip_tac
    >> gvs [rewrite_worker_def, evaluate_def]
    >> imp_res_tac env_rel_length_opt
    >> gvs [EL_APPEND_EQN]
    >> first_assum $ irule_at Any
    >> gvs []
    >> conj_tac
    >- imp_res_tac SUBMAP_TRANS
    >> conj_tac
    >-
     (irule only_fresh_trans
      >> rpt $ first_assum $ irule_at Any
      >> imp_res_tac evaluate_refs_SUBSET)
    >> conj_tac
    >-
     (irule holes_unchanged_except_trans
      >> first_assum $ irule_at Any
      >> gvs []
      >> irule holes_unchanged_except_subset
      >> first_assum $ irule_at Any
      >> gvs [])
    >> rw []
    >> rpt $ first_assum $ irule_at Any
    >> irule hole_has_val_submap
    >> first_assum $ irule_at Any
    >> gvs [])
  (* Error case *)
  >> gvs []
  >> ‘e' ≠ Rabort Rtype_error’ by (spose_not_then assume_tac >> gvs [])
  >> gvs [GSYM PULL_FORALL]
  >> rpt $ first_assum $ irule_at Any
  >> gvs []
  >> rw []
  >-
   (drule wrapper_strip_if_then
    >> strip_tac
    >-
     (gvs [evaluate_def]
      >> rpt $ first_assum $ irule_at Any)
    >> gvs [evaluate_def]
    >> rpt $ first_assum $ irule_at Any)
  >> gvs [rewrite_worker_def, evaluate_def]
  >> first_assum $ irule_at Any
  >> conj_tac
  >- gvs [opt_res_rel_def]
  >> gvs []
  >> irule holes_unchanged_except_subset
  >> first_assum $ irule_at Any
  >> gvs []
QED

Resume evaluate_rewrite_tmc[lett]:
  gvs [evaluate_def]
  >> gvs [CaseEq "prod", PULL_EXISTS]
  >> rename [‘evaluate (xs,env,s) = (rs,u)’]
  (* First inductive hypothesis *)
  >> first_assum $ qspecl_then [‘xs’, ‘s’] mp_tac
  >> impl_tac
  >- (imp_res_tac evaluate_clock >> gvs [])
  >> imp_res_tac env_rel_relax_opt
  >> asm_simp_tac std_ss [EVERY_DEF]
  >> rpt $ disch_then drule
  >> disch_then $ qspec_then ‘loc’ mp_tac
  >> impl_tac
  >- gvs [CaseEq "result"]
  >> pop_assum kall_tac
  >> gvs [GSYM PULL_FORALL]
  >> strip_tac
  >> pop_assum kall_tac
  >> reverse $ gvs [CaseEq "result"]
  >-
   (gvs [GSYM PULL_FORALL]
    >> first_assum $ irule_at Any
    >> gvs []
    >> rw []
    >-
     (drule wrapper_strip_let
      >> strip_tac
      >> gvs [evaluate_def]
      >> rpt $ first_assum $ irule_at Any)
    >> gvs [rewrite_worker_def, evaluate_def, opt_res_rel_def]
    >> rpt $ first_assum $ irule_at Any
    >> irule holes_unchanged_except_subset
    >> first_assum $ irule_at Any
    >> gvs [])
  >> rename [‘evaluate (_,_,_) = (Rval vs',u')’, ‘LIST_REL (v_rel f') _ _’]
  >> gvs []
  (* Second inductive hypothesis *)
  >> first_x_assum $ qspecl_then [‘[x2]’, ‘u’] mp_tac
  >> impl_tac
  >- (imp_res_tac evaluate_clock >> gvs [])
  >> imp_res_tac env_rel_submap
  >> imp_res_tac env_rel_append
  >> asm_simp_tac std_ss [EVERY_DEF]
  >> rpt $ disch_then drule
  >> disch_then $ qspec_then ‘loc’ mp_tac
  >> impl_tac
  >- gvs [LENGTH_APPEND]
  >> strip_tac
  >> rename [‘evaluate (_,_,_) = (r',t')’]
  >> gvs [GSYM PULL_FORALL]
  >> first_assum $ irule_at Any
  >> gvs []
  >> conj_tac
  >- imp_res_tac SUBMAP_TRANS
  >> conj_tac
  >-
   (irule only_fresh_trans
    >> first_assum $ irule_at Any
    >> imp_res_tac evaluate_refs_SUBSET
    >> gvs [])
  >> conj_tac
  >-
   (irule holes_unchanged_except_trans
    >> first_assum $ irule_at Any
    >> gvs [])
  >> gen_tac
  >> strip_tac
  >> first_x_assum $ qspec_then ‘loc_opt’ mp_tac
  >> impl_tac
  >- imp_res_tac evaluate_pres_opt_code
  >> strip_tac
  >> rw []
  >-
   (imp_res_tac evaluate_IMP_LENGTH
    >> gvs [rewrite_wrapper_def, CaseEq "option"]
    >> gvs [evaluate_def]
    >> first_assum $ irule_at Any
    >> gvs []
    >> conj_tac
    >- imp_res_tac SUBMAP_TRANS
    >> conj_tac
    >-
     (irule only_fresh_trans
      >> first_assum $ irule_at Any
      >> imp_res_tac evaluate_refs_SUBSET
      >> gvs [])
    >> irule holes_unchanged_except_trans
    >> first_assum $ irule_at Any
    >> gvs [])
  >> gvs []
  >> first_x_assum $ qspecl_then [‘hole_ptr’, ‘c’] mp_tac
  >> impl_tac
  >-
   (conj_tac
    >-
     (irule hole_has_val_append
      >> gvs []
      >> imp_res_tac env_rel_strip_extras
      >> gvs []
      >> irule unchanged_hole_has_val
      >> rpt $ first_assum $ irule_at Any
      >> gvs [])
    >> imp_res_tac env_rel_length_opt
    >> gvs [EL_APPEND_EQN])
  >> strip_tac
  >> gvs [rewrite_worker_def, evaluate_def]
  >> rpt $ first_assum $ irule_at Any
  >> imp_res_tac evaluate_IMP_LENGTH
  >> gvs []
  >> conj_tac
  >- imp_res_tac SUBMAP_TRANS
  >> conj_tac
  >-
   (irule only_fresh_trans
    >> rpt $ first_assum $ irule_at Any
    >> imp_res_tac evaluate_refs_SUBSET)
  >> conj_tac
  >-
   (irule holes_unchanged_except_trans
    >> first_assum $ irule_at Any
    >> gvs []
    >> irule holes_unchanged_except_subset
    >> first_assum $ irule_at Any
    >> gvs [])
  >> rw []
  >> rpt $ first_assum $ irule_at Any
  >> irule hole_has_val_submap
  >> imp_res_tac hole_has_val_unappend
  >> first_assum $ irule_at Any
  >> gvs []
QED

Resume evaluate_rewrite_tmc[raise]:
  gvs [evaluate_def]
  >> gvs [CaseEq "prod", PULL_EXISTS]
  >> rename [‘evaluate ([x],env,s) = (v,u)’]
  >> first_x_assum $ qspecl_then [‘[x]’, ‘s’, ‘env’] mp_tac
  >> impl_tac
  >- gvs []
  >> asm_simp_tac std_ss [EVERY_DEF]
  >> rpt $ disch_then drule
  >> disch_then $ qspec_then ‘loc’ mp_tac
  >> gvs []
  >> impl_tac
  >- (spose_not_then assume_tac >> gvs [])
  >> gvs [GSYM PULL_FORALL]
  >> strip_tac
  >> gvs [PULL_EXISTS, GSYM PULL_FORALL]
  >> rpt $ first_assum $ irule_at Any
  >> reverse $ gvs [CaseEq "result"]
  >-
   (rw []
    >- gvs [evaluate_def, rewrite_wrapper_def]
    >> gvs [evaluate_def, rewrite_worker_def, opt_res_rel_def]
    >> first_assum $ irule_at Any
    >> gvs []
    >> irule holes_unchanged_except_subset
    >> first_assum $ irule_at Any
    >> gvs [])
  >> imp_res_tac evaluate_SING_IMP
  >> gvs []
  >> rw []
  >- gvs [evaluate_def, rewrite_wrapper_def]
  >> gvs [evaluate_def, rewrite_worker_def, opt_res_rel_def]
  >> first_assum $ irule_at Any
  >> gvs []
  >> irule holes_unchanged_except_subset
  >> first_assum $ irule_at Any
  >> gvs []
QED

Resume evaluate_rewrite_tmc[tick]:
  gvs [evaluate_def]
  >> ‘s'.clock = s.clock’ by gvs [state_rel_def]
  >> gvs []
  >> Cases_on ‘s.clock’
  >-
   (gvs [GSYM PULL_FORALL]
    >> rpt $ first_assum $ irule_at Any
    >> gvs []
    >> gvs [only_fresh_refl, holes_unchanged_except_refl]
    >> rw []
    >-
     (gvs [rewrite_wrapper_def, evaluate_def]
      >> rpt $ first_assum $ irule_at Any
      >> conj_tac
      >> gvs [only_fresh_refl, holes_unchanged_except_refl])
    >> first_assum $ irule_at Any
    >> gvs [rewrite_worker_def, evaluate_def, opt_res_rel_def, holes_unchanged_except_refl, only_fresh_refl])
  >> gvs [GSYM PULL_FORALL]
  >> first_x_assum $ qspecl_then [‘[x]’, ‘dec_clock 1 s’] mp_tac
  >> impl_tac >- gvs [dec_clock_def]
  >> asm_simp_tac std_ss [EVERY_DEF]
  >> rpt $ disch_then drule
  >> drule state_rel_dec
  >> rpt $ disch_then drule
  >> disch_then $ qspec_then ‘1’ mp_tac
  >> impl_tac >- gvs []
  >> strip_tac
  >> disch_then drule
  >> disch_then $ qspec_then ‘loc’ mp_tac
  >> impl_tac >- gvs []
  >> strip_tac
  >> rename [‘evaluate ([x],env2,dec_clock 1 s') = (r',t')’]
  >> rpt $ first_assum $ irule_at Any
  >> gvs []
  >> gen_tac
  >> strip_tac
  >> first_x_assum drule
  >> strip_tac
  >> rw []
  >-
   (gvs [rewrite_wrapper_def, evaluate_def]
    >> first_assum $ irule_at Any
    >> gvs [])
  >> gvs [rewrite_worker_def, evaluate_def, PULL_EXISTS]
  >> first_x_assum drule
  >> strip_tac
  >> gvs []
  >> first_assum $ irule_at Any
  >> gvs []
QED

Theorem find_code_rel:
  ∀f vs vs' s s' dest args body.
    find_code dest vs s.code = SOME (args,body) ∧
    LIST_REL (v_rel f) vs vs' ∧
    state_rel f s s' ⇒
    no_mutcons body ∧
    ∃args' body' loc.
      find_code dest vs' s'.code = SOME (args',body') ∧
      env_rel F f args args' ∧
      LENGTH args = LENGTH args' ∧
      (body ≠ body' ⇒
       ∃loc_opt.
         optimised_code loc loc_opt s.code s'.code ∧
         rewrite_wrapper loc loc_opt (LENGTH args) body = SOME body')
Proof
  rpt gen_tac
  >> strip_tac
  >> ‘code_rel s.code s'.code’ by gvs [state_rel_def]
  >> imp_res_tac code_rel_cases
  >> imp_res_tac LIST_REL_LENGTH
  >> Cases_on ‘dest’ >> gvs [bvlSemTheory.find_code_def]
  >-
   (gvs [CaseEq "v", CaseEq "option", CaseEq "prod"]
    >> conj_tac
    >- rpt $ first_x_assum $ irule_at Any
    >> Cases_on ‘LAST vs’ >> gvs []
    >> imp_res_tac list_rel_last
    >> Cases_on ‘LAST vs'’ >> gvs [v_rel_cases]
    >> first_x_assum drule
    >> strip_tac
    >> first_assum $ irule_at Any
    >> qexists ‘loc’
    >> conj_tac
    >- (Cases_on ‘vs'’ >> gvs [])
    >> imp_res_tac list_rel_front
    >> conj_tac
    >- imp_res_tac list_rel_env_rel
    >> conj_tac
    >- imp_res_tac LIST_REL_LENGTH
    >> strip_tac
    >> gvs []
    >> first_assum $ irule_at Any
    >> Cases_on ‘arity + 1’
    >- gvs []
    >> gvs [LENGTH_FRONT, prim_recTheory.PRE_DEF]
    >> ‘arity = n’ by gvs []
    >> gvs [])
  >> gvs [CaseEq "option", CaseEq "prod"]
  >> rename [‘lookup loc _ = _’]
  >> conj_tac
  >- rpt $ first_x_assum $ irule_at Any
  >> first_x_assum drule
  >> strip_tac
  >> first_assum $ irule_at Any
  >> qexists ‘loc’
  >> conj_tac
  >- imp_res_tac list_rel_env_rel
  >> strip_tac
  >> gvs []
  >> first_assum $ irule_at Any
  >> gvs []
QED

Resume evaluate_rewrite_tmc[call_non_opt]:
  gvs [evaluate_def]
  >> IF_CASES_TAC >> gvs []
  >> gvs [CaseEq "prod", PULL_EXISTS]
  >> rename [‘evaluate (xs,env,s) = (v_xs,u)’]
  (* xs inductive hypothesis *)
  >> first_assum $ qspecl_then [‘xs’, ‘s’] mp_tac
  >> impl_tac
  >- gvs []
  >> imp_res_tac env_rel_relax_opt
  >> asm_simp_tac std_ss [EVERY_DEF]
  >> rpt $ disch_then drule
  >> pop_assum kall_tac
  >> impl_tac
  >- (CCONTR_TAC >> gvs [])
  >> disch_then $ qspec_then ‘loc’ mp_tac
  >> gvs [GSYM PULL_FORALL]
  >> strip_tac
  >> pop_assum kall_tac
  >> rename [‘state_rel f' u u'’, ‘result_rel _ _ _ v_xs'’]
  >> reverse $ gvs [CaseEq "result"]
  >- (* Error case *)
   (rename [‘evaluate (xs,env2,s') = (Rerr e',t')’, ‘exc_rel (v_rel f') e _’]
    >> gvs [GSYM PULL_FORALL]
    >> rpt $ first_assum $ irule_at Any
    >> gen_tac
    >> strip_tac
    >> rw []
    >- gvs [evaluate_def, rewrite_wrapper_def]
    >> gvs [evaluate_def, rewrite_worker_def, fill_hole_def]
    >> IF_CASES_TAC
    >- gvs []
    >> gvs []
    >> rpt $ first_assum $ irule_at Any
    >> conj_tac
    >- gvs [opt_res_rel_def]
    >> irule holes_unchanged_except_subset
    >> first_assum $ irule_at Any
    >> gvs [])
  >> gvs [GSYM PULL_FORALL, CaseEq "option", CaseEq "prod"]
  >> drule_all find_code_rel
  >> strip_tac
  >> gvs []
  >> ‘u.clock = u'.clock’ by gvs [state_rel_def]
  >> IF_CASES_TAC
  >-
   (qexistsl [‘u' with clock := 0’, ‘f'’, ‘Rerr (Rabort Rtimeout_error)’]
    >> gvs [state_rel_with_clock]
    >> rw []
    >- gvs [rewrite_wrapper_def]
    >> gvs [rewrite_worker_def]
    >> gvs [evaluate_def, fill_hole_def]
    >> IF_CASES_TAC
    >- gvs []
    >> gvs []
    >> first_assum $ irule_at Any
    >> gvs [opt_res_rel_def, state_rel_with_clock]
    >> irule holes_unchanged_except_subset
    >> first_assum $ irule_at Any
    >> gvs [])
  >> gvs [CaseEq "prod"]
  >> first_assum $ qspecl_then [‘[exp]’, ‘dec_clock (ticks + 1) u’] mp_tac
  >> impl_tac
  >- (imp_res_tac evaluate_clock >> gvs [dec_clock_def])
  >> rpt $ disch_then drule
  >> drule state_rel_dec
  >> Cases_on ‘u.clock’
  >- gvs []
  >> gvs []
  >> disch_then $ qspec_then ‘ticks + 1’ mp_tac
  >> impl_tac
  >- gvs []
  >> strip_tac
  >> disch_then drule
  >> disch_then $ qspec_then ‘loc'’ mp_tac
  >> impl_tac
  >- gvs [CaseEq "result", CaseEq "error_result"]
  >> strip_tac
  >> Cases_on ‘exp = body'’
  >-
   (gvs []
    >> pop_assum kall_tac
    >> reverse $ Cases_on ‘∃v_raise h. v3 = Rerr (Rraise v_raise) ∧ handler = SOME h’
    >-
     (gvs []
      >> qexistsl [‘t''’, ‘f''’, ‘r''’]
      >> conj_tac
      >- gvs [CaseEq "result", CaseEq "error_result", CaseEq "option"]
      >> ‘(v3,s'') = (r,t)’ by gvs [CaseEq "result", CaseEq "error_result", CaseEq "option"]
      >> gvs []
      >> conj_tac
      >- imp_res_tac SUBMAP_TRANS
      >> conj_tac
      >-
       (irule only_fresh_trans
        >> rpt $ first_assum $ irule_at Any
        >> imp_res_tac evaluate_refs_SUBSET)
      >> conj_tac
      >-
       (irule holes_unchanged_except_trans
        >> first_assum $ irule_at Any
        >> gvs []
        >> irule holes_unchanged_except_subset
        >> first_assum $ irule_at Any
        >> gvs [])
      >> rw []
      >- gvs [rewrite_wrapper_def]
      >> gvs [rewrite_worker_def]
      >> ho_match_mp_tac evaluate_fill_hole
      >> rpt $ first_assum $ irule_at Any
      >> gvs [evaluate_def]
      >> IF_CASES_TAC
      >- gvs []
      >> gvs []
      >> conj_tac
      >-
       (CASE_TAC
        >- (CASE_TAC >> CASE_TAC)
        >> CASE_TAC
        >> CASE_TAC
        >> gvs [])
      >> conj_tac
      >- imp_res_tac SUBMAP_TRANS
      >> conj_tac
      >-
       (irule holes_unchanged_except_trans
        >> first_assum $ irule_at Any
        >> gvs []
        >> irule holes_unchanged_except_subset
        >> first_assum $ irule_at Any
        >> gvs [])
      >> irule only_fresh_trans
      >> rpt $ first_assum $ irule_at Any
      >> imp_res_tac evaluate_refs_SUBSET)
    >> gvs []
    >> rename [‘state_rel _ k k'’, ‘v_rel _ _ v_raise'’, ‘LIST_REL _ vs vs'’]
    >> first_x_assum $ qspecl_then [‘[h]’, ‘k’] mp_tac
    >> impl_tac
    >- (imp_res_tac evaluate_clock >> gvs [dec_clock_def])
    >> disch_then drule
    >> ‘env_rel opt f'' (v_raise::env) (v_raise'::env2)’ by
      (imp_res_tac env_rel_submap
       >> imp_res_tac env_rel_cons)
    >> asm_simp_tac std_ss [EVERY_DEF]
    >> rpt $ disch_then drule
    >> impl_tac
    >- gvs [CaseEq "prod"]
    >> disch_then $ qspec_then ‘loc’ mp_tac
    >> strip_tac
    >> pop_assum kall_tac
    >> rpt $ first_assum $ irule_at Any
    >> conj_asm1_tac
    >- imp_res_tac SUBMAP_TRANS
    >> conj_asm1_tac
    >-
     (irule only_fresh_trans
      >> rpt $ first_assum $ irule_at $ Pos last
      >> imp_res_tac evaluate_refs_SUBSET
      >> gvs []
      >> conj_tac
      >- imp_res_tac SUBSET_TRANS
      >> irule only_fresh_trans
      >> rpt $ first_assum $ irule_at Any)
    >> conj_tac
    >-
     (irule holes_unchanged_except_trans
      >> first_assum $ irule_at $ Pos last
      >> gvs []
      >> conj_tac
      >- imp_res_tac SUBMAP_TRANS
      >> conj_tac
      >-
       (irule only_fresh_trans
        >> rpt $ first_assum $ irule_at $ Pos last
        >> imp_res_tac evaluate_refs_SUBSET)
      >> irule holes_unchanged_except_trans
      >> rpt $ first_assum $ irule_at $ Pos last)
    >> rw []
    >- gvs [rewrite_wrapper_def]
    >> gvs [rewrite_worker_def]
    >> ho_match_mp_tac evaluate_fill_hole
    >> rpt $ first_assum $ irule_at Any
    >> gvs [evaluate_def]
    >> irule holes_unchanged_except_trans
    >> rpt $ first_assum $ irule_at $ Pos last
    >> conj_tac
    >- imp_res_tac SUBMAP_TRANS
    >> conj_tac
    >-
     (irule only_fresh_trans
      >> rpt $ first_assum $ irule_at $ Pos last
      >> imp_res_tac evaluate_refs_SUBSET)
    >> irule holes_unchanged_except_trans
    >> first_assum $ irule_at $ Pos last
    >> gvs [])
  >> gvs []
  >> first_x_assum drule
  >> disch_then drule
  >> strip_tac
  >> gvs []
  >> reverse $ Cases_on ‘∃v_raise h. v3 = Rerr (Rraise v_raise) ∧ handler = SOME h’
  >-
   (gvs []
    >> qexistsl [‘t_wrap’, ‘f_wrap’, ‘r_wrap’]
    >> conj_tac
    >- gvs [CaseEq "result", CaseEq "error_result", CaseEq "option"]
    >> ‘(v3,s'') = (r,t)’ by gvs [CaseEq "result", CaseEq "error_result", CaseEq "option"]
    >> gvs []
    >> conj_tac
    >- imp_res_tac SUBMAP_TRANS
    >> conj_tac
    >-
     (irule only_fresh_trans
      >> rpt $ first_assum $ irule_at $ Pos last
      >> imp_res_tac evaluate_refs_SUBSET)
    >> conj_tac
    >-
     (irule holes_unchanged_except_trans
      >> first_assum $ irule_at $ Pos last
      >> gvs [])
    >> rw []
    >- gvs [rewrite_wrapper_def]
    >> gvs [rewrite_worker_def]
    >> ho_match_mp_tac evaluate_fill_hole
    >> rpt $ first_assum $ irule_at Any
    >> gvs [evaluate_def]
    >> IF_CASES_TAC
    >- gvs []
    >> gvs []
    >> conj_tac
    >-
     (CASE_TAC
      >- (CASE_TAC >> CASE_TAC)
      >> CASE_TAC
      >> CASE_TAC
      >> gvs [])
    >> conj_tac
    >- imp_res_tac SUBMAP_TRANS
    >> conj_tac
    >-
     (irule holes_unchanged_except_trans
      >> first_assum $ irule_at Any
      >> gvs []
      >> irule holes_unchanged_except_subset
      >> first_assum $ irule_at Any
      >> gvs [])
    >> irule only_fresh_trans
    >> rpt $ first_assum $ irule_at Any
    >> imp_res_tac evaluate_refs_SUBSET)
  >> gvs []
  >> rename [‘state_rel _ k k'’, ‘v_rel _ _ v_raise'’, ‘LIST_REL _ vs vs'’]
  >> first_x_assum $ qspecl_then [‘[h]’, ‘k’] mp_tac
  >> impl_tac
  >- (imp_res_tac evaluate_clock >> gvs [dec_clock_def])
  >> disch_then drule
  >> ‘env_rel opt f_wrap (v_raise::env) (v_raise'::env2)’ by
    (imp_res_tac env_rel_submap
     >> imp_res_tac env_rel_cons)
  >> asm_simp_tac std_ss [EVERY_DEF]
  >> rpt $ disch_then drule
  >> impl_tac
  >- gvs [CaseEq "prod"]
  >> disch_then $ qspec_then ‘loc’ mp_tac
  >> strip_tac
  >> pop_assum kall_tac
  >> rpt $ first_assum $ irule_at Any
  >> conj_asm1_tac
  >- imp_res_tac SUBMAP_TRANS
  >> conj_asm1_tac
  >-
   (irule only_fresh_trans
    >> rpt $ first_assum $ irule_at $ Pos last
    >> imp_res_tac evaluate_refs_SUBSET
    >> gvs []
    >> conj_tac
    >- imp_res_tac SUBSET_TRANS
    >> irule only_fresh_trans
    >> rpt $ first_assum $ irule_at Any)
  >> conj_tac
  >-
   (irule holes_unchanged_except_trans
    >> first_assum $ irule_at $ Pos last
    >> gvs []
    >> conj_tac
    >- imp_res_tac SUBMAP_TRANS
    >> conj_tac
    >-
     (irule only_fresh_trans
      >> rpt $ first_assum $ irule_at $ Pos last
      >> imp_res_tac evaluate_refs_SUBSET)
    >> irule holes_unchanged_except_trans
    >> rpt $ first_assum $ irule_at $ Pos last)
  >> rw []
  >- gvs [rewrite_wrapper_def]
  >> gvs [rewrite_worker_def]
  >> ho_match_mp_tac evaluate_fill_hole
  >> rpt $ first_assum $ irule_at Any
  >> gvs [evaluate_def]
  >> irule holes_unchanged_except_trans
  >> rpt $ first_assum $ irule_at $ Pos last
  >> conj_tac
  >- imp_res_tac SUBMAP_TRANS
  >> conj_tac
  >-
   (irule only_fresh_trans
    >> rpt $ first_assum $ irule_at $ Pos last
    >> imp_res_tac evaluate_refs_SUBSET)
  >> irule holes_unchanged_except_trans
  >> first_assum $ irule_at $ Pos last
  >> gvs []
QED

Definition dest_thunk_ret_rel_def:
  dest_thunk_ret_rel f t1 t2 ⇔
    ((t1 = BadRef ∧ t2 = BadRef) ∨
     (t1 = NotThunk ∧ t2 = NotThunk) ∨
     ∃tm1 tm2 v1 v2.
       t1 = IsThunk tm1 v1 ∧ t2 = IsThunk tm2 v2 ∧
       tm1 = tm2 ∧
       v_rel f v1 v2)
End

Theorem env_rel_el:
  ∀opt f env1 env2 n.
    env_rel opt f env1 env2 ∧
    n < LENGTH env1 ⇒
    v_rel f (EL n env1) (EL n env2)
Proof
  rw []
  >> gvs [env_rel_def]
  >> imp_res_tac LIST_REL_EL_EQN
  >> gvs [EL_APPEND_EQN]
QED

Theorem dest_thunk_rel:
  ∀opt f env1 env2 s1 s2 n.
    env_rel opt f env1 env2 ∧
    state_rel f s1 s2 ∧
    n < LENGTH env1 ⇒
    dest_thunk_ret_rel f (dest_thunk (EL n env1) s1.refs) (dest_thunk (EL n env2) s2.refs)
Proof
  rw []
  >> imp_res_tac env_rel_el
  >> gvs [v_rel_cases, dest_thunk_def, dest_thunk_ret_rel_def, CaseEq "option", state_rel_def, state_ref_rel_def]
  >> Cases_on ‘FLOOKUP s1.refs n'’
  >- gvs [FLOOKUP_DEF]
  >> gvs []
  >> first_x_assum drule
  >> strip_tac
  >> gvs [CaseEq "ref", CaseEq "thunk_mode", ref_rel_cases]
  >> qexistsl [‘tm’, ‘x'’, ‘y’]
  >> gvs []
  >> conj_tac
  >- (Cases_on ‘tm’ >> gvs [])
  >> conj_tac
  >- (Cases_on ‘tm’ >> gvs [])
  >> Cases_on ‘x'’ >> gvs [v_rel_cases]
QED

Resume evaluate_rewrite_tmc[force]:
  gvs [evaluate_def]
  >> imp_res_tac env_rel_length
  >> Cases_on ‘¬(n < LENGTH env1)’
  >- gvs []
  >> gvs [GSYM PULL_FORALL]
  >> imp_res_tac dest_thunk_rel
  >> gvs [dest_thunk_ret_rel_def, CaseEq "thunk_mode"]
  >-
   (first_assum $ irule_at Any
    >> gvs [only_fresh_refl, holes_unchanged_except_refl]
    >> rw []
    >- gvs [rewrite_wrapper_def]
    >> gvs [rewrite_worker_def]
    >> ho_match_mp_tac evaluate_fill_hole_val
    >> rpt $ first_assum $ irule_at Any
    >> gvs [evaluate_def, holes_unchanged_except_refl, only_fresh_refl])
  >> gvs [CaseEq "option", CaseEq "prod"]
  >> drule find_code_rel
  >> ‘LIST_REL (v_rel f) [EL n env1; v1] [EL n env2; v2]’ by
    (irule $ iffRL LIST_REL_EL_EQN
     >> gvs []
     >> rw []
     >> Cases_on ‘n'’
     >- (imp_res_tac env_rel_el >> gvs [])
     >> Cases_on ‘n''’
     >- gvs []
     >> gvs [])
  >> asm_simp_tac std_ss [EVERY_DEF]
  >> rpt $ disch_then drule
  >> strip_tac
  >> gvs []
  >> ‘s.clock = s'.clock’ by gvs [state_rel_def]
  >> IF_CASES_TAC
  >-
   (gvs []
    >> qexists ‘f’
    >> conj_tac
    >- gvs [state_rel_def]
    >> gvs [only_fresh_refl, holes_unchanged_except_refl]
    >> rw []
    >- gvs [rewrite_wrapper_def]
    >> gvs [rewrite_worker_def]
    >> gvs [evaluate_def, fill_hole_def]
    >> qexists ‘f’
    >> gvs [opt_res_rel_def, state_rel_def, holes_unchanged_except_refl, only_fresh_refl])
  >> gvs []
  >> first_x_assum $ qspecl_then [‘[exp]’, ‘dec_clock 1 s’] mp_tac
  >> impl_tac >- gvs [dec_clock_def]
  >> asm_simp_tac std_ss [EVERY_DEF]
  >> rpt $ disch_then drule
  >> disch_then $ qspec_then ‘dec_clock 1 s'’ mp_tac
  >> impl_tac >- gvs [dec_clock_def, state_rel_def]
  >> disch_then $ qspec_then ‘loc'’ mp_tac
  >> strip_tac
  >> rename [‘state_rel f' t t'’, ‘result_rel _ _ _ r'’]
  >> Cases_on ‘exp = body'’
  >-
   (gvs []
    >> first_assum $ irule_at Any
    >> gvs []
    >> rw []
    >- gvs [rewrite_wrapper_def]
    >> gvs [rewrite_worker_def]
    >> ho_match_mp_tac evaluate_fill_hole
    >> rpt $ first_assum $ irule_at Any
    >> gvs [evaluate_def])
  >> gvs []
  >> first_x_assum drule
  >> disch_then drule
  >> strip_tac
  >> gvs []
  >> first_assum $ irule_at Any
  >> gvs []
  >> rw []
  >- gvs [rewrite_wrapper_def]
  >> gvs [rewrite_worker_def]
  >> ho_match_mp_tac evaluate_fill_hole
  >> rpt $ first_assum $ irule_at Any
  >> gvs [evaluate_def]
QED

Finalise evaluate_rewrite_tmc;

Theorem evaluate_compile_prog:
   input_condition next prog ∧
   (∀n next cfg prog. co n = ((next,cfg),prog) ⇒ input_condition next prog) ∧
   (∀n. MEM n (MAP FST (SND (compile_prog next prog))) ∧ in_ns_2 n ⇒ n < FST (FST (co 0))) ∧
   evaluate ([Call 0 (SOME start) [] NONE], [],
             initial_state ffi0 (fromAList prog) co
                 (state_cc compile_prog cc) k) = (r, s) ∧
   r ≠ Rerr (Rabort Rtype_error) ⇒
   ∃f s2 r2.
     evaluate
      ([Call 0 (SOME start) [] NONE], [],
        initial_state ffi0 (fromAList (SND (compile_prog next prog)))
            (state_co compile_prog co) cc k)
     = (r2, s2) ∧
     result_rel (LIST_REL (v_rel f)) (v_rel f) r r2 ∧
     state_rel f s s2
Proof
  rw []
  >> qmatch_asmsub_abbrev_tac `(es,env,st1)`
  >> ‘env_rel F FEMPTY env env’ by gvs [env_rel_def, Abbr ‘env’]
  >> Cases_on `compile_prog next prog`
  >> fs []
  >> drule (GEN_ALL compile_prog_code_rel)
  >> impl_tac
  >- gvs [input_condition_def]
  >> strip_tac
  >> qmatch_goalsub_abbrev_tac`(es,env,st2)`
  >> ‘state_rel FEMPTY st1 st2’ by (
    gvs [state_rel_def, Abbr ‘st1’, Abbr ‘st2’, input_condition_def]
    >> gvs [domain_fromAList]
    >> conj_tac
    >- gvs [state_ref_rel_def]
    >> conj_tac
    >-
     (gvs [namespace_rel_def]
      >> conj_tac
      >-
       (gen_tac
        >> strip_tac
        >> CASE_TAC
        >-
         (spose_not_then assume_tac
          >> gvs [domain_lookup, lookup_fromAList, EVERY_FILTER]
          >> imp_res_tac ALOOKUP_MEM
          >> imp_res_tac EVERY_MEM
          >> gvs [])
        >> cheat
       )
      >> conj_tac
      >-
       (rw []
        >> cheat)
      >> cheat
      )
    >> rpt strip_tac
    >> pairarg_tac
    >> gvs []
    >> res_tac
    >> gvs [])
  >> drule evaluate_rewrite_tmc
  >> rpt $ disch_then $ drule_at Any
  >> disch_then $ qspecl_then [‘(st1.clock,list_size exp_size es)’, ‘start’] mp_tac
  >> impl_tac >- gvs [Abbr‘es’]
  >> strip_tac
  >> rpt $ first_assum $ irule_at Any
QED

Theorem compile_prog_semantics:
   input_condition n prog ∧
   (∀k n cfg prog. co k = ((n,cfg),prog) ⇒ input_condition n prog) ∧
   (∀k. MEM k (MAP FST prog2) ∧ in_ns_2 k ⇒ k < FST(FST (co 0))) ∧
   SND (compile_prog n prog) = prog2 ∧
   semantics ffi (fromAList prog) co (state_cc compile_prog cc) start ≠
      ffi$Fail ⇒
   semantics ffi (fromAList prog) co (state_cc compile_prog cc) start =
   semantics ffi (fromAList prog2) (state_co compile_prog co) cc start
Proof
  rw []
  >> gvs [semantics_def]
  >> IF_CASES_TAC
  >- gvs []
  >> gvs []
  >> DEEP_INTRO_TAC some_intro >> gvs []
  >> conj_tac
  >-
   (gen_tac
    >> strip_tac
    >> gvs []
    >> drule evaluate_compile_prog
    >> rpt $ disch_then drule
    >> impl_tac >- (spose_not_then assume_tac >> gvs [])
    >> strip_tac >> gvs []
    >> cheat)
  >> strip_tac
  >> gvs []
  >> cheat
QED
