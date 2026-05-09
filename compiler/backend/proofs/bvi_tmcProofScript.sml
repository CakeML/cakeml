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
[~MutBlock:]
  LIST_REL (v_rel f) xs1 ys1 ∧
  v_rel f h1 h2 ∧
  LIST_REL (v_rel f) xs2 ys2 ⇒
  ref_rel f (MutBlock n xs1 h1 ys1) (MutBlock n xs2 h2 ys2)
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
        EL 1 ys = Number hole_idx)
End

Definition code_rel_def:
  code_rel c1 c2 ⇔
    ∀loc arity exp.
      lookup loc c1 = SOME (arity, exp) ⇒
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
  simp [code_rel_def, SUBSET_DEF]
  >> CCONTR_TAC >> fs []
  >> Cases_on `lookup x c1`
  >- fs [lookup_NONE_domain]
  >> fs [GSYM lookup_NONE_domain]
  >> rename1 `SOME z`
  >> PairCases_on `z`
  >> rename [‘lookup x c1 = SOME (arity,exp)’]
  >> first_x_assum drule
  >> fs [compile_exp_def]
  >> strip_tac
  >> CASE_TAC
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

Definition input_condition_def:
  input_condition next prog ⇔
    EVERY (free_names next o FST) prog ∧
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

Definition state_rel_def:
  state_rel f s (t:('a,'ffi) bviSem$state) ⇔
    state_ref_rel f s.refs t.refs ∧
    t.clock = s.clock ∧
    t.global = s.global ∧
    t.ffi = s.ffi ∧
    t.compile_oracle = state_co compile_prog s.compile_oracle ∧
    s.compile = state_cc compile_prog t.compile ∧
    code_rel s.code t.code ∧
    namespace_rel s.code t.code ∧
    (∀n. let ((next,cfg),prog) = s.compile_oracle n in
            input_condition next prog) ∧
    (∀n. n ∈ domain t.code ∧ in_ns_2 n ⇒ n < FST(FST(s.compile_oracle 0)))
End

Theorem compile_prog_code_rel:
   compile_prog next prog = (next1, prog2) ∧
   ALL_DISTINCT (MAP FST prog) ∧
   EVERY (free_names next o FST) prog ⇒
     code_rel (fromAList prog) (fromAList prog2)
Proof
  cheat
QED

Definition opt_res_rel_def:
  opt_res_rel (r1 : (v list, v) result) (r2 : (v list, v) result) =
  case r1 of
  | Rval v1 => r2 = Rval [Block 0 []]
  | _ => r1 = r2
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
      env2 = env2' ++ [RefPtr F hole_ptr; Number hole_idx]
Proof
  rw []
  >> gvs [env_rel_def]
  >> qexistsl [‘xs’, ‘hole_ptr’, ‘hole_idx’]
  >> gvs []
  >> conj_tac
  >- (qexistsl [‘xs’, ‘[]’] >> gvs [])
  >> gvs []
  >> cheat (* this is easy but i'm not quite sure how to do it *)
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

Theorem evaluate_expand_env:
  ∀xs env s t r extra.
    evaluate (xs, env, s) = (r, t) ⇒
    evaluate (xs, env ++ extra, s) = (r, t)
Proof
  recInduct bviSemTheory.evaluate_ind
  >> rpt strip_tac
  >~ [‘evaluate ([],_,_)’] >-
   (gvs [evaluate_def])
  >~ [‘evaluate (x::y::xs,_,_)’] >-
   (simp [Once evaluate_CONS] >> cheat)
  >> cheat
QED

Theorem evaluate_pad_env_val:
  ∀xs env s t vs extra.
    evaluate (xs, env, s) = (Rval vs, t) ⇒
    evaluate (xs, env ++ extra, s) = (Rval vs, t)
Proof
  recInduct bviSemTheory.evaluate_ind
  >> rpt strip_tac
  >~ [‘evaluate ([],_,_)’] >-
   (gvs [evaluate_def])
  >~ [‘evaluate (x::y::xs,_,_)’] >-
   (cheat)
  >> cheat
QED

(* This could probably be combined with the above *)
Theorem evaluate_pad_env_err:
  ∀xs env s t e extra.
    evaluate (xs, env, s) = (Rerr e, t) ∧
    e ≠ Rabort Rtype_error ⇒
    evaluate (xs, env ++ extra, s) = (Rerr e, t)
Proof
  cheat
QED

Theorem do_app_rewrite_tmc:
  ∀f op vs vs' s s' r.
    bviSem$do_app op (REVERSE vs) s = r ∧
    LIST_REL (v_rel f) vs vs' ∧
    state_rel f s s' ∧
    r ≠ Rerr (Rabort Rtype_error) ⇒
    ∃r' f'.
      bviSem$do_app op (REVERSE vs') s' = r' ∧
      result_rel (PAIR_REL (v_rel f') (state_rel f')) (v_rel f') r r' ∧
      f SUBMAP f'
Proof
  rw [] >> cheat
QED

Theorem state_rel_do_app_aux:
  ∀f op vs vs' s s' t r.
    do_app_aux op vs s = r ∧
    LIST_REL (v_rel f) vs vs' ∧
    state_rel f s s' ∧
    op ≠ Install ∧
    (∀n. op ≠ Label n) ⇒
    ∃r' f' t'.
      do_app_aux op vs' s' = r' ∧
      state_rel f' t t' ∧
      f SUBMAP f'
Proof
  cheat
QED

Theorem state_rel_do_app:
  ∀f op vs vs' s s' t r.
    do_app op vs s = Rval (r,t) ∧
    LIST_REL (v_rel f) vs vs' ∧
    state_rel f s s' ∧
    op ≠ Install ∧
    (∀n. op ≠ Label n) ⇒
    ∃r' f' t'.
      do_app op vs' s' = Rval (r',t') ∧
      state_rel f' t t' ∧
      f SUBMAP f'
Proof
  rw [do_app_def]
  >> imp_res_tac state_rel_do_app_aux
  >> gvs []
  >> gvs [case_eq_thms]
  >> cheat
QED

Definition hole_has_val_def:
  hole_has_val (f : num |-> num) (env1 : v list) (env2 : v list) (refs : num |-> v ref) c =
  ∃hole_ptr tag left right.
    env2❲LENGTH env1❳ = RefPtr F hole_ptr ∧
    env2❲LENGTH env1 + 1❳ = Number (&LENGTH left) ∧
    hole_ptr ∉ FRANGE f ∧
    FLOOKUP refs hole_ptr = SOME (MutBlock tag left c right)
End

Definition holes_unchanged_except_def:
  holes_unchanged_except f refs refs' changed ⇔
    ∀ptr val.
      ptr ∉ FRANGE f ∧
      (∀b. RefPtr b ptr ∉ changed) ∧
      FLOOKUP refs ptr = SOME val ⇒
      FLOOKUP refs' ptr = SOME val
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
  >> first_x_assum $ qspecl_then [‘ptr’, ‘val’] mp_tac
  >> strip_tac
  >> gvs []
  >> pop_assum irule
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
  >> rpt $ first_x_assum $ qspecl_then [‘ptr’, ‘val’] mp_tac
  >> rpt strip_tac
  >> gvs []
  >> first_x_assum irule
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
  >> first_x_assum irule
  >> gvs []
  >> gen_tac
  >> first_x_assum $ qspec_then ‘b’ mp_tac
  >> strip_tac
  >> gvs [SUBSET_DEF]
  >> first_x_assum $ qspec_then ‘RefPtr b ptr’ mp_tac
  >> strip_tac
  >> gvs []
QED

Theorem holes_unchanged_except_filled:
  ∀f refs refs' k v b.
    holes_unchanged_except f refs refs' ∅ ⇒
    holes_unchanged_except f refs refs'⟨k ↦ v⟩ {RefPtr b k}
Proof
  rw [holes_unchanged_except_def] >> gvs [FLOOKUP_SIMP]
QED

Theorem unchanged_hole_has_val:
  ∀f f' env env' hole_ptr hole_idx refs refs' c changed.
    hole_has_val f env (env' ++ [RefPtr F hole_ptr; Number hole_idx]) refs c ∧
    only_fresh f f' refs ∧
    holes_unchanged_except f refs refs' changed ∧
    env_rel T f env (env' ++ [RefPtr F hole_ptr; Number hole_idx]) ∧
    (∀b. RefPtr b hole_ptr ∉ changed) ⇒
    hole_has_val f' env (env' ++ [RefPtr F hole_ptr; Number hole_idx]) refs' c
Proof
  rw [hole_has_val_def]
  >> drule env_rel_length_opt
  >> strip_tac
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

Theorem do_app_aux_rel:
  ∀f op vs vs' s s' v.
    do_app_aux op vs s = v ∧
    LIST_REL (v_rel f) vs vs' ∧
    state_rel f s s' ⇒
    ∃v'.
      do_app_aux op vs' s' = v' ∧
      OPTREL (OPTREL (PAIR_REL (v_rel f) (state_rel f))) v v'
Proof
  rw []
  >> simp [Once do_app_aux_def]
  >> Cases_on ‘do_app_aux op vs s’ >> gvs []
  >-
   (Cases_on ‘op’ >> gvs [do_app_aux_def]
    >-
     (Cases_on ‘vs’ >> gvs []
      >> gvs [state_rel_def]
      >> first_x_assum $ qspec_then ‘n’ mp_tac
      >> strip_tac
      >> spose_not_then assume_tac
      >> cheat)
    >> cheat)
  >> cheat
QED

Theorem do_app_op_rel:
  ∀f op vs vs' s s' v.
    do_app op vs s = Rval v ∧
    LIST_REL (v_rel f) vs vs' ∧
    state_rel f s s' ⇒
    ∃v'.
      do_app op vs' s' = Rval v' ∧
      PAIR_REL (v_rel f) (state_rel f) v v'
Proof
  rw [do_app_def]
  >- cheat
  >> Cases_on ‘∃i. op = IntOp i’
  >-
   (gvs []
    >> Cases_on ‘i’ >> gvs []
    >> gvs [do_app_aux_def, bvlSemTheory.do_app_def, AllCaseEqs ()]
    >> imp_res_tac LIST_REL_LENGTH
    >> cheat)
  >> cheat
QED

(* This could be unified with non err case using res_rel *)
Theorem do_app_op_err_rel:
  do_app (FFI i) vs u = Rerr (Rabort (Rffi_error e)) ∧
  state_rel f u u' ∧
  LIST_REL (v_rel f) vs vs' ⇒
  do_app (FFI i) vs' u' = Rerr (Rabort (Rffi_error e))
Proof
  rw [do_app_def]
  >> Cases_on ‘do_app_aux (FFI i) vs u’ >> gvs []
  >> drule do_app_aux_rel
  >> disch_then drule
  >> disch_then drule
  >> strip_tac
  >> gvs []
  >> Cases_on ‘do_app_aux (FFI i) vs' u'’ >> gvs []
  >> reverse $ Cases_on ‘x’ >> gvs []
  >- (Cases_on ‘x''’ >> gvs [])
  >> Cases_on ‘bvlSem$do_app (FFI i) vs (bvi_to_bvl u)’ >> gvs []
  >- (Cases_on ‘a’ >> gvs [])
  >> Cases_on ‘bvlSem$do_app (FFI i) vs' (bvi_to_bvl u')’ >> gvs []
  >> cheat
QED

Theorem do_app_holes_unchanged:
  ∀f s t u changed vs v t op.
    holes_unchanged_except f s.refs t.refs changed ∧
    do_app op vs t = Rval (v,u) ⇒
    holes_unchanged_except f s.refs u.refs changed
Proof
  rw [holes_unchanged_except_def]
  >> gvs [do_app_def]
  >> Cases_on ‘op’ >> gvs []
  >> cheat
QED

Theorem wrapper_strip_if_then:
  rewrite_wrapper loc loc_opt arity (If x1 x2 x3) = SOME w ⇒
  ∃w2 w3.
    w = If x1 w2 w3 ∧
    (rewrite_wrapper loc loc_opt arity x2 = SOME w2 ∨
     w2 = x2)
Proof
  rw []
  >> gvs [rewrite_wrapper_def]
  >> Cases_on ‘rewrite_wrapper loc loc_opt arity x2’
  >> Cases_on ‘rewrite_wrapper loc loc_opt arity x3’
  >> gvs []
QED

Theorem wrapper_strip_if_else:
  rewrite_wrapper loc loc_opt arity (If x1 x2 x3) = SOME w ⇒
  ∃w2 w3.
    w = If x1 w2 w3 ∧
    (rewrite_wrapper loc loc_opt arity x3 = SOME w3 ∨
     w3 = x3)
Proof
  rw []
  >> gvs [rewrite_wrapper_def]
  >> Cases_on ‘rewrite_wrapper loc loc_opt arity x2’
  >> Cases_on ‘rewrite_wrapper loc loc_opt arity x3’
  >> gvs []
QED

Theorem wrapper_strip_let:
  ∀loc loc_opt arity xs x w.
    rewrite_wrapper loc loc_opt arity (Let xs x) = SOME w ⇒
    ∃w'.
      w = Let xs w' ∧
      rewrite_wrapper loc loc_opt (arity + LENGTH xs) x = SOME w'
Proof
  rw []
  >> gvs [rewrite_wrapper_def]
  >> Cases_on ‘rewrite_wrapper loc loc_opt (arity + LENGTH xs) x’
  >> gvs []
QED

Theorem wrapper_strip_tick:
  ∀loc loc_opt arity x w.
    rewrite_wrapper loc loc_opt arity (Tick x) = SOME w ⇒
    ∃w'.
      w = Tick w' ∧
      rewrite_wrapper loc loc_opt arity x = SOME w'
Proof
  rw [] >> gvs [rewrite_wrapper_def]
QED

Definition is_block_op_cons_def:
  is_block_op_cons op ⇔
    ∃block_tag.
      op = BlockOp (Cons block_tag)
End

(* This was copied from bvlPropsScript but I don't see it for bviPropsScript. Consider putting it there *)
Theorem evaluate_refs_SUBSET:
  (evaluate (xs,env,s) = (res,t)) ==> FDOM s.refs SUBSET FDOM t.refs
Proof
  cheat
QED

Theorem evaluate_err:
  evaluate (xs,env,s) = (Rerr e,t) ⇒
  ∃l x r v u.
    xs = l ++ [x] ++ r ∧
    evaluate (l, env,s) = (Rval v,u) ∧
    evaluate ([x],env,u) = (Rerr e,t)
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

Theorem find_code_rel:
  ∀f vs vs' s s' dest args exp.
    find_code dest vs s.code = SOME (args,exp) ∧
    LIST_REL (v_rel f) vs vs' ∧
    state_rel f s s' ⇒
    ∃args' exp' opt.
      opt = (exp ≠ exp') ∧
      find_code dest vs' s'.code = SOME (args',exp') ∧
      env_rel F f args args' ∧
      LENGTH args = LENGTH args' ∧
      (opt ⇒
       ∃loc loc_opt i extras.
         rewrite_wrapper loc loc_opt i exp = SOME exp' ∧
         env_rel T f args (args' ++ extras))
Proof
  rw []
  >> drule LIST_REL_LENGTH
  >> strip_tac
  >> gvs []
  >> Cases_on ‘dest’ >> gvs [bvlSemTheory.find_code_def]
  >-
   (Cases_on ‘vs' = []’ >> gvs []
    >> Cases_on ‘LAST vs’ >> gvs []
    >> Cases_on ‘LAST vs'’ >> gvs []
    >> drule_all list_rel_last
    >> strip_tac
    >> gvs [v_rel_cases]
    >> Cases_on ‘lookup n s.code’ >> gvs []
    >> Cases_on ‘x’ >> gvs []
    >> rename [‘lookup n s.code = SOME (arity,exp)’]
    >> drule list_rel_front
    >> strip_tac
    >> drule list_rel_env_rel
    >> disch_then $ irule_at Any
    >> drule LIST_REL_LENGTH
    >> strip_tac
    >> gvs []
    >> gvs [state_rel_def, code_rel_def]
    >> last_x_assum drule
    >> strip_tac
    >> Cases_on ‘compile_exp n n' arity exp’ >> gvs []
    >> Cases_on ‘x’ >> gvs []
    >> rename [‘compile_exp n n' arity exp = SOME (exp_wrap, exp_work)’]
    >> strip_tac
    >> gvs [compile_exp_def]
    >> Cases_on ‘rewrite_wrapper n n' arity exp’ >> gvs []
    >> pop_assum $ irule_at Any
    >> gvs [env_rel_def]
    >> first_assum $ irule_at $ Pos $ el 2
    >> gvs []
    >> qexists ‘[RefPtr F hole_ptr; Number hole_idx]’
    >> gvs [])
  >> Cases_on ‘lookup x s.code’ >> gvs []
  >> Cases_on ‘x'’ >> gvs [state_rel_def, code_rel_def]
  >> rename [‘lookup n s.code = SOME (LENGTH args, exp)’]
  >> irule_at Any list_rel_env_rel
  >> gvs []
  >> last_x_assum drule
  >> strip_tac
  >> Cases_on ‘compile_exp n n' (LENGTH args) exp’ >> gvs []
  >> Cases_on ‘x’ >> gvs []
  >> rename [‘compile_exp n n' (LENGTH args) exp = SOME (exp_wrap,exp_work)’]
  >> strip_tac
  >> gvs [compile_exp_def]
  >> Cases_on ‘rewrite_wrapper n n' (LENGTH args) exp’ >> gvs []
  >> pop_assum $ irule_at Any
  >> gvs [env_rel_def]
  >> first_assum $ irule_at $ Pos $ el 2
  >> gvs []
  >> qexists ‘[RefPtr F hole_ptr; Number hole_idx]’
  >> gvs []
QED

Theorem evaluate_fill_hole:
  ∀exp f f' env1 env2 v s t s' t' c.
    evaluate ([exp],env2,s') = (Rval [v],t') ∧
    env_rel T f env1 env2 ∧
    state_rel f s s' ∧
    f ⊑ f' ∧
    hole_has_val f env1 env2 s'.refs c ∧
    holes_unchanged_except f s'.refs t'.refs ∅ ∧
    only_fresh f f' s'.refs ∧
    state_rel f' t t' ⇒
    ∃r t''.
      evaluate ([fill_hole (LENGTH env1) (LENGTH env1 + 1) exp],env2,s') = (r,t'') ∧
      opt_res_rel (Rval [v]) r ∧
      state_rel f' t t'' ∧
      holes_unchanged_except f s'.refs t''.refs {env2❲LENGTH env1❳} ∧
      hole_has_val f env1 env2 t''.refs v
Proof
  rw []
  >> drule env_rel_length_opt
  >> strip_tac
  >> drule env_rel_extras_opt
  >> strip_tac
  >> gvs [evaluate_def, fill_hole_def, do_app_def, do_app_aux_def, hole_has_val_def, holes_unchanged_except_def,
          case_eq_thms, PULL_EXISTS, FLOOKUP_SIMP, bvlSemTheory.Unit_def, backend_commonTheory.tuple_tag_def, opt_res_rel_def]
  >> first_x_assum $ drule_all
  >> strip_tac
  >> gvs []
  >> conj_tac
  >-
   (irule state_rel_filled
    >> gvs []
    >> irule non_fresh_not_in_frange
    >> first_assum $ irule_at Any
    >> gvs [FLOOKUP_DEF])
  >> metis_tac []
QED

Theorem evaluate_fill_hole_err:
  ∀exp f f' env1 env2 e s t s' t' c.
    evaluate ([exp],env2,s') = (Rerr e,t') ∧
    env_rel T f env1 env2 ∧
    state_rel f s s' ∧
    f ⊑ f' ∧
    hole_has_val f env1 env2 s'.refs c ∧
    holes_unchanged_except f s'.refs t'.refs ∅ ∧
    only_fresh f f' s'.refs ∧
    state_rel f' t t' ⇒
    ∃r t''.
      evaluate ([fill_hole (LENGTH env1) (LENGTH env1 + 1) exp],env2,s') = (r,t'') ∧
      opt_res_rel (Rerr e) r ∧
      state_rel f' t t'' ∧
      holes_unchanged_except f s'.refs t''.refs {env2❲LENGTH env1❳}
Proof
  rw []
  >> drule env_rel_length_opt
  >> strip_tac
  >> drule env_rel_extras_opt
  >> strip_tac
  >> gvs [fill_hole_def, evaluate_def]
  >> gvs [evaluate_def, fill_hole_def, do_app_def, do_app_aux_def, hole_has_val_def, holes_unchanged_except_def,
          case_eq_thms, PULL_EXISTS, FLOOKUP_SIMP, bvlSemTheory.Unit_def, backend_commonTheory.tuple_tag_def, opt_res_rel_def]
QED

(* BVI props? *)
Theorem evaluate_clock_non_increase:
  ∀xs env s r t.
    evaluate (xs,env,s) = (r,t) ⇒
    t.clock ≤ s.clock
Proof
  recInduct bviSemTheory.evaluate_ind
  >> rw [evaluate_def]
  >-
   (gvs [CaseEq "prod"]
    >> rename [‘evaluate ([x],env,s) = (rx,u)’]
    >> Cases_on ‘rx’ >> gvs []
    >> gvs [CaseEq "prod"]
    >> rename [‘evaluate (y::xs,env,u) = (ry,w)’]
    >> Cases_on ‘ry’ >> gvs [])
  >> cheat
QED

Theorem WF_I_I[local]:
  WF (measure I LEX measure I)
Proof
  irule WF_LEX >> simp [prim_recTheory.WF_measure]
QED

Theorem evaluate_rewrite_tmc:
  ∀n xs ^s env1 r t opt f s' env2.
    evaluate (xs, env1, s) = (r, t) ∧
    n = (s.clock, list_size exp_size xs) ∧
    env_rel opt f env1 env2 ∧
    state_rel f s s' ∧
    (opt ⇒ LENGTH xs = 1) ∧
    r ≠ Rerr (Rabort Rtype_error) ⇒
    ∃t' f' r'.
      evaluate (xs, env2, s') = (r', t') ∧
      result_rel (LIST_REL (v_rel f')) (v_rel f') r r' ∧
      state_rel f' t t' ∧
      f SUBMAP f' ∧
      only_fresh f f' s'.refs ∧
      holes_unchanged_except f s'.refs t'.refs ∅ ∧
      (opt ⇒
       (∀loc loc_opt arity wrap work.
          rewrite_wrapper loc loc_opt arity (HD xs) = SOME wrap ⇒
          ∃t1.
            evaluate ([wrap], env2, s') = (r',t1) ∧
            state_rel f' t t1) ∧
       (∀loc loc_opt i j wrap work.
          i = LENGTH env1 ∧
          j = LENGTH env1 + 1 ∧
          (∃c. hole_has_val f env1 env2 s'.refs c) ∧
          rewrite_worker loc loc_opt i j (HD xs) = work ⇒
          ∃rrr t2.
            evaluate ([work], env2, s') = (rrr,t2) ∧
            opt_res_rel r' rrr ∧
            state_rel f' t t2 ∧
            holes_unchanged_except f s'.refs t2.refs {EL i env2} ∧
            ∀res_v.
              r' = Rval [res_v] ⇒
              hole_has_val f env1 env2 t2.refs res_v))
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
  >> Cases_on ‘h’
  >~ [‘Var n’] >- suspend "var"
  >~ [‘If x1 x2 x3’] >- suspend "if"
  >~ [‘Let xs x2’] >- suspend "lett"
  >~ [‘Raise x’] >- suspend "raise"
  >~ [‘Op op xs’] >- suspend "op"
  >~ [‘Tick x’] >- suspend "tick"
  >~ [‘Force force_loc n’] >- suspend "force"
  >~ [‘Call ticks dest xs handler’] >- suspend "call"
QED

Resume evaluate_rewrite_tmc[list]:
  gvs [evaluate_def]
  (* First inductive hypothesis *)
  >> gvs [CaseEq "prod", PULL_EXISTS]
  >> rename[‘evaluate ([x],env,s) = (rx,u)’]
  >> first_assum $ qspecl_then [‘[x]’, ‘s’, ‘env’] mp_tac
  >> gvs []
  >> disch_then drule
  >> disch_then drule
  >> impl_tac
  >- (spose_not_then assume_tac >> fs [])
  >> strip_tac
  >> gvs []
  >> rename [‘evaluate ([x],env2,s') = (rx',u')’]
  >> reverse $ Cases_on ‘rx’ >> gvs []
  >- (first_x_assum $ irule_at Any >> fs [])
  (* Second inductive hypothesis *)
  >> gvs [CaseEq "prod", PULL_EXISTS]
  >> qpat_x_assum ‘_ = _’ mp_tac
  >> rename [‘evaluate (y::xs,env,u) = (ry,w)’]
  >> strip_tac
  >> rename [‘LIST_REL (v_rel f'') vx vx'’]
  >> first_x_assum $ qspecl_then [‘y::xs’, ‘u’, ‘env’] mp_tac
  >> gvs []
  >> imp_res_tac evaluate_clock_non_increase
  >> gvs []
  >> drule_all env_rel_submap
  >> strip_tac
  >> disch_then drule
  >> disch_then drule
  >> gvs []
  >> impl_tac
  >- (spose_not_then assume_tac >> fs [])
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
  >> ho_match_mp_tac evaluate_fill_hole
  >> gvs [evaluate_def]
  >> rpt $ first_assum $ irule_at Any
QED

Resume evaluate_rewrite_tmc[if]:
  gvs [evaluate_def]
  >> gvs [CaseEq "prod", PULL_EXISTS]
  >> rename [‘evaluate ([x1],env,s) = (r1,u)’]
  (* First inductive hypothesis *)
  >> first_assum $ qspecl_then [‘[x1]’,‘s’,‘env’] mp_tac
  >> gvs []
  >> disch_then $ qspec_then ‘F’ mp_tac
  >> disch_then $ drule_at $ Pos $ el 2
  >> drule env_rel_relax_opt
  >> strip_tac
  >> gvs []
  >> disch_then drule
  >> Cases_on ‘r1’ >> gvs []
  >-
   (strip_tac
    >> imp_res_tac evaluate_SING_IMP
    >> gvs []
    >> rename [‘state_rel f' u u'’]
    >> rename [‘v_rel f' v1 v1'’]
    >> Cases_on ‘v1 = Boolv T’ >> gvs []
    >- (* Then inductive hypothesis *)
     (‘v1' = Boolv T’ by (drule $ iffLR v_rel_cases >> gvs [bvlSemTheory.Boolv_def])
      >> gvs []
      >> first_x_assum $ qspecl_then [‘[x2]’, ‘u’, ‘env’] mp_tac
      >> imp_res_tac evaluate_clock_non_increase
      >> gvs []
      >> qpat_x_assum ‘env_rel F _ _ _’ kall_tac
      >> drule_all env_rel_submap
      >> strip_tac
      >> disch_then drule
      >> disch_then drule
      >> strip_tac
      >> qexistsl [‘t''’, ‘f'³'’, ‘r''’]
      >> gvs []
      >> rpt gen_tac
      >> fs[GSYM PULL_FORALL]
      >> strip_tac
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
      >> strip_tac
      >> gvs []
      >> conj_tac
      >-
       (strip_tac
        >> drule wrapper_strip_if_then
        >> strip_tac >> gvs [evaluate_def]
        >> first_x_assum $ qspecl_then [‘loc’, ‘loc_opt’, ‘arity’, ‘w2’] mp_tac
        >> gvs [])
      >> rw []
      >> first_x_assum $ qspecl_then [‘loc'’, ‘loc_opt'’, ‘c’] mp_tac
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
      >> drule_all env_rel_length_opt
      >> strip_tac
      >> gvs [EL_APPEND_EQN]
      >> conj_tac
      >-
       (irule holes_unchanged_except_trans
        >> first_assum $ irule_at Any
        >> gvs [holes_unchanged_except_def])
      >> rw []
      >> irule hole_has_val_submap
      >> first_assum $ irule_at Any
      >> gvs [])
    (* Else inductive hypothesis *)
    >> Cases_on ‘v1 = Boolv F’ >> gvs []
    >> ‘v1' = Boolv F’ by (drule $ iffLR v_rel_cases >> gvs [bvlSemTheory.Boolv_def])
    >> gvs []
    >> first_x_assum $ qspecl_then [‘[x3]’, ‘u’, ‘env’] mp_tac
    >> imp_res_tac evaluate_clock_non_increase
    >> gvs []
    >> qpat_x_assum ‘env_rel F _ _ _’ kall_tac
    >> drule_all env_rel_submap
    >> strip_tac
    >> disch_then drule
    >> disch_then drule
    >> strip_tac
    >> qexistsl [‘t''’, ‘f'³'’, ‘r''’]
    >> gvs []
    >> rpt gen_tac
    >> fs[GSYM PULL_FORALL]
    >> strip_tac
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
    >> strip_tac
    >> gvs []
    >> conj_tac
    >-
     (strip_tac
      >> drule wrapper_strip_if_else
      >> strip_tac >> gvs [evaluate_def]
      >> first_x_assum $ qspecl_then [‘loc’, ‘loc_opt’, ‘arity’, ‘w3’] mp_tac
      >> gvs [])
    >> rw []
    >> first_x_assum $ qspecl_then [‘loc'’, ‘loc_opt'’, ‘c’] mp_tac
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
    >> drule_all env_rel_length_opt
    >> strip_tac
    >> gvs [EL_APPEND_EQN]
    >> conj_tac
    >-
     (irule holes_unchanged_except_trans
      >> first_assum $ irule_at Any
      >> gvs [holes_unchanged_except_def])
    >> rw []
    >> irule hole_has_val_submap
    >> first_assum $ irule_at Any
    >> gvs [])
  (* Error case *)
  >> strip_tac
  >> rename [‘evaluate ([x1],env2,s') = (r1',u')’]
  >> gvs []
  >> ‘e' ≠ Rabort Rtype_error’ by (spose_not_then assume_tac >> gvs [])
  >> gvs [GSYM PULL_FORALL]
  >> first_assum $ irule_at Any
  >> gvs []
  >> rw []
  >-
   (drule wrapper_strip_if_then
    >> strip_tac
    >> gvs [evaluate_def])
  >> gvs [rewrite_worker_def, evaluate_def, opt_res_rel_def, holes_unchanged_except_def]
QED

Resume evaluate_rewrite_tmc[lett]:
  gvs [evaluate_def]
  >> gvs [CaseEq "prod", PULL_EXISTS]
  >> rename [‘evaluate (xs,env,s) = (rs,u)’]
  (* First inductive hypothesis *)
  >> first_x_assum $ qspec_then ‘F’ mp_tac
  >> simp []
  >> disch_then $ drule_at $ Pos $ el 2
  >> drule env_rel_relax_opt
  >> strip_tac
  >> gvs []
  >> rename [‘env_rel F f env env2’]
  >> disch_then drule
  >> Cases_on ‘rs’ >> gvs []
  >-
   (rename [‘evaluate (xs,env,s) = (Rval vs,u)’]
    >> strip_tac
    >> rename [‘evaluate (xs, env2, s') = (rs', u')’]
    >> rename [‘LIST_REL (v_rel f') vs vs'’]
    (* Second inductive hypothesis *)
    >> first_x_assum $ qspec_then ‘opt’ mp_tac
    >> gvs []
    >> disch_then $ drule_at $ Pos $ el 2
    >> disch_then $ qspec_then ‘vs' ++ env2’ mp_tac
    >> impl_tac
    >-
     (irule env_rel_append
      >> gvs []
      >> irule env_rel_submap
      >> first_assum $ irule_at Any
      >> gvs [])
    >> strip_tac
    >> drule evaluate_pad_env_val
    >> disch_then $ qspec_then ‘[RefPtr F hole_ptr; Number hole_idx]’ mp_tac
    >> gvs []
    >> strip_tac
    >> qexists ‘f'³'’
    >> gvs []
    >> rw [] >> gvs []
    >- imp_res_tac SUBMAP_TRANS
    >-
     (irule only_fresh_trans
      >> rpt $ goal_assum $ drule_at Any
      >> irule evaluate_refs_SUBSET
      >> rpt $ goal_assum $ drule_at Any)
    >-
     (irule holes_unchanged_except_trans
      >> first_assum $ irule_at Any
      >> gvs [])
    >-
     (drule wrapper_strip_let
      >> strip_tac
      >> last_x_assum drule
      >> strip_tac
      >> gvs [evaluate_def])
    >> first_x_assum $ qspecl_then [‘loc’, ‘loc_opt’, ‘c’] mp_tac
    >> impl_tac
    >-
     (irule hole_has_val_append
      >> gvs []
      >> drule_all env_rel_strip_extras
      >> strip_tac
      >> gvs []
      >> irule unchanged_hole_has_val
      >> first_assum $ irule_at Any
      >> gvs [])
    >> strip_tac
    >> rev_drule evaluate_IMP_LENGTH
    >> gvs [rewrite_worker_def, evaluate_def]
    >> strip_tac
    >> drule_all env_rel_length_opt
    >> strip_tac
    >> drule LIST_REL_LENGTH
    >> strip_tac
    >> gvs [EL_APPEND_EQN]
    >> conj_tac
    >-
     (irule holes_unchanged_except_trans
      >> first_x_assum $ irule_at Any
      >> gvs [holes_unchanged_except_def])
    >> rw []
    >> irule hole_has_val_submap
    >> first_assum $ irule_at Any
    >> irule hole_has_val_unappend
    >> first_assum $ irule_at Any
    >> gvs [])
  >> strip_tac
  >> rename [‘evaluate (xs,env2,s') = (r',t')’]
  >> gvs []
  >> ‘e' ≠ Rabort Rtype_error’ by (spose_not_then assume_tac >> gvs [])
  >> drule_all evaluate_pad_env_err
  >> strip_tac
  >> gvs []
  >> goal_assum $ drule_at Any
  >> gvs []
  >> rw []
  >- (drule wrapper_strip_let
      >> strip_tac
      >> gvs [evaluate_def])
  >> gvs [rewrite_worker_def, evaluate_def, opt_res_rel_def]
  >> gvs [holes_unchanged_except_def]
QED

Resume evaluate_rewrite_tmc[raise]:
  gvs [evaluate_def]
  >> gvs [CaseEq "prod", PULL_EXISTS]
  >> rename [‘evaluate ([x],env,s) = (v,u)’]
  >> Cases_on ‘opt’ >> gvs[]
  >-
   (first_x_assum $ qspec_then ‘T’ mp_tac
    >> disch_then drule
    >> disch_then drule
    >> impl_tac >> gvs []
    >- (Cases_on ‘v’ >> gvs [] >> qexists ‘c’ >> gvs [])
    >> strip_tac
    >> rename [‘evaluate ([x],env2,s') = (v',u')’]
    >> goal_assum $ drule_at Any
    >> goal_assum $ drule_at Any
    >> Cases_on ‘v’
    >> gvs [rewrite_wrapper_def, rewrite_worker_def, evaluate_def, opt_res_rel_def]
    >> imp_res_tac evaluate_SING_IMP
    >> gvs [holes_unchanged_except_def])
  >> first_x_assum $ qspec_then ‘F’ mp_tac
  >> gvs []
  >> disch_then drule
  >> disch_then drule
  >> impl_tac
  >- (Cases_on ‘v’ >> gvs [])
  >> strip_tac
  >> rename [‘evaluate ([x],env2,s') = (v',u')’]
  >> rpt $ goal_assum $ drule_at Any
  >> Cases_on ‘v’ >> gvs []
  >> imp_res_tac evaluate_SING_IMP
  >> gvs []
QED

Resume evaluate_rewrite_tmc[op]:

  gvs [evaluate_def]
  >> gvs [CaseEq "prod", PULL_EXISTS]
  >> rename [‘evaluate (xs,env,s) = (rs,u)’]
  >> first_assum $ qspecl_then [‘xs’, ‘s’, ‘env’] mp_tac
  >> gvs []
  >> disch_then $ qspec_then ‘F’ mp_tac
  >> drule_all env_rel_relax_opt
  >> strip_tac
  >> disch_then drule
  >> disch_then drule
  >> gvs []
  >> impl_tac
  >- (spose_not_then assume_tac >> gvs [])
  >> strip_tac
  >> gvs [GSYM PULL_FORALL]
  >> rename [‘evaluate (xs,env2,s') = (rs',u')’]
  >> qpat_assum ‘f ⊑ _’ $ irule_at Any
  >> reverse $ Cases_on ‘rs’ >> gvs []
  >- (* Error evaluating args *)
   (rename [‘evaluate (xs,env2,s') = (Rerr e',t')’]
    >> strip_tac
    >> gvs []
    >> conj_tac
    >-
     (rw []
      >> gvs [rewrite_wrapper_def]
      >> gvs [CaseEq "option"]
      >> rename [‘dest_Cons op = SOME tag’]
      >> ‘op = BlockOp (Cons tag)’ by
        (spose_not_then assume_tac
         >> Cases_on ‘op’ >> gvs [dest_Cons_def]
         >> Cases_on ‘b’ >> gvs [dest_Cons_def])
      >> gvs [rewrite_wrapper_cons_def]
      >> gvs [CaseEq "option", CaseEq "prod"]
      >> rename [‘cb_to_hb cb = (hb,call_ts,call_args)’]
      >> ‘evaluate ([Op (BlockOp (Cons tag)) xs],env,s) = (Rerr e,t)’ by gvs [evaluate_def]
      >> drule evaluate_bvi_to_cb
      >> disch_then drule
      >> gvs []
      >> strip_tac
      >> gvs [evaluate_def]
      (* Hypothesis on bs *)
      >> first_assum $ qspecl_then [‘bs’, ‘s’] mp_tac
      >> gvs []
      >> impl_tac
      >- (imp_res_tac bvi_to_cb_size >> gvs [])
      >> disch_then drule
      >> disch_then drule
      >> disch_then drule
      >> gvs []
      >> strip_tac
      >> gvs []
      >> rename [‘f ⊑ f''’]
      >> cheat)
    >> rw []
    >> gvs [rewrite_worker_def, evaluate_def]
    >> CASE_TAC >> gvs []
    >-
     (gvs [evaluate_def, fill_hole_def, opt_res_rel_def]
      >> irule holes_unchanged_except_subset
      >> first_assum $ irule_at Any
      >> gvs [])
    >> gvs [evaluate_def, rewrite_worker_cons_def]
    >> CASE_TAC >> gvs []
    >-
     (gvs [evaluate_def, fill_hole_def, opt_res_rel_def]
      >> irule holes_unchanged_except_subset
      >> first_assum $ irule_at Any
      >> gvs [])
    >> cheat)
  >> rename [‘LIST_REL (v_rel f'') vs vs'’]
  >> reverse $ Cases_on ‘do_app op (REVERSE vs) u’ >> gvs []
  >- (* FFI *)
   (drule do_app_err
    >> strip_tac >> gvs []
    >> rename [‘do_app (FFI i) (REVERSE vs) u = Rerr (Rabort (Rffi_error e))’]
    >> drule do_app_op_err_rel
    >> disch_then $ qspecl_then [‘REVERSE vs'’, ‘u'’, ‘f''’] mp_tac
    >> disch_then drule
    >> drule $ iffLR list_rel_reverse
    >> gvs []
    >> strip_tac
    >> strip_tac
    >> conj_tac
    >-
     (rw []
      >> cheat)
    >> gvs []
    >> rpt gen_tac
    >> strip_tac
    >> gvs [rewrite_worker_def, dest_Cons_def]
    >> ho_match_mp_tac evaluate_fill_hole_err
    >> gvs [evaluate_def]
    >> rpt $ first_assum $ irule_at Any)
  >> rename [‘do_app op (REVERSE vs) u = Rval v’]
  >> drule $ iffLR list_rel_reverse
  >> strip_tac
  >> drule_all do_app_op_rel
  >> strip_tac
  >> gvs []
  >> Cases_on ‘v’ >> gvs []
  >> Cases_on ‘v'’ >> gvs []
  >> rename [‘v_rel f' v v'’]
  >> rename [‘state_rel f' t t'’]
  >> conj_asm1_tac
  >-
   (irule do_app_holes_unchanged
    >> first_assum $ irule_at Any
    >> gvs [])
  >> strip_tac
  >> gvs []
  >> conj_tac
  >-
   (cheat)
  >> rw []
  >> gvs [rewrite_worker_def]
  >> CASE_TAC >> gvs []
  >-
   (ho_match_mp_tac evaluate_fill_hole
    >> gvs [evaluate_def]
    >> rpt $ first_assum $ irule_at Any)
  (* Cons *)
  >> rename [‘dest_Cons op = SOME tag’]
  >> ‘op = BlockOp (Cons tag)’ by
    (spose_not_then assume_tac
     >> Cases_on ‘op’ >> gvs [dest_Cons_def]
     >> Cases_on ‘b’ >> gvs [dest_Cons_def])
  >> gvs [rewrite_worker_cons_def]
  >> CASE_TAC >> gvs []
  >-
   (ho_match_mp_tac evaluate_fill_hole
    >> gvs [evaluate_def]
    >> rpt $ first_assum $ irule_at Any)

    (* Move? *)
  >> Cases_on ‘x’ >> gvs []
  >> rename [‘bvi_to_cb loc tag args = SOME (bs,cb)’]
  (* Phase 1 theorem in s *)
  >> ‘evaluate ([Op (BlockOp (Cons tag)) args],env,s) = (Rval [v],t)’ by gvs [evaluate_def]
  >> drule evaluate_bvi_to_cb
  >> disch_then drule
  >> gvs []
  >> strip_tac
  >> CASE_TAC
  >> CASE_TAC
  >> rename [‘cb_to_hb cb = (hb,call_ts,call_args)’]
  >> gvs [evaluate_def]
  >> Cases_on ‘rs’ >> gvs []
  >> rename [‘evaluate (bs,env,s) = (Rval as,s)’]
  (* Phase 1 theorem in s' *)
  >> ‘evaluate ([Op (BlockOp (Cons tag)) args],env2,s') = (Rval [v'],t')’ by gvs [evaluate_def]
  >> drule evaluate_bvi_to_cb
  >> disch_then drule
  >> gvs []
  >> strip_tac
  >> gvs []
  >> reverse CASE_TAC
  >- (first_x_assum $ qspec_then ‘e’ assume_tac >> gvs [])
  >> qpat_x_assum ‘∀e. Rval a ≠ Rerr e’ kall_tac
  >> rename [‘evaluate (bs,env2,s') = (Rval as',s')’]
  >> first_x_assum $ qspec_then ‘as'’ assume_tac
  >> gvs []
  (* Hypothesis on bs *)
  >> first_assum $ qspecl_then [‘bs’, ‘s’] mp_tac
  >> gvs []
  >> impl_tac
  >- (imp_res_tac bvi_to_cb_size >> gvs [])
  >> disch_then drule
  >> disch_then drule
  >> disch_then drule
  >> gvs []
  >> strip_tac
  >> gvs []
  >> rename [‘f ⊑ f''’]
  (* Experimental - unify maps *)
  >> rev_drule state_rel_unique_map
  >> disch_then drule
  >> strip_tac
  >> gvs []
  (* Hypothesis on cb_to_bvi loc cb *)
  >> first_assum $ qspecl_then [‘[cb_to_bvi loc cb]’, ‘s’] mp_tac
  >> impl_tac
  >-
   (imp_res_tac evaluate_clock_non_increase
    >> imp_res_tac bvi_to_cb_size
    >> gvs [])
  >> disch_then drule   
  >> disch_then $ drule_at $ Pos $ el 2
  >> qpat_x_assum ‘env_rel F _ _ _’ kall_tac
  >> drule env_rel_append
  >> disch_then $ qspecl_then [‘as'’, ‘as’] mp_tac
  >> disch_then drule
  >> strip_tac
  >> disch_then drule
  >> gvs []
  >> strip_tac
  >> gvs []
  >> pop_assum kall_tac
  >> pop_assum kall_tac
  (* Experimental - unify maps *)
  >> drule state_rel_unique_map
  >> disch_then rev_drule
  >> strip_tac
  >> gvs []
  (* Phase 2 theorem *)
  >> gvs [evaluate_def]
  >> drule evaluate_hb_to_bvi_worker
  >> disch_then drule
  >> imp_res_tac bvi_to_cb_wf
  >> gvs []
  >> disch_then drule
  >> disch_then drule
  >> disch_then drule
  >> disch_then $ drule_at Any
  >> disch_then $ drule_at Any
  >> disch_then $ drule_at Any
  >> rev_drule_all env_rel_strip_extras
  >> strip_tac
  >> gvs []       
  >> drule_all hole_has_val_append
  >> strip_tac
  >> gvs [APPEND_ASSOC]
  >> disch_then drule
  >> disch_then $ qspecl_then [‘loc_opt'’] assume_tac
  >> gvs []
  >> ‘LENGTH bs = LENGTH as’ by imp_res_tac evaluate_IMP_LENGTH
  >> gvs [opt_res_rel_def]
  >> conj_tac
  >-
   (irule holes_unchanged_except_trans
    >> gvs [EL_APPEND_EQN]
    >> rev_drule env_rel_length_opt
    >> strip_tac
    >> gvs []
    >> drule env_rel_length_opt
    >> strip_tac
    >> gvs []
    >> first_assum $ irule_at $ Pos $ el 4
    >> gvs []
    >> irule holes_unchanged_except_subset
    >> qexists ‘∅’
    >> gvs [])
  >> irule hole_has_val_unappend
  >> rpt $ first_assum $ irule_at Any
  >> gvs []
QED

(* Is this true ? *)
Theorem state_rel_unique_map:
  ∀f f' s s'.
    state_rel f s s' ∧
    state_rel f' s s' ⇒
    f = f'
Proof
  rw []
  >> irule $ iffLR fmap_EQ_THM
  >> gvs [state_rel_def, state_ref_rel_def]
  >> rw []
  >> Cases_on ‘FLOOKUP s.refs x’ >> gvs [FLOOKUP_DEF]
  >> first_x_assum drule
  >> strip_tac
  >> last_x_assum drule
  >> strip_tac
  >> cheat
QED

Theorem evaluate_bvi_to_cb:
  ∀loc tag args env s t r bs cb.
    evaluate ([Op (BlockOp (Cons tag)) args],env,s) = (r,t) ∧
    bvi_to_cb loc tag args = SOME (bs,cb) ∧
    r ≠ Rerr (Rabort Rtype_error) ⇒
    ∃rs.
      evaluate (bs,env,s) = (rs,s) ∧
      (∀as.
         rs = Rval as ⇒
         evaluate ([cb_to_bvi loc cb],as ++ env,s) = (r,t)) ∧
      (∀e.
         rs = Rerr e ⇒
         (r,t) = (rs,s))
Proof
  rw []
  >> gvs [state_rel_def, state_ref_rel_def]
  >> cheat
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

(* I've broken this up to be more modular, keeping around for reference while I work on those proofs.
Theorem evaluate_hb_to_bvi:
  ∀cb tag left cb' right loc loc_opt f f' env1 env2 hole_ptr hole_idx r' s t s' t' c hb call_ts call_args.
    evaluate ([cb_to_bvi loc cb],env2 ++ [RefPtr F hole_ptr; hole_idx],s') = (r',t') ∧
    cb_to_hb cb = (hb,call_ts,call_args) ∧
    cb = CallBlock tag left cb' right ∧
    env_rel T f env1 (env2 ++ [RefPtr F hole_ptr; hole_idx]) ∧
    state_rel f s s' ∧
    f ⊑ f' ∧
    hole_has_val f env1 (env2 ++ [RefPtr F hole_ptr; hole_idx]) s'.refs c ∧
    holes_unchanged_except f s'.refs t'.refs ∅ ∧
    only_fresh f f' s'.refs ∧
    state_rel f' t t' ∧
    r' ≠ Rerr (Rabort Rtype_error) ⇒
    ∃idx new_ptr hole_val left' right' r_mc' t_mc' s_call' r_call' t_call' env3.
      r_mc' = Rval [RefPtr F new_ptr] ∧
      (*t_mc' = ???*)
      (*s_call' = t_mc' with refs := t_mc'.refs⟨hole_ptr ↦ MutBlock tag left' hole_val right'⟩ ∧*)
      env3 = Unit::RefPtr F new_ptr::(env2 ++ [RefPtr F hole_ptr; hole_idx]) ∧
      idx = Op (IntOp (Const (&LENGTH left))) [] ∧ (* or left' ? or both? *)
      (*new_ptr = LEAST ptr. ptr ∉ FDOM s'.refs ∧*)
      evaluate ([hb_to_mutcons hb],env2 ++ [RefPtr F hole_ptr; hole_idx],s') = (r_mc',t_mc') ∧
      (* state_rel f' s t_mc' ∧ *)
      holes_unchanged_except f s'.refs t_mc'.refs {RefPtr F new_ptr} ∧
      evaluate ([optimise_call loc_opt idx (Var 0) call_ts call_args],env3,s_call') = (r_call',t_call')
Proof
  gen_tac
  >> Induct_on ‘cb’ >> rw []
  >> gvs [cb_to_hb_def, CaseEq "prod"]
  >> rename [‘evaluate ([cb_to_bvi loc (CallBlock tag left child right)],env2 ++ [RefPtr F hole_ptr; hole_idx],s') = (r',t')’]
  >> qpat_x_assum ‘evaluate ([cb_to_bvi loc (CallBlock tag left child right)],env2 ++ [RefPtr F hole_ptr; hole_idx],s') = (r',t')’ assume_tac
  >> gvs [hb_to_mutcons_def, evaluate_def, cb_to_bvi_def]
  >> gvs [evaluate_APPEND]
  >> gvs [CaseEq "prod"]
  >> drule evaluate_var_list
  >> strip_tac
  >> gvs []
  >> Cases_on ‘v3' ≠ Rerr (Rabort Rtype_error)’ >> gvs []
  >> gvs [CaseEq "prod"]
  >> rename [‘evaluate ([cb_to_bvi loc child],env2 ++ [RefPtr F hole_ptr; hole_idx],s') = (r_child',t_child')’]
  >> first_x_assum drule
  >> reverse $ Cases_on ‘child’ >> gvs []
  >-
   (gvs [GSYM PULL_EXISTS, cb_to_hb_def]
    (* hb_to_mutcons *)
    >> gvs [hb_to_mutcons_def, evaluate_def, do_app_def, do_app_aux_def, backend_commonTheory.small_enough_int_def]
    >> Cases_on ‘evaluate (MAP (λn. Var n) right, env2 ++ [RefPtr F hole_ptr; hole_idx],s')’
    >> reverse $ Cases_on ‘q’ >> gvs []
    >- cheat (* right cannot fail *)
    >> drule evaluate_var_list
    >> strip_tac
    >> gvs []
    >> rename [‘evaluate (MAP (λn. Var n) right,env2 ++ [RefPtr F hole_ptr; hole_idx],s') = (Rval (MAP (λn. (env2 ++ [RefPtr F hole_ptr; hole_idx])❲n❳) right),s')’]
    >> gvs [hb_to_mutcons_def, evaluate_def, do_app_def, do_app_aux_def, backend_commonTheory.small_enough_int_def]
    >> irule_at Any holes_unchanged_except_filled
    >> irule_at Any holes_unchanged_except_refl
    (* optimise_call *)
    >> gvs [optimise_call_def, evaluate_def, do_app_def, do_app_aux_def]
    >> CASE_TAC >> gvs []
    >> gvs [CaseEq "prod"]
    >> simp [Once evaluate_CONS]
    >> gvs [evaluate_def]
    >> gvs [cb_to_bvi_def, evaluate_def]
    >> gvs [CaseEq "prod"]
    >> qspec_then ‘call_args’ mp_tac evaluate_var_list
    >> disch_then drule
    >> strip_tac
    >> Cases_on ‘v5'’ >> gvs []
    (*
    >> qspecl_then [‘call_args’, ‘[Unit; RefPtr F (LEAST ptr. ptr ∉ FDOM s'.refs)]’, ‘env2’, ‘s'’, ‘’] mp_tac evaluate_var_list_binders
    >> strip_tac
    >> gvs []*)
    >> cheat (* ??? *))
  >> rename [‘cb_to_hb (CallBlock tag left child right) = (hb,call_ts,call_args)’]
  >> gvs [cb_to_hb_def, CaseEq "prod"]
  >> rpt $ disch_then drule
  >> ‘holes_unchanged_except f s'.refs t_child'.refs ∅’ by cheat (* Is this true? *)
  >> rpt $ disch_then drule
  >> ‘state_rel f' t t_child'’ by cheat (* Is this true? As of now, t only appears here *)
  >> disch_then drule
  >> disch_then $ qspec_then ‘loc_opt’ mp_tac
  >> impl_tac
  >- (spose_not_then assume_tac >> gvs [])
  >> strip_tac
  >> gvs [GSYM PULL_EXISTS]
  >> cheat
QED
*)

Theorem evaluate_hb_to_mutcons:
  ∀cb tag left child right hb call_ts call_args loc f env1 env2 r' s t s' t' c.
    evaluate ([cb_to_bvi loc cb],env2,s') = (r',t') ∧
    cb_to_hb cb = (hb,call_ts,call_args) ∧
    cb = CallBlock tag left child right ∧
    env_rel T f env1 env2 ∧
    hole_has_val f env1 env2 s'.refs c ∧
    holes_unchanged_except f s'.refs t'.refs ∅ ∧
    r' ≠ Rerr (Rabort Rtype_error) ⇒
    ∃new_ptr t_mc'.
      evaluate ([hb_to_mutcons hb],env2,s') = (Rval [RefPtr F new_ptr],t_mc') ∧
      (*f ⊑ f' ∧ *)
      (*state_rel f' t t_mc' ∧ *)
      (*only_fresh f f' s'.refs ∧ *)
      holes_unchanged_except f s'.refs t_mc'.refs {RefPtr F new_ptr}
Proof
  gen_tac
  >> Induct_on ‘cb’ >> rw []
  >> gvs [cb_to_hb_def, CaseEq "prod"]
  >> rename [‘evaluate ([cb_to_bvi loc (CallBlock tag left child right)],env2,s') = (r',t')’]
  >> qpat_x_assum ‘evaluate ([cb_to_bvi loc (CallBlock tag left child right)],env2,s') = (r',t')’ assume_tac
  >> gvs [hb_to_mutcons_def, evaluate_def, cb_to_bvi_def]
  >> gvs [evaluate_APPEND, CaseEq "prod"]
  >> drule evaluate_var_list
  >> strip_tac
  >> gvs []
  >> Cases_on ‘v3' ≠ Rerr (Rabort Rtype_error)’ >> gvs []
  >> gvs [CaseEq "prod"]
  >> rename [‘evaluate ([cb_to_bvi loc child],env2,s') = (r_child',t_child')’]
  >> first_x_assum drule
  >> reverse $ Cases_on ‘child’ >> gvs []
  >-
   (gvs [GSYM PULL_EXISTS, cb_to_hb_def, hb_to_mutcons_def, evaluate_def, do_app_def, do_app_aux_def, backend_commonTheory.small_enough_int_def]
    >> Cases_on ‘evaluate (MAP (λn. Var n) right, env2,s')’
    >> reverse $ Cases_on ‘q’ >> gvs []
    >- cheat (* right cannot fail *)
    >> drule evaluate_var_list
    >> strip_tac
    >> gvs []
    >> rename [‘evaluate (MAP (λn. Var n) right,env2,s') = (Rval (MAP (λn. (env2)❲n❳) right),s')’]
    >> irule_at Any holes_unchanged_except_filled
    >> irule_at Any holes_unchanged_except_refl)
  >> rename [‘cb_to_hb (CallBlock tag left child right) = (hb,call_ts,call_args)’]
  >> gvs [cb_to_hb_def, CaseEq "prod"]
  >> rpt $ disch_then drule
  >> ‘holes_unchanged_except f s'.refs t_child'.refs ∅’ by cheat (* Is this true? *)
  >> rpt $ disch_then drule
  >> impl_tac
  >- (spose_not_then assume_tac >> gvs [])
  >> strip_tac
  >> gvs [GSYM PULL_EXISTS]
  >> cheat
QED

Theorem evaluate_optimise_call:
  ∀cb tag left child right hb call_ts call_args loc loc_opt hole_idx hole_ptr new_ptr f f' env1 env2 r' s t s' t' c.
    evaluate ([cb_to_bvi loc cb],env2,s') = (r',t') ∧
    cb_to_hb cb = (hb,call_ts,call_args) ∧
    cb = CallBlock tag left child right ∧
    env_rel T f env1 env2 ∧
    env2❲LENGTH env1❳ = RefPtr F hole_ptr ∧
    env2❲LENGTH env1 + 1❳ = Number hole_idx ∧
    (* hole_idx = &LENGTH left ∧    not sure if useful here, but something to have somewhere *)
    state_rel f s s' ∧
    f ⊑ f' ∧
    hole_has_val f env1 env2 s'.refs c ∧
    holes_unchanged_except f s'.refs t'.refs ∅ ∧
    only_fresh f f' s'.refs ∧
    state_rel f' t t' ∧
    r' ≠ Rerr (Rabort Rtype_error) ⇒
    ∃env3 r_call' t_call'.
      env3 = Unit::RefPtr F new_ptr::env2 ∧
      evaluate ([optimise_call loc_opt (Op (IntOp (Const hole_idx)) []) (Var 1) call_ts call_args],env3,s') = (r_call',t_call') ∧
      opt_res_rel r' r_call' ∧
      holes_unchanged_except f s'.refs t_call'.refs {RefPtr F hole_ptr}
Proof
  gen_tac
  >> Induct_on ‘cb’ >> rw []
  >> gvs [cb_to_hb_def, CaseEq "prod"]
  >> rename [‘evaluate ([cb_to_bvi loc (CallBlock tag left child right)],env2,s') = (r',t')’]
  >> qpat_x_assum ‘evaluate ([cb_to_bvi loc (CallBlock tag left child right)],env2,s') = (r',t')’ assume_tac
  >> gvs [hb_to_mutcons_def, evaluate_def, cb_to_bvi_def]
  >> gvs [evaluate_APPEND]
  >> gvs [CaseEq "prod"]
  >> drule evaluate_var_list
  >> strip_tac
  >> gvs []
  >> Cases_on ‘v3' ≠ Rerr (Rabort Rtype_error)’ >> gvs []
  >> gvs [CaseEq "prod"]
  >> rename [‘evaluate ([cb_to_bvi loc child],env2,s') = (r_child',t_child')’]
  >> first_x_assum drule
  >> reverse $ Cases_on ‘child’ >> gvs []
  >-
   (gvs [GSYM PULL_EXISTS, cb_to_hb_def, hb_to_mutcons_def, evaluate_def, do_app_def, do_app_aux_def, backend_commonTheory.small_enough_int_def]
    >> Cases_on ‘evaluate (MAP (λn. Var n) right, env2,s')’
    >> reverse $ Cases_on ‘q’ >> gvs []
    >- cheat (* right cannot fail *)
    >> drule evaluate_var_list
    >> strip_tac
    >> gvs []
    >> rename [‘evaluate (MAP (λn. Var n) right,env2,s') = (Rval (MAP (λn. (env2)❲n❳) right),s')’]
    >> irule_at Any holes_unchanged_except_filled
    >> irule_at Any holes_unchanged_except_refl)
  >> rename [‘cb_to_hb (CallBlock tag left child right) = (hb,call_ts,call_args)’]
  >> gvs [cb_to_hb_def, CaseEq "prod"]
  >> rpt $ disch_then drule
  >> ‘holes_unchanged_except f s'.refs t_child'.refs ∅’ by cheat (* Is this true? *)
  >> rpt $ disch_then drule
  >> ‘state_rel f' t t_child'’ by cheat (* Is this true? As of now, t only appears here *)
  >> disch_then drule
  >> impl_tac
  >- (spose_not_then assume_tac >> gvs [])
  >> strip_tac
  >> gvs [GSYM PULL_EXISTS]
  >> cheat
QED

Theorem evaluate_hb_to_bvi_wrapper:
  evaluate ([cb_to_bvi loc cb],env2,s) = (r,t) ∧
  cb_to_hb cb = (hb,call_ts,call_args) ∧
  cb = CallBlock tag left child right ∧
  env_rel T f env1 env2 ∧
  r ≠ Rerr (Rabort Rtype_error) ⇒
  ∃r' t'.
    evaluate ([],env2,s) = (r',t') ∧
    res_rel (v_rel f) r r' ∧
    state_rel f t t'
Proof
  cheat
QED

Theorem evaluate_hb_to_bvi_worker:
  ∀cb tag left child right loc loc_opt f f' env1 env2 r' s t s' t' c hb call_ts call_args.
    evaluate ([cb_to_bvi loc cb],env2,s') = (r',t') ∧
    cb_to_hb cb = (hb,call_ts,call_args) ∧
    cb = CallBlock tag left child right ∧
    env_rel T f env1 env2 ∧
    state_rel f s s' ∧
    f ⊑ f' ∧
    hole_has_val f env1 env2 s'.refs c ∧
    holes_unchanged_except f s'.refs t'.refs ∅ ∧
    only_fresh f f' s'.refs ∧
    state_rel f' t t' ∧
    r' ≠ Rerr (Rabort Rtype_error) ⇒
    ∃r'' t''.
      evaluate ([hb_to_bvi_worker loc loc_opt (LENGTH env1) (LENGTH env1 + 1) hb call_ts call_args],env2,s') = (r'',t'') ∧
      opt_res_rel r' r'' ∧
      state_rel f' t t'' ∧
      holes_unchanged_except f s'.refs t''.refs {env2❲LENGTH env1❳} ∧
      ∀v.
        r' = Rval [v] ⇒
        hole_has_val f env1 env2 t''.refs v
Proof
  rw []
  >> imp_res_tac env_rel_strip_extras
  >> gvs []
  >> gvs [cb_to_hb_def, CaseEq "prod", hb_to_bvi_worker_def, Once evaluate_def]
  >> rename [‘cb_to_hb child = (hole,call_ts,call_args)’]
  (* mutcons exp *)
  >> drule evaluate_hb_to_mutcons
  >> disch_then $ qspecl_then [‘tag’, ‘left’, ‘child’, ‘right’] mp_tac
  >> gvs [cb_to_hb_def]
  >> disch_then drule_all
  >> strip_tac             
  >> gvs [Once evaluate_def]
  (* update hole *)
  >> gvs [evaluate_def]
  >> rename [‘env_rel F f env1 env2’]
  >> imp_res_tac env_rel_length_opt
  >> gvs [EL, EL_APPEND_EQN]
  >> gvs [do_app_def, do_app_aux_def]
  >> ‘(RefPtr F new_ptr::(env2 ++ [RefPtr F hole_ptr; Number hole_idx]))❲LENGTH env1 + 1❳ = RefPtr F hole_ptr’ by
    (Cases_on ‘LENGTH env1 + 1’ >> gvs []
     >> gvs [EL_APPEND_EQN]
     >> ‘n = LENGTH env1’ by gvs []
     >> gvs [])
  >> gvs []
  >> pop_assum kall_tac
  >> ‘(RefPtr F new_ptr::(env2 ++ [RefPtr F hole_ptr; Number hole_idx]))❲LENGTH env1 + 2❳ = Number hole_idx’ by
    (Cases_on ‘LENGTH env1 + 2’ >> gvs []
     >> gvs [EL_APPEND_EQN]
     >> ‘n = LENGTH env1 + 1’ by gvs []
     >> gvs [])
  >> gvs []
  >> pop_assum kall_tac
  >> drule unchanged_hole_has_val
  >> disch_then $ drule_at $ Pos $ el 2
  >> disch_then drule
  >> disch_then drule
  >> ‘∀b. RefPtr b hole_ptr ∉ {RefPtr F new_ptr}’ by (cheat) (* additional conclusion from evaluate_hb_to_bvi.
                                                                at least that new_ptr ≠ hole_ptr, possibly something stronger
                                                                (that it is fresh/not in domain of f) *)
  >> disch_then drule
  >> simp [hole_has_val_def]
  >> gvs [EL_APPEND_EQN]
  >> strip_tac (* HERE is where tag' left' etc are introduced. New assumption to tie these to original? *)
  >> gvs []
  (* optimise_call *)
  >> cheat
QED

Resume evaluate_rewrite_tmc[tick]:
  gvs [evaluate_def]
  >> ‘s'.clock = s.clock’ by gvs [state_rel_def]
  >> gvs []
  >> Cases_on ‘s.clock’
  >> gvs []
  >-
   (goal_assum $ drule_at Any
    >> gvs []
    >> rw []
    >- gvs [only_fresh_refl]
    >- irule holes_unchanged_except_refl
    >-
     (goal_assum $ drule_at Any
      >> drule wrapper_strip_tick
      >> strip_tac
      >> gvs [evaluate_def])
    >> goal_assum $ drule_at Any
    >> gvs [rewrite_worker_def, evaluate_def, opt_res_rel_def, holes_unchanged_except_refl])
  >> first_x_assum $ qspec_then ‘opt’ mp_tac
  >> simp []
  >> disch_then drule
  >> drule state_rel_dec
  >> gvs []
  >> disch_then $ qspec_then ‘1’ mp_tac
  >> strip_tac
  >> gvs []
  >> disch_then drule
  >> strip_tac
  >> gvs []
  >> rename [‘evaluate ([x],env2,dec_clock 1 s') = (r',t')’]
  >> first_assum $ irule_at Any
  >> gvs []
  >> strip_tac
  >> gvs []
  >> conj_tac
  >-
   (rw []
    >> drule wrapper_strip_tick
    >> strip_tac
    >> gvs [evaluate_def]
    >> first_x_assum $ irule_at Any
    >> qexistsl [‘arity’, ‘loc’, ‘loc_opt’]
    >> gvs [])
  >> rw [rewrite_worker_def, evaluate_def]
QED

Resume evaluate_rewrite_tmc[force]:
  cheat
QED

Resume evaluate_rewrite_tmc[call]:

  gvs [evaluate_def]
  >> IF_CASES_TAC >> gvs []
  >> gvs [CaseEq "prod", PULL_EXISTS]
  >> rename [‘evaluate (xs,env,s) = (v_xs,u)’]
  (* xs inductive hypothesis *)
  >> first_x_assum $ qspec_then ‘F’ mp_tac
  >> drule env_rel_relax_opt
  >> gvs []
  >> strip_tac
  >> rpt $ disch_then drule
  >> impl_tac
  >- (CCONTR_TAC >> gvs [])
  >> strip_tac
  >> gvs []
  >> reverse $ Cases_on ‘v_xs’ >> gvs []
  >- (* Error case *)
   (rename [‘evaluate (xs,env2,s') = (Rerr e',t')’]
    >> first_assum $ irule_at $ Pos hd
    >> gvs []
    >> rw [rewrite_wrapper_def]
    >> qexistsl [‘Rerr e'’, ‘t'’]
    >> gvs [opt_res_rel_def]
    >> conj_tac
    >- (gvs [rewrite_worker_def, fill_hole_def, evaluate_def] >> IF_CASES_TAC >> gvs [])
    >> irule holes_unchanged_except_subset
    >> first_assum $ irule_at Any
    >> gvs [])
  >> qpat_x_assum ‘evaluate (_,env2,_) = (Rval _, _)’ $ mk_asm "eval_xs'"
  >> rename [‘evaluate (xs,env,s) = (Rval v_xs,u)’]
  >> Cases_on ‘find_code dest v_xs u.code’ >> gvs []
  >> Cases_on ‘x’ >> gvs []
  >> rename [‘find_code dest v_xs u.code = SOME (args,exp)’]
  >> asm_x "eval_xs'" assume_tac
  >> rename [‘evaluate (xs,env2,s') = (Rval v_xs',u')’]
  >> drule_all find_code_rel
  >> strip_tac
  >> gvs []
  >> ‘u'.clock = u.clock’ by (gvs [state_rel_def])
  >> gvs []
  >> IF_CASES_TAC >> gvs []
  >- (* Clock ran out *)
   (drule_all state_rel_with_clock
    >> disch_then $ qspec_then ‘0’ mp_tac
    >> strip_tac
    >> first_assum $irule_at $ Pos hd
    >> gvs []
    >> strip_tac
    >> gvs [rewrite_wrapper_def]
    >> rw []
    >> simp [rewrite_worker_def]
    >> ho_match_mp_tac evaluate_fill_hole_err
    >> first_assum $ irule_at Any
    >> gvs [evaluate_def]
    >> IF_CASES_TAC >> gvs []
    >> first_assum $ irule_at Any)
  (* Clock did not run out *)
  >> Cases_on ‘evaluate ([exp],args,dec_clock (ticks + 1) u)’ >> gvs []
  >> rename [‘evaluate ([exp],args,dec_clock (ticks + 1) u) = (v_exp, w)’]
  (* Call body inductive hypothesis *)
  >> first_x_assum $ qspec_then ‘exp ≠ exp'’ mp_tac
  >> gvs []
  >> drule state_rel_dec
  >> Cases_on ‘u.clock’ >> gvs []
  >> disch_then $ qspec_then ‘ticks + 1’ mp_tac
  >> gvs []
  >> strip_tac
  >> disch_then $ drule_at $ Pos $ el 2
  >> Cases_on ‘exp = exp'’ >> gvs []
  >-
   (disch_then drule
    >> gvs []
    >> impl_tac
    >- (spose_not_then assume_tac >> gvs [])
    >> strip_tac
    >> gvs []
    >> rename [‘evaluate ([exp],args',dec_clock (ticks + 1) u') = (v_exp',w')’]
    >> Cases_on ‘v_exp’ >> gvs []
    >-
     (imp_res_tac evaluate_SING_IMP
      >> gvs []
      >> rename [‘state_rel f3 t t'’]
      >> rename [‘v_rel f3 v_exp v_exp'’]
      >> first_assum $ irule_at $ Pos hd
      >> gvs []
      >> conj_asm1_tac
      >- (irule SUBMAP_TRANS >> first_assum $ irule_at Any >> gvs [])
      >> conj_asm1_tac
      >-
       (imp_res_tac evaluate_refs_SUBSET
        >> drule_all only_fresh_trans
        >> gvs [])
      >> conj_asm1_tac
      >- (irule_at Any holes_unchanged_except_trans
          >> first_assum $ irule_at $ Pos $ el 4
          >> gvs [])
      >> strip_tac
      >> gvs []
      >> conj_tac
      >- rw [rewrite_wrapper_def]
      >> rw []
      >> gvs [rewrite_worker_def]
      >> ho_match_mp_tac evaluate_fill_hole
      >> gvs [evaluate_def]
      >> IF_CASES_TAC >> gvs []
      >> rpt $ first_assum $ irule_at Any)
    >> Cases_on ‘e’ >> gvs []
    >-
     (Cases_on ‘handler’ >> gvs []
      >-
       (irule_at Any holes_unchanged_except_trans
        >> first_assum $ irule_at Any
        >> first_assum $ irule_at Any
        >> gvs []
        >> conj_tac
        >- (imp_res_tac SUBMAP_TRANS >> gvs [])
        >> conj_tac
        >-
         (imp_res_tac only_fresh_trans
          >> imp_res_tac evaluate_refs_SUBSET
          >> gvs [])
        >> strip_tac
        >> gvs []
        >> conj_tac
        >> rw [rewrite_wrapper_def]
        >> rw []
        >> gvs [rewrite_worker_def, fill_hole_def, evaluate_def]
        >> gvs [opt_res_rel_def]
        >> drule_all holes_unchanged_except_trans
        >> gvs []
        >> strip_tac
        >> irule holes_unchanged_except_subset
        >> first_x_assum $ irule_at Any
        >> gvs [])
      >> rename [‘v_rel f3 v v'’]
      >> first_x_assum $ qspec_then ‘F’ mp_tac
      >> gvs []
      >> disch_then $ drule_at $ Pos $ el 2
      >> gvs []
      >> disch_then $ qspec_then ‘v'::env2’ mp_tac
      >> impl_tac
      >-
       (irule env_rel_cons
        >> gvs []
        >> irule env_rel_submap
        >> first_assum $ irule_at $ Pos $ el 2
        >> imp_res_tac SUBMAP_TRANS)
      >> strip_tac
      >> gvs []
      >> rename [‘evaluate ([x],v'::env2,w') = (v_x',t')’]
      >> rename [‘result_rel (LIST_REL (v_rel f4)) (v_rel f4) v_x v_x'’]
      >> first_assum $ irule_at Any
      >> gvs []
      >> conj_asm1_tac
      >- (imp_res_tac SUBMAP_TRANS >> gvs [])
      >> conj_asm1_tac
      >-
       (imp_res_tac only_fresh_trans
        >> imp_res_tac evaluate_refs_SUBSET
        >> imp_res_tac SUBSET_TRANS
        >> gvs [])
      >> conj_asm1_tac
      >- imp_res_tac holes_unchanged_except_trans
      >> strip_tac
      >> gvs [rewrite_wrapper_def]
      >> rw []
      >> gvs [rewrite_worker_def]
      >> Cases_on ‘v_x'’ >> gvs []
      >-
       (imp_res_tac evaluate_SING_IMP
        >> gvs []
        >> ho_match_mp_tac evaluate_fill_hole
        >> gvs [evaluate_def]
        >> rpt $ first_assum $ irule_at Any)
      >> ho_match_mp_tac evaluate_fill_hole_err
      >> gvs [evaluate_def]
      >> rpt $ first_assum $ irule_at Any)
    >> first_assum $ irule_at Any
    >> conj_asm1_tac
    >- imp_res_tac SUBMAP_TRANS
    >> conj_asm1_tac
    >-
     (irule only_fresh_trans
      >> first_assum $ irule_at Any
      >> conj_tac
      >- imp_res_tac evaluate_refs_SUBSET
      >> gvs [])
    >> conj_asm1_tac
    >- imp_res_tac holes_unchanged_except_trans
    >> strip_tac
    >> gvs [rewrite_wrapper_def]
    >> rw []
    >> gvs [rewrite_worker_def]
    >> ho_match_mp_tac evaluate_fill_hole_err
    >> gvs [evaluate_def]
    >> IF_CASES_TAC >> gvs []
    >> rpt $ first_assum $ irule_at Any)


  >> rename [‘exp ≠ wrap’]
  >> rename [‘env_rel F f'' args args_exp’]
  >> disch_then drule
  >> impl_tac
  >- (spose_not_then assume_tac >> gvs [])
  >> drule env_rel_extras_opt
  >> strip_tac
  >> gvs [EL_APPEND_EQN]
  >> strip_tac
  >> gvs []
  >> rename [‘evaluate ([exp],args_exp ++ extras,dec_clock (ticks + 1) u') = (v_exp',t')’]
  >> last_x_assum drule
  >> strip_tac
  >> gvs []
  >> rename [‘state_rel f3 t t_wrap’]
  >> Cases_on ‘v_exp’ >> gvs []
  >-
   (imp_res_tac evaluate_SING_IMP
    >> gvs []
    >> rename [‘v_rel f3 v_exp v_exp'’]
    >> Cases_on ‘evaluate ([wrap],args_exp,dec_clock (ticks + 1) u')’ >> gvs []
    >> rename [‘evaluate ([wrap],args_exp,dec_clock (ticks + 1) u') = (v_wrap',t_wrap')’]
    >> drule evaluate_expand_env
    >> disch_then $ qspec_then ‘extras’ assume_tac
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
    >- cheat
    >> rw [rewrite_wrapper_def, rewrite_worker_def]
    >> irule evaluate_fill_hole
    >> gvs []
    >> rpt $ first_assum $ irule_at Any
    >> gvs [evaluate_def]
    >> IF_CASES_TAC >> gvs [])
  >> Cases_on ‘evaluate ([wrap],args_exp,dec_clock (ticks + 1) u')’ >> gvs []
  >> rename [‘evaluate ([wrap],args_exp,dec_clock (ticks + 1) u') = (v_wrap',t_wrap')’]
  >> drule evaluate_expand_env
  >> disch_then $ qspec_then ‘extras’ assume_tac
  >> gvs []
  >> Cases_on ‘e’ >> gvs []
  >-
   (CASE_TAC >> gvs []
    >-
     (first_assum $ irule_at Any
      >> gvs []
      >> conj_asm1_tac
      >- imp_res_tac SUBMAP_TRANS
      >> conj_asm1_tac
      >-
       (irule only_fresh_trans
        >> rpt $ first_assum $ irule_at Any
        >> imp_res_tac evaluate_refs_SUBSET)
      >> conj_asm1_tac
      >- cheat
      >> rw [rewrite_wrapper_def, rewrite_worker_def]
      >> ho_match_mp_tac evaluate_fill_hole_err
      >> gvs []
      >> rpt $ first_assum $ irule_at Any
      >> gvs [evaluate_def])
    >> first_x_assum $ qspec_then ‘F’ mp_tac
    >> cheat)
  >> cheat
QED

Finalise evaluate_rewrite_tmc

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
    >- (gvs [namespace_rel_def]
        >> conj_tac
        >- (strip_tac
            >> strip_tac
            >> gvs []
            >> CASE_TAC
            >- (cheat)
            >> cheat
           )
        >> cheat)
    >> rpt strip_tac
    >> pairarg_tac
    >> gvs []
    >> res_tac
    >> gvs [])
  >> drule evaluate_rewrite_tmc
  >> disch_then (qspec_then `F` drule)
  >> rpt (disch_then drule)
  >> fs []
  >> strip_tac
  >> gvs []
  >> qexists ‘f'’
  >> gvs []
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
  cheat
QED
