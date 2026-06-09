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
[~MutBlock:] (* Remove *)
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
      (* No mutblock property *)
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

(* This should say: expression in prog satisfies no-mutblock property *)
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

(* Can't be type error *)
Theorem evaluate_expand_env:
  ∀xs env s t r extra.
    evaluate (xs, env, s) = (r, t) ∧
    r ≠ Rerr (Rabort Rtype_error) ⇒
    evaluate (xs, env ++ extra, s) = (r, t)
Proof
  recInduct bviSemTheory.evaluate_ind
  >> rpt strip_tac
  >~ [‘evaluate ([],_,_)’] >-
   (gvs [evaluate_def])
  >~ [‘evaluate (x::y::xs,_,_)’] >-
   (simp [Once evaluate_CONS]
    >> CASE_TAC
    >> cheat)
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

Definition hole_has_val_def:
  hole_has_val (f : num |-> num) (env1 : v list) (env2 : v list) (refs : num |-> v ref) c ⇔
  LENGTH env2 = LENGTH env1 + 2 ∧
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
    (*env_rel T f env (env' ++ [RefPtr F hole_ptr; Number hole_idx]) ∧*)
    (∀b. RefPtr b hole_ptr ∉ changed) ⇒
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


(* Keep this one *)
Theorem do_app_op_rel:
  ∀f op vs vs' s s' t v.
    do_app op vs s = Rval (v,t) ∧
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
  rw [do_app_def]
  >-
   (gvs [do_install_def, CaseEq "list", CaseEq "option"]
    >> cheat)
  >> Cases_on ‘∃i. op = IntOp i’
  >-
   (gvs []
    >> Cases_on ‘i’ >> gvs []
    >> gvs [do_app_aux_def, bvlSemTheory.do_app_def, AllCaseEqs ()]
    >> imp_res_tac LIST_REL_LENGTH
    >> cheat)
  >> cheat
QED

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

Theorem wrapper_strip_if_then:
  rewrite_wrapper loc loc_opt (If x1 x2 x3) = SOME w ⇒
  ∃w2 w3.
    w = If x1 w2 w3 ∧
    (rewrite_wrapper loc loc_opt x2 = SOME w2 ∨
     w2 = x2)
Proof
  rw []
  >> gvs [rewrite_wrapper_def]
  >> Cases_on ‘rewrite_wrapper loc loc_opt x2’
  >> Cases_on ‘rewrite_wrapper loc loc_opt x3’
  >> gvs []
QED

Theorem wrapper_strip_if_else:
  rewrite_wrapper loc loc_opt (If x1 x2 x3) = SOME w ⇒
  ∃w2 w3.
    w = If x1 w2 w3 ∧
    (rewrite_wrapper loc loc_opt x3 = SOME w3 ∨
     w3 = x3)
Proof
  rw []
  >> gvs [rewrite_wrapper_def]
  >> Cases_on ‘rewrite_wrapper loc loc_opt x2’
  >> Cases_on ‘rewrite_wrapper loc loc_opt x3’
  >> gvs []
QED

Theorem wrapper_strip_let:
  ∀loc loc_opt xs x w.
    rewrite_wrapper loc loc_opt (Let xs x) = SOME w ⇒
    ∃w'.
      w = Let xs w' ∧
      rewrite_wrapper loc loc_opt x = SOME w'
Proof
  rw []
  >> gvs [rewrite_wrapper_def]
  >> Cases_on ‘rewrite_wrapper loc loc_opt x’
  >> gvs []
QED

Theorem wrapper_strip_tick:
  ∀loc loc_opt x w.
    rewrite_wrapper loc loc_opt (Tick x) = SOME w ⇒
    ∃w'.
      w = Tick w' ∧
      rewrite_wrapper loc loc_opt x = SOME w'
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
       ∃loc loc_opt extras.
         rewrite_wrapper loc loc_opt exp = SOME exp' ∧
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
    >> Cases_on ‘rewrite_wrapper n n' exp’ >> gvs []
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
  >> rename [‘compile_exp n n' arity exp = SOME (exp_wrap,exp_work)’]
  >> strip_tac
  >> gvs [compile_exp_def]
  >> Cases_on ‘rewrite_wrapper n n' exp’ >> gvs []
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
    ∃r t'' f_work.
      evaluate ([fill_hole (LENGTH env1) (LENGTH env1 + 1) exp],env2,s') = (r,t'') ∧
      opt_res_rel (Rval [v]) r ∧
      state_rel f_work t t'' ∧
      f ⊑ f_work ∧
      only_fresh f f_work s'.refs ∧
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
  >> first_assum $ irule_at Any
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

Theorem evaluate_vars:
  ∀ns opt f env1 env2 (s1 : (num # γ, 'ffi) state) (s2 : (γ, 'ffi) state) t1 r1.
    evaluate (MAP (λn. Var n) ns,env1,s1) = (r1,t1) ∧
    env_rel opt f env1 env2 ∧
    r1 ≠ Rerr (Rabort Rtype_error) ⇒
    (r1,t1) = (Rval (MAP (λn. env1❲n❳) ns),s1) ∧
    evaluate (MAP (λn. Var n) ns,env2,s2) = (Rval (MAP (λn. env2❲n❳) ns),s2)
Proof
  Induct
  >- gvs [evaluate_def]
  >> rpt gen_tac
  >> strip_tac
  >> gvs [evaluate_def, evaluate_CONS]
  >> reverse $ Cases_on ‘h < LENGTH env1’
  >- gvs []
  >> imp_res_tac env_rel_length
  >> gvs [CaseEq "prod"]
  >> first_x_assum drule
  >> disch_then drule
  >> impl_tac >- gvs [CaseEq "result"]
  >> disch_then $ qspec_then ‘s2’ assume_tac
  >> gvs []
QED

Theorem shift_vars_zero:
  ∀ns.
    shift_vars 0 ns = ns
Proof
  Induct
  >- gvs [shift_vars_def]
  >> rw []
  >> gvs [shift_vars_def]
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

(* Use n+1 and n, subtracting nats is dangerous *)
Theorem evaluate_shift_vars_cons:
  ∀vs env s b n.
    evaluate (MAP (λn. Var n) (shift_vars n vs),b::env,s) =
    evaluate (MAP (λn. Var n) (shift_vars (n - 1) vs),env,s)
Proof
  cheat
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
  ∀cb loc env s bs r t.
    evaluate ([cb_to_bvi loc cb],env,s) = (r,t) ⇒
    evaluate ([cb_to_bvi loc (shift_cb (LENGTH bs) cb)],bs ++ env,s) = (r,t)
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
  ∀cb loc env s b r t.
    evaluate ([cb_to_bvi loc cb],env,s) = (r,t) ⇒
    evaluate ([cb_to_bvi loc (shift_cb 1 cb)],b::env,s) = (r,t)
Proof
  rw []
  >> drule evaluate_shift_cb
  >> disch_then $ qspec_then ‘[b]’ mp_tac
  >> gvs []
QED

Theorem evaluate_pure_exps:
  ∀xs.
    pure_exps xs ⇒
    ∃v. ∀env s.
          evaluate (xs,env,s) = (Rval v,s)
Proof
  recInduct pure_exps_ind
  >> rw []
  >> gvs [pure_exps_def, evaluate_def]
  >> Cases_on ‘op’ >> gvs [pure_op_def, do_app_def, do_app_aux_def]
  >- (Cases_on ‘i’ >> gvs [pure_op_def] >> Cases_on ‘args’ >> gvs [pure_op_def, evaluate_def])
  >-
   (Cases_on ‘b’ >> gvs [pure_op_def, evaluate_def, do_app_def, do_app_aux_def, bvl_to_bvi_id, bvlSemTheory.do_app_def, bvi_to_bvl_def]
    >- (qexists ‘[Block n (REVERSE v)]’
        >> gvs []
        >> rw []
        >> cheat)
    >> cheat)
  >> cheat
QED

Theorem evaluate_bvi_to_cb_aux_inl:
  ∀loc tag args bs vs.
    bvi_to_cb_aux loc tag args = SOME (bs,INL vs) ⇒
    bs = args ∧
    ∃v. ∀s env.
      evaluate (args,env,s) = (Rval v,s) ∧
      evaluate (MAP (λn. Var n) vs,v,s) = (Rval v,s)
Proof
  recInduct bvi_to_cb_aux_ind >> rw [bvi_to_cb_aux_def, call_to_cb_def] >> gvs [evaluate_def]
  >- (gvs [CaseEq "prod", CaseEq "option", CaseEq "prod"])
  >- (gvs [CaseEq "prod", CaseEq "option", CaseEq "prod"])
  >- (gvs [CaseEq "option", CaseEq "prod", CaseEq "sum", evaluate_def])
  >-
   (imp_res_tac evaluate_pure_exps
    >> qexists ‘v’
    >> rpt gen_tac
    >> first_x_assum $ qspecl_then [‘env’, ‘s’] mp_tac
    >> gvs [evaluate_def]
    >> strip_tac
    >> gvs [CaseEq "option", CaseEq "prod", CaseEq "sum", CaseEq "result", evaluate_def])
  >- (gvs [CaseEq "option", CaseEq "prod", CaseEq "sum"])
  >- (gvs [CaseEq "option", CaseEq "prod", CaseEq "sum"])
  >- (gvs [pure_exps_def])
  >- (gvs [pure_exps_def])
  >-
   (gvs [pure_exps_def]
    >> imp_res_tac evaluate_pure_exps
    >> qexists ‘v'’
    >> rpt gen_tac
    >> last_x_assum $ qspecl_then [‘env’, ‘s’] mp_tac
    >> strip_tac
    >> first_x_assum $ qspecl_then [‘v ++ env’, ‘s’] mp_tac
    >> strip_tac
    >> imp_res_tac evaluate_SING_IMP
    >> imp_res_tac evaluate_IMP_LENGTH
    >> gvs [evaluate_def])
  >- (gvs [pure_exps_def])
  >- (gvs [pure_exps_def])
  >- (gvs [pure_exps_def])
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
  >> qexists ‘HD v'::v’
  >> gvs [evaluate_APPEND]
  >> gen_tac
  >> last_x_assum $ qspecl_then [‘s’, ‘HD v'::v’] mp_tac
  >> strip_tac >> gvs []
  >> imp_res_tac evaluate_SING_IMP >> gvs []
  >> drule evaluate_expand_env
  >> disch_then $ qspec_then ‘v’ mp_tac
  >> strip_tac
  >> gvs [APPEND]
  >> first_x_assum $ qspecl_then [‘s’, ‘v’] mp_tac
  >> strip_tac
  >> gvs [evaluate_shift_vars_sing, APPEND]
QED

Theorem evaluate_bvi_to_cb_aux_inr:
  ∀loc tag args env s t r bs cb.
    bvi_to_cb_aux loc tag args = SOME (bs,INR cb) ∧
    evaluate ([Op (BlockOp (Cons tag)) args],env,s) = (r,t) ∧
    r ≠ Rerr (Rabort Rtype_error) ⇒
    ∃as u.
      evaluate (bs,env,s) = (as,u) ∧
      (∀vs.
         as = Rval vs ⇒
         evaluate ([cb_to_bvi loc cb],vs,u) = (r,t)) ∧
      (∀e.
         as = Rerr e ⇒
         (as,u) = (r,t))
Proof
  recInduct bvi_to_cb_aux_ind
  >> rw [bvi_to_cb_aux_def, call_to_cb_def]
  >-
   (gvs [CaseEq "prod", CaseEq "option"]
    >> rename [‘bind 0 args = (vs,n')’]
    >> gvs [evaluate_def, cb_to_bvi_def, evaluate_def]
    >> gvs [CaseEq "prod"]
    >> Cases_on ‘v5'’ >> gvs []
    >> drule evaluate_binders
    >> disch_then drule
    >> disch_then $ qspec_then ‘[]’ mp_tac
    >> gvs [])
  >-
   (gvs [evaluate_def, cb_to_bvi_def, CaseEq "option"]
    >> Cases_on ‘op’ >> gvs [dest_Cons_def]
    >> Cases_on ‘b’ >> gvs [dest_Cons_def]
    >> gvs [CaseEq "prod", CaseEq "sum", PULL_EXISTS]
    >> first_x_assum drule
    >> gvs []
    >> impl_tac >- gvs [CaseEq "prod", CaseEq "result"]
    >> strip_tac
    >> first_assum $ irule_at Any
    >> rw []
    >> gvs [cb_to_bvi_def, evaluate_def])
  >-
   (gvs [evaluate_def, cb_to_bvi_def, CaseEq "option"]
    >> Cases_on ‘op’ >> gvs [dest_Cons_def]
    >> Cases_on ‘b’ >> gvs [dest_Cons_def]
    >> gvs [CaseEq "prod", CaseEq "sum", PULL_EXISTS]
    >> first_x_assum drule
    >> gvs []
    >> impl_tac >- gvs [CaseEq "prod", CaseEq "result"]
    >> strip_tac
    >> first_assum $ irule_at Any
    >> rw []
    >> gvs [cb_to_bvi_def, evaluate_def])
  >> rename [‘evaluate ([Op (BlockOp (Cons tag)) (x1::x2::xs)],env,s) = (r,t)’]
  >> gvs [CaseEq "option", CaseEq "prod", CaseEq "sum"]
  >-
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
      >> gvs [cb_to_bvi_def, evaluate_def]
      >> simp [Once evaluate_CONS, evaluate_def]
      >> Cases_on ‘evaluate ([cb_to_bvi loc child],a',u)’ >> gvs []
      >> drule evaluate_expand_env
      >> disch_then $ qspec_then ‘v’ mp_tac
      >> impl_tac >- gvs [CaseEq "prod", CaseEq "result"]
      >> strip_tac
      >> gvs []
      >> Cases_on ‘q’ >> gvs []
      >> gvs [CaseEq "result", CaseEq "prod"]
      >> gvs [do_app_def, do_app_aux_def, bvl_to_bvi_id]
      >> gvs [PULL_EXISTS]
      >> gvs [GSYM PULL_FORALL]
      >> first_assum $ qspec_then ‘r’ mp_tac
      >> strip_tac
      >> imp_res_tac evaluate_IMP_LENGTH
      >> gvs [evaluate_shift_vars])
    >> strip_tac
    >> gvs [CaseEq "call_block", CaseEq "list"]
    >> gvs [evaluate_APPEND]
    >> Cases_on ‘as’ >> gvs []
    >> imp_res_tac evaluate_bvi_to_cb_aux_inl
    >> gvs []
    >> gvs [cb_to_bvi_def, evaluate_def]
    >> simp [Once evaluate_CONS, evaluate_def]
    >> Cases_on ‘evaluate ([cb_to_bvi loc child],a,u)’ >> gvs []
    >> drule evaluate_expand_env
    >> disch_then $ qspec_then ‘v’ mp_tac
    >> impl_tac >- gvs [CaseEq "prod", CaseEq "result"]
    >> strip_tac
    >> gvs []
    >> Cases_on ‘q’ >> gvs []
    >> gvs [do_app_def, do_app_aux_def])
  >> gvs [evaluate_def]
  >> gvs [CaseEq "prod"]
  >> reverse $ Cases_on ‘cb'’ >> gvs [shift_cb_def]
  >> rename [‘bvi_to_cb_aux loc tag (x2::xs) = SOME (bs2,INR (CallBlock n left cb' right))’]
  >> simp [Once evaluate_CONS, evaluate_def]
  >> gvs [CaseEq "prod"]
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
    >> gvs [CaseEq "prod", CaseEq "result"]
    >> Cases_on ‘evaluate ([cb_to_bvi loc cb'],a'',r)’ >> gvs []
    >> drule evaluate_shift_cb_sing
    >> disch_then $ qspec_then ‘HD a’ mp_tac
    >> strip_tac
    >> gvs [do_app_def, do_app_aux_def])
  >> strip_tac
  >> gvs []
  >> reverse CASE_TAC >> gvs []
  >> gvs [cb_to_bvi_def, evaluate_def]
  >> simp [Once evaluate_CONS, evaluate_def]
  >> gvs [evaluate_APPEND, evaluate_def]
  >> gvs [evaluate_shift_vars_sing]
  >> gvs [CaseEq "prod"]
  >> Cases_on ‘evaluate ([cb_to_bvi loc cb'],a',s2')’ >> gvs []
  >> drule evaluate_shift_cb_sing
  >> disch_then $ qspec_then ‘HD a’ mp_tac
  >> strip_tac
  >> gvs [CaseEq "prod", CaseEq "result", do_app_def, do_app_aux_def]
QED

Theorem evaluate_bvi_to_cb:
  ∀cb loc x env s t r bs.
    evaluate ([x],env,s) = (r,t) ∧
    r ≠ Rerr (Rabort Rtype_error) ∧
    bvi_to_cb loc x = SOME (bs,cb) ⇒
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
    >> drule evaluate_expand_env
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
  >> irule evaluate_expand_env
  >> gvs []
QED

Theorem WF_I_I[local]:
  WF (measure I LEX measure I)
Proof
  irule WF_LEX >> simp [prim_recTheory.WF_measure]
QED

Theorem evaluate_rewrite_tmc:
  ∀n xs ^s env1 loc r t opt f s' env2.
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
       (∀loc_opt.
          (∀wrap work.
             rewrite_wrapper loc loc_opt (HD xs) = SOME wrap ⇒
             ∃t1 f_wrap.
               evaluate ([wrap], env2, s') = (r',t1) ∧
               state_rel f_wrap t t1 ∧
               f SUBMAP f_wrap ∧
               only_fresh f f_wrap s'.refs) ∧
          (∀i j wrap work.
             i = LENGTH env1 ∧
             j = LENGTH env1 + 1 ∧
             (∃c. hole_has_val f env1 env2 s'.refs c) ∧
             rewrite_worker loc loc_opt i j (HD xs) = work ⇒
             ∃rrr t2 f_work.
               evaluate ([work], env2, s') = (rrr,t2) ∧
               opt_res_rel r' rrr ∧
               state_rel f_work t t2 ∧
               f SUBMAP f_work ∧
               only_fresh f f_work s'.refs ∧
               holes_unchanged_except f s'.refs t2.refs {EL i env2} ∧
               ∀res_v.
                 r' = Rval [res_v] ⇒
                 hole_has_val f env1 env2 t2.refs res_v)))
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
  >> reverse $ Cases_on ‘bvi_to_cb loc h = NONE’
  >-
   (Cases_on ‘bvi_to_cb loc h’
    >- gvs []
    >> Cases_on ‘x’
    >> gvs []
    >> rename [‘bvi_to_cb _ x = SOME (bs,cb)’]
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
  >> first_assum $ qspecl_then [‘xs’, ‘s’, ‘env’, ‘loc’] mp_tac
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
  >> Cases_on ‘v’
  >> rename [‘do_app op _ _ = Rval (v,r)’]
  >> gvs [CaseEq "prod"]
  >> drule $ iffLR list_rel_reverse
  >> strip_tac
  >> drule_all do_app_op_rel
  >> strip_tac
  >> gvs [CaseEq "prod"]
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
  >> ho_match_mp_tac evaluate_fill_hole
  >> gvs [evaluate_def]
  >> rpt $ first_assum $ irule_at Any
QED

(* I think this can replace the "wf" theorem *)
Theorem bvi_to_cb_cases:
  ∀loc x bs cb.
    bvi_to_cb loc x = SOME (bs,cb) ⇒
    (∃tag args l child r.
       x = Op (BlockOp (Cons tag)) args ∧
       cb = CallBlock tag l child r) ∨
    (∃ts args.
       x = Call ts (SOME loc) args NONE)
Proof
  rw []
  >> Cases_on ‘cb’
  >-
   (Cases_on ‘x’ >> gvs [bvi_to_cb_def, call_to_cb_def, CaseEq "option", CaseEq "prod", CaseEq "sum"]
    >> Cases_on ‘o'’ >> gvs [dest_Cons_def]
    >> Cases_on ‘b’ >> gvs [dest_Cons_def]
    >> imp_res_tac bvi_to_cb_aux_wf
    >> gvs [])
  >> Cases_on ‘x’ >> gvs [bvi_to_cb_def, call_to_cb_def, CaseEq "option", CaseEq "prod", CaseEq "sum"]
  >> imp_res_tac bvi_to_cb_aux_wf
  >> gvs []
QED

(*
Definition hypothesis_def:
  hypothesis xs' (s'' : (num # γ, 'ffi) bviSem$state) env1' loc' r' t' opt' f' s'³' env2' (s : (num # γ, 'ffi) bviSem$state) ⇔
    s''.clock < s.clock ⇒
    ∀env1' loc' r'' t' opt' f'' s'³' env2'.
      evaluate (xs',env1',s'') = (r'',t') ∧
      env_rel opt' f'' env1' env2' ∧ state_rel f'' s'' s'³' ∧
      (opt' ⇒ LENGTH xs' = 1) ∧ r'' ≠ Rerr (Rabort Rtype_error) ⇒
      ∃t'' f'³' r'³'.
        evaluate (xs',env2',s'³') = (r'³',t'') ∧
        result_rel (LIST_REL (v_rel f'³')) (v_rel f'³') r'' r'³' ∧
        state_rel f'³' t' t'' ∧ f'' ⊑ f'³' ∧
        only_fresh f'' f'³' s'³'.refs ∧
        holes_unchanged_except f'' s'³'.refs t''.refs ∅ ∧
        ∀loc_opt.
          (∀wrap.
             LENGTH xs' = 1 ∧
             rewrite_wrapper loc' loc_opt (HD xs') = SOME wrap ⇒
             ∃t1 f_wrap.
               evaluate ([wrap],env2',s'³') = (r'³',t1) ∧
               state_rel f_wrap t' t1 ∧ f'' ⊑ f_wrap ∧
               only_fresh f'' f_wrap s'³'.refs) ∧
          (opt' ∧ (∃c. hole_has_val f'' env1' env2' s'³'.refs c) ⇒
           ∃rrr t2 f_work.
             evaluate
             ([rewrite_worker loc' loc_opt (LENGTH env1') (LENGTH env1' + 1) (HD xs')],env2',s'³') = (rrr,t2) ∧
             opt_res_rel r'³' rrr ∧ state_rel f_work t' t2 ∧
             f'' ⊑ f_work ∧ only_fresh f'' f_work s'³'.refs ∧
             holes_unchanged_except f'' s'³'.refs t2.refs {env2'❲LENGTH env1'❳} ∧
             ∀res_v.
               r'³' = Rval [res_v] ⇒
               hole_has_val f'' env1' env2' t2.refs res_v)
End
*)

Definition opt_res_rel_def:
  opt_res_rel f (r1 : (v list, v) result) (r2 : (v list, v) result) =
  case (r1,r2) of
  | (Rval v1,Rval [Block 0 []]) => T
  | (Rerr e1,Rerr e2) => exc_rel (v_rel f) e1 e2
  | _ => F
End

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

Definition hypothesis_def:
  hypothesis xs ^s (sc : (num # γ, 'ffi) bviSem$state) ⇔
    s.clock < sc.clock ⇒
    ∀env1 loc r t opt f s' env2.
      evaluate (xs, env1, s) = (r, t) ∧
      env_rel opt f env1 env2 ∧
      state_rel f s s' ∧
      (opt ⇒ LENGTH xs = 1) ∧
      r ≠ Rerr (Rabort Rtype_error) ⇒
      (∃t' f' r'.
         evaluate (xs, env2, s') = (r', t') ∧
         result_rel (LIST_REL (v_rel f')) (v_rel f') r r' ∧
         state_rel f' t t' ∧
         f SUBMAP f' ∧
         only_fresh f f' s'.refs ∧
         holes_unchanged_except f s'.refs t'.refs ∅) ∧
      (∀loc_opt.
         (∀wrap. (* I think we also need length xs = 1 *)
            rewrite_wrapper loc loc_opt (HD xs) = SOME wrap ⇒
            ∃t_wrap f_wrap r_wrap.
              evaluate ([wrap], env2, s') = (r_wrap,t_wrap) ∧
              result_rel (LIST_REL (v_rel f_wrap)) (v_rel f_wrap) r r_wrap ∧
              state_rel f_wrap t t_wrap ∧
              f SUBMAP f_wrap ∧
              only_fresh f f_wrap s'.refs ∧
              holes_unchanged_except f s'.refs t_wrap.refs ∅) ∧
         (opt ⇒
          (∀i j work.
             i = LENGTH env1 ∧
             j = LENGTH env1 + 1 ∧
             (∃c. hole_has_val f env1 env2 s'.refs c) ∧
             rewrite_worker loc loc_opt i j (HD xs) = work ⇒
             ∃r_work f_work t_work.
               evaluate ([work], env2, s') = (r_work,t_work) ∧
               opt_res_rel f_work r r_work ∧
               state_rel f_work t t_work ∧
               f SUBMAP f_work ∧
               only_fresh f f_work s'.refs ∧
               holes_unchanged_except f s'.refs t_work.refs {EL i env2} ∧
               ∀res_v.
                 r = Rval [res_v] ⇒
                 ∃res_v' ptr.
                   EL i env2 = RefPtr F ptr ∧
                   mb_rel f_work (t_work.refs \\ ptr) res_v res_v' ∧
                   hole_has_val f env1 env2 t_work.refs res_v')))
End

Definition alloc_hole_has_val_def:
  alloc_hole_has_val f refs extras i_ptr c_idx c ⇔
    ∃hole_ptr tag left right.
      i_ptr < LENGTH extras ∧
      extras❲i_ptr❳ = RefPtr F hole_ptr ∧
      c_idx = LENGTH left ∧
      hole_ptr ∉ FRANGE f ∧
      FLOOKUP refs hole_ptr = SOME (MutBlock tag left c right)
End

(* Move me. This is duplicated somewhere... *)
Theorem length_shift_vars:
  ∀l n.
     LENGTH (shift_vars n l) = LENGTH l
Proof
  Induct
  >- gvs [shift_vars_def]
  >> rw []
  >> gvs [shift_vars_def]
QED

(* Move me *)
Theorem shift_cb_dist:
  shift_cb n1 (shift_cb n2 cb) =
  shift_cb (n1 + n2) cb
Proof
  cheat
QED

Theorem env_rel_args:
  ∀args opt f env1 env2 (s1 : (num # γ, 'ffi) bviSem$state).
    env_rel opt f env1 env2 ∧
    evaluate (MAP (λn. Var n) args,env1,s1) = (Rval (MAP (λn. env1❲n❳) args),s1) ⇒
    env_rel F f (MAP (λn. env1❲n❳) args) (MAP (λn. env2❲n❳) args)
Proof
  cheat
QED

Theorem env_rel_opt_args:
  ∀args opt f env1 env2 (s1 : (num # γ, 'ffi) bviSem$state) ptr idx.
    env_rel opt f env1 env2 ∧
    evaluate (MAP (λn. Var n) args,env1,s1) = (Rval (MAP (λn. env1❲n❳) args),s1) ⇒
    env_rel T f (MAP (λn. env1❲n❳) args) (MAP (λn. env2❲n❳) args ++ [RefPtr F ptr; Number idx])
Proof
  cheat
QED

Theorem code_rel_cases:
  ∀arity exp loc s1 s2 f.
    lookup loc s1.code = SOME (arity,exp) ∧
    state_rel f s1 s2 ⇒
    ∃exp'.
      lookup loc s2.code = SOME (arity,exp') ∧
      (exp ≠ exp' ⇒
       ∃n.
         rewrite_wrapper loc n exp = SOME exp')
Proof
  rw []
  >> gvs [state_rel_def, code_rel_def]
  >> first_x_assum drule
  >> strip_tac
  >> Cases_on ‘compile_exp loc n arity exp’
  >- gvs []
  >> gvs []
  >> Cases_on ‘x’
  >> gvs [compile_exp_def, CaseEq "option"]
  >> rw []
  >> qexists ‘n’
  >> gvs []
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
      >> cheat)
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

Theorem evaluate_cb:
  ∀cb bs loc loc_opt exp wrap work arity f opt env env2 ^s s' t t' r r'.
    evaluate ([cb_to_bvi loc cb],env,s) = (r,t) ∧
    env_rel opt f env env2 ∧
    state_rel f s s' ∧
    lookup loc s.code = SOME (arity,exp) ∧
    lookup loc s'.code = SOME (arity,wrap) ∧
    rewrite_wrapper loc loc_opt exp = SOME wrap ∧
    lookup loc_opt s'.code = SOME (arity + 2, work) ∧
    rewrite_worker loc loc_opt arity (arity + 1) exp = work ∧
    r ≠ Rerr (Rabort Rtype_error) ∧
    (∀xs' s''.
       hypothesis xs' s'' s) ⇒
    (∃r' t' f'.
       evaluate ([cb_to_bvi loc cb],env2,s') = (r',t') ∧
       result_rel (LIST_REL (v_rel f')) (v_rel f') r r' ∧
       state_rel f' t t' ∧
       f ⊑ f' ∧
       only_fresh f f' s'.refs ∧
       holes_unchanged_except f s'.refs t'.refs ∅) ∧
    (∀tag left child right.
       cb = CallBlock tag left child right ⇒
       ∃t_wrap f_wrap r_wrap.
         evaluate ([cb_to_bvi_wrapper tag left child right loc_opt], env2, s') = (r_wrap,t_wrap) ∧
         result_rel (LIST_REL (v_rel f_wrap)) (v_rel f_wrap) r r_wrap ∧
         state_rel f_wrap t t_wrap ∧
         f SUBMAP f_wrap ∧
         only_fresh f f_wrap s'.refs ∧
         holes_unchanged_except f s'.refs t_wrap.refs ∅) ∧
    (∀refs extras ptr idx.
       state_ref_rel f s.refs refs ∧
       (∃c. alloc_hole_has_val f refs extras ptr idx c) ⇒
       ∃r_aux t_aux f_aux.
         evaluate ([cb_to_bvi_worker_aux (shift_cb (LENGTH extras) cb) loc_opt ptr idx],extras ++ env2,s' with refs := refs) = (r_aux,t_aux) ∧
         opt_res_rel f_aux r r_aux ∧
         state_rel f_aux t t_aux ∧
         f ⊑ f_aux ∧
         only_fresh f f_aux refs ∧
         holes_unchanged_except f refs t_aux.refs {extras❲ptr❳} ∧
         ∀res_v.
           r = Rval [res_v] ⇒
           ∃res_v' p.
             EL ptr extras = RefPtr F p  ∧
             mb_rel f_aux (t_aux.refs \\ p) res_v res_v' ∧
             alloc_hole_has_val f t_aux.refs extras ptr idx res_v') ∧
    (opt ⇒
     (∀ptr idx work.
        ptr = LENGTH env ∧
        idx = LENGTH env + 1 ∧
        (∃c. hole_has_val f env env2 s'.refs c) ⇒
        ∃r_work f_work t_work.
          evaluate ([cb_to_bvi_worker cb loc_opt ptr idx], env2, s') = (r_work,t_work) ∧
          opt_res_rel f_work r r_work ∧
          state_rel f_work t t_work ∧
          f SUBMAP f_work ∧
          only_fresh f f_work s'.refs ∧
          holes_unchanged_except f s'.refs t_work.refs {EL ptr env2} ∧
          ∀res_v.
            r = Rval [res_v] ⇒
            ∃res_v' p.
              EL ptr env2 = RefPtr F p ∧
              mb_rel f_work (t_work.refs \\ p) res_v res_v' ∧
              hole_has_val f env env2 t_work.refs res_v'))
Proof

  reverse $ Induct
  >-
   (rpt gen_tac
    >> strip_tac
    >> rename [‘RCall ts args’]
    >> gvs [cb_to_bvi_def, evaluate_def, CaseEq "prod"]
    >> drule_then drule evaluate_vars
    >> impl_tac >- (spose_not_then assume_tac >> gvs [CaseEq "prod"])
    >> strip_tac
    >> gvs []
    >> gvs [bvlSemTheory.find_code_def, CaseEq "prod", CaseEq "option"]
    >> ‘s.clock = s'.clock’ by gvs [state_rel_def]
    >> gvs []
    >> Cases_on ‘s'.clock < ts + 1’
    >-
     (gvs []
      >> cheat)
    >> gvs [CaseEq "prod"]
    >> ‘(v3,s'³') = (r,t)’ by gvs [CaseEq "result", CaseEq "error_result"]
    >> rw []
    (* Untransformed *)
    >-
     (gvs [hypothesis_def]
      >> first_x_assum $ qspecl_then [‘[exp]’, ‘dec_clock (ts + 1) s’] mp_tac
      >> impl_tac >- gvs [dec_clock_def]
      >> drule_all env_rel_args
      >> strip_tac
      >> rpt $ disch_then drule
      >> ‘state_rel f (dec_clock (ts + 1) s) (dec_clock (ts + 1) s')’ by
        (irule state_rel_dec
         >> Cases_on ‘s'.clock’
         >- gvs []
         >> gvs [])
      >> disch_then drule
      >> gvs [GSYM PULL_FORALL]
      >> strip_tac
      >> rename [‘state_rel _ t _’]
      >> first_x_assum drule
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
     (gvs [shift_cb_def, cb_to_bvi_worker_def, cb_to_bvi_worker_aux_def, optimise_call_def, evaluate_def, evaluate_APPEND, evaluate_shift_vars]
      >> gvs [alloc_hole_has_val_def, do_app_def, do_app_aux_def]
      >> ‘backend_common$small_enough_int (&LENGTH left)’ by cheat
      >> gvs [bvlSemTheory.find_code_def, EL_APPEND_EQN]
      >> gvs [hypothesis_def]
      >> first_x_assum $ qspecl_then [‘[exp]’, ‘dec_clock (ts + 1) s’] mp_tac
      >> impl_tac >- gvs [dec_clock_def]
      >> disch_then drule
      >> drule_then drule env_rel_opt_args
      >> disch_then $ qspecl_then [‘hole_ptr’, ‘&LENGTH left’] assume_tac
      >> disch_then drule
      >> disch_then $ qspecl_then [‘loc’, ‘dec_clock (ts + 1) (s' with refs := refs)’] mp_tac
      >> impl_tac
      >-
       (gvs []
        >> gvs [state_rel_def, dec_clock_def])
      >> strip_tac
      >> rename [‘state_rel _ t _’]
      >> first_x_assum $ qspec_then ‘loc_opt’ mp_tac
      >> gvs []
      >> strip_tac
      >> pop_assum mp_tac
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
      >> conj_tac
      >- gvs [EL_APPEND_EQN, LENGTH_MAP]
      >> rw []
      >> ‘hole_ptr = ptr'’ by gvs [EL_APPEND_EQN, LENGTH_MAP]
      >> gvs []
      >> first_assum $ irule_at Any
      >> gvs [hole_has_val_def, EL_APPEND_EQN, LENGTH_MAP])
    (* Work *)
    >> gvs [cb_to_bvi_worker_def, evaluate_def]
    >> gvs [optimise_call_def, evaluate_def, evaluate_APPEND]
    >> imp_res_tac env_rel_length_opt
    >> gvs [bvlSemTheory.find_code_def, EL_APPEND_EQN]
    >> gvs [hypothesis_def]
    >> first_x_assum $ qspecl_then [‘[exp]’, ‘dec_clock (ts + 1) s’] mp_tac
    >> impl_tac >- gvs [dec_clock_def]
    >> disch_then drule
    >> drule_then drule env_rel_opt_args
    >> imp_res_tac env_rel_strip_extras
    >> disch_then $ qspecl_then [‘hole_ptr’, ‘hole_idx’] assume_tac
    >> disch_then drule
    >> disch_then $ qspecl_then [‘loc’, ‘dec_clock (ts + 1) s'’] mp_tac
    >> impl_tac
    >-
     (gvs []
      >> gvs [state_rel_def, dec_clock_def])
    >> strip_tac
    >> rename [‘state_rel _ t _’]
    >> first_x_assum $ qspec_then ‘loc_opt’ mp_tac
    >> gvs []
    >> strip_tac
    >> pop_assum mp_tac
    >> impl_tac
    >-
     (gvs [hole_has_val_def]
      >> gvs [EL_APPEND_EQN, LENGTH_MAP])
    >> strip_tac
    >> gvs []
    >> qexistsl [‘r_work’, ‘f_work’, ‘t_work’]
    >> ‘(env2' ++ [RefPtr F hole_ptr; Number hole_idx])❲LENGTH env❳ = RefPtr F hole_ptr’ by gvs [EL_APPEND_EQN]
    >> ‘(env2' ++ [RefPtr F hole_ptr; Number hole_idx])❲LENGTH env + 1❳ = Number hole_idx’ by gvs [EL_APPEND_EQN]
    >> gvs []
    >> conj_tac
    >-
     (CASE_TAC >> gvs []
      >> CASE_TAC >> gvs [])
    >> conj_tac
    >- gvs [EL_APPEND_EQN, LENGTH_MAP]
    >> rw []
    >> ‘hole_ptr = ptr’ by gvs [EL_APPEND_EQN, LENGTH_MAP]
    >> gvs []
    >> first_assum $ irule_at Any
    >> gvs [hole_has_val_def, EL_APPEND_EQN, LENGTH_MAP])

  >> rpt gen_tac
  >> strip_tac
  >> rename [‘CallBlock tag left child right’]
  >> gvs [cb_to_bvi_def, evaluate_def, evaluate_APPEND, CaseEq "prod"]
  >> drule_then drule evaluate_vars
  >> impl_tac >- (spose_not_then assume_tac >> gvs [CaseEq "prod"])
  >> strip_tac
  >> gvs [CaseEq "prod"]
  >> last_x_assum drule
  >> rpt $ disch_then drule
  >> impl_tac >- gvs [CaseEq "prod", CaseEq "result"]
  >> strip_tac >> gvs []
  >> rename [‘state_rel f' u u'’, ‘result_rel _ _ r r'’]
  >> reverse $ Cases_on ‘r’
  >- cheat
  >> gvs [CaseEq "prod"]
  >> rename [‘state_rel f' u u'’]
  >> drule_then drule evaluate_vars
  >> impl_tac >- gvs [CaseEq "prod", CaseEq "result"]
  >> strip_tac
  >> gvs []
  >> rename [‘state_rel f' u u'’]
  >> rw []
  (* Untransformed *)
  >-
   (gvs [do_app_def, do_app_aux_def, bvl_to_bvi_id]
    >> first_assum $ irule_at Any
    >> imp_res_tac evaluate_SING_IMP
    >> gvs [REVERSE_APPEND]
    >> simp [Once v_rel_cases]
    >> irule LIST_REL_APPEND_suff
    >> irule_at Any LIST_REL_APPEND_suff
    >> simp [LIST_REL_MAP]
    >> rpt $ irule_at Any LIST_REL_refl
    >> simp []
    (* Lemma? *)
    >> cheat)

  (* Wrap *)
  >-
   (gvs [cb_to_bvi_wrapper_def, evaluate_def, mut_cons_def, evaluate_APPEND]
    >> gvs [do_app_def, do_app_aux_def, backend_commonTheory.small_enough_int_def]
    >> gvs [LENGTH_MAP, REVERSE_APPEND, TAKE_APPEND, DROP_APPEND, GSYM MAP_REVERSE, GSYM MAP_TAKE, GSYM MAP_DROP, DROP_LENGTH_TOO_LONG]
    >> ‘TAKE (LENGTH right) (REVERSE right) = REVERSE right’ by gvs [LENGTH_REVERSE, TAKE_LENGTH_ID]
    >> simp []
    >> gvs [EL_APPEND_EQN, LENGTH_MAP, LENGTH_REVERSE]
    >> first_x_assum $ qspecl_then [‘s'.refs⟨
                                     (LEAST ptr. ptr ∉ FDOM s'.refs) ↦
                                     MutBlock tag (MAP (λn. env2❲n❳) (REVERSE right)) (Number 0) (MAP (λn. env2❲n❳) (REVERSE left))⟩’,
                                    ‘[RefPtr F (LEAST ptr. ptr ∉ FDOM s'.refs)]’, ‘0’, ‘LENGTH right’] mp_tac

    >> impl_tac
    >-
     (conj_tac
      >-
       (irule state_ref_rel_filled
        >> cheat)
      >> gvs [alloc_hole_has_val_def, FLOOKUP_SIMP]
      >> cheat)
    >> strip_tac
    >> gvs []
    >> imp_res_tac evaluate_SING_IMP
    >> gvs []
    >> reverse CASE_TAC
    >- gvs [opt_res_rel_def]
    >> imp_res_tac evaluate_SING_IMP
    >> gvs []
    >> rename [‘opt_res_rel _ (Rval [v]) (Rval [v'])’]
    >> gvs [bvi_tmcTheory.finalise_cons_def, evaluate_def]
    >> gvs [do_app_def, do_app_aux_def]
    >> gvs [alloc_hole_has_val_def]
    >> drule mb_rel_cons
    >> rpt $ disch_then $ drule_at Any
    (* At this point, what we need:
       holes_unchanged_except should be stronger: for the "changed" holes, _only_ the hole should be changed.
       ie. tag/left/right should be the same.
       this will give us MAP (λn. env2)s instead of left'/right'.
       Then we need a lemma to get LIST_REL for the MAP (λn. env1) to MAP (λn. env2).
       Then we need lemmas for only_fresh/holes_unchanged_except removing a pointer from the refs which should be easy.
     *)
    >> disch_then $ qspecl_then [‘MAP (λn. env❲n❳) (REVERSE right)’, ‘MAP (λn. env❲n❳) (REVERSE left)’] mp_tac
    >> impl_tac >- cheat
    >> strip_tac
    >> ‘state_ref_rel f_aux u.refs t_aux.refs’ by gvs [state_rel_def]
    >> drule_all evaluate_finalise_cons
    >> strip_tac
    >> gvs []
    >> qexists ‘f_aux’
    >> gvs [bvl_to_bvi_id]
    >> cheat)

  (* Aux *)
  >-
   (gvs [cb_to_bvi_worker_aux_def, evaluate_def, shift_cb_def]
    >> gvs [mut_cons_def, evaluate_def, evaluate_APPEND]
    >> gvs [evaluate_shift_vars]
    >> gvs [do_app_def, do_app_aux_def, backend_commonTheory.small_enough_int_def]
    >> gvs [length_shift_vars]
    >> gvs [LENGTH_MAP, REVERSE_APPEND, TAKE_APPEND, DROP_APPEND, GSYM MAP_REVERSE, GSYM MAP_TAKE, GSYM MAP_DROP, DROP_LENGTH_TOO_LONG]
    >> gvs [update_cons_def, evaluate_def]
    >> gvs [do_app_def, do_app_aux_def]
    >> ‘backend_common$small_enough_int (&idx)’ by cheat
    >> gvs []
    >> Cases_on ‘ptr + 1’
    >- gvs []
    >> ‘n = ptr’ by gvs []
    >> gvs [alloc_hole_has_val_def]
    >> gvs [FLOOKUP_SIMP, EL_APPEND_EQN]
    >> IF_CASES_TAC
    >- cheat (* contradiction *)
    >> gvs []

    >> first_x_assum $ qspecl_then [‘refs⟨
                                     hole_ptr ↦ MutBlock tag' left' (RefPtr F (LEAST ptr. ptr ∉ FDOM refs)) right';
                                     (LEAST ptr. ptr ∉ FDOM refs) ↦ MutBlock tag
                                                                  (MAP (λn. env2❲n❳) (TAKE (LENGTH right) (REVERSE right)))
                                                                  (Number 0)
                                                                  (MAP (λn. env2❲n❳) (REVERSE left))⟩’,
                                    ‘Unit::RefPtr F (LEAST ptr. ptr ∉ FDOM refs)::extras’, ‘1’, ‘LENGTH right’] mp_tac

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
          >> cheat (* contradiction on FLOOKUP refs (LEAST ptr. ptr ∉ FDOM refs) = SOME w *))
        >> gvs [])
      >> qexistsl [‘Number 0’, ‘tag’, ‘(MAP (λn. env2❲n❳) (TAKE (LENGTH right) (REVERSE right)))’, ‘(MAP (λn. env2❲n❳) (REVERSE left))’]
      >> conj_tac
      >- gvs [LENGTH_MAP]
      >> conj_tac
      >- cheat
      >> gvs [FLOOKUP_SIMP])
    >> strip_tac
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
    >- cheat
    >> conj_tac
    >- cheat
    >> imp_res_tac evaluate_SING_IMP
    >> gvs []
    (* This isn't going to work without the mutblock relation *)
    >> cheat)

  (* Work *)
  >> gvs [evaluate_def, cb_to_bvi_worker_def, mut_cons_def, evaluate_APPEND]
  >> gvs [do_app_def, do_app_aux_def, backend_commonTheory.small_enough_int_def]
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
  >> IF_CASES_TAC
  >- cheat
  >> gvs [hole_has_val_def]
  >> ‘hole_ptr = hole_ptr'’ by gvs [EL_APPEND_EQN]
  >> ‘hole_idx = &LENGTH left'’ by gvs [EL_APPEND_EQN]
  >> ‘TAKE (LENGTH right) (REVERSE right) = REVERSE right’ by gvs [LENGTH_REVERSE, TAKE_LENGTH_ID]
  >> simp []
  (* This should probably be simplified before we get here. *)

  >> first_x_assum $ qspecl_then [‘s'.refs⟨
                                   hole_ptr ↦ MutBlock tag' left' (RefPtr F (LEAST ptr. ptr ∉ FDOM s'.refs)) right';
                                   (LEAST ptr. ptr ∉ FDOM s'.refs) ↦ MutBlock tag
                                                                   (MAP (λn. (env2' ++ [RefPtr F hole_ptr; Number (&LENGTH left')])❲n❳) (REVERSE right))
                                                                   (MAP (λn. (env2' ++ [RefPtr F hole_ptr; Number (&LENGTH left')])❲n❳) (REVERSE right) ++
                                                                    Number 0::MAP (λn. (env2' ++ [RefPtr F hole_ptr; Number (&LENGTH left')])❲n❳) (REVERSE left))❲LENGTH right❳
                                                                   (MAP (λn. (env2' ++ [RefPtr F hole_ptr; Number (&LENGTH left')])❲n❳) (REVERSE left))⟩’,
                                  ‘[Unit; RefPtr F (LEAST ptr. ptr ∉ FDOM s'.refs)]’, ‘1’, ‘LENGTH right’] mp_tac

  >> impl_tac
  >-
   (conj_tac
    >- (* LEMMA *)
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
        >> cheat (* contradiction on FLOOKUP refs (LEAST ptr. ptr ∉ FDOM refs) = SOME w *))
      >> gvs [])
    >> gvs [alloc_hole_has_val_def]
    >> gvs [FLOOKUP_SIMP, LENGTH_MAP]
    >> cheat)
  >> strip_tac
  >> gvs []
  >> qexists ‘f_aux’
  >> imp_res_tac evaluate_SING_IMP
  >> gvs []
  >> conj_tac
  >- gvs [opt_res_rel_def]
  >> conj_tac
  >- gvs [bvl_to_bvi_id]
  >> cheat
QED

Resume evaluate_rewrite_tmc[call_block]:
  cheat
(*  (* Phase 1 theorem in s *)
  drule_all evaluate_bvi_to_cb
  >> simp [Once evaluate_def]
  >> strip_tac
  >> gvs [CaseEq "prod"]
  >> rename [‘evaluate (bs,env,s) = (as,u)’]
  (* Hypothesis on bs *)
  >> first_assum $ qspecl_then [‘bs’, ‘s’] mp_tac
  >> impl_tac
  >- (imp_res_tac bvi_to_cb_size >> gvs [])
  >> imp_res_tac env_rel_relax_opt
  >> rpt $ disch_then drule
  >> impl_tac
  >- (gvs [] >> spose_not_then assume_tac >> gvs [])
  >> disch_then $ qspec_then ‘loc’ assume_tac
  >> gvs []
  >> rename [‘evaluate (bs,env2,s') = (as',u')’]
  >> rename [‘f ⊑ f'’]
  (* Phase 1 theorem in s' *)
  >> Cases_on ‘evaluate ([x],env2,s')’
  >> rename [‘evaluate ([x],env2,s') = (r',t')’]
  >> drule evaluate_bvi_to_cb
  >> disch_then $ drule_at Any
  >> impl_tac >- cheat (* I think I broke something *)
  >> simp [Once evaluate_def]
  >> strip_tac
  >> reverse $ gvs [CaseEq "result"]
  >- (* bs fails *)
   (rename [‘exc_rel (v_rel f') e e'’]
    >> qexistsl [‘t'’, ‘f'’, ‘Rerr e'’]
    >> gvs []
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
  >> rename [‘LIST_REL (v_rel f') vs vs'’]
  >> qpat_x_assum ‘env_rel _ _ _ _’ kall_tac
  >> qrefinel [‘t'’, ‘_’, ‘r'’]
  >> gvs [GSYM PULL_FORALL]
  >> cheat *)
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
  >> imp_res_tac evaluate_clock
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
  >> gvs []
QED

Resume evaluate_rewrite_tmc[if]:
  gvs [evaluate_def]
  >> gvs [CaseEq "prod", PULL_EXISTS]
  >> rename [‘evaluate ([x1],env,s) = (r1,u)’]
  (* First inductive hypothesis *)
  >> first_assum $ qspecl_then [‘[x1]’,‘s’,‘env’, ‘loc’] mp_tac
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
      >> first_x_assum $ qspecl_then [‘[x2]’, ‘u’, ‘env’, ‘loc’] mp_tac
      >> imp_res_tac evaluate_clock
      >> gvs []
      >> qpat_x_assum ‘env_rel F _ _ _’ kall_tac
      >> drule_all env_rel_submap
      >> strip_tac
      >> disch_then drule
      >> disch_then drule
      >> fs[GSYM PULL_FORALL]
      >> strip_tac
      >> qexistsl [‘t''’, ‘f'³'’, ‘r''’]
      >> gvs []
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
      >> strip_tac
      >> gvs []
      >> rpt gen_tac
      >> first_x_assum $ qspecl_then [‘loc_opt’] mp_tac
      >> strip_tac
      >> rw []
      >-
       (drule wrapper_strip_if_then
        >> strip_tac
        >-
         (gvs [evaluate_def]
          >> rpt $ first_assum $ irule_at Any
          >> conj_tac
          >- imp_res_tac SUBMAP_TRANS
          >> irule only_fresh_trans
          >> rpt $ first_assum $ irule_at Any
          >> imp_res_tac evaluate_refs_SUBSET)
        >> gvs [evaluate_def]
        >> rpt $ first_assum $ irule_at Any
        >> conj_tac
        >- imp_res_tac SUBMAP_TRANS
        >> irule only_fresh_trans
        >> rpt $ first_assum $ irule_at Any
        >> imp_res_tac evaluate_refs_SUBSET)
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
      >> drule_all env_rel_length_opt
      >> strip_tac
      >> gvs [EL_APPEND_EQN]
      >> first_assum $ irule_at Any
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
        >> gvs [holes_unchanged_except_def])
      >> rw []
      >> irule hole_has_val_submap
      >> first_assum $ irule_at Any
      >> gvs [])
    (* Else inductive hypothesis *)
    >> Cases_on ‘v1 = Boolv F’ >> gvs []
    >> ‘v1' = Boolv F’ by (drule $ iffLR v_rel_cases >> gvs [bvlSemTheory.Boolv_def])
    >> gvs []
    >> first_x_assum $ qspecl_then [‘[x3]’, ‘u’, ‘env’, ‘loc’] mp_tac
    >> imp_res_tac evaluate_clock
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
    >> strip_tac
    >> gvs []
    >> first_x_assum $ qspecl_then [‘loc_opt’] mp_tac
    >> strip_tac
    >> rw []
    >-
     (drule wrapper_strip_if_else
      >> strip_tac
      >-
       (gvs [evaluate_def]
        >> rpt $ first_assum $ irule_at Any
        >> conj_tac
        >- imp_res_tac SUBMAP_TRANS
        >> irule only_fresh_trans
        >> rpt $ first_assum $ irule_at Any
        >> imp_res_tac evaluate_refs_SUBSET)
      >> gvs [evaluate_def]
      >> rpt $ first_assum $ irule_at Any
      >> conj_tac
      >- imp_res_tac SUBMAP_TRANS
      >> irule only_fresh_trans
      >> rpt $ first_assum $ irule_at Any
      >> imp_res_tac evaluate_refs_SUBSET)
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
    >> drule_all env_rel_length_opt
    >> strip_tac
    >> gvs [EL_APPEND_EQN]
    >> first_assum $ irule_at Any
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
    >-
     (gvs [evaluate_def]
      >> rpt $ first_assum $ irule_at Any)
    >> gvs [evaluate_def]
    >> rpt $ first_assum $ irule_at Any)
  >> gvs [rewrite_worker_def, evaluate_def, opt_res_rel_def, holes_unchanged_except_def]
  >> rpt $ first_assum $ irule_at Any
QED

Resume evaluate_rewrite_tmc[lett]:
  gvs [evaluate_def]
  >> gvs [CaseEq "prod", PULL_EXISTS]
  >> rename [‘evaluate (xs,env,s) = (rs,u)’]
  (* First inductive hypothesis *)
  >> first_assum $ qspecl_then [‘xs’, ‘s’, ‘env’] mp_tac
  >> impl_tac
  >- (imp_res_tac evaluate_clock >> gvs [])
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
    >> gvs []
    (* Second inductive hypothesis *)
    >> first_x_assum $ qspecl_then [‘[x2]’, ‘u’, ‘vs ++ env’] mp_tac
    >> impl_tac
    >- (imp_res_tac evaluate_clock >> gvs [])
    >> gvs []
    >> disch_then $ drule_at $ Pos $ el 2
    >> disch_then $ qspecl_then [‘loc’, ‘opt’, ‘vs' ++ env2’] mp_tac
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
    >> qexistsl [‘t''’, ‘f'³'’, ‘r''’]
    >> rpt gen_tac
    >> gvs []
    >> first_x_assum $ qspec_then ‘loc_opt’ mp_tac
    >> gvs [GSYM PULL_FORALL]
    >> strip_tac
    >> gvs []
    >> rw []
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
      >> gvs [evaluate_def]
      >> first_assum $ irule_at Any
      >> conj_tac
      >- imp_res_tac SUBMAP_TRANS
      >> irule only_fresh_trans
      >> rpt $ first_assum $ irule_at Any
      >> imp_res_tac evaluate_refs_SUBSET)
    >> gvs []
    >> first_x_assum $ qspec_then ‘c’ mp_tac
    >> impl_tac
    >-
     (irule hole_has_val_append
      >> gvs []
      >> drule_all env_rel_strip_extras
      >> strip_tac
      >> gvs []
      >> irule unchanged_hole_has_val
      >> first_assum $ irule_at Any
      >> qexists ‘EMPTY’
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
  >> gvs [GSYM PULL_FORALL]
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
  >> gvs [holes_unchanged_except_def]
QED

Resume evaluate_rewrite_tmc[raise]:
  gvs [evaluate_def]
  >> gvs [CaseEq "prod", PULL_EXISTS]
  >> rename [‘evaluate ([x],env,s) = (v,u)’]
  >> first_x_assum $ qspecl_then [‘[x]’, ‘s’, ‘env’] mp_tac
  >> impl_tac
  >- gvs []
  >> rpt $ disch_then drule
  >> disch_then $ qspec_then ‘loc’ mp_tac
  >> gvs []
  >> impl_tac
  >- (spose_not_then assume_tac >> gvs [])
  >> gvs [GSYM PULL_FORALL]
  >> strip_tac
  >> gvs [PULL_EXISTS, GSYM PULL_FORALL]
  >> rpt $ first_assum $ irule_at Any
  >> gvs []
  >> Cases_on ‘v’ >> gvs []
  >-
   (imp_res_tac evaluate_SING_IMP
    >> gvs []
    >> rw []
    >-
     (gvs [evaluate_def, rewrite_wrapper_def])
    >> gvs [evaluate_def, rewrite_worker_def, opt_res_rel_def]
    >> first_assum $ irule_at Any
    >> gvs [holes_unchanged_except_def])
  >> rw []
  >- gvs [evaluate_def, rewrite_wrapper_def]
  >> gvs [evaluate_def, rewrite_worker_def, opt_res_rel_def]
  >> first_assum $ irule_at Any
  >> gvs [holes_unchanged_except_def]
QED

Resume evaluate_rewrite_tmc[tick]:
  cheat
       (*
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
*)
QED

Resume evaluate_rewrite_tmc[force]:
  cheat
QED

Resume evaluate_rewrite_tmc[call_non_opt]:

  gvs [evaluate_def]
  >> IF_CASES_TAC >> gvs []
  >> gvs [CaseEq "prod", PULL_EXISTS]
  >> rename [‘evaluate (xs,env,s) = (v_xs,u)’]
  (* xs inductive hypothesis *)
  >> first_assum $ qspecl_then [‘xs’, ‘s’, ‘env’] mp_tac
  >> impl_tac
  >- gvs []
  >> disch_then drule
  >> drule env_rel_relax_opt
  >> gvs []
  >> strip_tac
  >> rpt $ disch_then drule
  >> impl_tac
  >- (CCONTR_TAC >> gvs [])
  >> disch_then $ qspec_then ‘loc’ mp_tac
  >> strip_tac
  >> gvs []
  >> reverse $ Cases_on ‘v_xs’ >> gvs []
  >- (* Error case *)
   (rename [‘evaluate (xs,env2,s') = (Rerr e',t')’]
    >> qexistsl [‘t'’, ‘f''’, ‘Rerr e'’]
    >> rpt gen_tac
    >> gvs []
    >> strip_tac
    >> gvs [rewrite_wrapper_def]
    >> rw []
    >> gvs [rewrite_worker_def, fill_hole_def, evaluate_def] >> IF_CASES_TAC >> gvs []
    >> gvs [opt_res_rel_def]
    >> qexists ‘f''’
    >> gvs []
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
    >> qexistsl [‘u' with clock := 0’, ‘f''’, ‘Rerr (Rabort Rtimeout_error)’]
    >> gvs []
    >> rw []
    >- gvs [rewrite_wrapper_def]
    >> gvs [rewrite_worker_def]
    >> qrefinel [‘_’, ‘_’, ‘f''’]
    >> gvs []
    >> ho_match_mp_tac evaluate_fill_hole_err
    >> first_assum $ irule_at Any
    >> gvs [evaluate_def]
    >> IF_CASES_TAC >> gvs []
    >> first_assum $ irule_at Any)
  (* Clock did not run out *)
  >> gvs [CaseEq "prod"]
  >> rename [‘evaluate ([exp],args,dec_clock (ticks + 1) u) = (v_exp, w)’]
  (* Call body inductive hypothesis *)
  >> first_assum $ qspecl_then [‘[exp]’, ‘dec_clock (ticks + 1) u’, ‘args’] mp_tac
  >> impl_tac
  >- (imp_res_tac evaluate_clock >> gvs [dec_clock_def])
  >> rpt $ disch_then drule
  >> drule state_rel_dec
  >> Cases_on ‘u.clock’ >> gvs []
  >> disch_then $ qspec_then ‘ticks + 1’ mp_tac
  >> gvs []
  >> strip_tac
  >> disch_then drule
  >> impl_tac
  >- (spose_not_then assume_tac >> gvs [])
  >> strip_tac
  >> gvs [GSYM PULL_FORALL, PULL_EXISTS]
  >> Cases_on ‘exp = exp'’ >> gvs []
  >-
   (gvs []
    >> rename [‘evaluate ([exp],args',dec_clock (ticks + 1) u') = (v_exp',w')’]
    >> Cases_on ‘v_exp’ >> gvs []
    >-
     (imp_res_tac evaluate_SING_IMP
      >> gvs []
      >> rename [‘state_rel f3 t t'’]
      >> rename [‘v_rel f3 v_exp v_exp'’]
      >> qexistsl [‘t'’, ‘f3’, ‘Rval [v_exp']’]
      >> gen_tac
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
      >> rw []
      >- gvs [rewrite_wrapper_def]
      >> gvs [rewrite_worker_def]
      >> ho_match_mp_tac evaluate_fill_hole
      >> gvs [evaluate_def]
      >> IF_CASES_TAC >> gvs []
      >> rpt $ first_assum $ irule_at Any)
    >> rename [‘exc_rel (v_rel f3) _ _’]
    >> Cases_on ‘e’ >> gvs []
    >-
     (Cases_on ‘handler’ >> gvs []
      >-
       (qexistsl [‘w'’, ‘f3’, ‘Rerr (Rraise v')’]
        >> gen_tac
        >> gvs []
        >> irule_at Any holes_unchanged_except_trans
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
        >> gvs [rewrite_worker_def, fill_hole_def, evaluate_def]
        >> gvs [opt_res_rel_def]
        >> qexists ‘f3’
        >> gvs []
        >> conj_tac
        >- imp_res_tac SUBMAP_TRANS
        >> conj_tac
        >-
         (irule only_fresh_trans
          >> rpt $ first_assum $ irule_at Any
          >> imp_res_tac evaluate_refs_SUBSET)
        >> drule_all holes_unchanged_except_trans
        >> gvs []
        >> strip_tac
        >> irule holes_unchanged_except_subset
        >> first_x_assum $ irule_at Any
        >> gvs [])
      >> rename [‘v_rel f3 v v'’]
      >> gvs [PULL_FORALL]
      >> first_assum $ qspecl_then [‘[x]’, ‘w’, ‘v::env’] mp_tac
      >> impl_tac
      >-
       (imp_res_tac evaluate_clock
        >> gvs []
        >> spose_not_then assume_tac
        >> gvs [state_rel_def, dec_clock_def])
      >> disch_then drule
      >> rev_drule_all env_rel_submap
      >> strip_tac
      >> drule_all env_rel_submap
      >> strip_tac
      >> drule_all env_rel_cons
      >> strip_tac
      >> rpt $ disch_then drule
      >> disch_then $ qspec_then ‘loc’ mp_tac
      >> impl_tac
      >- gvs []
      >> gvs [GSYM PULL_FORALL]
      >> strip_tac
      >> rename [‘evaluate ([x],v'::env2,w') = (v_x',t')’]
      >> rename [‘result_rel (LIST_REL (v_rel f4)) (v_rel f4) v_x v_x'’]
      >> rpt $ first_assum $ irule_at Any
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
      >> rw []
      >- gvs [rewrite_wrapper_def]
      >> gvs [rewrite_worker_def]
      >> Cases_on ‘v_x'’ >> gvs []
      >-
       (imp_res_tac evaluate_SING_IMP
        >> gvs []
        >> ho_match_mp_tac evaluate_fill_hole
        >> gvs [evaluate_def]
        >> rpt $ first_assum $ irule_at Any)
      (* Probably should just update evaluate_fill_hole_err to return a map.... *)
      >> qrefinel [‘_’, ‘_’, ‘f4’]
      >> gvs []
      >> ho_match_mp_tac evaluate_fill_hole_err
      >> gvs [evaluate_def]
      >> rpt $ first_assum $ irule_at Any)
    >> gvs [GSYM PULL_FORALL]
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
    >> qrefinel [‘_’, ‘_’, ‘f3’]
    >> gvs []
    >> ho_match_mp_tac evaluate_fill_hole_err
    >> gvs [evaluate_def]
    >> IF_CASES_TAC >> gvs []
    >> rpt $ first_assum $ irule_at Any)
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
  cheat
  (*
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
                *)
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
QED
