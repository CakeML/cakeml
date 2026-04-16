(*
  Correctness proof for bvi_tailrec
*)
Theory bvi_tmcProof
Ancestors
  bvi_tmc bviProps bviSem bvlSem[qualified] backend_common[qualified]
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
     (*if ~opt then ys = [] else*)
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
        ∀exp_aux exp_opt.
          compile_exp loc n arity exp = SOME (exp_aux,exp_opt) ⇒
          lookup loc c2 = SOME (arity, exp_aux) ∧
          lookup n c2 = SOME (arity + 2, exp_opt)
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

Theorem evaluate_mem_op_update_cons:
  ∀i j n hole_ptr hole_idx hole_val tag l c r env s s'.
    i < LENGTH env ∧
    j < LENGTH env ∧
    n < LENGTH env ∧
    env❲j❳ = Number hole_idx ∧
    env❲n❳ = RefPtr F hole_ptr ∧
    FLOOKUP s.refs hole_ptr = SOME (MutBlock tag l c r) ∧
    hole_idx = &LENGTH l ∧
    s' = s with refs := s.refs⟨hole_ptr ↦ MutBlock tag l env❲i❳ r⟩ ⇒
    evaluate ([Op (MemOp UpdateCons) [Var i; Var j; Var n]],env,s) = (Rval [Block 0 []],s')
Proof
  rw []
  >> gvs [evaluate_def]
  >> gvs [do_app_def]
  >> gvs [do_app_aux_def]
  >> gvs [bvlSemTheory.Unit_def, backend_commonTheory.tuple_tag_def]
  >> gvs [backend_commonTheory.tuple_tag_def]
QED

Theorem evaluate_mem_op_update_cons2:
  ∀f n i j tag l c r v env env' s s' t t'.
    env_rel T f env env' ∧
    n < LENGTH env ∧
    i = LENGTH env ∧
    j = LENGTH env + 1 ∧
    (*FLOOKUP s'.refs hole_ptr = SOME (MutBlock tag l c r) ∧*)
    (*hole_idx = &LENGTH l ∧*)
    (*t' = s' with refs := s'.refs⟨hole_ptr ↦ MutBlock tag l env❲n❳ r⟩*)
    evaluate ([Var n], env, s) = (Rval v, t) ∧
    state_rel f s s' ⇒
    evaluate ([Op (MemOp UpdateCons) [Var n; Var j; Var i]],env',s') = (Rval [Block 0 []],t')
(* state rel?*)
Proof
  rw []
  >> imp_res_tac env_rel_length_opt
  >> drule env_rel_extras_opt
  >> strip_tac
  >> simp [evaluate_def]
  >> gvs [do_app_def]
  >> gvs [do_app_aux_def]
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

Theorem unchanged_hole_has_val:
  ∀f f' env env' hole_ptr hole_idx refs refs' c changed.
    hole_has_val f env (env' ++ [RefPtr F hole_ptr; Number hole_idx]) refs c ∧
    only_fresh f f' refs ∧
    holes_unchanged_except f refs refs' ∅ ∧
    env_rel T f env (env' ++ [RefPtr F hole_ptr; Number hole_idx]) ⇒
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
  ∀f.
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
  rw [do_app_def] >> cheat
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

Theorem aux_strip_if_then:
  rewrite_aux loc loc_opt arity (If x1 x2 x3) = SOME aux ⇒
  ∃aux2 aux3.
    aux = If x1 aux2 aux3 ∧
    (rewrite_aux loc loc_opt arity x2 = SOME aux2 ∨
     aux2 = x2)
Proof
  rw []
  >> gvs [rewrite_aux_def]
  >> Cases_on ‘rewrite_aux loc loc_opt arity x2’
  >> Cases_on ‘rewrite_aux loc loc_opt arity x3’
  >> gvs []
QED

Theorem aux_strip_if_else:
  rewrite_aux loc loc_opt arity (If x1 x2 x3) = SOME aux ⇒
  ∃aux2 aux3.
    aux = If x1 aux2 aux3 ∧
    (rewrite_aux loc loc_opt arity x3 = SOME aux3 ∨
     aux3 = x3)
Proof
  rw []
  >> gvs [rewrite_aux_def]
  >> Cases_on ‘rewrite_aux loc loc_opt arity x2’
  >> Cases_on ‘rewrite_aux loc loc_opt arity x3’
  >> gvs []
QED

Theorem aux_strip_let:
  ∀loc loc_opt arity xs x aux.
    rewrite_aux loc loc_opt arity (Let xs x) = SOME aux ⇒
    ∃aux'.
      aux = Let xs aux' ∧
      rewrite_aux loc loc_opt (arity + LENGTH xs) x = SOME aux'
Proof
  rw []
  >> gvs [rewrite_aux_def]
  >> Cases_on ‘rewrite_aux loc loc_opt (arity + LENGTH xs) x’
  >> gvs []
QED

Theorem aux_strip_tick:
  ∀loc loc_opt arity x aux.
    rewrite_aux loc loc_opt arity (Tick x) = SOME aux ⇒
    ∃aux'.
      aux = Tick aux' ∧
      rewrite_aux loc loc_opt arity x = SOME aux'
Proof
  rw [] >> gvs [rewrite_aux_def]
QED

(* TODO: uniqueness, effectfulness *)
(* Definition has_tmc_call_def:
  has_tmc_call loc (Op (BlockOp (Cons tag)) xs) ⇔
    (∃t args h n.
       EL n xs = Call t loc args h) ∨
    (∃n block_op_cons.
       EL n xs = block_op_cons ∧
       has_tmc_call loc block_op_cons)
End *)

Definition is_block_op_cons_def:
  is_block_op_cons op ⇔
    ∃block_tag.
      op = BlockOp (Cons block_tag)
End

Theorem ry:
  ∀loc tag xs n args h i l hole r.
    cons_to_tc_and_hb loc tag xs = (TCall n args h)⁺ (HoleBlock i l hole r) ⇒
    xs = l ++ [Call n (SOME loc) args h] ++ r
Proof
  cheat
QED

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

Theorem aux_strip_op:
  ∀loc loc_opt arity op xs aux.
    rewrite_aux loc loc_opt arity (Op op xs) = SOME aux ⇒
    is_block_op_cons op ∧
    ∃mut_cons tail_call finalise tag i l hole r hole_ptr hole_idx t args h.
      mut_cons = Op (MemOp (MutCons tag i)) (l ++ [hole] ++ r) ∧
      tail_call = Call t (SOME loc_opt) (Op (IntOp (Const (&LENGTH l))) [] :: Var hole_ptr :: args) h ∧
      finalise = Op (MemOp FinaliseCons) [Var hole_ptr] ∧
      aux = Let [mut_cons; tail_call] $ finalise ∧
      xs = l ++ [Call t (SOME loc) args h] ++ r
Proof
  rw []
  >-
   (gvs [rewrite_aux_def, is_block_op_cons_def]
    >> pop_assum mp_tac
    >> CASE_TAC
    >> strip_tac
    >> Cases_on ‘op’ >> gvs [dest_Cons_def]
    >> Cases_on ‘b’ >> gvs [dest_Cons_def])
  >> gvs [rewrite_aux_def]
  >> pop_assum mp_tac
  >> CASE_TAC
  >> strip_tac
  >> gvs [rewrite_aux_BlockOp_Cons_def]
  >> pop_assum mp_tac
  >> CASE_TAC
  >> Cases_on ‘h’ >> gvs []
  >> Cases_on ‘t’ >> gvs []
  >> strip_tac
  >> Cases_on ‘to_mut_cons (HoleBlock n l0 o' l)’ >> gvs [to_mut_cons_def]
  >> rename [‘cons_to_tc_and_hb loc tag xs = (TCall n args h)⁺ (HoleBlock i l hole r)’]
  >> qexists ‘l’
  >> gvs []
  >> drule ry
  >> gvs []
QED

Theorem rewrite_aux_args_err:
  rewrite_aux loc loc_opt arity (Op op xs) = SOME exp_aux ∧
  evaluate (xs,env2,s') = (Rerr e',t'') ⇒
  evaluate ([exp_aux],env2,s') = (Rerr e',t'')
Proof
  rw []
  >> drule aux_strip_op
  >> strip_tac
  >> gvs [is_block_op_cons_def]
  >> simp [Once evaluate_def]
  >> simp [Once evaluate_def]
  >> simp [Once evaluate_def]
  >> cheat
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
  >> cheat
     (* Can't set up induction on this *)
QED

Theorem list_rel_front:
  ∀r l1 l2.
    LIST_REL r l1 l2 ⇒
    LIST_REL r (FRONT l1) (FRONT l2)
Proof
  cheat
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
    ∃args' exp'.
      find_code dest vs' s'.code = SOME (args',exp') ∧
      env_rel F f args args' ∧
      (exp ≠ exp' ⇒
       ∃loc loc_opt i.
         rewrite_aux loc loc_opt i exp = SOME exp')
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
    >> gvs [state_rel_def, code_rel_def]
    >> last_x_assum drule
    >> strip_tac
    >> Cases_on ‘compile_exp n n' arity exp’ >> gvs []
    >> Cases_on ‘x’ >> gvs []
    >> pop_assum mp_tac
    >> gvs [compile_exp_def]
    >> CASE_TAC >> gvs []
    >> strip_tac
    >> strip_tac
    >> gvs []
    >> first_assum $ irule_at Any)
  >> Cases_on ‘lookup x s.code’ >> gvs []
  >> Cases_on ‘x'’ >> gvs [state_rel_def, code_rel_def]
  >> irule_at Any list_rel_env_rel
  >> gvs []
  >> last_x_assum drule
  >> strip_tac
  >> Cases_on ‘compile_exp x n (LENGTH args) exp’ >> gvs []
  >> Cases_on ‘x'’ >> gvs []
  >> pop_assum mp_tac
  >> gvs [compile_exp_def]
  >> CASE_TAC >> gvs []
  >> strip_tac
  >> strip_tac
  >> gvs []
  >> first_assum $ irule_at Any
QED

(* Not used, not sure how useful *)
Theorem rewrite_opt_base:
  ∀loc loc_opt arity exp env1 env2 s s' t t' v v' f c.
    arity = &LENGTH env1 ∧
    rewrite_aux loc loc_opt arity exp = NONE ∧
    evaluate ([exp],env1,s) = (Rval [v],t) ∧
    evaluate ([exp],env2,s') = (Rval [v'],t') ∧
    hole_has_val f env1 env2 s'.refs c ∧
    state_rel f s s' ∧
    env_rel T f env1 env2
    ⇒
    ∃exp_opt hole_ptr tag left c right t'_filled.
      exp_opt = rewrite_opt loc loc_opt arity (arity + 1) (arity + 2) exp ∧

      env2❲LENGTH env1❳ = RefPtr F hole_ptr ∧
      env2❲LENGTH env1 + 1❳ = Number (&LENGTH left) ∧
      hole_ptr ∉ FRANGE f ∧
      FLOOKUP s'.refs hole_ptr = SOME (MutBlock tag left c right) ∧
      
      t'_filled = t' with refs := t'.refs⟨hole_ptr ↦ MutBlock tag left v' right⟩ ∧
      evaluate ([exp_opt],env2,s') = (Rval [Block 0 []],t'_filled)
Proof
  rw []
  >> drule env_rel_length_opt
  >> strip_tac
  >> drule env_rel_extras_opt
  >> strip_tac
  >> gvs [hole_has_val_def]
  >> Cases_on ‘exp’ >> gvs [rewrite_aux_def]
  >~ [‘rewrite_opt _ _ _ _ _ (Var n)’] >-
   (gvs [rewrite_opt_def, evaluate_def]
    >> Cases_on ‘n < LENGTH env1’
    >> gvs [do_app_def, do_app_aux_def, bvlSemTheory.Unit_def, backend_commonTheory.tuple_tag_def])
  >~ [‘rewrite_opt _ _ _ _ _ (Call ticks dest xs handler)’] >-
   (gvs [rewrite_opt_def, evaluate_def]
    >> gvs [do_app_def, do_app_aux_def]
    >> cheat
QED

Theorem evaluate_rewrite_tmc:
   ∀xs env1 ^s r t opt f s' env2.
     evaluate (xs, env1, s) = (r, t) ∧
     env_rel opt f env1 env2 ∧
     state_rel f s s' ∧
     (opt ⇒
      LENGTH xs = 1 ∧
      ∃c. hole_has_val f env1 env2 s'.refs c) ∧
     r ≠ Rerr (Rabort Rtype_error) ⇒
     ∃t' f' r'.
       evaluate (xs, env2, s') = (r', t') ∧
       result_rel (LIST_REL (v_rel f')) (v_rel f') r r' ∧
       state_rel f' t t' ∧
       f SUBMAP f' ∧
       only_fresh f f' s'.refs ∧
       holes_unchanged_except f s'.refs t'.refs ∅ ∧
       (opt ⇒
        (∀loc loc_opt arity exp_aux exp_opt.
           rewrite_aux loc loc_opt arity (HD xs) = SOME exp_aux ⇒
           ∃t1.
             evaluate ([exp_aux], env2, s') = (r',t1) ∧
             state_rel f' t t1) ∧
        (∀loc loc_opt i j k exp_aux exp_opt.
           i = LENGTH env1 ∧
           j = LENGTH env1 + 1 ∧
           k = LENGTH env1 + 2 ∧
           rewrite_opt loc loc_opt i j k (HD xs) = exp_opt ⇒
           ∃rrr t2.
             evaluate ([exp_opt], env2, s') = (rrr,t2) ∧
             opt_res_rel r' rrr ∧
             state_rel f' t t2 ∧
             holes_unchanged_except f s'.refs t2.refs {EL i env2} ∧
             ∀res_v.
                r' = Rval [res_v] ⇒
                hole_has_val f env1 env2 t2.refs res_v))
Proof

  recInduct bviSemTheory.evaluate_ind
  >> rpt strip_tac
  >~ [‘evaluate ([],_,_)’] >-
   (gvs [evaluate_def] >> first_x_assum $ irule_at Any >> fs [only_fresh_def, holes_unchanged_except_def])
  >~ [‘evaluate (x::y::xs,_,_)’] >-
   (gvs [evaluate_def]
    (* First inductive hypothesis *)
    >> gvs [CaseEq "prod", PULL_EXISTS]
    >> rename[‘evaluate ([x],env,s) = (rx,u)’]
    >> first_x_assum $ qspec_then ‘F’ mp_tac
    >> simp []
    >> disch_then drule
    >> disch_then drule
    >> impl_tac
    >- (spose_not_then assume_tac >> fs [])
    >> strip_tac >> fs []
    >> rename [‘evaluate ([x],env2,s') = (rx',u')’]
    >> reverse $ Cases_on ‘rx’ >> gvs []
    >- (first_x_assum $ irule_at Any >> fs [])
    (* Second inductive hypothesis *)
    >> gvs [CaseEq "prod", PULL_EXISTS]
    >> qpat_x_assum ‘_ = _’ mp_tac
    >> rename [‘evaluate (y::xs,env,u) = (ry,w)’]
    >> strip_tac
    >> rename [‘LIST_REL (v_rel f'') vx vx'’]
    >> first_x_assum $ qspec_then ‘F’ mp_tac
    >> simp []
    >> drule_all env_rel_submap
    >> strip_tac
    >> disch_then drule
    >> disch_then drule
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
    >> rpt $ goal_assum $ drule_at Any)
  >~ [‘Var n’] >-
   (gvs [evaluate_def]
    >> Cases_on ‘n < LENGTH env’ >> gvs []
    >> ‘n < LENGTH env2’ by (drule_all env_rel_length >> gvs [])                 
    >> gvs []
    >> drule_all env_rel_el_v_rel
    >> strip_tac
    >> goal_assum $ drule_at Any
    >> gvs []
    >> conj_tac
    >- (irule only_fresh_refl)
    >> conj_tac
    >- irule holes_unchanged_except_refl
    >> strip_tac
    >> gvs []
    >> conj_tac
    >- (rpt gen_tac >> gvs [rewrite_aux_def])
    >> rpt gen_tac
    >> gvs [opt_res_rel_def]
    >> gvs [rewrite_opt_def]
    (* Lemma for evaluating Op (MemOp UpdateCons)? *)
    >> gvs [evaluate_def]
    >> drule env_rel_length_opt
    >> gvs []
    >> strip_tac
    >> gvs [do_app_def]
    >> gvs [do_app_aux_def]
    >> drule env_rel_extras_opt
    >> strip_tac
    >> gvs []
    >> gvs [case_eq_thms]
    >> gvs [PULL_EXISTS]
    >> gvs [bvlSemTheory.Unit_def, backend_commonTheory.tuple_tag_def]
    >> gvs [hole_has_val_def, FLOOKUP_SIMP]
    >> gvs [state_rel_def, state_ref_rel_def, FLOOKUP_SIMP]
    >> rpt strip_tac
    >-
     (last_x_assum drule
      >> strip_tac
      >> goal_assum $ drule_at Any
      >> goal_assum $ drule_at Any
      >> IF_CASES_TAC
      >> gvs [flookup_thm, FRANGE_DEF])
    >> gvs [holes_unchanged_except_def]
    >> gvs [FLOOKUP_SIMP]
    >> rw []
    >> metis_tac [])
  >~ [‘If x1 x2 x3’] >-
   (gvs [evaluate_def]
    >> gvs [CaseEq "prod", PULL_EXISTS]
    >> rename [‘evaluate ([x1],env,s) = (r1,u)’]
    (* First inductive hypothesis *)
    >> first_x_assum $ qspec_then ‘F’ mp_tac
    >> simp []
    >> disch_then $ drule_at $ Pos $ el 2
    >> drule env_rel_relax_opt
    >> strip_tac
    >> gvs []
    >> disch_then drule
    >> Cases_on ‘r1’ >> gvs []
    >-
     (imp_res_tac evaluate_SING_IMP
      >> gvs []
      >> rename [‘evaluate ([x1],env,s) = (Rval [v1],u)’]
      >> Cases_on ‘v1 = Boolv T’ >> gvs []
      >- (* Then inductive hypothesis *)
       (strip_tac
        >> rename [‘v_rel f' (Boolv T) v1'’]
        >> rename [‘evaluate ([x1],env2,s') = (r1',u')’]
        >> gvs []
        >> drule evaluate_pad_env_val
        >> disch_then $ qspec_then ‘[RefPtr F hole_ptr; Number hole_idx]’ mp_tac
        >> gvs []
        >> strip_tac
        >> ‘v1' = Boolv T’ by (drule $ iffLR v_rel_cases >> gvs [bvlSemTheory.Boolv_def])
        >> gvs []
        >> last_x_assum $ qspec_then ‘opt’ mp_tac
        >> disch_then $ drule_at $ Pos $ el 2
        >> qpat_x_assum ‘env_rel F f env env2’ kall_tac
        >> drule_all env_rel_submap
        >> strip_tac
        >> disch_then drule
        >> gvs []
        >> impl_tac
        >-
         (strip_tac
          >> gvs []
          >> qexists ‘c’
          >> drule env_rel_strip_extras
          >> strip_tac
          >> gvs []
          >> irule unchanged_hole_has_val
          >> goal_assum $ drule_at $ Pos hd
          >> gvs [])
        >> strip_tac
        >> gvs []
        >> goal_assum $ drule_at Any
        >> gvs []
        >> rw [] >> gvs []
        >- imp_res_tac SUBMAP_TRANS
        >-
         (irule only_fresh_trans
          >> goal_assum $ drule_at $ Pos $ el 2
          >> goal_assum $ drule_at Any
          >> irule evaluate_refs_SUBSET
          >> qexistsl [‘env2’, ‘Rval [Boolv T]’, ‘[x1]’]
          >> gvs [])
        >-
         (irule holes_unchanged_except_trans
          >> first_assum $ irule_at Any
          >> gvs [])
        >-
         (drule aux_strip_if_then
          >> strip_tac
          >-
           (first_x_assum drule
            >> strip_tac
            >> goal_assum $ drule_at Any
            >> gvs [evaluate_def])
          >> gvs [evaluate_def])
        >> first_x_assum $ qspecl_then [‘loc’, ‘loc_opt’] mp_tac
        >> strip_tac
        >> gvs [rewrite_opt_def, evaluate_def]
        >> drule_all env_rel_length_opt
        >> strip_tac
        >> gvs [EL_APPEND_EQN]
        >> conj_tac
        >-
         (irule holes_unchanged_except_trans
          >> first_assum $ irule_at Any
          >> gvs [holes_unchanged_except_def])
        >> gen_tac
        >> strip_tac
        >> first_x_assum $ qspec_then ‘res_v’ mp_tac
        >> gvs []
        >> strip_tac
        >> drule_all hole_has_val_submap
        >> gvs [])
      (* Else inductive hypothesis *)
      >> strip_tac
      >> rename [‘v_rel f'' v1 v1'’]
      >> rename [‘evaluate ([x1],env2,s') = (r1',u')’]
      >> gvs []
      >> drule evaluate_pad_env_val
      >> disch_then $ qspec_then ‘[RefPtr F hole_ptr; Number hole_idx]’ mp_tac
      >> gvs []
      >> strip_tac
      >> Cases_on ‘v1 = Boolv F’ >> gvs []
      >> ‘v1' = Boolv F’ by (drule $ iffLR v_rel_cases >> gvs [bvlSemTheory.Boolv_def])
      >> gvs []
      >> last_x_assum $ qspec_then ‘opt’ mp_tac
      >> disch_then $ drule_at $ Pos $ el 2
      >> qpat_x_assum ‘env_rel F f env env2’ kall_tac
      >> drule_all env_rel_submap
      >> strip_tac
      >> disch_then drule
      >> gvs []
      >> impl_tac
      >-
       (strip_tac
        >> gvs []
        >> qexists ‘c’
        >> drule env_rel_strip_extras
        >> strip_tac
        >> gvs []
        >> irule unchanged_hole_has_val
        >> goal_assum $ drule_at $ Pos hd
        >> gvs [])
      >> strip_tac
      >> gvs []
      >> goal_assum $ drule_at Any
      >> gvs []
      >> rw []
      >> gvs []
      >- imp_res_tac SUBMAP_TRANS
      >-
       (irule only_fresh_trans
        >> goal_assum $ drule_at $ Pos $ el 2
        >> goal_assum $ drule_at Any
        >> irule evaluate_refs_SUBSET
        >> qexistsl [‘env2’, ‘Rval [Boolv F]’, ‘[x1]’]
        >> gvs [])
      >-
       (irule holes_unchanged_except_trans
        >> first_assum $ irule_at Any
        >> gvs [])
      >-
       (drule aux_strip_if_else
        >> strip_tac
        >-
         (first_x_assum drule
          >> strip_tac
          >> goal_assum $ drule_at Any
          >> gvs [evaluate_def])
        >> gvs [evaluate_def])
      >> first_x_assum $ qspecl_then [‘loc’, ‘loc_opt’] mp_tac
      >> strip_tac
      >> gvs [rewrite_opt_def, evaluate_def]
      >> drule_all env_rel_length_opt
      >> strip_tac
      >> gvs [EL_APPEND_EQN]
      >> conj_tac
      >-
       (irule holes_unchanged_except_trans
        >> first_assum $ irule_at Any
        >> gvs [holes_unchanged_except_def])
      >> gen_tac
      >> strip_tac
      >> first_x_assum $ qspec_then ‘res_v’ mp_tac
      >> gvs []
      >> strip_tac
      >> drule_all hole_has_val_submap
      >> gvs [])
    >> strip_tac
    >> rename [‘evaluate ([x1],env2,s') = (r1',u')’]
    >> gvs []
    >> ‘e' ≠ Rabort Rtype_error’ by (spose_not_then assume_tac >> gvs [])
    >> drule_all evaluate_pad_env_err
    >> disch_then $ qspec_then ‘[RefPtr F hole_ptr; Number hole_idx]’ mp_tac
    >> gvs []
    >> strip_tac
    >> goal_assum $ drule_at Any
    >> gvs []
    >> rw []
    >-
     (drule aux_strip_if_then
      >> strip_tac
      >> gvs [evaluate_def])
    >> gvs [rewrite_opt_def, evaluate_def, opt_res_rel_def, holes_unchanged_except_def])
  >~ [‘Let xs x2’] >-
   (gvs [evaluate_def]
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
       (qpat_x_assum ‘env_rel F f env env2’ kall_tac
        >> drule_all env_rel_submap
        >> strip_tac
        >> drule_all env_rel_append
        >> gvs []
        >> strip_tac
        >> strip_tac
        >> gvs []
        >> qexists ‘c’
        >> pop_assum mp_tac
        >> drule_all env_rel_strip_extras
        >> strip_tac
        >> gvs []
        >> strip_tac
        >> irule unchanged_hole_has_val
        >> drule_all holes_unchanged_except_submap
        >> strip_tac
        >> goal_assum $ drule_at $ Pos $ el 2
        >> goal_assum $ drule_at $ Pos $ el 2
        >> rw []
        >- irule only_fresh_refl
        >> drule_at Any hole_has_val_append
        >> disch_then $ qspecl_then [‘s'.refs’, ‘env2' ++ [RefPtr F hole_ptr; Number hole_idx]’, ‘env’, ‘c’] mp_tac
        >> impl_tac >> gvs []
        >> irule unchanged_hole_has_val
        >> goal_assum $ drule_at $ Pos $ el 4
        >> gvs []
        >> simp [holes_unchanged_except_def])
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
       (drule aux_strip_let
        >> strip_tac
        >> last_x_assum drule
        >> strip_tac
        >> gvs [evaluate_def])
      >> first_x_assum $ qspecl_then [‘loc’, ‘loc_opt’] mp_tac
      >> strip_tac
      >> rev_drule evaluate_IMP_LENGTH
      >> gvs [rewrite_opt_def, evaluate_def]
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
      >> strip_tac
      >> strip_tac
      >> first_x_assum drule
      >> strip_tac
      >> irule hole_has_val_submap
      >> goal_assum $ drule_at Any
      >> irule hole_has_val_unappend
      >> rpt $ goal_assum $ drule_at Any
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
    >- (drule aux_strip_let
        >> strip_tac
        >> gvs [evaluate_def])
    >> gvs [rewrite_opt_def, evaluate_def, opt_res_rel_def]
    >> gvs [holes_unchanged_except_def])
  >~ [‘Raise x’] >-
   (gvs [evaluate_def]
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
      >> gvs [rewrite_aux_def, rewrite_opt_def, evaluate_def, opt_res_rel_def]
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
    >> gvs [])
  >~ [‘Op op xs’] >-
     
   (gvs [evaluate_def]
    >> gvs [CaseEq "prod", PULL_EXISTS]
    >> rename [‘evaluate (xs,env,s) = (rs,u)’]
    >> first_assum $ qspecl_then [‘F’, ‘f’, ‘s'’, ‘env2’] mp_tac
    >> impl_tac
    >-
     (gvs []
      >> conj_tac
      >- (irule env_rel_relax_opt >> first_assum $ irule_at Any)
      >> spose_not_then assume_tac
      >> gvs [])
    >> strip_tac
    >> gvs []
    >> rename [‘evaluate (xs,env2,s') = (rs',u')’]
    >> qpat_assum ‘f ⊑ _’ $ irule_at Any
    >> reverse $ Cases_on ‘rs’ >> gvs []
    >-
     (strip_tac
      >> gvs []
      >> first_x_assum $ qspec_then ‘F’ mp_tac
      >> gvs []
      >> drule env_rel_relax_opt
      >> strip_tac
      >> disch_then drule
      >> disch_then drule
      >> strip_tac
      >> gvs []
      >> conj_tac
      >-
       (rw []
        >> qexists ‘t''’
        >> gvs []
        >> drule aux_strip_op
        >> strip_tac
        >> gvs [is_block_op_cons_def]
        >> cheat)
      >> rw []
      >> gvs [rewrite_opt_def, evaluate_def]
      >> CASE_TAC >> gvs []
      >-
       (gvs [evaluate_def, opt_res_rel_def]
        >> irule holes_unchanged_except_subset
        >> first_assum $ irule_at Any
        >> gvs [])
      >> gvs [evaluate_def, rewrite_opt_BlockOp_Cons_def]
      >> CASE_TAC >> gvs []
      >-
       (gvs [evaluate_def, opt_res_rel_def]
        >> irule holes_unchanged_except_subset
        >> first_assum $ irule_at Any
        >> gvs [])
      >-
       (gvs [evaluate_def, opt_res_rel_def]
        >> irule holes_unchanged_except_subset
        >> first_assum $ irule_at Any
        >> gvs [])
      >> Cases_on ‘h’ >> gvs []
      >> Cases_on ‘t'’ >> gvs []
      >> rename [‘cons_to_tc_and_hb loc x xs = (TCall ticks args handler')⁺ (HoleBlock tag l hole r)’]
      >> gvs [Once evaluate_def]
      >> CASE_TAC >> gvs []
      >> CASE_TAC >> gvs []
      >> gvs [evaluate_def]
      >> cheat
      )
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
        >> drule aux_strip_op
        >> strip_tac
        >> gvs [is_block_op_cons_def])
      >> gvs []
      >> rpt gen_tac
      >> qexists ‘(Rerr (Rabort (Rffi_error e)))’
      >> gvs [opt_res_rel_def]
      >> qexists ‘u'’
      >> gvs []
      >> drule holes_unchanged_except_subset
      >> strip_tac
      >> pop_assum $ irule_at Any
      >> irule_at Any EMPTY_SUBSET
      >> simp [rewrite_opt_def, dest_Cons_def, evaluate_def])
    (* lemma that do_app op (REVERSE a) u = Rval a' implies do_app op (REVERSE v') u' equals some other Rval that is v_rel related to a' *)
    >> rename [‘do_app op (REVERSE vs) u = Rval v’]
    >> drule $ iffLR list_rel_reverse
    >> strip_tac
    >> drule_all do_app_op_rel
    >> strip_tac
    >> gvs []
    >> Cases_on ‘v’ >> gvs []
    >> Cases_on ‘v'’ >> gvs []
    >> rename [‘state_rel f'' t t'’]
    >> rename [‘v_rel f'' v v'’]

    >> first_x_assum $ qspec_then ‘F’ mp_tac
    >> gvs []
    >> drule env_rel_relax_opt
    >> strip_tac
    >> disch_then drule
    >> disch_then drule
    >> strip_tac
    >> gvs []
    >> rename [‘state_rel f3 u u'’]
    >> rename [‘LIST_REL (v_rel f3) vs vs'’]
    >> conj_tac
    >- (irule do_app_holes_unchanged
        >> first_assum $ irule_at Any
        >> gvs [])
    >> strip_tac
    >> gvs []
    >> conj_tac
    >-
     (rw []
      >> drule aux_strip_op
      >> strip_tac
      >> gvs [is_block_op_cons_def]
      >> cheat)
    >> rpt gen_tac
    >> cheat)
  >~ [‘Tick x’] >-     
   (gvs [evaluate_def]
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
        >> drule aux_strip_tick
        >> strip_tac
        >> gvs [evaluate_def])
      >> goal_assum $ drule_at Any
      >> gvs [rewrite_opt_def, evaluate_def, opt_res_rel_def, holes_unchanged_except_refl])
    >> first_x_assum $ qspec_then ‘opt’ mp_tac
    >> simp []
    >> disch_then drule
    >> drule state_rel_dec
    >> gvs []
    >> disch_then $ qspec_then ‘1’ mp_tac
    >> strip_tac
    >> gvs []
    >> disch_then drule
    >> impl_tac
    >- rw []
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
      >> drule aux_strip_tick
      >> strip_tac
      >> gvs [evaluate_def]
      >> first_x_assum $ irule_at Any
      >> qexistsl [‘arity’, ‘loc’, ‘loc_opt’]
      >> gvs [])
    >> rw [rewrite_opt_def, evaluate_def])
  >~ [‘Force force_loc n’] >-
     cheat
  >~ [‘Call ticks dest xs handler’] >-
     
   (gvs [evaluate_def]
    >> IF_CASES_TAC >> gvs []
    >> gvs [CaseEq "prod", PULL_EXISTS]
    >> rename [‘evaluate (xs,env,s) = (v_xs,u)’]
    (* xs inductive hypothesis *)
    >> first_x_assum $ qspec_then ‘F’ mp_tac
    >> drule env_rel_relax_opt
    >> gvs []
    >> strip_tac
    >> rpt $ disch_then drule
    >> Cases_on ‘v_xs’ >> gvs []
    >-
     (rename [‘evaluate (xs,env,s) = (Rval v_xs,u)’]
      >> Cases_on ‘find_code dest v_xs u.code’ >> gvs []
      >> Cases_on ‘x’ >> gvs []
      >> rename [‘find_code dest v_xs u.code = SOME (args,exp)’]
      >> strip_tac
      >> gvs []
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
        >> gvs []
        >> conj_tac
        >- (rw [] >> gvs [rewrite_aux_def])
        >> rw []
        >> simp [rewrite_opt_def]
        >> pop_assum $ irule_at Any
        >> qexists ‘Rerr (Rabort Rtimeout_error)’
        >> gvs [opt_res_rel_def]
        >> irule_at Any holes_unchanged_except_subset
        >> first_assum $ irule_at $ Pos hd
        >> gvs []
        >> gvs [evaluate_def]
        >> IF_CASES_TAC >> gvs [])
      (* Clock did not run out *)
      >> Cases_on ‘evaluate ([exp],args,dec_clock (ticks + 1) u)’ >> gvs []
      >> rename [‘evaluate ([exp],args,dec_clock (ticks + 1) u) = (v_exp, w)’]
      >> first_x_assum $ qspec_then ‘F’ mp_tac
      >> gvs []
      >> disch_then drule
      >> drule state_rel_dec
      >> Cases_on ‘u.clock’ >> gvs []
      >> disch_then $ qspec_then ‘ticks + 1’ mp_tac
      >> gvs []
      >> strip_tac
      >> disch_then drule
      >> impl_tac
      >- (spose_not_then assume_tac >> gvs [])
      >> strip_tac
      >> gvs []
      >> rename [‘evaluate ([exp],args',dec_clock (ticks + 1) u') = (v_exp',w')’]

      >> Cases_on ‘v_exp’ >> gvs []
      >-
       (rename [‘state_rel f3 t t'’]
        >> rename [‘LIST_REL (v_rel f3) v_exp v_exp'’]
        >> Cases_on ‘exp = exp'’ >> gvs []
        >-
         (first_assum $ irule_at $ Pos hd
          >> gvs []
          >> conj_tac
          >- (irule SUBMAP_TRANS >> first_assum $ irule_at Any >> gvs [])
          >> conj_tac
          >- cheat (* not sure *)
          >> conj_tac
          >- (irule_at Any holes_unchanged_except_trans
              >> first_assum $ irule_at $ Pos $ el 4
              >> gvs [])
          >> strip_tac
          >> gvs []
          >> conj_tac
          >- rw [rewrite_aux_def]
          >> rw []
(* HERE *)
          >> gvs [opt_res_rel_def]

          >> gvs [rewrite_opt_def, evaluate_def]
          >> IF_CASES_TAC >> gvs []
          >> drule env_rel_length_opt
          >> strip_tac
          >> IF_CASES_TAC >> gvs []
          >> gvs [do_app_def, do_app_aux_def]
          >> gvs [case_eq_thms]
          >> gvs [env_rel_def]
                 )
                           
      >> Cases_on ‘exp = exp'’ >> gvs []
      >-
       (Cases_on ‘v_exp’ >> gvs []
        >-
         (rename [‘LIST_REL (v_rel f'³') v v'’]
          >> first_assum $ irule_at $ Pos $ el 4
          >> gvs []

          >> v_rel_submap
                        
          >> drule_all SUBMAP_TRANS
          >> strip_tac
          >> gvs []
          >> drule_all only_fresh_submap
                 )
                 )

                     
      >> Cases_on ‘evaluate ([exp'],args',dec_clock (ticks + 1) u')’ >> gvs []
      >> Cases_on ‘q’ >> gvs []
      >-
       (Cases_on ‘v_exp’ >> gvs []
        >-
         (rename [‘LIST_REL (v_rel f'³') v_exp v_exp'’]
          >> cheat)
        >> cheat)
      >>
        cheat)
    (* Error case *)
    >> strip_tac
    >> gvs []
    >> rename [‘evaluate (xs,env2,s') = (Rerr e',t')’]
    >> first_assum $ irule_at $ Pos hd
    >> gvs []
    >> strip_tac
    >> conj_tac
    >- rw [rewrite_aux_def]
    >> rw []
    >> gvs []
    >> qexistsl [‘Rerr e'’, ‘t'’]
    >> gvs [opt_res_rel_def]
    >> conj_tac
    >- (gvs [rewrite_opt_def, evaluate_def] >> IF_CASES_TAC >> gvs [])
    >> irule holes_unchanged_except_subset
    >> pop_assum $ irule_at Any
    >> gvs [])
QED

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

