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
    if ~opt then ys = [] else
      LENGTH ys = 2 ∧
      ∃hole_ptr hole_idx.
        EL 0 ys = RefPtr F hole_ptr ∧
        EL 1 ys = Number hole_idx
End

Definition code_rel_def:
  code_rel c1 c2 ⇔
    ∀loc arity exp exp_aux exp_opt.
      ∃n.
        lookup loc c1 = SOME (arity, exp) ⇒
        (compile_exp loc n arity exp = NONE ⇒
         lookup loc c2 = SOME (arity, exp)) ∧
        (compile_exp loc n arity exp = SOME (exp_aux, exp_opt) ⇒
         lookup loc c2 = SOME (arity, exp_aux) ∧
         lookup n c2 = SOME (arity + 1, exp_opt))
End

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

Theorem env_rel_submap:
  env_rel opt f env1 env2 ∧ f SUBMAP f' ⇒ env_rel opt f' env1 env2
Proof
  strip_tac
  >> gvs [env_rel_def]
  >> reverse (Cases_on ‘opt’)
  >> gvs [LIST_REL_EL_EQN]
  >- (rw []
      >> first_x_assum $ qspec_then ‘n’ mp_tac
      >> strip_tac
      >> gvs []
      >> drule_all v_rel_submap
      >> fs [])
  >> qexistsl [‘xs’, ‘ys’]
  >> gvs []
  >> rw []
  >> first_x_assum $ qspec_then ‘n’ mp_tac
  >> strip_tac
  >> gvs []
  >> drule_all v_rel_submap
  >> fs []
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
  ∀f env env'.
    env_rel T f env env' ⇒
    LENGTH env' = LENGTH env + 2
Proof
  rw [env_rel_def]
  >> drule LIST_REL_LENGTH
  >> gvs [APPEND_LENGTH_EQ]
QED

Theorem env_rel_length_non_opt:
  ∀f env env'.
    env_rel F f env env' ⇒
    LENGTH env' = LENGTH env
Proof
  rw [env_rel_def]
  >> drule LIST_REL_LENGTH
  >> gvs []
QED

Theorem env_rel_length:
  ∀opt f env1 env2.
    env_rel opt f env1 env2 ⇒ LENGTH env2 >= LENGTH env1
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

Theorem env_rel_non_opt:
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
  >> cheat
QED

(*Definition build_v_rel_def:
  (build_v_rel _ (Number i) = Number i) ∧
  (build_v_rel _ (Word64 w) = Word64 w) ∧
  (build_v_rel f (Block n xs) =
   let ys = MAP (build_v_rel f) xs in
     Block n ys) ∧
  (build_v_rel _ (CodePtr n) = CodePtr n) ∧
  (build_v_rel f (RefPtr b n) =
   case FLOOKUP f n of
   | SOME m => RefPtr b m) ∧
End*)

Theorem v_rel_functional:
  ∀f x y z.
    v_rel f x y ∧
    v_rel f x z ⇒
    y = z
Proof
  Induct_on ‘v_rel’
  >> rw []
  >> gvs [v_rel_cases]
  >> rename [‘LIST_REL (v_rel f) xs zs’]
  >> Induct_on ‘xs’ >> gvs []
  >> strip_tac
  >> strip_tac
  >> cheat
QED

Theorem env_rel_total:
  ∀opt f env1.
    ∃env2.
      env_rel opt f env1 env2
Proof
  rw []
  >> gvs [env_rel_def]
  >> cheat (* Use build_v_rel - except i don't think this holds for any f *)
QED

Theorem state_rel_dec:
  ∀n f s s'.
    state_rel f s s' ∧
    s.clock = SUC n ∧
    s'.clock = SUC n ⇒
    state_rel f (dec_clock 1 s) (dec_clock 1 s')
Proof
  rw [] >> gvs [state_rel_def, dec_clock_def]
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

Theorem aux_strip_op:
  ∀loc loc_opt arity op xs aux.
    ~is_block_op_cons op ∧
    rewrite_aux loc loc_opt arity (Op op xs) = SOME aux ⇒
    ∃aux' i j.
      aux = Op (MemOp UpdateCons) [Var i; Var j; Op op xs]
Proof
  rw []>> gvs [is_block_op_cons_def, rewrite_aux_def]
  >> Cases_on ‘op’ >> gvs []
  >> gvs [rewrite_aux_BlockOp_Cons_def]
  >> Cases_on ‘b’ >> gvs []                
QED

Theorem aux_strip_op_BlockOpCons:
  ∀loc loc_opt arity block_tag op xs aux.
    is_block_op_cons op ∧
    rewrite_aux loc loc_opt arity (Op op xs) = SOME aux ⇒
    ∃aux'.
      aux = ARB
Proof
  rw [] >> cheat
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

(* Rename this *)
Theorem dest_thunk_tmc:
  ∀n opt f env env2 s s' tm v v'.
    env_rel opt f env env2 ∧
    state_rel f s s' ∧
    v_rel f v v' ∧
    dest_thunk env❲n❳ s.refs = IsThunk tm v ⇒
    dest_thunk env2❲n❳ s'.refs = IsThunk tm v'
Proof
  rw []
  >> Cases_on ‘env❲n❳’ >> gvs [dest_thunk_def]
  >> rename [‘env❲n❳ = RefPtr b ptr’]
  >> Cases_on ‘FLOOKUP s.refs ptr’ >> gvs []
  >> Cases_on ‘x’ >> gvs []
  >> ‘tm = t ∧ v = a’ by (Cases_on ‘t’ >> gvs [])
  >> gvs [env_rel_def, EL_APPEND_EQN]
  >> rename [‘FLOOKUP s.refs ptr = SOME (Thunk tm v)’]
  >> rename [‘LIST_REL (v_rel f) env env2’]
  >> drule $ iffLR LIST_REL_EL_EQN
  >> strip_tac
  >> ‘n < LENGTH env’ by cheat
  >> gvs []
  >> first_x_assum drule
  >> strip_tac
  >> drule $ iffLR v_rel_cases
  >> simp []
  >> strip_tac
  >> rename [‘env2❲n❳ = RefPtr b ptr'’]                
  >> gvs [dest_thunk_def, state_rel_def, state_ref_rel_def]
  >> last_x_assum drule
  >> strip_tac
  >> gvs [ref_rel_cases]
  >> rename [‘FLOOKUP s'.refs ptr' = SOME (Thunk tm v')’]
  >> Cases_on ‘tm’ >> gvs []
  >> drule v_rel_functional
  >> disch_then $ qspec_then ‘v''’ mp_tac
  >> fs []
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

Theorem ry:
  rewrite_opt loc next arity (arity + 1) (arity + 2) exp = opt
  ⇒
  FLOOKUP s'.refs hole_ptr = SOME (MutBlock tag l c r) ∧
  hole_idx = &LENGTH l
Proof
  cheat
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
             ∀res_v.
                r' = Rval [res_v] ⇒
                hole_has_val f env1 env2 t2.refs res_v))
Proof

  recInduct bviSemTheory.evaluate_ind
  >> rpt strip_tac
  >~ [‘evaluate ([],_,_)’] >-
   (gvs [evaluate_def] >> first_x_assum $ irule_at Any >> fs [])
  >~ [‘evaluate (x::y::xs,_,_)’] >-
   (gvs [evaluate_def]
    (* First inductive hypothesis *)
    >> gvs [CaseEq "prod", PULL_EXISTS]
    >> rename[‘evaluate ([x],env,s) = (r1,s1)’]
    >> first_x_assum $ qspec_then ‘F’ mp_tac
    >> simp []
    >> disch_then drule
    >> disch_then drule
    >> impl_tac
    >- (spose_not_then assume_tac >> fs [])
    >> strip_tac >> fs []
    >> reverse $ Cases_on ‘r1’ >> gvs []
    >- (pop_assum $ irule_at Any >> fs [])
    (* Second inductive hypothesis *)
    >> gvs [CaseEq "prod", PULL_EXISTS]
    >> qpat_x_assum ‘_ = _’ kall_tac
    >> rename[‘evaluate (y::xs,env,s1) = (r2,s2)’]
    >> first_x_assum $ qspec_then ‘F’ mp_tac
    >> simp []
    >> drule_all env_rel_submap
    >> strip_tac
    >> disch_then drule
    >> disch_then drule
    >> impl_tac
    >- (spose_not_then assume_tac >> fs [])
    >> strip_tac >> fs []
    >> Cases_on ‘r2’ >> gvs []
    >-
     (rename [‘state_rel f3 s3 t3’]
      >> qexists ‘f3’ >> fs []
      >> imp_res_tac evaluate_SING_IMP >> gvs []
      >> drule_all v_rel_submap >> rw []
      >> imp_res_tac SUBMAP_TRANS)
    >> rename [‘state_rel f3 s3 t3’]
    >> qexists ‘f3’ >> fs []
    >> imp_res_tac SUBMAP_TRANS)
  >~ [‘Var n’] >-
   (gvs [evaluate_def]
    >> Cases_on ‘n < LENGTH env’ >> gvs []
    >> ‘n < LENGTH env2’ by (drule_all env_rel_length >> gvs [])                 
    >> gvs []
    >> drule_all env_rel_el_v_rel
    >> strip_tac
    >> goal_assum $ drule_at Any
    >> gvs []
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
    >> last_x_assum drule
    >> strip_tac
    >> goal_assum $ drule_at Any
    >> goal_assum $ drule_at Any
    >> IF_CASES_TAC
    >> gvs [flookup_thm, FRANGE_DEF])
  >~ [‘If x1 x2 x3’] >-
   (gvs [evaluate_def]
    >> gvs [CaseEq "prod", PULL_EXISTS]
    >> rename [‘evaluate ([x1],env,s) = (r1,s1)’]
    >> Cases_on ‘opt’
    >> gvs []
    (* Opt *)
    (* First inductive hypothesis *)
    >- (first_x_assum $ qspec_then ‘F’ mp_tac
        >> simp []
        >> disch_then $ drule_at $ Pos $ el 2
        >> drule env_rel_non_opt
        >> strip_tac
        >> gvs []
        >> rename [‘env_rel F f env env2’]
        >> disch_then drule
        >> Cases_on ‘r1’
        >> gvs []
        >- (imp_res_tac evaluate_SING_IMP
            >> gvs []
            >> rename [‘evaluate ([x1],env,s) = (Rval [v1],s1)’]
            >> Cases_on ‘v1 = Boolv T’
            >> gvs []
            (* Then inductive hypothesis *)
            >- (strip_tac
                >> rename [‘v_rel f'' (Boolv T) v1'’]
                >> rename [‘evaluate ([x1],env2,s') = (r1',s1')’]
                >> gvs []
                >> drule evaluate_pad_env_val
                >> disch_then $ qspec_then ‘[RefPtr F hole_ptr; Number hole_idx]’ mp_tac
                >> gvs []
                >> strip_tac
                >> ‘v1' = Boolv T’ by (drule $ iffLR v_rel_cases >> gvs [bvlSemTheory.Boolv_def])
                >> gvs []
                >> last_x_assum $ qspec_then ‘T’ mp_tac
                >> disch_then $ drule_at $ Pos $ el 2
                >> qpat_x_assum ‘env_rel F f env env2’ kall_tac
                >> drule_all env_rel_submap
                >> strip_tac
                >> disch_then drule
                >> strip_tac
                >> gvs []
                >> goal_assum $ drule_at Any
                >> gvs []
                >> rw []
                >- (imp_res_tac SUBMAP_TRANS)
                >- (drule aux_strip_if_then
                    >> strip_tac
                    >- (first_x_assum drule
                        >> strip_tac
                        >> goal_assum $ drule_at Any
                        >> gvs [evaluate_def])
                    >> gvs [evaluate_def])
                >> first_x_assum $ qspecl_then [‘loc’, ‘loc_opt’] mp_tac
                >> strip_tac
                >> gvs [rewrite_opt_def, evaluate_def])
            (* Then inductive hypothesis *) (* TODO - maybe some of this can be factored out *)
            >> strip_tac
            >> rename [‘v_rel f'' v1 v1'’]
            >> rename [‘evaluate ([x1],env2,s') = (r1',s1')’]
            >> gvs []
            >> drule evaluate_pad_env_val
            >> disch_then $ qspec_then ‘[RefPtr F hole_ptr; Number hole_idx]’ mp_tac
            >> gvs []
            >> strip_tac
            >> Cases_on ‘v1 = Boolv F’
            >> gvs []
            >> ‘v1' = Boolv F’ by (drule $ iffLR v_rel_cases >> gvs [bvlSemTheory.Boolv_def])
            >> gvs []
            >> last_x_assum $ qspec_then ‘T’ mp_tac
            >> disch_then $ drule_at $ Pos $ el 2
            >> qpat_x_assum ‘env_rel F f env env2’ kall_tac
            >> drule_all env_rel_submap
            >> strip_tac
            >> disch_then drule
            >> strip_tac
            >> gvs []
            >> goal_assum $ drule_at Any
            >> gvs []
            >> rw []
            >- (imp_res_tac SUBMAP_TRANS)
            >- (drule aux_strip_if_else
                >> strip_tac
                >- (first_x_assum drule
                    >> strip_tac
                    >> goal_assum $ drule_at Any
                    >> gvs [evaluate_def])
                >> gvs [evaluate_def])
            >> first_x_assum $ qspecl_then [‘loc’, ‘loc_opt’] mp_tac
            >> strip_tac
            >> gvs [rewrite_opt_def, evaluate_def])
        >> strip_tac
        >> rename [‘evaluate ([x1],env2,s') = (r1',s1')’]
        >> gvs []
        >> ‘e' ≠ Rabort Rtype_error’ by (spose_not_then assume_tac >> gvs [])
        >> drule_all evaluate_pad_env_err
        >> disch_then $ qspec_then ‘[RefPtr F hole_ptr; Number hole_idx]’ mp_tac
        >> gvs []
        >> strip_tac
        >> goal_assum $ drule_at Any
        >> gvs []
        >> rw []
        >- (drule aux_strip_if_then
            >> strip_tac
            >> gvs [evaluate_def])
        >> gvs [rewrite_opt_def, evaluate_def, opt_res_rel_def])
    (* Non opt *)
    (* First inductive hypothesis *)
    >> first_x_assum $ qspec_then ‘F’ mp_tac
    >> gvs []
    >> disch_then drule
    >> disch_then drule
    >> impl_tac
    >> gvs []
    >- (spose_not_then assume_tac >> fs [])
    >> strip_tac
    >> rename [‘evaluate ([x1],env2,s') = (r1',s1')’]
    >> gvs []
    >> Cases_on ‘r1’
    >> gvs []
    >- (imp_res_tac evaluate_SING_IMP
        >> gvs []
        >> rename [‘v_rel f'' v1 v1'’]
        >> Cases_on ‘v1 = Boolv T’
        >> gvs []
        (* then inductive hypothesis *)
        >- (first_x_assum $ qspec_then ‘F’ mp_tac
            >> simp []
            >> drule_all env_rel_submap
            >> strip_tac
            >> disch_then drule_all
            >> strip_tac
            >> ‘v1' = Boolv T’ by (drule $ iffLR v_rel_cases >> gvs [bvlSemTheory.Boolv_def])
            >> gvs []
            >> qexists ‘f'³'’
            >> gvs []
            >> imp_res_tac SUBMAP_TRANS)
        (* else inductive hypothesis *)
        >> Cases_on ‘v1 = Boolv F’
        >> gvs []
        >> first_x_assum $ qspec_then ‘F’ mp_tac
        >> simp []
        >> drule_all env_rel_submap
        >> strip_tac
        >> disch_then drule_all
        >> strip_tac
        >> ‘v1' = Boolv F’ by (drule $ iffLR v_rel_cases >> gvs [bvlSemTheory.Boolv_def])
        >> gvs []
        >> qexists ‘f'³'’
        >> gvs []
        >> imp_res_tac SUBMAP_TRANS)
    >> qexists ‘f''’
    >> gvs [])
  >~ [‘Let xs x2’] >-     
   (gvs [evaluate_def]
    >> gvs [CaseEq "prod", PULL_EXISTS]
    >> rename [‘evaluate (xs,env,s) = (rs,u)’]
    >> Cases_on ‘opt’
    >> gvs []
    (* Opt *)
    (* First inductive hypothesis *)
    >- (first_x_assum $ qspec_then ‘F’ mp_tac
        >> simp []
        >> disch_then $ drule_at $ Pos $ el 2
        >> drule env_rel_non_opt
        >> strip_tac
        >> gvs []
        >> rename [‘env_rel F f env env2’]
        >> disch_then drule
        >> Cases_on ‘rs’
        >> gvs []
        (* Second inductive hypothesis *)
        >- (rename [‘evaluate (xs,env,s) = (Rval vs,u)’]
            >> strip_tac
            >> rename [‘evaluate (xs, env2, s') = (rs', u')’]
            >> rename [‘LIST_REL (v_rel f'') vs vs'’]
            >> first_x_assum $ qspec_then ‘T’ mp_tac
            >> gvs []
            >> disch_then $ drule_at $ Pos $ el 2
            >> disch_then $ qspec_then ‘vs' ++ env2 ++ [RefPtr F hole_ptr; Number hole_idx]’ mp_tac
            >> impl_tac
            >- (qpat_x_assum ‘env_rel F f env env2’ kall_tac
                >> drule_all env_rel_submap
                >> strip_tac
                >> drule_all env_rel_append
                >> gvs [])
            >> strip_tac
            >> drule evaluate_pad_env_val
            >> disch_then $ qspec_then ‘[RefPtr F hole_ptr; Number hole_idx]’ mp_tac
            >> gvs []
            >> strip_tac
            >> qexists ‘f'³'’
            >> gvs []
            >> rw []
            >- (imp_res_tac SUBMAP_TRANS)
            >- (drule aux_strip_let
                >> strip_tac
                >> last_x_assum drule
                >> strip_tac
                >> gvs [evaluate_def])
            >> first_x_assum $ qspecl_then [‘loc’, ‘loc_opt’] mp_tac
            >> strip_tac
            >> rev_drule evaluate_IMP_LENGTH
            >> gvs [rewrite_opt_def, evaluate_def])
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
        >> gvs [rewrite_opt_def, evaluate_def, opt_res_rel_def])
    (* Non-opt *)
    (* First inductive hypothesis *)
    >> first_x_assum $ qspec_then ‘F’ mp_tac
    >> gvs []
    >> disch_then drule
    >> disch_then drule
    >> strip_tac
    >> Cases_on ‘rs’
    >> gvs []
    (* Second inductive hypothesis *)
    >- (first_x_assum $ qspec_then ‘F’ mp_tac
        >> simp []
        >> drule_all env_rel_submap
        >> strip_tac
        >> strip_tac
        >> drule_all env_rel_append
        >> strip_tac
        >> first_x_assum drule_all
        >> strip_tac
        >> gvs []
        >> qexists ‘f'³'’
        >> rw []
        >> imp_res_tac SUBMAP_TRANS)
    >> goal_assum $ drule_at Any
    >> gvs [])
  >~ [‘Raise x’] >-
   (gvs [evaluate_def]
    >> gvs [CaseEq "prod", PULL_EXISTS]
    >> rename [‘evaluate ([x],env,s) = (v,u)’]
    >> Cases_on ‘opt’ >> gvs[]
    >- (first_x_assum $ qspec_then ‘T’ mp_tac
        >> disch_then drule
        >> disch_then drule
        >> impl_tac
        >- (Cases_on ‘v’ >> gvs [])
        >> gvs []
        >> strip_tac
        >> rename [‘evaluate ([x],env2,s') = (v',u')’]
        >> goal_assum $ drule_at Any
        >> goal_assum $ drule_at Any
        >> Cases_on ‘v’
        >> gvs [rewrite_aux_def, rewrite_opt_def, evaluate_def, opt_res_rel_def]
        >> imp_res_tac evaluate_SING_IMP
        >> gvs [])
    >> first_x_assum $ qspec_then ‘F’ mp_tac
    >> gvs []
    >> disch_then drule
    >> disch_then drule
    >> impl_tac
    >- (Cases_on ‘v’ >> gvs [])
    >> strip_tac
    >> rename [‘evaluate ([x],env2,s') = (v',u')’]
    >> goal_assum $ drule_at Any
    >> goal_assum $ drule_at Any
    >> Cases_on ‘v’
    >> gvs [rewrite_aux_def, rewrite_opt_def, evaluate_def, opt_res_rel_def]
    >> imp_res_tac evaluate_SING_IMP
    >> gvs [])
  >~ [‘Op op xs’] >-
   cheat
   (*gvs [evaluate_def]
    >> gvs [CaseEq "prod", PULL_EXISTS]
    >> rename [‘evaluate (xs,env,s) = (rs,u)’]
    >> first_x_assum $ qspec_then ‘F’ mp_tac
    >> gvs []
    >> strip_tac
    >> Cases_on ‘opt’ >> gvs []
    (* Opt *)
    (* First inductive hypothesis *)                   
    >- (first_x_assum $ drule_at Any
        >> drule env_rel_non_opt
        >> strip_tac
        >> gvs []
        >> rename [‘env_rel F f env env2’]
        >> Cases_on ‘rs’ >> gvs []
        >- (rename [‘evaluate (xs,env,s) = (Rval vs,u)’]
            >> disch_then drule
            >> strip_tac
            >> gvs []
            >> rename [‘evaluate (xs,env2,s') = (Rval vs',u')’]
            >> drule evaluate_pad_env_val
            >> strip_tac
            >> gvs []                        
            >> Cases_on ‘do_app op (REVERSE vs) u’ >> gvs []
            >- (Cases_on ‘a’ >> gvs []
                >> rename [‘do_app op (REVERSE vs) u = Rval (v,t)’]
                >> drule state_rel_do_app
                >> disch_then drule

             drule_all do_app_rewrite_tmc
                >> strip_tac
                >> rename [‘f' ⊑ f''’]
                >> Cases_on ‘r'’ >> gvs []
                >> Cases_on ‘a’ >> gvs []
                >> Cases_on ‘a'’ >> gvs []
                >> rename [‘state_rel f'' t t'’]
                >> rename [‘v_rel f'' v v'’]
                >> goal_assum $ drule_at Any
                >> gvs []
                >> conj_tac
                >- (imp_res_tac SUBMAP_TRANS)
                >> rw []
                >- (goal_assum $ drule_at Any
                    >> reverse $ Cases_on ‘is_block_op_cons op’ >> gvs[]
                    >- (drule_all aux_strip_op
                        >> strip_tac
                        >> gvs [evaluate_def]
                        (* HERE *)
                                
                        >> Cases_on ‘i < LENGTH env2 + 2’ >> gvs []
                        >- (Cases_on ‘j < LENGTH env2 + 2’ >> gvs []
                            >- (


                             CASE_TAC >> gvs []

                                                        
                                >> Cases_on ‘a’ >> gvs []
                                >> Cases_on ‘v’ >> Cases_on ‘v'’ >> gvs [v_rel_cases]
                                >> gvs [do_app_def]
                                   
                                >> gvs [do_app_def, do_app_aux_def]
                               
                               gvs [do_app_def]
                                >> 
                                        cheat)
                            >> cheat)
                        >> cheat)
                    >> cheat)
                >> cheat)
            >> cheat)
        >> cheat)
    >> cheat*)
  >~ [‘Tick x’] >-
   (gvs [evaluate_def]
    >> ‘s'.clock = s.clock’ by gvs [state_rel_def]
    >> gvs []
    >> Cases_on ‘s.clock’
    >> gvs []
    >- (goal_assum $ drule_at Any
        >> gvs []
        >> rw []
        >- (goal_assum $ drule_at Any
            >> drule aux_strip_tick
            >> strip_tac
            >> gvs [evaluate_def])
        >> (goal_assum $ drule_at Any
            >> gvs [rewrite_opt_def, evaluate_def, opt_res_rel_def]))
    >> Cases_on ‘opt’
    >> gvs []
    (* Opt *)
    >- (first_x_assum $ qspec_then ‘T’ mp_tac
        >> simp []
        >> disch_then drule
        >> drule_all state_rel_dec
        >> strip_tac
        >> disch_then drule
        >> strip_tac
        >> gvs []
        >> qexists ‘f''’
        >> gvs []
        >> rpt gen_tac
        >> rw []
        >> gvs []
        >- (drule aux_strip_tick
            >> strip_tac
            >> last_x_assum drule
            >> strip_tac
            >> qexists ‘t1’
            >> gvs [evaluate_def])
        >> pop_assum $ qspecl_then [‘loc’, ‘loc_opt’] mp_tac             
        >> strip_tac
        >> qexistsl [‘rrr’, ‘t2’]
        >> gvs [rewrite_opt_def, evaluate_def])
    (* Non-opt *)
    >> first_x_assum $ qspec_then ‘F’ mp_tac
    >> simp []
    >> disch_then drule
    >> drule_all state_rel_dec
    >> strip_tac
    >> disch_then drule
    >> fs [])
  >~ [‘Force force_loc n’] >-
     cheat
   (*gvs [evaluate_def]
    >> Cases_on ‘n < LENGTH env’ >> gvs []
    >> drule env_rel_length
    >> strip_tac
    >> gvs []
    >> Cases_on ‘dest_thunk env❲n❳ s.refs’ >> gvs []
    >> rename [‘dest_thunk env❲n❳ s.refs = IsThunk tm v’]

    >> drule_all env_rel_el_v_rel
    >> strip_tac

        (* SKip *)
    >> drule_at (Pos last) dest_thunk_tmc
    >> rpt (disch_then drule)
    >> strip_tac

    >> Cases_on ‘env❲n❳’ >> gvs [dest_thunk_def]
    >> rename [‘env❲n❳ = RefPtr b ptr’]
    >> Cases_on ‘env2❲n❳’ >> gvs [v_rel_cases]
    >> rename [‘env2❲n❳ = RefPtr b ptr'’]
    >> Cases_on ‘tm’ >> gvs []
    >- (Cases_on ‘FLOOKUP s.refs ptr’ >> gvs []
        >> Cases_on ‘x’ >> gvs []
        >> Cases_on ‘t’ >> gvs []
        >> cheat)
    >> Cases_on ‘FLOOKUP s.refs ptr’ >> gvs []
    >> Cases_on ‘x’ >> gvs []
    >> Cases_on ‘t'’ >> gvs []
    >> rename [‘FLOOKUP s.refs ptr = SOME (Thunk NotEvaluated v)’]
    >> Cases_on ‘find_code (SOME force_loc) [RefPtr b ptr; v] s.code’ >> gvs []
    >> Cases_on ‘x’ >> gvs []
    >> rename [‘find_code (SOME force_loc) [RefPtr b ptr; v] s.code = SOME (thunk_env, thunk_exp)’]
    >> ‘s'.clock = s.clock’ by gvs [state_rel_def]
    >> Cases_on ‘s.clock’ >> gvs []
    >- (cheat)
    >> last_x_assum $ qspec_then ‘F’ mp_tac
    >> gvs []
    >> drule state_rel_dec
    >> gvs []
    >> strip_tac
    >> disch_then $ drule_at $ Pos $ el 2
    >> disch_then 

                       

    >> drule_at (Pos last) dest_thunk_tmc
    >> rpt (disch_then drule)
    >> strip_tac
    >> Cases_on ‘tm’ >> gvs []
    >- (gvs [state_rel_def]
        >> gvs [dest_thunk_def]
        >> )

                           
    >> Cases_on ‘dest_thunk env2❲n❳ s'.refs’ >> gvs []
    >- ()



    >> 
       
    *)
  >~ [‘Call ticks dest xs handler’] >-
   (gvs [evaluate_def] >> cheat)
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
            >- ()
            )
        )
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

