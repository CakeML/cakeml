(*
  Correctness proof for bvi_tailrec
*)
Theory bvi_tmcProof
Ancestors
  bvi_tmc bviProps bviSem
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

Definition optimized_code_def:
  optimized_code loc arity exp loc_opt c exp_aux exp_opt ⇔
    compile_exp loc loc_opt arity exp = SOME (exp_aux, exp_opt) ∧
    lookup loc c                      = SOME (arity, exp_aux) ∧
    lookup loc_opt c                  = SOME (arity + 2, exp_opt)
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

Theorem state_rel_dec:
  ∀n.
    state_rel f s s' ∧
    s.clock = SUC n ∧
    s'.clock = SUC n ⇒
    state_rel f (dec_clock 1 s) (dec_clock 1 s')
Proof
  cheat
QED

Theorem env_rel_append:
  env_rel F f'' env env2 ∧
  LIST_REL (v_rel f'') x y ⇒
  env_rel F f'' (x ++ env) (y ++ env2)
Proof
  cheat
QED

Theorem evaluate_rewrite_tmc:
   ∀xs env1 ^s r t opt f s' env2.
     evaluate (xs, env1, s) = (r, t) ∧
     env_rel opt f env1 env2 ∧
     state_rel f s s' ∧
     (opt ⇒ LENGTH xs = 1) ∧
     r ≠ Rerr (Rabort Rtype_error) ⇒
     ∃t' f' r'.
       evaluate (xs, env2, s') = (r', t') ∧
       result_rel (LIST_REL (v_rel f')) (v_rel f') r r' ∧
       state_rel f' t t' ∧
       f SUBMAP f' ∧
       (opt ⇒
         ∀arity loc loc_opt exp_aux exp_opt.
           (* lookup loc s.code = SOME (arity, HD xs) ∧ *)
           optimized_code loc arity (HD xs) loc_opt s'.code exp_aux exp_opt ⇒
           (∃t1.
              evaluate ([exp_aux], env2, s') = (r',t1) ∧
              state_rel f' t t1) ∧
           (∃rrr t2.
              evaluate ([exp_opt], env2, s') = (rrr,t2) ∧
              opt_res_rel r' rrr ∧
              state_rel f' t t2))
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
    >> impl_tac >-
     (spose_not_then assume_tac >> fs [])
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
    >> impl_tac >-
     (spose_not_then assume_tac >> fs [])
    >> strip_tac >> fs []
    >> Cases_on ‘r2’ >> gvs []
    >- (rename [‘state_rel f3 s3 t3’]
        >> qexists ‘f3’ >> fs []
        >> imp_res_tac evaluate_SING_IMP >> gvs []
        >> drule_all v_rel_submap >> rw []
        >> imp_res_tac SUBMAP_TRANS)
    >> rename [‘state_rel f3 s3 t3’]
    >> qexists ‘f3’ >> fs []
    >> imp_res_tac SUBMAP_TRANS)
  >~ [‘Var n’] >-
   cheat
   (*gvs [evaluate_def]
    >> Cases_on ‘opt’ >-
     (Cases_on ‘n < LENGTH env’ >-
       (gvs [env_rel_def]
        >> rw [] >-
         (gvs [rich_listTheory.is_prefix_el]) >-
         (cheat)
        >> qexistsl [‘Rval [env❲n❳]’, ‘s'’]
        >> rw [] >-
         (cheat)
         >> (cheat))
      >> gvs [])
    >> gvs [env_rel_def]
    >> cheat*)
  >~ [‘If x1 x2 x3’] >-
   (gvs [evaluate_def] >> cheat)
  >~ [‘Let xs x2’] >-
   (gvs [evaluate_def]
    >> gvs [CaseEq "prod", PULL_EXISTS]
    >> Cases_on ‘opt’
    >> gvs []
    >- (cheat)
    (* Non-opt *)
    (* First inductive hypothesis *)
    >> first_x_assum $ qspec_then ‘F’ mp_tac
    >> gvs []
    >> disch_then drule
    >> disch_then drule
    >> strip_tac
    >> Cases_on ‘v2’
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
        >> qexists ‘f'³'’ (* Rename me *)
        >> rw []
        >> imp_res_tac SUBMAP_TRANS)
    >> cheat)
  >~ [‘Raise x1’] >-
   (gvs [evaluate_def] >> cheat)
  >~ [‘Op op xs’] >-
   (gvs [evaluate_def] >> cheat)
  >~ [‘Tick x’] >-
   (gvs [evaluate_def]
    >> ‘s'.clock = s.clock’ by gvs [state_rel_def]
    >> gvs []
    >> Cases_on ‘s.clock’
    >> gvs []
    >- (cheat) (* Prove timeout error? *)
    >> gvs [CaseEq "prod", PULL_EXISTS]
    >> Cases_on ‘opt’
    >> gvs []
    >- (first_x_assum $ qspec_then ‘T’ mp_tac
        >> simp []
        >> disch_then drule
        >> drule_all state_rel_dec
        >> gvs []
        >> strip_tac
        >> disch_then drule
        >> strip_tac
        >> gvs []
        >> qexists ‘f''’
        >> strip_tac
        >> gvs []
        >> rpt gen_tac
        >> strip_tac
        >> gvs []

        >> first_x_assum $ qspecl_then [‘arity’, ‘loc’, ‘loc_opt’, ‘exp_aux’, ‘exp_opt’] mp_tac
        >> gvs []
        >> cheat)
    >> first_x_assum $ qspec_then ‘F’ mp_tac
    >> simp []
    >> disch_then drule
    >> drule_all state_rel_dec
    >> strip_tac
    >> disch_then drule
    >> fs [])
  >~ [‘Force force_loc n’] >-
   (gvs [evaluate_def] >> cheat)
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
   ∃s2.
     evaluate
      ([Call 0 (SOME start) [] NONE], [],
        initial_state ffi0 (fromAList (SND (compile_prog next prog)))
            (state_co compile_prog co) cc k)
      = (r, s2) ∧
     state_rel s s2
Proof
  rw []
  >> qmatch_asmsub_abbrev_tac `(es,env,st1)`
  >> `env_rel F 0 env env` by fs [env_rel_def]
  >> Cases_on `compile_prog next prog`
  >> fs []
  >> drule (GEN_ALL compile_prog_code_rel)
  >> strip_tac
  >> qmatch_goalsub_abbrev_tac`(es,env,st2)`
  (* >> `state_rel st1 st2` by cheat *)
  >> sg `state_rel st1 st2` >-
   (simp[state_rel_def,Abbr`st1`,Abbr`st2`,domain_fromAList]
    >> rfs[input_condition_def]
    >> reverse conj_tac >-
     (rw []
      >> last_x_assum(qspec_then`n`mp_tac)
      >> cheat)
    >> cheat)
  >> drule evaluate_rewrite_tmc
  >> disch_then (qspec_then `F` drule)
  >> rpt (disch_then drule)
  >> fs []
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

