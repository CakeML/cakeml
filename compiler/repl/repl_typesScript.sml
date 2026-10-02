(*
  Proofs about how the REPL uses types and the type inferencer
*)
Theory repl_types
Ancestors
  semanticsProps evaluate semanticPrimitives infer inferSound
  typeSound semantics envRel primSemEnv typeSoundInvariants
  namespaceProps inferProps ml_prog
  evaluate_skip evaluate_init repl_inputInvariant primTypes typeSystem
Libs
  preamble

Datatype:
  simple_type = Bool | Str | Exn
End

Definition to_type_def:
  to_type Bool = Infer_Tapp [] Tbool_num ∧
  to_type Str  = Infer_Tapp [] Tstring_num ∧
  to_type Exn  = Infer_Tapp [] Texn_num
End

Definition check_ref_types_def:
  check_ref_types types (env :semanticPrimitives$v sem_env) (name,ty,loc) ⇔
    nsLookup types.inf_v name = SOME (0,Infer_Tapp [to_type ty] Tref_num) ∧
    nsLookup env.v name = SOME (Loc T loc)
End

Definition roll_back_def:
  roll_back (old_ienv:inf_env, old_next_id:num)
            (new_ienv:inf_env, new_next_id:num) =
    (old_ienv, new_next_id)
End

Theorem FST_roll_back[simp]:
  FST (roll_back x y) = FST x
Proof
  Cases_on`x` \\ Cases_on`y` \\ rw[roll_back_def]
QED

Theorem SND_roll_back[simp]:
  SND (roll_back x y) = SND y
Proof
  Cases_on`x` \\ Cases_on`y` \\ rw[roll_back_def]
QED

(* Empty metadata is the legacy REPL instance. Nonempty metadata is seeded
   by the joint certificate, not independent map and store witnesses. *)
Definition input_init_ok_def:
  input_init_ok catalogue slots tids tenv st env <=>
    (catalogue = FEMPTY /\ slots = FEMPTY) \/
    initial_input_certificate catalogue slots tids tenv st env
End

Inductive repl_types_input:
[repl_types_input_init:]
  (∀ffi rs decs types (s:'ffi semanticPrimitives$state) env ck b.
     infertype_prog_inc (init_config, start_type_id) decs = M_success types ∧
     evaluate$evaluate_decs (init_state ffi with clock := ck) init_env decs = (s,Rval env) ∧
     EVERY (check_ref_types (FST types) (extend_dec_env env init_env)) rs ∧
     input_init_ok catalogue slots (set_ids start_type_id (SND types))
       (ienv_to_tenv (FST types)) s (extend_dec_env env init_env) ⇒
     repl_types_input catalogue slots b (ffi,rs) (types,s,extend_dec_env env init_env))
[repl_types_input_skip:]
  (∀ffi rs types junk ck t e (s:'ffi semanticPrimitives$state) env.
     repl_types_input catalogue slots T (ffi,rs) (types,s,env) ⇒
     repl_types_input catalogue slots T (ffi,rs) (types,s with <| refs  := s.refs ++ junk                  ;
                                            clock := s.clock - ck                    ;
                                            next_type_stamp := s.next_type_stamp + t ;
                                            next_exn_stamp  := s.next_exn_stamp + e  |>,env))
[repl_types_input_eval:]
  (∀ffi rs decs types new_types (s:'ffi semanticPrimitives$state) env new_env new_s b.
     repl_types_input catalogue slots b (ffi,rs) (types,s,env) ∧
     infertype_prog_inc types decs = M_success new_types ∧
     evaluate$evaluate_decs s env decs = (new_s,Rval new_env) ⇒
     repl_types_input catalogue slots b (ffi,rs) (new_types,new_s,extend_dec_env new_env env))
[repl_types_input_exn:]
  (∀ffi rs decs types new_types (s:'ffi semanticPrimitives$state) env e new_s b.
     repl_types_input catalogue slots b (ffi,rs) (types,s,env) ∧
     infertype_prog_inc types decs = M_success new_types ∧
     evaluate$evaluate_decs s env decs = (new_s,Rerr (Rraise e)) ⇒
     repl_types_input catalogue slots b (ffi,rs) (roll_back types new_types,new_s,env))
[repl_types_input_exn_assign:]
  (∀ffi rs decs types new_types (s:'ffi semanticPrimitives$state) env e
    new_s name loc new_store b.
     repl_types_input catalogue slots b (ffi,rs) (types,s,env) ∧
     infertype_prog_inc types decs = M_success new_types ∧
     evaluate$evaluate_decs s env decs = (new_s,Rerr (Rraise e)) ∧
     MEM (name,Exn,loc) rs ∧
     store_assign loc (Refv e) new_s.refs = SOME new_store ⇒
     repl_types_input catalogue slots b (ffi,rs) (roll_back types new_types,new_s with refs := new_store,env))
[repl_types_input_str_assign:]
  (∀ffi rs types (s:'ffi semanticPrimitives$state) env t name loc new_store b.
     repl_types_input catalogue slots b (ffi,rs) (types,s,env) ∧
     MEM (name,Str,loc) rs ∧
     store_assign loc (Refv (Litv (StrLit t))) s.refs = SOME new_store ⇒
     repl_types_input catalogue slots b (ffi,rs) (types,s with refs := new_store,env))
[repl_types_input_trusted_assign:]
  (∀ffi rs types (s:'ffi semanticPrimitives$state) env value loc ty new_store b.
     repl_types_input catalogue slots b (ffi,rs) (types,s,env) ∧
     FLOOKUP slots loc = SOME ty ∧ trusted_input_value catalogue ty value ∧
     store_assign loc (Refv value) s.refs = SOME new_store ⇒
     repl_types_input catalogue slots b (ffi,rs) (types,s with refs := new_store,env))
End

Definition repl_types_def:
  repl_types = repl_types_input FEMPTY FEMPTY
End

fun empty_input_instance definition theorem =
  theorem |> Q.SPECL [`FEMPTY`, `FEMPTY`]
  |> PURE_REWRITE_RULE
    [input_init_ok_def, GSYM definition, FLOOKUP_EMPTY,
     optionTheory.NOT_NONE_SOME, REFL_CLAUSE, AND_CLAUSES, OR_CLAUSES,
     IMP_CLAUSES, FORALL_SIMP, EXISTS_SIMP];

Theorem repl_types_init = GEN_ALL
  (empty_input_instance repl_types_def repl_types_input_init);
Theorem repl_types_skip = GEN_ALL
  (empty_input_instance repl_types_def repl_types_input_skip);
Theorem repl_types_eval = GEN_ALL
  (empty_input_instance repl_types_def repl_types_input_eval);
Theorem repl_types_exn = GEN_ALL
  (empty_input_instance repl_types_def repl_types_input_exn);
Theorem repl_types_exn_assign = GEN_ALL
  (empty_input_instance repl_types_def repl_types_input_exn_assign);
Theorem repl_types_str_assign = GEN_ALL
  (empty_input_instance repl_types_def repl_types_input_str_assign);
Theorem repl_types_rules = LIST_CONJ
  [repl_types_init, repl_types_skip, repl_types_eval, repl_types_exn,
   repl_types_exn_assign, repl_types_str_assign];
Theorem repl_types_cases = GEN_ALL
  (empty_input_instance repl_types_def repl_types_input_cases);
Theorem repl_types_ind =
  empty_input_instance repl_types_def repl_types_input_ind |> GEN_ALL;
Theorem repl_types_strongind =
  empty_input_instance repl_types_def repl_types_input_strongind |> GEN_ALL;
val _ = IndDefLib.export_rule_induction "repl_types_strongind";

(* Mirror definitions for repl_types using the type system directly *)
Definition to_type_TS_def:
  to_type_TS Bool = Tapp [] Tbool_num ∧
  to_type_TS Str  = Tapp [] Tstring_num ∧
  to_type_TS Exn  = Tapp [] Texn_num
End

Definition check_ref_types_TS_def:
  check_ref_types_TS types (env :semanticPrimitives$v sem_env) (name,ty,loc) ⇔
    nsLookup types.v name = SOME (0,Tapp [to_type_TS ty] Tref_num) ∧
    nsLookup env.v name = SOME (Loc T loc)
End

Inductive repl_types_TS_input:
[repl_types_TS_input_init:]
  (∀ffi rs decs tids tenv (s:'ffi semanticPrimitives$state) env ck.
     type_ds T prim_tenv decs tids tenv ∧
     DISJOINT tids {Tlist_num; Tbool_num; Texn_num} ∧
     evaluate$evaluate_decs (init_state ffi with clock := ck) init_env decs = (s,Rval env) ∧
     EVERY (check_ref_types_TS (extend_dec_tenv tenv prim_tenv) (extend_dec_env env init_env)) rs ∧
     input_init_ok catalogue slots tids (extend_dec_tenv tenv prim_tenv)
       s (extend_dec_env env init_env) ⇒
     repl_types_TS_input catalogue slots (ffi,rs)
       (tids,extend_dec_tenv tenv prim_tenv,s,extend_dec_env env init_env))
[repl_types_TS_input_eval:]
  (∀ffi rs decs tids tenv (s:'ffi semanticPrimitives$state) env
    new_tids new_tenv new_env new_s.
     repl_types_TS_input catalogue slots (ffi,rs) (tids,tenv,s,env) ∧
     type_ds T tenv decs new_tids new_tenv ∧
     DISJOINT tids new_tids ∧
     evaluate$evaluate_decs s env decs = (new_s,Rval new_env) ⇒
     repl_types_TS_input catalogue slots (ffi,rs)
       (tids ∪ new_tids,extend_dec_tenv new_tenv tenv,new_s,extend_dec_env new_env env))
[repl_types_TS_input_exn:]
  (∀ffi rs decs tids tenv (s:'ffi semanticPrimitives$state) env
    new_tids new_tenv new_s e.
     repl_types_TS_input catalogue slots (ffi,rs) (tids,tenv,s,env) ∧
     type_ds T tenv decs new_tids new_tenv ∧
     DISJOINT tids new_tids ∧
     evaluate$evaluate_decs s env decs = (new_s,Rerr (Rraise e)) ⇒
     repl_types_TS_input catalogue slots (ffi,rs) (tids ∪ new_tids,tenv,new_s,env))
[repl_types_TS_input_exn_assign:]
  (∀ffi rs decs tids tenv (s:'ffi semanticPrimitives$state) env
    new_tids new_tenv new_s e name loc new_store.
     repl_types_TS_input catalogue slots (ffi,rs) (tids,tenv,s,env) ∧
     type_ds T tenv decs new_tids new_tenv ∧
     DISJOINT tids new_tids ∧
     evaluate$evaluate_decs s env decs = (new_s,Rerr (Rraise e)) ∧
     MEM (name,Exn,loc) rs ∧
     store_assign loc (Refv e) new_s.refs = SOME new_store ⇒
     repl_types_TS_input catalogue slots (ffi,rs)
       (tids ∪ new_tids,tenv,new_s with refs := new_store,env))
[repl_types_TS_input_str_assign:]
  (∀ffi rs tids tenv (s:'ffi semanticPrimitives$state) env t name loc new_store.
     repl_types_TS_input catalogue slots (ffi,rs) (tids,tenv,s,env) ∧
     MEM (name,Str,loc) rs ∧
     store_assign loc (Refv (Litv (StrLit t))) s.refs = SOME new_store ⇒
     repl_types_TS_input catalogue slots (ffi,rs) (tids,tenv,s with refs := new_store,env))
[repl_types_TS_input_trusted_assign:]
  (∀ffi rs tids tenv (s:'ffi semanticPrimitives$state) env value loc ty new_store.
     repl_types_TS_input catalogue slots (ffi,rs) (tids,tenv,s,env) ∧
     FLOOKUP slots loc = SOME ty ∧ trusted_input_value catalogue ty value ∧
     store_assign loc (Refv value) s.refs = SOME new_store ⇒
     repl_types_TS_input catalogue slots (ffi,rs) (tids,tenv,s with refs := new_store,env))
End

Definition repl_types_TS_def:
  repl_types_TS = repl_types_TS_input FEMPTY FEMPTY
End

Theorem repl_types_TS_init = GEN_ALL
  (empty_input_instance repl_types_TS_def repl_types_TS_input_init);
Theorem repl_types_TS_eval = GEN_ALL
  (empty_input_instance repl_types_TS_def repl_types_TS_input_eval);
Theorem repl_types_TS_exn = GEN_ALL
  (empty_input_instance repl_types_TS_def repl_types_TS_input_exn);
Theorem repl_types_TS_exn_assign = GEN_ALL
  (empty_input_instance repl_types_TS_def repl_types_TS_input_exn_assign);
Theorem repl_types_TS_str_assign = GEN_ALL
  (empty_input_instance repl_types_TS_def repl_types_TS_input_str_assign);
Theorem repl_types_TS_rules = LIST_CONJ
  [repl_types_TS_init, repl_types_TS_eval, repl_types_TS_exn,
   repl_types_TS_exn_assign, repl_types_TS_str_assign];
Theorem repl_types_TS_cases = GEN_ALL
  (empty_input_instance repl_types_TS_def repl_types_TS_input_cases);
Theorem repl_types_TS_ind =
  empty_input_instance repl_types_TS_def repl_types_TS_input_ind |> GEN_ALL;
Theorem repl_types_TS_strongind =
  empty_input_instance repl_types_TS_def repl_types_TS_input_strongind |> GEN_ALL;
val _ = IndDefLib.export_rule_induction "repl_types_TS_strongind";

Theorem init_config_tenv_to_ienv:
  init_config = tenv_to_ienv prim_tenv
Proof
  rw[init_config_def, tenv_to_ienv_def]
  \\ EVAL_TAC
QED

Theorem ienv_to_tenv_init_config:
  ienv_to_tenv init_config = prim_tenv
Proof
  EVAL_TAC
QED

Theorem tenv_ok_prim_tenv[simp]:
  tenv_ok prim_tenv
Proof
  EVAL_TAC \\ rw[]
  \\ Cases_on`id`
  \\ fs[namespaceTheory.nsLookup_def]
  \\ pop_assum mp_tac
  \\ rw[] \\ rw[]
  \\ EVAL_TAC
QED

Theorem env_rel_init_config:
  env_rel prim_tenv init_config
Proof
  simp[init_config_tenv_to_ienv]
  \\ irule env_rel_tenv_to_ienv
  \\ simp[]
QED

Theorem inf_set_tids_ienv_init_config[simp]:
  inf_set_tids_ienv (count start_type_id) init_config
Proof
  EVAL_TAC
  \\ rpt conj_tac
  \\ Cases \\ simp[namespaceTheory.nsLookup_def]
  \\ rw[] \\ simp[]
  \\ EVAL_TAC \\ simp[]
QED

Theorem ienv_ok_init_config:
  ienv_ok {} init_config
Proof
  EVAL_TAC>>
  CONJ_TAC>- (
    Induct>>
    simp[namespaceTheory.nsLookup_def])>>
  CONJ_TAC>- (
    Induct>>
    simp[namespaceTheory.nsLookup_def]>>
    rw[]>>EVAL_TAC)>>
  Induct>>
  simp[namespaceTheory.nsLookup_def]>>
  rw[]>>EVAL_TAC
QED

Theorem repl_types_input_inference_invariants:
  !catalogue slots b (ffi:'ffi ffi_state) rs types st env.
    repl_types_input catalogue slots b (ffi,rs) (types,st,env) ==>
    ienv_ok {} (FST types) /\ start_type_id <= SND types
Proof
  qx_genl_tac [`catalogue`,`slots`] >> Induct_on `repl_types_input` >> rw []
  >- (
    mp_tac (Q.SPECL [`(init_config,start_type_id)`,`decs`,`types`]
      infertype_prog_inc_sound) >> simp [ienv_ok_init_config])
  >- (
    mp_tac (Q.SPECL [`(init_config,start_type_id)`,`decs`,`types`]
      infertype_prog_inc_sound) >> simp [ienv_ok_init_config]) >>
  drule_all infertype_prog_inc_sound >> strip_tac >> fs [] >> decide_tac
QED

Theorem repl_types_input_ienv_ok:
  !catalogue slots b (ffi:'ffi ffi_state) rs types st env.
    repl_types_input catalogue slots b (ffi,rs) (types,st,env) ==>
    ienv_ok {} (FST types)
Proof
  rpt strip_tac >> drule repl_types_input_inference_invariants >> simp []
QED

Theorem repl_types_ienv_ok:
  ∀b (ffi:'ffi ffi_state) rs types s env.
  repl_types b (ffi,rs) (types,s,env) ⇒
  ienv_ok {} (FST types)
Proof
  rpt strip_tac >> fs [repl_types_def] >>
  drule repl_types_input_ienv_ok >> simp []
QED

Theorem repl_types_input_next_id:
  !catalogue slots b (ffi:'ffi ffi_state) rs types st env.
    repl_types_input catalogue slots b (ffi,rs) (types,st,env) ==>
    start_type_id <= SND types
Proof
  rpt strip_tac >> drule repl_types_input_inference_invariants >> simp []
QED

Theorem repl_types_next_id:
  ∀b (ffi:'ffi ffi_state) rs types s env.
  repl_types b (ffi,rs) (types,s,env) ⇒
  start_type_id ≤ SND types
Proof
  rpt strip_tac >> fs [repl_types_def] >>
  drule repl_types_input_next_id >> simp []
QED

Theorem convert_t_to_type:
  convert_t(to_type t) = to_type_TS t
Proof
  Cases_on`t`>>EVAL_TAC
QED

Theorem check_ref_types_check_ref_types_TS:
  check_ref_types ienv env x ⇒
  check_ref_types_TS (ienv_to_tenv ienv) env x
Proof
  PairCases_on`x`>>
  rw[check_ref_types_TS_def,check_ref_types_def]>>
  fs[ienv_to_tenv_def,nsLookup_nsMap]>>
  EVAL_TAC>>
  fs[convert_t_to_type]
QED

Definition ref_lookup_ok_def:
  ref_lookup_ok refs (name:(mlstring,mlstring) id,ty,loc) =
    ∃v:semanticPrimitives$v.
      store_lookup loc refs = SOME (Refv v) ∧
      (ty = Bool ⇒ v = Boolv T ∨ v = Boolv F) ∧
      (ty = Str ⇒ ∃t. v = Litv (StrLit t)) ∧
      (ty = Exn ⇒ ∃s ls. v = Conv (SOME (ExnStamp s)) ls)
End

Definition primitive_slots_hold_def:
  primitive_slots_hold rs tenvS <=>
    EVERY (\(name,ty,loc).
      FLOOKUP tenvS loc = SOME (Ref_t (to_type_TS ty))) rs
End

Theorem primitive_slots_hold_initial:
  type_all_env ctMap tenvS env tenv /\
  EVERY (check_ref_types_TS tenv env) rs ==>
  primitive_slots_hold rs tenvS
Proof
  simp [primitive_slots_hold_def, EVERY_MEM, FORALL_PROD] >>
  disch_then strip_assume_tac >>
  qx_genl_tac [`ref_name`,`ty`,`loc`] >> strip_tac >>
  qpat_x_assum `!name ty loc. MEM _ rs ==> _`
    (qspecl_then [`ref_name`,`ty`,`loc`] mp_tac) >>
  simp [check_ref_types_TS_def] >> strip_tac >>
  drule_all (REWRITE_RULE [Tref_def] type_all_env_reference) >> simp []
QED

Theorem primitive_slots_hold_extension:
  primitive_slots_hold rs tenvS /\ store_type_extension tenvS new_store ==>
  primitive_slots_hold rs new_store
Proof
  strip_tac >> drule store_type_extension_weakS >>
  fs [primitive_slots_hold_def, weakeningTheory.weakS_def,
    EVERY_MEM, FORALL_PROD] >> rpt strip_tac >> res_tac >>
  metis_tac [FLOOKUP_SUBMAP]
QED

Theorem primitive_slot_value_canonical:
  good_ctMap ctMap /\ type_v 0 ctMap tenvS value (to_type_TS ty) ==>
  (ty = Bool ==> value = Boolv T \/ value = Boolv F) /\
  (ty = Str ==> ?text. value = Litv (StrLit text)) /\
  (ty = Exn ==> ?stamp fields. value = Conv (SOME (ExnStamp stamp)) fields)
Proof
  Cases_on `ty` >> simp [to_type_TS_def] >> strip_tac
  >~ [`type_v _ _ _ _ (Tapp [] Tbool_num)`] >- (
    fs [good_ctMap_def] >>
    drule_all (REWRITE_RULE [Tbool_def] prim_canonical_Boolv_thm) >>
    disch_then (qx_choose_then `flag` assume_tac) >>
    Cases_on `flag` >> simp [])
  >~ [`type_v _ _ _ _ (Tapp [] Tstring_num)`] >- (
    fs [good_ctMap_def] >>
    drule_all (REWRITE_RULE [Tstring_def]
      (el 3 (CONJUNCTS prim_canonical_values_thm))) >> simp []) >>
  fs [good_ctMap_def, ctMap_has_exns_def] >>
  drule_all (el 3 (CONJUNCTS ctor_canonical_values_thm)) >>
  simp [semanticPrimitivesTheory.bind_stamp_def,
    semanticPrimitivesTheory.chr_stamp_def,
    semanticPrimitivesTheory.div_stamp_def,
    semanticPrimitivesTheory.subscript_stamp_def,
    semanticPrimitivesTheory.same_type_def]
QED


Theorem primitive_slots_ref_lookup:
  primitive_slots_hold rs tenvS /\ good_ctMap ctMap /\
  type_s ctMap refs tenvS ==>
  EVERY (ref_lookup_ok refs) rs
Proof
  rw [primitive_slots_hold_def, EVERY_MEM, FORALL_PROD] >> res_tac >>
  drule_all type_s_reference >>
  disch_then (qx_choose_then `stored_value` strip_assume_tac) >>
  drule_all primitive_slot_value_canonical >> strip_tac >>
  simp [ref_lookup_ok_def] >> qexists_tac `stored_value` >> simp []
QED


Theorem input_typing_primitive_assign:
  input_typing_witnesses catalogue slots tids tenv
    (st:'ffi semanticPrimitives$state) env ctMap tenvS /\
  primitive_slots_hold rs tenvS /\ MEM (ref_name,ty,loc) rs /\
  type_v 0 ctMap tenvS value (to_type_TS ty) /\
  store_assign loc (Refv value) st.refs = SOME new_refs ==>
  input_typing_witnesses catalogue slots tids tenv
    (st with refs := new_refs) env ctMap tenvS
Proof
  strip_tac >>
  `FLOOKUP tenvS loc = SOME (Ref_t (to_type_TS ty))` by (
    fs [primitive_slots_hold_def, EVERY_MEM, FORALL_PROD] >> res_tac) >>
  drule_all input_typing_reference_assign >> simp []
QED


Theorem input_typing_initial_primitive_slots:
  type_ds T prim_tenv decs tids decl_tenv /\
  DISJOINT tids {Tlist_num; Tbool_num; Texn_num} /\
  evaluate_decs (init_state ffi with clock := ck) init_env decs =
    (st,Rval decl_env) /\
  EVERY (check_ref_types_TS (extend_dec_tenv decl_tenv prim_tenv)
    (extend_dec_env decl_env init_env)) rs /\
  input_init_ok catalogue slots tids (extend_dec_tenv decl_tenv prim_tenv)
    st (extend_dec_env decl_env init_env) ==>
  ?ctMap tenvS.
    input_typing_witnesses catalogue slots tids
      (extend_dec_tenv decl_tenv prim_tenv) st
      (extend_dec_env decl_env init_env) ctMap tenvS /\
    primitive_slots_hold rs tenvS
Proof
  strip_tac >>
  `initial_input_certificate catalogue slots tids
    (extend_dec_tenv decl_tenv prim_tenv) st
    (extend_dec_env decl_env init_env)` by (
      fs [input_init_ok_def] >>
      mp_tac (Q.SPECL [`tids`,`init_state ffi`,`init_env`]
        prim_type_sound_invariants) >> simp [init_state_env_thm] >>
      disch_then (qx_choose_then `primitive_map` strip_assume_tac) >>
      `type_sound_invariant (init_state ffi with clock := ck)
        init_env primitive_map FEMPTY tids prim_tenv` by (
          simp [type_sound_invariant_clock]) >>
      drule_all decs_type_sound >> simp [] >>
      disch_then (qx_choosel_then [`result_map`,`result_store`] strip_assume_tac) >>
      simp [initial_input_certificate_def] >>
      qexistsl_tac [`result_map`,`result_store`] >>
      simp [input_typing_witnesses_def, catalogue_matches_def, input_slots_hold_def] >>
      qpat_x_assum `FRANGE _ SUBSET prim_type_ids` mp_tac >>
      qpat_x_assum `FRANGE _ DIFF FRANGE _ SUBSET tids` mp_tac >> SET_TAC []) >>
  qpat_x_assum `initial_input_certificate _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [initial_input_certificate_def]) >>
  disch_then (qx_choosel_then [`seed_map`,`seed_store`] strip_assume_tac) >>
  `type_all_env seed_map seed_store
    (extend_dec_env decl_env init_env) (extend_dec_tenv decl_tenv prim_tenv)` by (
      fs [input_typing_witnesses_def, type_sound_invariant_def]) >>
  drule_all primitive_slots_hold_initial >> strip_tac >>
  qexistsl_tac [`seed_map`,`seed_store`] >> simp []
QED


Theorem repl_types_TS_input_witnesses:
  !catalogue slots (ffi:'ffi ffi_state) rs tids tenv st env.
    repl_types_TS_input catalogue slots (ffi,rs) (tids,tenv,st,env) ==>
    ?ctMap tenvS.
      input_typing_witnesses catalogue slots tids tenv st env ctMap tenvS /\
      primitive_slots_hold rs tenvS
Proof
  qx_genl_tac [`catalogue`,`slots`] >>
  Induct_on `repl_types_TS_input` >> rpt conj_tac >> rpt gen_tac >> rw []
  >- suspend "Init"
  >- suspend "Eval"
  >- suspend "Exn"
  >- suspend "ExnAssign"
  >- suspend "StringAssign"
  >- suspend "TrustedAssign"
QED

Resume repl_types_TS_input_witnesses[Init]:
  `DISJOINT tids {Tlist_num; Tbool_num; Texn_num}` by simp [] >>
  drule_all input_typing_initial_primitive_slots >> simp []
QED

Resume repl_types_TS_input_witnesses[Eval]:
  `DISJOINT new_tids tids` by metis_tac [DISJOINT_SYM] >>
  drule (REWRITE_RULE [GSYM prim_type_ids_def]
    (CONJUNCT2 typeSysPropsTheory.type_d_tids_disjoint)) >> strip_tac >>
  drule_all input_typing_declarations_success >>
  disch_then (qx_choosel_then [`result_map`,`result_store`] strip_assume_tac) >>
  drule_all primitive_slots_hold_extension >> strip_tac >>
  qexistsl_tac [`result_map`,`result_store`] >> simp []
QED

Resume repl_types_TS_input_witnesses[Exn]:
  `DISJOINT new_tids tids` by metis_tac [DISJOINT_SYM] >>
  drule (REWRITE_RULE [GSYM prim_type_ids_def]
    (CONJUNCT2 typeSysPropsTheory.type_d_tids_disjoint)) >> strip_tac >>
  drule_all input_typing_declarations_raise >>
  disch_then (qx_choosel_then [`result_map`,`result_store`] strip_assume_tac) >>
  drule_all primitive_slots_hold_extension >> strip_tac >>
  qexistsl_tac [`result_map`,`result_store`] >> simp []
QED

Resume repl_types_TS_input_witnesses[ExnAssign]:
  `DISJOINT new_tids tids` by metis_tac [DISJOINT_SYM] >>
  drule (REWRITE_RULE [GSYM prim_type_ids_def]
    (CONJUNCT2 typeSysPropsTheory.type_d_tids_disjoint)) >> strip_tac >>
  drule_all input_typing_declarations_raise >>
  disch_then (qx_choosel_then [`result_map`,`result_store`] strip_assume_tac) >>
  drule_all primitive_slots_hold_extension >> strip_tac >>
  qmatch_asmsub_rename_tac
    `store_assign _ (Refv raised_value) _ = SOME _` >>
  `type_v 0 result_map result_store raised_value (to_type_TS Exn)` by
    fs [to_type_TS_def] >>
  drule_all input_typing_primitive_assign >> strip_tac >>
  qexistsl_tac [`result_map`,`result_store`] >> simp []
QED

Resume repl_types_TS_input_witnesses[StringAssign]:
  qmatch_asmsub_rename_tac
    `input_typing_witnesses _ _ _ _ _ _ old_map old_store` >>
  qmatch_asmsub_rename_tac
    `store_assign _ (Refv (Litv (StrLit input_text))) _ = SOME _` >>
  `type_v 0 old_map old_store (Litv (StrLit input_text)) (to_type_TS Str)` by
    simp [to_type_TS_def, Once type_v_cases] >>
  drule_all input_typing_primitive_assign >> strip_tac >>
  qexistsl_tac [`old_map`,`old_store`] >> simp []
QED

Resume repl_types_TS_input_witnesses[TrustedAssign]:
  qmatch_asmsub_rename_tac
    `input_typing_witnesses _ _ _ _ _ _ old_map old_store` >>
  drule_all input_typing_trusted_assign >> strip_tac >>
  qexistsl_tac [`old_map`,`old_store`] >> simp []
QED

Finalise repl_types_TS_input_witnesses;


Theorem repl_types_TS_input_thm:
  repl_types_TS_input catalogue slots (ffi,rs) (tids,tenv,st,env) ==>
  initial_input_certificate catalogue slots tids tenv st env /\
  EVERY (ref_lookup_ok st.refs) rs /\
  !decs new_ids new_tenv new_st result.
    type_ds T tenv decs new_ids new_tenv /\ DISJOINT tids new_ids /\
    evaluate_decs st env decs = (new_st,result) ==>
    result <> Rerr (Rabort Rtype_error)
Proof
  strip_tac >> drule repl_types_TS_input_witnesses >>
  disch_then (qx_choosel_then [`current_map`,`current_store`] strip_assume_tac) >>
  conj_tac >- (
    rewrite_tac [initial_input_certificate_def] >>
    qexistsl_tac [`current_map`,`current_store`] >> simp []) >>
  conj_tac >- (
    `good_ctMap current_map /\ type_s current_map st.refs current_store` by
      fs [input_typing_witnesses_def, type_sound_invariant_def] >>
    drule_all primitive_slots_ref_lookup >> simp []) >>
  qx_genl_tac [`decs`,`new_ids`,`new_tenv`,`new_st`,`result`] >> strip_tac >>
  `DISJOINT new_ids tids` by metis_tac [DISJOINT_SYM] >>
  drule (REWRITE_RULE [GSYM prim_type_ids_def]
    (CONJUNCT2 typeSysPropsTheory.type_d_tids_disjoint)) >> strip_tac >>
  drule_all input_typing_declarations_no_type_error >> simp []
QED



Theorem repl_types_TS_thm:
  ∀(ffi:'ffi ffi_state) rs tids tenv s env.
    repl_types_TS (ffi,rs) (tids,tenv,s,env) ⇒
      (∃ctMap tenvS.
        FRANGE ((SND o SND) o_f ctMap) ⊆ tids ∪ prim_type_ids ∧
        type_sound_invariant s env ctMap tenvS {} tenv) ∧
      EVERY (ref_lookup_ok s.refs) rs ∧
      ∀decs new_tids new_tenv new_s res.
        type_ds T tenv decs new_tids new_tenv ∧
        DISJOINT tids new_tids ∧
        evaluate_decs s env decs = (new_s,res) ⇒
        res ≠ Rerr (Rabort Rtype_error)
Proof
  qx_genl_tac [`ffi`,`rs`,`tids`,`tenv`,`s`,`env`] >> strip_tac >>
  fs [repl_types_TS_def] >> drule repl_types_TS_input_thm >> strip_tac >>
  conj_tac >- (
    qpat_x_assum `initial_input_certificate _ _ _ _ _ _`
      (mp_tac o REWRITE_RULE [initial_input_certificate_def]) >>
    disch_then (qx_choosel_then [`current_map`,`current_store`] strip_assume_tac) >>
    qexistsl_tac [`current_map`,`current_store`] >> fs [input_typing_witnesses_def]) >>
  metis_tac []
QED

Theorem DISJOINT_set_ids:
  tids ⊆ count id ⇒
  DISJOINT tids (set_ids id id')
Proof
  rw[set_ids_def,count_def,DISJOINT_DEF,EXTENSION,SUBSET_DEF]>>
  CCONTR_TAC>>
  fs[]>>
  first_x_assum drule>>
  fs[]
QED

Theorem set_ids_SUBSET[simp]:
  set_ids id id' ⊆ count id'
Proof
  rw[set_ids_def,count_def,SUBSET_DEF]
QED


Theorem set_ids_UNION:
  id ≤ id' ∧ sid ≤ id ⇒
  set_ids sid id' = set_ids sid id ∪ set_ids id id'
Proof
  rw[set_ids_def,EXTENSION,EQ_IMP_THM]
QED

Theorem repl_types_input_F_TS:
  !catalogue slots (ffi:'ffi ffi_state) rs types st env.
    repl_types_input catalogue slots F (ffi,rs) (types,st,env) ==>
    repl_types_TS_input catalogue slots (ffi,rs)
      (set_ids start_type_id (SND types),ienv_to_tenv (FST types),st,env)
Proof
  qx_genl_tac [`catalogue`,`slots`] >> Induct_on `repl_types_input` >> rw []
  >~ [`input_init_ok _ _ _ _ _ _`] >- (
    qmatch_asmsub_rename_tac
      `infertype_prog_inc _ _ = M_success initialized_types` >>
    mp_tac (Q.SPECL [`(init_config,start_type_id)`,`decs`,`initialized_types`]
      infertype_prog_inc_sound) >> simp [ienv_ok_init_config] >>
    strip_tac >> qmatch_asmsub_rename_tac `type_ds T _ _ _ decl_tenv` >>
    `EVERY (check_ref_types_TS (ienv_to_tenv (FST initialized_types))
       (extend_dec_env env init_env)) rs` by (
         fs [EVERY_MEM] >> rw [] >> res_tac >>
         drule check_ref_types_check_ref_types_TS >> simp []) >>
    `DISJOINT (set_ids start_type_id (SND initialized_types))
       {Tlist_num;Tbool_num;Texn_num}` by (
         simp [IN_DISJOINT] >> EVAL_TAC) >>
    fs [ienv_to_tenv_init_config] >>
    irule_at Any repl_types_TS_input_init >> simp [] >>
    conj_tac >- (
      qpat_x_assum `ienv_to_tenv _ = _` (SUBST1_TAC o SYM) >> simp []) >>
    qexistsl_tac [`ck`,`decs`] >> simp []) >> fs []
  >~ [`trusted_input_value _ _ _`] >- (
    metis_tac [repl_types_TS_input_trusted_assign])
  >~ [`MEM (_,Str,_) _`] >- (
    metis_tac [repl_types_TS_input_str_assign]) >>
  qmatch_asmsub_rename_tac
    `infertype_prog_inc previous_types _ = M_success updated_types` >>
  drule repl_types_input_inference_invariants >> strip_tac >>
  drule_all infertype_prog_inc_sound >>
  strip_tac >> qmatch_asmsub_rename_tac `type_ds T _ _ _ decl_tenv` >>
  `set_ids start_type_id (SND updated_types) =
     set_ids start_type_id (SND previous_types) UNION
     set_ids (SND previous_types) (SND updated_types)` by (
       irule set_ids_UNION >> simp []) >>
  `DISJOINT (set_ids start_type_id (SND previous_types))
     (set_ids (SND previous_types) (SND updated_types))` by (
       irule DISJOINT_set_ids >> simp []) >>
  asm_rewrite_tac []
  >~ [`evaluate_decs _ _ _ = (_,Rval _)`] >- (
    drule_all repl_types_TS_input_eval >> simp [])
  >~ [`store_assign _ _ _ = SOME _`] >- (
    drule_all repl_types_TS_input_exn_assign >> simp []) >>
  drule_all repl_types_TS_input_exn >> simp []
QED


Theorem repl_types_F_repl_types_TS:
  ∀(ffi:'ffi ffi_state) rs types s env.
    repl_types F (ffi,rs) (types,s,env) ⇒
    repl_types_TS (ffi,rs) (set_ids start_type_id (SND types),ienv_to_tenv (FST types),s,env)
Proof
  rw [repl_types_def,repl_types_TS_def] >>
  drule repl_types_input_F_TS >> simp []
QED

Theorem repl_types_input_F_thm:
  !catalogue slots (ffi:'ffi ffi_state) rs input_types st env.
    repl_types_input catalogue slots F (ffi,rs) (input_types,st,env) ==>
    initial_input_certificate catalogue slots
      (set_ids start_type_id (SND input_types))
      (ienv_to_tenv (FST input_types)) st env /\
    EVERY (ref_lookup_ok st.refs) rs /\
    !decs updated_types new_st result.
      infertype_prog_inc input_types decs = M_success updated_types /\
      evaluate_decs st env decs = (new_st,result) ==>
      result <> Rerr (Rabort Rtype_error)
Proof
  qx_genl_tac [`catalogue`,`slots`,`ffi`,`rs`,`input_types`,`st`,`env`] >>
  strip_tac >> drule repl_types_input_F_TS >> strip_tac >>
  drule repl_types_TS_input_thm >> strip_tac >>
  conj_tac >- simp [] >> conj_tac >- simp [] >>
  qx_genl_tac [`decs`,`updated_types`,`new_st`,`result`] >> strip_tac >>
  drule repl_types_input_inference_invariants >> strip_tac >>
  drule_all infertype_prog_inc_sound >> strip_tac >>
  qmatch_asmsub_rename_tac `type_ds T _ _ _ decl_tenv` >>
  `DISJOINT (set_ids start_type_id (SND input_types))
     (set_ids (SND input_types) (SND updated_types))` by (
       irule DISJOINT_set_ids >> simp []) >>
  qpat_x_assum `!decs new_ids new_tenv new_st result. _`
    (qspecl_then [`decs`,`set_ids (SND input_types) (SND updated_types)`,
       `decl_tenv`,`new_st`,`result`] mp_tac) >> simp []
QED

Theorem repl_types_F_thm:
  ∀(ffi:'ffi ffi_state) rs types s env.
    repl_types F (ffi,rs) (types,s,env) ⇒
      EVERY (ref_lookup_ok s.refs) rs ∧
      ∀decs new_t new_s res.
        infertype_prog_inc types decs = M_success new_t ∧
        evaluate_decs s env decs = (new_s,res) ⇒
        res ≠ Rerr (Rabort Rtype_error)
Proof
  rw [repl_types_def] >> drule repl_types_input_F_thm >> simp []
QED

Theorem input_init_ok_bounds:
  input_init_ok catalogue slots tids tenv
    (st:'ffi semanticPrimitives$state) env ==>
  input_metadata_bounds catalogue slots st
Proof
  rw [input_init_ok_def]
  >- simp [input_metadata_bounds_def,catalogue_stamps_def] >>
  fs [initial_input_certificate_def] >>
  drule input_typing_witnesses_bounds >> simp []
QED

Theorem input_init_ok_clock:
  input_init_ok catalogue slots tids tenv (st with clock := ck) env <=>
  input_init_ok catalogue slots tids tenv (st:'ffi semanticPrimitives$state) env
Proof
  simp [input_init_ok_def,initial_input_certificate_clock]
QED

Theorem repl_types_input_skip_alt:
  repl_types_input catalogue slots T (ffi,rs) (input_types,st,env) /\
  st.ffi = next_st.ffi /\ st.refs ≼ next_st.refs /\
  next_st.clock <= st.clock /\ st.eval_state = next_st.eval_state /\
  st.next_type_stamp <= next_st.next_type_stamp /\
  st.next_exn_stamp <= next_st.next_exn_stamp ==>
  repl_types_input catalogue slots T (ffi,rs) (input_types,next_st,env)
Proof
  strip_tac >> fs [rich_listTheory.IS_PREFIX_APPEND] >>
  qmatch_asmsub_rename_tac `next_st.refs = st.refs ++ junk` >>
  `next_st = st with <|refs := st.refs ++ junk;
     clock := st.clock - (st.clock - next_st.clock);
     next_type_stamp := st.next_type_stamp +
       (next_st.next_type_stamp - st.next_type_stamp);
     next_exn_stamp := st.next_exn_stamp +
       (next_st.next_exn_stamp - st.next_exn_stamp)|>` by (
         fs [semanticPrimitivesTheory.state_component_equality]) >>
  pop_assum SUBST1_TAC >> irule repl_types_input_skip >> simp []
QED

Theorem repl_types_skip_alt:
  repl_types T (ffi,rs) (t,s,env) ∧
  s.ffi = s1.ffi ∧
  s.refs ≼ s1.refs ∧
  s1.clock ≤ s.clock ∧
  s.eval_state = s1.eval_state ∧
  s.next_type_stamp ≤ s1.next_type_stamp ∧
  s.next_exn_stamp ≤ s1.next_exn_stamp ⇒
  repl_types T (ffi,rs) (t,s1,env)
Proof
  rw [repl_types_def] >> drule_all repl_types_input_skip_alt >> simp []
QED

Theorem repl_types_input_set_clock:
  !catalogue slots b (ffi:'ffi ffi_state) rs input_types st env.
    repl_types_input catalogue slots b (ffi,rs) (input_types,st,env) ==>
    !ck. repl_types_input catalogue slots b (ffi,rs)
      (input_types,st with clock := ck,env)
Proof
  qx_genl_tac [`catalogue`,`slots`] >> Induct_on `repl_types_input` >>
  rpt conj_tac >> rpt gen_tac >> rw []
  >- suspend "Init"
  >- suspend "Skip"
  >- suspend "Eval"
  >- suspend "Exn"
  >- suspend "ExnAssign"
  >- suspend "StringAssign"
  >- suspend "TrustedAssign"
QED

Resume repl_types_input_set_clock[Init]:
  qmatch_goalsub_rename_tac `_ with clock := output_clock` >>
  drule evaluatePropsTheory.evaluate_decs_set_clock >> simp [] >>
  disch_then (qspec_then `output_clock`
    (qx_choose_then `initial_clock` assume_tac)) >> fs [] >>
  metis_tac [repl_types_input_init,input_init_ok_clock]
QED

Resume repl_types_input_set_clock[Skip]:
  qmatch_goalsub_rename_tac
    `previous_state with <|clock := output_clock; refs := _;
       next_type_stamp := _; next_exn_stamp := _|>` >>
  irule repl_types_input_skip_alt >>
  qexists_tac `previous_state with clock := output_clock` >>
  simp [rich_listTheory.IS_PREFIX_APPEND]
QED

Resume repl_types_input_set_clock[Eval]:
  qmatch_goalsub_rename_tac `_ with clock := output_clock` >>
  drule evaluatePropsTheory.evaluate_decs_set_clock >> simp [] >>
  disch_then (qspec_then `output_clock`
    (qx_choose_then `input_clock` assume_tac)) >>
  qpat_x_assum `!ck. repl_types_input _ _ _ _ _`
    (qspec_then `input_clock` assume_tac) >>
  irule_at Any repl_types_input_eval >> simp [] >> metis_tac []
QED

Resume repl_types_input_set_clock[Exn]:
  qmatch_goalsub_rename_tac `_ with clock := output_clock` >>
  drule evaluatePropsTheory.evaluate_decs_set_clock >> simp [] >>
  disch_then (qspec_then `output_clock`
    (qx_choose_then `input_clock` assume_tac)) >>
  qpat_x_assum `!ck. repl_types_input _ _ _ _ _`
    (qspec_then `input_clock` assume_tac) >>
  irule_at Any repl_types_input_exn >> simp [] >> metis_tac []
QED

Resume repl_types_input_set_clock[ExnAssign]:
  qmatch_goalsub_rename_tac
    `result_state with <|clock := output_clock; refs := assigned_store|>` >>
  drule evaluatePropsTheory.evaluate_decs_set_clock >> simp [] >>
  disch_then (qspec_then `output_clock`
    (qx_choose_then `input_clock` assume_tac)) >>
  qpat_x_assum `!ck. repl_types_input _ _ _ _ _`
    (qspec_then `input_clock` assume_tac) >>
  `result_state with <|clock := output_clock; refs := assigned_store|> =
     (result_state with clock := output_clock) with refs := assigned_store`
    by simp [] >>
  asm_rewrite_tac [] >> irule_at Any repl_types_input_exn_assign >>
  simp [] >> metis_tac []
QED

Resume repl_types_input_set_clock[StringAssign]:
  qmatch_goalsub_rename_tac
    `previous_state with <|clock := output_clock; refs := assigned_store|>` >>
  `previous_state with <|clock := output_clock; refs := assigned_store|> =
     (previous_state with clock := output_clock) with refs := assigned_store`
    by simp [] >>
  asm_rewrite_tac [] >> irule_at Any repl_types_input_str_assign >>
  simp [] >> metis_tac []
QED

Resume repl_types_input_set_clock[TrustedAssign]:
  qmatch_goalsub_rename_tac
    `previous_state with <|clock := output_clock; refs := assigned_store|>` >>
  `previous_state with <|clock := output_clock; refs := assigned_store|> =
     (previous_state with clock := output_clock) with refs := assigned_store`
    by simp [] >>
  asm_rewrite_tac [] >> irule_at Any repl_types_input_trusted_assign >>
  simp [] >> metis_tac []
QED

Finalise repl_types_input_set_clock;

Theorem repl_types_set_clock:
  ∀b ffi rs t s env.
    repl_types b (ffi,rs) (t,s,env) ⇒
    ∀ck. repl_types b (ffi,rs) (t,s with clock := ck,env)
Proof
  rw [repl_types_def] >> drule repl_types_input_set_clock >> simp []
QED

Theorem INJ_count_ADD[local]:
  INJ f a (count k) ⇒ INJ f a (count (t + k))
Proof
  fs [INJ_DEF] \\ rw [] \\ res_tac \\ fs []
QED

Theorem repl_types_input_T_F:
  !catalogue slots (ffi:'ffi ffi_state) rs types physical physical_env.
    repl_types_input catalogue slots T (ffi,rs)
      (types,physical,physical_env) ==>
    ?clean clean_env fr ft fe l.
      repl_types_input catalogue slots F (ffi,rs) (types,clean,clean_env) /\
      state_rel l fr ft fe clean physical /\
      env_rel fr ft fe clean_env physical_env /\
      input_stamp_fix catalogue ft /\ FDOM slots SUBSET count l /\
      EVERY (\(name,ty,loc). loc < l) rs
Proof
  qx_genl_tac [‘catalogue’,‘slots’] >> Induct_on ‘repl_types_input’ >>
  rpt conj_tac >> rpt gen_tac >> rw []
  >- suspend "Init"
  >- suspend "Skip"
  >- suspend "Eval"
  >- suspend "Exn"
  >- suspend "ExnAssign"
  >- suspend "StringAssign"
  >- suspend "TrustedAssign"
QED

Resume repl_types_input_T_F[Init]:
  drule input_init_ok_bounds >> strip_tac >>
  drule evaluate_decs_init >> rw [] >> gvs [] >>
  ‘repl_types_input catalogue slots F (ffi,rs)
    (types,s,extend_dec_env env init_env)’ by (
      metis_tac [repl_types_input_init]) >>
  ‘input_stamp_fix catalogue (FUN_FMAP I (count s.next_type_stamp))’ by (
    drule input_stamp_fix_identity >> simp []) >>
  qexistsl_tac [‘s’,‘extend_dec_env env init_env’,
    ‘FUN_FMAP I (count (LENGTH s.refs))’,
    ‘FUN_FMAP I (count s.next_type_stamp)’,
    ‘FUN_FMAP I (count s.next_exn_stamp)’,‘LENGTH s.refs’] >>
  simp [] >> fs [input_metadata_bounds_def,SUBSET_DEF] >>
  fs [EVERY_MEM,FORALL_PROD] >> rw [] >> res_tac >>
  fs [check_ref_types_def,env_rel_def] >>
  imp_res_tac nsAll2_nsLookup1 >> imp_res_tac nsAll2_nsLookup2 >>
  gvs [] >> res_tac >> fs [Once v_rel_cases,FLOOKUP_FUN_FMAP]
QED

Resume repl_types_input_T_F[Skip]:
  rename [‘repl_types_input _ _ F _ (saved_types,saved_state,saved_env)’,
    ‘state_rel protected_prefix ref_map type_map exn_map saved_state physical_state’] >>
  qmatch_goalsub_rename_tac ‘physical_state.clock - skipped_clock’ >>
  qexistsl_tac [‘saved_state with clock := saved_state.clock - skipped_clock’,
    ‘saved_env’,‘ref_map’,‘type_map’,‘exn_map’,‘protected_prefix’] >>
  simp [] >> conj_tac
  >- metis_tac [repl_types_input_set_clock] >>
  fs [state_rel_def,SF SFY_ss] >> rw [] >> gvs [INJ_count_ADD] >>
  qmatch_goalsub_rename_tac ‘FLOOKUP ref_map index’ >>
  qpat_x_assum ‘!n. if n < LENGTH saved_state.refs then _ else _’
    (qspec_then ‘index’ assume_tac) >> gvs [EL_APPEND1]
QED

Resume repl_types_input_T_F[Eval]:
  gvs [] >>
  rename [‘state_rel protected_prefix ref_map type_map exn_map clean_state physical_state’,
    ‘repl_types_input _ _ F _ (old_types,clean_state,clean_env)’,
    ‘evaluate_decs physical_state physical_env declarations = (_,Rval _)’] >>
  namedCases_on ‘evaluate_decs clean_state clean_env declarations’
    ["result_state result"] >>
  drule_all evaluate_decs_skip >>
  disch_then (qx_choosel_then [‘physical_result_state’,‘physical_result’,
    ‘next_ref_map’,‘next_type_map’,‘next_exn_map’] strip_assume_tac) >>
  namedCases_on ‘result’ ["clean_declarations","error"] >> gvs [res_rel_def] >>
  ‘input_stamp_fix catalogue next_type_map’ by (
    drule_all input_stamp_fix_extension >> simp []) >>
  qexistsl_tac [‘result_state’,‘extend_dec_env clean_declarations clean_env’,
    ‘next_ref_map’,‘next_type_map’,‘next_exn_map’,‘protected_prefix’] >>
  simp [] >> metis_tac [repl_types_input_eval]
QED

Resume repl_types_input_T_F[Exn]:
  gvs [] >>
  rename [‘state_rel protected_prefix ref_map type_map exn_map clean_state physical_state’,
    ‘repl_types_input _ _ F _ (old_types,clean_state,clean_env)’,
    ‘evaluate_decs physical_state physical_env declarations = (_,Rerr (Rraise _))’] >>
  namedCases_on ‘evaluate_decs clean_state clean_env declarations’
    ["result_state result"] >>
  drule_all evaluate_decs_skip >>
  disch_then (qx_choosel_then [‘physical_result_state’,‘physical_result’,
    ‘next_ref_map’,‘next_type_map’,‘next_exn_map’] strip_assume_tac) >>
  namedCases_on ‘result’ ["clean_declarations","error"] >> gvs [res_rel_def] >>
  namedCases_on ‘error’ ["clean_exception","abort"] >> gvs [res_rel_def] >>
  ‘env_rel next_ref_map next_type_map next_exn_map clean_env physical_env’ by (
    drule_all env_rel_update >> simp []) >>
  ‘input_stamp_fix catalogue next_type_map’ by (
    drule_all input_stamp_fix_extension >> simp []) >>
  qexistsl_tac [‘result_state’,‘clean_env’,‘next_ref_map’,
    ‘next_type_map’,‘next_exn_map’,‘protected_prefix’] >>
  simp [] >> metis_tac [repl_types_input_exn]
QED

Resume repl_types_input_T_F[ExnAssign]:
  gvs [] >>
  rename [‘state_rel protected_prefix ref_map type_map exn_map clean_state physical_state’,
    ‘repl_types_input _ _ F _ (old_types,clean_state,clean_env)’,
    ‘evaluate_decs physical_state physical_env declarations =
      (assigned_state,Rerr (Rraise physical_exception))’,
    ‘store_assign assigned_loc (Refv physical_exception) assigned_state.refs =
      SOME assigned_refs’] >>
  namedCases_on ‘evaluate_decs clean_state clean_env declarations’
    ["result_state result"] >>
  drule_all evaluate_decs_skip >>
  disch_then (qx_choosel_then [‘physical_result_state’,‘physical_result’,
    ‘next_ref_map’,‘next_type_map’,‘next_exn_map’] strip_assume_tac) >>
  namedCases_on ‘result’ ["clean_declarations","error"] >> gvs [res_rel_def] >>
  namedCases_on ‘error’ ["clean_exception","abort"] >> gvs [res_rel_def] >>
  ‘env_rel next_ref_map next_type_map next_exn_map clean_env physical_env’ by (
    drule_all env_rel_update >> simp []) >>
  ‘input_stamp_fix catalogue next_type_map’ by (
    drule_all input_stamp_fix_extension >> simp []) >>
  ‘assigned_loc < protected_prefix’ by (fs [EVERY_MEM,FORALL_PROD] >> res_tac) >>
  ‘FLOOKUP next_ref_map assigned_loc = SOME assigned_loc’ by fs [state_rel_def] >>
  ‘ref_rel (v_rel next_ref_map next_type_map next_exn_map)
    (Refv clean_exception) (Refv physical_exception)’ by simp [ref_rel_def] >>
  drule_all state_rel_store_assign_success >>
  disch_then (qx_choose_then ‘clean_refs’ strip_assume_tac) >>
  qexistsl_tac [‘result_state with refs := clean_refs’,‘clean_env’,
    ‘next_ref_map’,‘next_type_map’,‘next_exn_map’,‘protected_prefix’] >>
  simp [] >> metis_tac [repl_types_input_exn_assign]
QED

Resume repl_types_input_T_F[StringAssign]:
  gvs [] >>
  rename [‘state_rel protected_prefix ref_map type_map exn_map clean_state physical_state’,
    ‘repl_types_input _ _ F _ (old_types,clean_state,clean_env)’,
    ‘store_assign assigned_loc (Refv (Litv (StrLit text))) physical_state.refs =
      SOME assigned_refs’] >>
  ‘assigned_loc < protected_prefix’ by (fs [EVERY_MEM,FORALL_PROD] >> res_tac) >>
  ‘FLOOKUP ref_map assigned_loc = SOME assigned_loc’ by fs [state_rel_def] >>
  ‘ref_rel (v_rel ref_map type_map exn_map)
    (Refv (Litv (StrLit text))) (Refv (Litv (StrLit text)))’ by
      simp [ref_rel_def,v_rel_def] >>
  drule_all state_rel_store_assign_success >>
  disch_then (qx_choose_then ‘clean_refs’ strip_assume_tac) >>
  qexistsl_tac [‘clean_state with refs := clean_refs’,‘clean_env’,
    ‘ref_map’,‘type_map’,‘exn_map’,‘protected_prefix’] >>
  simp [] >> metis_tac [repl_types_input_str_assign]
QED

Resume repl_types_input_T_F[TrustedAssign]:
  gvs [] >>
  rename [‘state_rel protected_prefix ref_map type_map exn_map clean_state physical_state’,
    ‘repl_types_input _ _ F _ (old_types,clean_state,clean_env)’,
    ‘store_assign assigned_loc (Refv value) physical_state.refs = SOME assigned_refs’] >>
  ‘assigned_loc < protected_prefix’ by (fs [SUBSET_DEF,flookup_thm] >> res_tac) >>
  ‘FLOOKUP ref_map assigned_loc = SOME assigned_loc’ by fs [state_rel_def] >>
  ‘v_rel ref_map type_map exn_map value value’ by (
    fs [trusted_input_value_def] >> res_tac) >>
  ‘ref_rel (v_rel ref_map type_map exn_map) (Refv value) (Refv value)’ by
    simp [ref_rel_def] >>
  drule_all state_rel_store_assign_success >>
  disch_then (qx_choose_then ‘clean_refs’ strip_assume_tac) >>
  qexistsl_tac [‘clean_state with refs := clean_refs’,‘clean_env’,
    ‘ref_map’,‘type_map’,‘exn_map’,‘protected_prefix’] >>
  simp [] >> metis_tac [repl_types_input_trusted_assign]
QED

Finalise repl_types_input_T_F;

Theorem repl_types_T_F:
  ∀(ffi:'ffi ffi_state) rs types t env1.
    repl_types T (ffi,rs) (types,t,env1) ⇒
    ∃s env fr ft fe l.
      repl_types F (ffi,rs) (types,s,env) ∧
      state_rel l fr ft fe s t ∧
      env_rel fr ft fe env env1 ∧
      EVERY (λ(a,b,loc). loc < l) rs
Proof
  rw [repl_types_def] >> drule repl_types_input_T_F >> metis_tac []
QED


Theorem repl_types_thm:
  ∀(ffi:'ffi ffi_state) b rs types s env.
    repl_types b (ffi,rs) (types,s,env) ⇒
      EVERY (ref_lookup_ok s.refs) rs ∧
      ∀decs new_t new_s res.
        infertype_prog_inc types decs = M_success new_t ∧
        evaluate_decs s env decs = (new_s,res) ⇒
        res ≠ Rerr (Rabort Rtype_error)
Proof
  reverse (Cases_on ‘b’) >- metis_tac [repl_types_F_thm]
  \\ rpt gen_tac \\ strip_tac
  \\ drule repl_types_T_F \\ strip_tac
  \\ drule repl_types_F_thm
  \\ rpt strip_tac
  >-
   (fs [EVERY_MEM,FORALL_PROD] \\ rw [] \\ res_tac
    \\ fs [ref_lookup_ok_def,state_rel_def] \\ res_tac
    \\ gvs [store_lookup_def]
    \\ rename [‘n1 < LENGTH s'.refs’]
    \\ first_x_assum (qspec_then ‘n1’ mp_tac) \\ fs []
    \\ Cases_on ‘EL n1 s'.refs’ \\ strip_tac \\ fs [ref_rel_def]
    \\ rename [‘xx = Str’] \\ Cases_on ‘xx’
    \\ gvs [semanticPrimitivesTheory.Boolv_def]
    \\ gvs [v_rel_cases]
    \\ Cases_on ‘t2’ \\ gvs [stamp_rel_cases])
  \\ gvs []
  \\ first_x_assum $ drule_then assume_tac
  \\ Cases_on ‘evaluate_decs s' env' decs’ \\ fs []
  \\ drule_all evaluate_decs_skip \\ strip_tac \\ gvs []
  \\ Cases_on ‘r’ \\ fs []
  \\ Cases_on ‘e’ \\ fs []
QED


val _ = List.app (fn theorem => let
  val (oracles,axioms) = Tag.dest_tag (Thm.tag theorem)
  in
    if null (hyp theorem) andalso null axioms andalso
      List.all (fn name => name = "DISK_THM") oracles
    then () else failwith "REPL type support has admissions"
  end)
  [FST_roll_back, SND_roll_back, repl_types_init, repl_types_skip, repl_types_eval,
   repl_types_exn, repl_types_exn_assign, repl_types_str_assign, repl_types_rules,
   repl_types_cases, repl_types_ind, repl_types_strongind, repl_types_TS_init, repl_types_TS_eval,
   repl_types_TS_exn, repl_types_TS_exn_assign, repl_types_TS_str_assign, repl_types_TS_rules,
   repl_types_TS_cases, repl_types_TS_ind, repl_types_TS_strongind, init_config_tenv_to_ienv,
   ienv_to_tenv_init_config, tenv_ok_prim_tenv, env_rel_init_config,
   inf_set_tids_ienv_init_config, ienv_ok_init_config, repl_types_input_inference_invariants,
   repl_types_input_ienv_ok, repl_types_ienv_ok, repl_types_input_next_id, repl_types_next_id,
   convert_t_to_type, check_ref_types_check_ref_types_TS, primitive_slots_hold_initial,
   primitive_slots_hold_extension, primitive_slot_value_canonical, primitive_slots_ref_lookup,
   input_typing_primitive_assign, input_typing_initial_primitive_slots,
   repl_types_TS_input_witnesses, repl_types_TS_input_thm, repl_types_TS_thm, DISJOINT_set_ids,
   set_ids_SUBSET, set_ids_UNION, repl_types_input_F_TS, repl_types_F_repl_types_TS,
   repl_types_input_F_thm, repl_types_F_thm, input_init_ok_bounds, input_init_ok_clock, repl_types_input_skip_alt,
   repl_types_skip_alt, repl_types_input_set_clock, repl_types_set_clock, INJ_count_ADD,
   repl_types_input_T_F, repl_types_T_F, repl_types_thm, repl_types_input_init, repl_types_input_eval,
   repl_types_input_exn, repl_types_input_exn_assign, repl_types_input_str_assign,
   repl_types_input_trusted_assign, repl_types_input_rules, repl_types_input_cases,
   repl_types_input_ind, repl_types_input_strongind, repl_types_TS_input_init,
   repl_types_TS_input_eval, repl_types_TS_input_exn, repl_types_TS_input_exn_assign,
   repl_types_TS_input_str_assign, repl_types_TS_input_trusted_assign, repl_types_TS_input_rules,
   repl_types_TS_input_cases, repl_types_TS_input_ind, repl_types_TS_input_strongind,
   repl_types_input_skip];
