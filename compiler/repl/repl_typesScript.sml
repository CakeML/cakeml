(*
  Proofs about how the REPL uses types and the type inferencer
*)
open preamble
open semanticsPropsTheory evaluateTheory semanticPrimitivesTheory
open inferTheory inferSoundTheory typeSoundTheory semanticsTheory
     envRelTheory primSemEnvTheory typeSoundInvariantsTheory
     namespacePropsTheory inferPropsTheory repl_check_and_tweakTheory
open ml_progTheory evaluate_skipTheory

val _ = new_theory "repl_types";

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
    nsLookup env.v name = SOME (Loc loc)
End

Inductive repl_types:
[repl_types_init:]
  (∀ffi rs decs types (s:'ffi semanticPrimitives$state) env ck b.
     infertype_prog_inc (init_config, start_type_id) decs = Success types ∧
     evaluate$evaluate_decs (init_state ffi with clock := ck) init_env decs = (s,Rval env) ∧
     EVERY (check_ref_types (FST types) (extend_dec_env env init_env)) rs ⇒
     repl_types b (ffi,rs) (types,s,extend_dec_env env init_env)) ∧
[repl_types_skip:]
  (∀ffi rs types junk ck t e (s:'ffi semanticPrimitives$state) env.
     repl_types T (ffi,rs) (types,s,env) ⇒
     repl_types T (ffi,rs) (types,s with <| refs  := s.refs ++ junk                  ;
                                            clock := s.clock - ck                    ;
                                            next_type_stamp := s.next_type_stamp + t ;
                                            next_exn_stamp  := s.next_exn_stamp + e  |>,env)) ∧
[repl_types_eval:]
  (∀ffi rs decs types new_types (s:'ffi semanticPrimitives$state) env new_env new_s b.
     repl_types b (ffi,rs) (types,s,env) ∧
     infertype_prog_inc types decs = Success new_types ∧
     evaluate$evaluate_decs s env decs = (new_s,Rval new_env) ⇒
     repl_types b (ffi,rs) (new_types,new_s,extend_dec_env new_env env)) ∧
[repl_types_exn:]
  (∀ffi rs decs types new_types (s:'ffi semanticPrimitives$state) env e new_s b.
     repl_types b (ffi,rs) (types,s,env) ∧
     infertype_prog_inc types decs = Success new_types ∧
     evaluate$evaluate_decs s env decs = (new_s,Rerr (Rraise e)) ⇒
     repl_types b (ffi,rs) (roll_back types new_types,new_s,env)) ∧
[repl_types_exn_assign:]
  (∀ffi rs decs types new_types (s:'ffi semanticPrimitives$state) env e
    new_s name loc new_store b.
     repl_types b (ffi,rs) (types,s,env) ∧
     infertype_prog_inc types decs = Success new_types ∧
     evaluate$evaluate_decs s env decs = (new_s,Rerr (Rraise e)) ∧
     MEM (name,Exn,loc) rs ∧
     store_assign loc (Refv e) new_s.refs = SOME new_store ⇒
     repl_types b (ffi,rs) (roll_back types new_types,new_s with refs := new_store,env)) ∧
[repl_types_str_assign:]
  (∀ffi rs types (s:'ffi semanticPrimitives$state) env t name loc new_store b.
     repl_types b (ffi,rs) (types,s,env) ∧
     MEM (name,Str,loc) rs ∧
     store_assign loc (Refv (Litv (StrLit t))) s.refs = SOME new_store ⇒
     repl_types b (ffi,rs) (types,s with refs := new_store,env))
End

(* Mirror definitions for repl_types using the type system directly *)
Definition to_type_TS_def:
  to_type_TS Bool = Tapp [] Tbool_num ∧
  to_type_TS Str  = Tapp [] Tstring_num ∧
  to_type_TS Exn  = Tapp [] Texn_num
End

Definition check_ref_types_TS_def:
  check_ref_types_TS types (env :semanticPrimitives$v sem_env) (name,ty,loc) ⇔
    nsLookup types.v name = SOME (0,Tapp [to_type_TS ty] Tref_num) ∧
    nsLookup env.v name = SOME (Loc loc)
End

Inductive repl_types_TS:
[repl_types_TS_init:]
  (∀ffi rs decs tids tenv (s:'ffi semanticPrimitives$state) env ck.
     type_ds T prim_tenv decs tids tenv ∧
     DISJOINT tids {Tlist_num; Tbool_num; Texn_num} ∧
     evaluate$evaluate_decs (init_state ffi with clock := ck) init_env decs = (s,Rval env) ∧
     EVERY (check_ref_types_TS (extend_dec_tenv tenv prim_tenv) (extend_dec_env env init_env)) rs ⇒
     repl_types_TS (ffi,rs) (tids,extend_dec_tenv tenv prim_tenv,s,extend_dec_env env init_env)) ∧
[repl_types_TS_eval:]
  (∀ffi rs decs tids tenv (s:'ffi semanticPrimitives$state) env
    new_tids new_tenv new_env new_s.
     repl_types_TS (ffi,rs) (tids,tenv,s,env) ∧
     type_ds T tenv decs new_tids new_tenv ∧
     DISJOINT tids new_tids ∧
     evaluate$evaluate_decs s env decs = (new_s,Rval new_env) ⇒
     repl_types_TS (ffi,rs) (tids ∪ new_tids,extend_dec_tenv new_tenv tenv,new_s,extend_dec_env new_env env)) ∧
[repl_types_TS_exn:]
  (∀ffi rs decs tids tenv (s:'ffi semanticPrimitives$state) env
    new_tids new_tenv new_s e.
     repl_types_TS (ffi,rs) (tids,tenv,s,env) ∧
     type_ds T tenv decs new_tids new_tenv ∧
     DISJOINT tids new_tids ∧
     evaluate$evaluate_decs s env decs = (new_s,Rerr (Rraise e)) ⇒
     repl_types_TS (ffi,rs) (tids ∪ new_tids,tenv,new_s,env)) ∧
[repl_types_TS_exn_assign:]
  (∀ffi rs decs tids tenv (s:'ffi semanticPrimitives$state) env
    new_tids new_tenv new_s e name loc new_store.
     repl_types_TS (ffi,rs) (tids,tenv,s,env) ∧
     type_ds T tenv decs new_tids new_tenv ∧
     DISJOINT tids new_tids ∧
     evaluate$evaluate_decs s env decs = (new_s,Rerr (Rraise e)) ∧
     MEM (name,Exn,loc) rs ∧
     store_assign loc (Refv e) new_s.refs = SOME new_store ⇒
     repl_types_TS (ffi,rs) (tids ∪ new_tids,tenv,new_s with refs := new_store,env)) ∧
[repl_types_TS_str_assign:]
  (∀ffi rs tids tenv (s:'ffi semanticPrimitives$state) env t name loc new_store.
     repl_types_TS (ffi,rs) (tids,tenv,s,env) ∧
     MEM (name,Str,loc) rs ∧
     store_assign loc (Refv (Litv (StrLit t))) s.refs = SOME new_store ⇒
     repl_types_TS (ffi,rs) (tids,tenv,s with refs := new_store,env))
End

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

Theorem repl_types_ienv_ok:
  ∀b (ffi:'ffi ffi_state) rs types s env.
  repl_types b (ffi,rs) (types,s,env) ⇒
  ienv_ok {} (FST types)
Proof
  Induct_on`repl_types`
  \\ rw[infertype_prog_inc_def, CaseEq"exc"]
  \\ fs[PULL_EXISTS]
  >- (
    every_case_tac
    \\ fs[]
    \\ drule (CONJUNCT2 infer_d_check)
    \\ rw[]
    \\ match_mp_tac ienv_ok_extend_dec_ienv
    \\ fs[ienv_ok_init_config])
  >- (
    rename1`_ tys decs = Success _`
    \\ Cases_on`tys` \\ fs[infertype_prog_inc_def]
    \\ every_case_tac \\ fs[]
    \\ drule (CONJUNCT2 infer_d_check)
    \\ rw[]
    \\ match_mp_tac ienv_ok_extend_dec_ienv
    \\ metis_tac[])
QED

Theorem repl_types_next_id:
  ∀b (ffi:'ffi ffi_state) rs types s env.
  repl_types b (ffi,rs) (types,s,env) ⇒
  start_type_id ≤ SND types
Proof
  Induct_on`repl_types`
  \\ rw[infertype_prog_inc_def, CaseEq"exc"]
  \\ fs[PULL_EXISTS]
  >- (
    every_case_tac
    \\ fs[]
    \\ drule (CONJUNCT2 infer_d_next_id_mono)
    \\ rw[init_infer_state_def])
  \\ (
    rename1`_ tys decs = Success _`
    \\ Cases_on`tys` \\ fs[infertype_prog_inc_def]
    \\ fs[CaseEqs["infer$exc","prod"]] \\ fs[]
    \\ drule (CONJUNCT2 infer_d_next_id_mono)
    \\ simp[init_infer_state_def]
    \\ rw[])
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
  ref_lookup_ok refs (name:(string,string) id,ty,loc) =
    ∃v:semanticPrimitives$v.
      store_lookup loc refs = SOME (Refv v) ∧
      (ty = Bool ⇒ v = Boolv T ∨ v = Boolv F) ∧
      (ty = Str ⇒ ∃t. v = Litv (StrLit t))
End

Theorem type_d_tids_disjoint:
  (!b tenv d tids tenv'.
   type_d b tenv d tids tenv' ⇒
     DISJOINT tids (set (Tlist_num::Tbool_num::prim_type_nums))) ∧
  (!b tenv ds tids tenv'.
   type_ds b tenv ds tids tenv' ⇒
     DISJOINT tids (set (Tlist_num::Tbool_num::prim_type_nums)))
Proof
  ho_match_mp_tac typeSystemTheory.type_d_ind \\ rw[]
QED

Theorem ref_lookup_ok_store_assign:
  EVERY (ref_lookup_ok store) rs ∧
  MEM (n,Str,loc) rs ∧
  store_assign loc (Refv (Litv (StrLit t))) store = SOME new_store ⇒
  EVERY (ref_lookup_ok new_store) rs
Proof
  simp[store_assign_def]>>
  simp[EVERY_MEM,FORALL_PROD] >>
  rw[]>>fs[ref_lookup_ok_def]>>
  first_assum drule>>
  pop_assum mp_tac>>
  first_x_assum drule>>
  rw[]>>
  fs[store_lookup_def,EL_LUPDATE]>>
  IF_CASES_TAC
  >- (
    rw[]>>fs[Boolv_def])>>
  metis_tac[]
QED

Theorem type_d_assign_str:
  nsLookup tenv.v n = SOME (0,Tapp [Tapp [] Tstring_num ] Tref_num) ==>
  type_d T tenv
  (Dlet ARB Pany (App Opassign [Var n; Lit (StrLit t)]))
  {}  <|v := nsEmpty; c := nsEmpty; t := nsEmpty|>
Proof
  rw[]
  \\ simp[Once typeSystemTheory.type_d_cases,typeSystemTheory.is_value_def]
  \\ simp[astTheory.pat_bindings_def]
  \\ simp[Once typeSystemTheory.type_p_cases]
  \\ simp[typeSystemTheory.tenv_add_tvs_def]
  \\ simp[typeSystemTheory.type_pe_determ_def]
  \\ simp[Once typeSystemTheory.type_p_cases]
  \\ simp[Once typeSystemTheory.type_p_cases]
  \\ simp[Once typeSystemTheory.type_e_cases]
  \\ simp[Once typeSystemTheory.type_e_cases]
  \\ simp[Once typeSystemTheory.type_e_cases]
  \\ simp[Once typeSystemTheory.type_e_cases]
  \\ simp[Once typeSystemTheory.type_e_cases]
  \\ simp[Once typeSystemTheory.type_e_cases]
  \\ simp[Once typeSystemTheory.type_op_def]
  \\ simp[PULL_EXISTS,typeSystemTheory.check_freevars_def]
  \\ simp[typeSystemTheory.lookup_var_def]
  \\ EVAL_TAC
QED

Theorem type_v_invert_strlit:
  ∀n ct tenv l ty.
  l = Litv (StrLit t) ∧
  type_v n ct tenv l ty ⇒
  ty = Tstring
Proof
  Induct_on`type_v` \\ rw[]
QED

Theorem type_s_store_assign_StrLit:
  type_s ctMap st tenvS ∧
  EVERY (ref_lookup_ok st) rs ∧
  MEM (n,Str,loc) rs ∧
  store_assign loc (Refv (Litv (StrLit t))) st = SOME new_st ⇒
  type_s ctMap new_st tenvS
Proof
  simp[store_assign_def]
  \\ strip_tac
  \\ fs[EVERY_MEM]
  \\ first_x_assum drule
  \\ simp[ref_lookup_ok_def]
  \\ strip_tac
  \\ fs[type_s_def,store_assign_def,type_sv_def]
  \\ rw[]
  \\ fs[store_lookup_def]
  \\ fs[EL_LUPDATE]
  \\ pop_assum mp_tac \\ rw[]
  >- (
    `type_sv ctMap tenvS (EL l st) st'` by metis_tac[]
    \\ qpat_x_assum`EL l st = _` SUBST_ALL_TAC
    \\ Cases_on`st'`\\fs[type_sv_def]
    \\ metis_tac[type_v_invert_strlit,type_v_cases] )
  \\ metis_tac[]
QED

Theorem repl_types_TS_thm:
  ∀(ffi:'ffi ffi_state) rs tids tenv s env.
    repl_types_TS (ffi,rs) (tids,tenv,s,env) ⇒
      (* Probably keep more information about ctMap tenvS *)
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
  Induct_on`repl_types_TS`
  \\ CONJ_TAC
  >- (
    rpt gen_tac \\ strip_tac \\ simp[]
    \\ drule_then drule decs_type_sound \\ simp[]
    \\ resolve_then Any (qspecl_then[`tids`,`ffi`]mp_tac)
         (GSYM init_state_env_thm)
         prim_type_sound_invariants
    \\ impl_tac >- fs[]
    \\ strip_tac \\ strip_tac
    \\ ‘type_sound_invariant (init_state ffi with clock := ck)
          init_env ctMap FEMPTY tids prim_tenv’ by
      fs [type_sound_invariant_def,consistent_ctMap_def,SF SFY_ss]
    \\ first_x_assum drule \\ strip_tac
    \\ conj_tac >- (
      first_assum $ irule_at Any \\ simp[]
      \\ fs[SUBSET_DEF]
      \\ metis_tac[] )
    \\ conj_tac
    >- (
      fs[EVERY_MEM, FORALL_PROD] \\ rw[]
      \\ first_x_assum drule
      \\ rw[check_ref_types_TS_def, ref_lookup_ok_def]
      \\ fs[type_sound_invariant_def]
      \\ fs[type_s_def]
      \\ qmatch_goalsub_rename_tac`store_lookup l s.refs`
      \\ first_x_assum(qspec_then`l`mp_tac)
      \\ fs[type_all_env_def]
      \\ drule_then drule nsAll2_nsLookup1
      \\ fs[typeSystemTheory.extend_dec_tenv_def]
      \\ simp[Once type_v_cases]
      \\ simp[EVAL``Tref_num = Tarray_num``]
      \\ strip_tac \\ strip_tac
      \\ first_x_assum drule
      \\ Cases_on`v` \\ simp[type_sv_def]
      \\ fs[good_ctMap_def, ctMap_has_bools_def]
      \\ rw[] \\ fs[to_type_TS_def]
      \\ pop_assum mp_tac
      \\ simp[Once type_v_cases]
      \\ rw[] \\ TRY (ntac 4 (pop_assum mp_tac) \\ EVAL_TAC \\ NO_TAC)
      \\ TRY (drule_then drule typeSysPropsTheory.type_funs_Tfn \\ rw[])
      >- (
        qhdtm_x_assum`ctMap_ok`mp_tac
        \\ simp[ctMap_ok_def]
        \\ rpt strip_tac
        \\ reverse(Cases_on`stamp`)
        >- ( res_tac \\ pop_assum mp_tac \\ EVAL_TAC )
        \\ qmatch_asmsub_rename_tac`TypeStamp cn n`
        \\ `same_type (TypeStamp "True" bool_type_num) (TypeStamp cn n)`
        by ( first_x_assum irule \\ simp[] )
        \\ pop_assum mp_tac
        \\ simp[same_type_def]
        \\ strip_tac \\ rw[]
        \\ `cn = "True" ∨ cn = "False"` by metis_tac[NOT_SOME_NONE]
        \\ rveq
        \\ EVAL_TAC
        \\ qhdtm_x_assum`FLOOKUP`mp_tac
        \\ qhdtm_x_assum`FLOOKUP`mp_tac
        \\ qhdtm_x_assum`FLOOKUP`mp_tac
        \\ simp[]
        \\ rpt strip_tac
        \\ rveq
        \\ qhdtm_x_assum`LIST_REL`mp_tac
        \\ simp[])
      \\ qhdtm_x_assum`ctMap_ok`mp_tac
      \\ simp[ctMap_ok_def]
      \\ spose_not_then strip_assume_tac
      \\ reverse(Cases_on`stamp`)
      >- ( res_tac \\ pop_assum mp_tac \\ EVAL_TAC )
      \\ res_tac
      \\ ntac 2 (pop_assum mp_tac)
      \\ EVAL_TAC)
    \\ rpt gen_tac \\ strip_tac
    \\ CCONTR_TAC \\ fs[]
    \\ drule_then drule decs_type_sound
    \\ simp[]
    \\ fs[type_sound_invariant_def, consistent_ctMap_def]
    \\ first_assum $ irule_at Any \\ simp[]
    \\ reverse conj_tac >- metis_tac[]
    \\  fs[IN_DISJOINT, SUBSET_DEF]
    \\ strip_tac \\ spose_not_then strip_assume_tac
    \\ `x NOTIN tids` by metis_tac[]
    \\ `x IN FRANGE ((SND o SND) o_f ctMap)` by metis_tac[]
    \\ `x IN prim_type_ids` by metis_tac[]
    \\ fs[IN_FRANGE_FLOOKUP, FLOOKUP_o_f, CaseEq"option"]
    \\ rveq \\ PairCases_on`v` \\ fs[] \\ rveq
    \\ drule (CONJUNCT2 type_d_tids_disjoint)
    \\ simp[IN_DISJOINT]
    \\ first_assum $ irule_at Any
    \\ pop_assum mp_tac
    \\ EVAL_TAC )
  \\ CONJ_TAC >- (
    rpt gen_tac \\ strip_tac \\ simp[]
    \\ drule_then drule decs_type_sound \\ simp[]
    \\ fs[]
    \\ disch_then (qspecl_then[`ctMap`,`tenvS`] mp_tac)
    \\ impl_tac >- (
      fs[type_sound_invariant_def,consistent_ctMap_def]
      \\ reverse conj_tac >- metis_tac[]
      \\  fs[IN_DISJOINT, SUBSET_DEF]
      \\ strip_tac \\ spose_not_then strip_assume_tac
      \\ `x NOTIN tids` by metis_tac[]
      \\ `x IN FRANGE ((SND o SND) o_f ctMap)` by metis_tac[]
      \\ `x IN prim_type_ids` by metis_tac[]
      \\ fs[IN_FRANGE_FLOOKUP, FLOOKUP_o_f, CaseEq"option"]
      \\ rveq \\ PairCases_on`v` \\ fs[] \\ rveq
      \\ drule (CONJUNCT2 type_d_tids_disjoint)
      \\ simp[IN_DISJOINT]
      \\ first_assum $ irule_at Any
      \\ pop_assum mp_tac
      \\ EVAL_TAC )
    \\ strip_tac
    \\ conj_tac >- (
      first_assum $ irule_at Any
      \\ fs[SUBSET_DEF]
      \\ metis_tac[] )
    \\ conj_tac>-
      cheat
    \\ rpt gen_tac \\ strip_tac
    \\ CCONTR_TAC \\ fs[]
    \\ drule_then drule decs_type_sound
    \\ simp[]
    \\ fs[type_sound_invariant_def, consistent_ctMap_def]
    \\ first_assum $ irule_at Any \\ simp[]
    \\ reverse conj_tac >- metis_tac[]
    \\  fs[IN_DISJOINT, SUBSET_DEF]
    \\ strip_tac \\ spose_not_then strip_assume_tac
    \\ `x NOTIN tids` by metis_tac[]
    \\ `x IN FRANGE ((SND o SND) o_f ctMap)` by metis_tac[]
    \\ `x IN prim_type_ids` by metis_tac[]
    \\ fs[IN_FRANGE_FLOOKUP, FLOOKUP_o_f, CaseEq"option"]
    \\ rveq \\ PairCases_on`v` \\ fs[] \\ rveq
    \\ drule (CONJUNCT2 type_d_tids_disjoint)
    \\ simp[IN_DISJOINT]
    \\ first_assum $ irule_at Any
    \\ pop_assum mp_tac
    \\ EVAL_TAC)
  \\ CONJ_TAC >- (
    rpt gen_tac \\ strip_tac \\ simp[]
    \\ drule_then drule decs_type_sound \\ simp[]
    \\ fs[]
    \\ disch_then (qspecl_then[`ctMap`,`tenvS`] mp_tac)
    \\ impl_tac >- (
      fs[type_sound_invariant_def,consistent_ctMap_def]
      \\ reverse conj_tac >- metis_tac[]
      \\  fs[IN_DISJOINT, SUBSET_DEF]
      \\ strip_tac \\ spose_not_then strip_assume_tac
      \\ `x NOTIN tids` by metis_tac[]
      \\ `x IN FRANGE ((SND o SND) o_f ctMap)` by metis_tac[]
      \\ `x IN prim_type_ids` by metis_tac[]
      \\ fs[IN_FRANGE_FLOOKUP, FLOOKUP_o_f, CaseEq"option"]
      \\ rveq \\ PairCases_on`v` \\ fs[] \\ rveq
      \\ drule (CONJUNCT2 type_d_tids_disjoint)
      \\ simp[IN_DISJOINT]
      \\ first_assum $ irule_at Any
      \\ pop_assum mp_tac
      \\ EVAL_TAC )
    \\ strip_tac
    \\ conj_tac >- (
      first_assum $ irule_at Any
      \\ fs[SUBSET_DEF]
      \\ metis_tac[] )
    \\ conj_tac>-
      cheat
    \\ rpt gen_tac \\ strip_tac
    \\ CCONTR_TAC \\ fs[]
    \\ drule_then drule decs_type_sound
    \\ simp[]
    \\ fs[type_sound_invariant_def, consistent_ctMap_def]
    \\ first_assum $ irule_at Any \\ simp[]
    \\ reverse conj_tac >- metis_tac[]
    \\  fs[IN_DISJOINT, SUBSET_DEF]
    \\ strip_tac \\ spose_not_then strip_assume_tac
    \\ `x NOTIN tids` by metis_tac[]
    \\ `x IN FRANGE ((SND o SND) o_f ctMap)` by metis_tac[]
    \\ `x IN prim_type_ids` by metis_tac[]
    \\ fs[IN_FRANGE_FLOOKUP, FLOOKUP_o_f, CaseEq"option"]
    \\ rveq \\ PairCases_on`v` \\ fs[] \\ rveq
    \\ drule (CONJUNCT2 type_d_tids_disjoint)
    \\ simp[IN_DISJOINT]
    \\ first_assum $ irule_at Any
    \\ pop_assum mp_tac
    \\ EVAL_TAC)
  \\ CONJ_TAC >- (
    rpt gen_tac \\ strip_tac \\ simp[]
    \\ drule_then drule decs_type_sound \\ simp[]
    \\ fs[]
    \\ disch_then (qspecl_then[`ctMap`,`tenvS`] mp_tac)
    \\ impl_tac >- (
      fs[type_sound_invariant_def,consistent_ctMap_def]
      \\ reverse conj_tac >- metis_tac[]
      \\  fs[IN_DISJOINT, SUBSET_DEF]
      \\ strip_tac \\ spose_not_then strip_assume_tac
      \\ `x NOTIN tids` by metis_tac[]
      \\ `x IN FRANGE ((SND o SND) o_f ctMap)` by metis_tac[]
      \\ `x IN prim_type_ids` by metis_tac[]
      \\ fs[IN_FRANGE_FLOOKUP, FLOOKUP_o_f, CaseEq"option"]
      \\ rveq \\ PairCases_on`v` \\ fs[] \\ rveq
      \\ drule (CONJUNCT2 type_d_tids_disjoint)
      \\ simp[IN_DISJOINT]
      \\ first_assum $ irule_at Any
      \\ pop_assum mp_tac
      \\ EVAL_TAC )
    \\ strip_tac
    \\ conj_tac >- (
      cheat)
    \\ conj_tac >- (
      cheat)
    \\ rpt gen_tac \\ strip_tac
    \\ CCONTR_TAC \\ fs[]
    \\ drule_then drule decs_type_sound
    \\ simp[]
    \\ fs[type_sound_invariant_def, consistent_ctMap_def]
    \\ first_assum $ irule_at Any \\ simp[]
    \\ reverse conj_tac >- (
      conj_tac >- metis_tac[]
      \\ cheat (* should be proved earlier *))
    \\  fs[IN_DISJOINT, SUBSET_DEF]
    \\ strip_tac \\ spose_not_then strip_assume_tac
    \\ `x NOTIN tids` by metis_tac[]
    \\ `x IN FRANGE ((SND o SND) o_f ctMap)` by metis_tac[]
    \\ `x IN prim_type_ids` by metis_tac[]
    \\ fs[IN_FRANGE_FLOOKUP, FLOOKUP_o_f, CaseEq"option"]
    \\ rveq \\ PairCases_on`v` \\ fs[] \\ rveq
    \\ drule (CONJUNCT2 type_d_tids_disjoint)
    \\ simp[IN_DISJOINT]
    \\ first_assum $ irule_at Any
    \\ pop_assum mp_tac
    \\ EVAL_TAC)
  \\ (
    rpt gen_tac \\ strip_tac \\ fs[]
    \\ CONJ_TAC >- (
      fs[type_sound_invariant_def]
      \\ first_assum $ irule_at Any
      \\ CONJ_TAC>- (
        fs[consistent_ctMap_def]
        \\ metis_tac[])
      \\ fs[consistent_ctMap_def]
      \\ CONJ_TAC >- metis_tac[]
      \\ metis_tac[type_s_store_assign_StrLit])
    \\ CONJ_TAC >- metis_tac[ref_lookup_ok_store_assign]
    \\ rpt gen_tac \\ strip_tac
    \\ CCONTR_TAC \\ fs[]
    \\ drule_then drule decs_type_sound
    \\ simp[]
    \\ fs[type_sound_invariant_def, consistent_ctMap_def]
    \\ first_assum $ irule_at Any \\ simp[]
    \\ reverse conj_tac >- (
      conj_tac >- metis_tac[]
      \\ metis_tac[type_s_store_assign_StrLit])
    \\  fs[IN_DISJOINT, SUBSET_DEF]
    \\ strip_tac \\ spose_not_then strip_assume_tac
    \\ `x NOTIN tids` by metis_tac[]
    \\ `x IN FRANGE ((SND o SND) o_f ctMap)` by metis_tac[]
    \\ `x IN prim_type_ids` by metis_tac[]
    \\ fs[IN_FRANGE_FLOOKUP, FLOOKUP_o_f, CaseEq"option"]
    \\ rveq \\ PairCases_on`v` \\ fs[] \\ rveq
    \\ drule (CONJUNCT2 type_d_tids_disjoint)
    \\ simp[IN_DISJOINT]
    \\ first_assum $ irule_at Any
    \\ pop_assum mp_tac
    \\ EVAL_TAC)
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

Theorem count_id_MORE:
  tids ⊆ count id ∧ id ≤ id' ⇒ tids ⊆ count id'
Proof
  rw[count_def,SUBSET_DEF]>>
  first_x_assum drule>>
  fs[]
QED

Theorem set_ids_UNION:
  id ≤ id' ∧ sid ≤ id ⇒
  set_ids sid id' = set_ids sid id ∪ set_ids id id'
Proof
  rw[set_ids_def,EXTENSION,EQ_IMP_THM]
QED

Theorem repl_types_F_repl_types_TS:
  ∀(ffi:'ffi ffi_state) rs types s env.
    repl_types F (ffi,rs) (types,s,env) ⇒
    repl_types_TS (ffi,rs) (set_ids start_type_id (SND types),ienv_to_tenv (FST types),s,env)
Proof
  Induct_on`repl_types`
  \\ rw[infertype_prog_inc_def, CaseEq"exc", init_infer_state_def]
  \\ fs[PULL_EXISTS]
  >- (
    every_case_tac \\ fs[]
    \\ drule (CONJUNCT2 infer_d_sound)
    \\ disch_then (resolve_then Any mp_tac env_rel_init_config)
    \\ impl_tac>- simp[]
    \\ strip_tac
    \\ rveq
    \\ simp[ienv_to_tenv_extend,ienv_to_tenv_init_config]
    \\ irule_at Any repl_types_TS_init
    \\ simp[]
    \\ rpt (CONJ_TAC >- EVAL_TAC)
    \\ reverse CONJ_TAC >-
      (asm_exists_tac >> fs[])
    \\ qpat_x_assum`_ _ rs` mp_tac
    \\ match_mp_tac EVERY_MONOTONIC
    \\ rw[]
    \\ simp[GSYM ienv_to_tenv_init_config, GSYM ienv_to_tenv_extend]
    \\ match_mp_tac check_ref_types_check_ref_types_TS
    \\ metis_tac[])
  >- (
    rename1`_ A decs = Success _`
    \\ `∃tys id. A = (tys,id)` by metis_tac[PAIR]
    \\ rw[] \\ fs[infertype_prog_inc_def]
    \\ every_case_tac \\ fs[]
    \\ drule (CONJUNCT2 infer_d_sound)
    \\ disch_then(qspec_then `ienv_to_tenv tys` mp_tac)
    \\ impl_tac >- (
      drule repl_types_next_id
      \\ simp[init_infer_state_def]
      \\ metis_tac[repl_types_ienv_ok, env_rel_ienv_to_tenv,FST])
    \\ strip_tac
    \\ imp_res_tac (CONJUNCT2 infer_d_next_id_mono)
    \\ drule repl_types_next_id
    \\ rveq \\ fs[init_infer_state_def]
    \\ strip_tac
    \\ drule_then drule set_ids_UNION
    \\ disch_then SUBST_ALL_TAC
    \\ simp[ienv_to_tenv_extend]
    \\ irule_at Any repl_types_TS_eval
    \\ CONJ_TAC >-
      (match_mp_tac DISJOINT_set_ids>>simp[init_infer_state_def])
    \\ asm_exists_tac \\ simp[])
  >- (
    rename1`_ A decs = Success _`
    \\ `∃tys id. A = (tys,id)` by metis_tac[PAIR]
    \\ rw[] \\ fs[infertype_prog_inc_def]
    \\ fs[CaseEqs["infer$exc","prod"]] \\ rveq
    \\ drule (CONJUNCT2 infer_d_sound)
    \\ disch_then(qspec_then `ienv_to_tenv tys` mp_tac)
    \\ impl_tac >- (
      drule repl_types_next_id
      \\ simp[init_infer_state_def]
      \\ metis_tac[repl_types_ienv_ok, env_rel_ienv_to_tenv,FST])
    \\ strip_tac
    \\ imp_res_tac (CONJUNCT2 infer_d_next_id_mono)
    \\ drule repl_types_next_id
    \\ rveq \\ fs[init_infer_state_def]
    \\ strip_tac
    \\ drule_then drule set_ids_UNION
    \\ disch_then SUBST_ALL_TAC
    \\ simp[ienv_to_tenv_extend]
    \\ irule_at Any repl_types_TS_exn
    \\ CONJ_TAC >-
      (match_mp_tac DISJOINT_set_ids>>simp[init_infer_state_def])
    \\ asm_exists_tac \\ simp[]
    \\ metis_tac[])
  >- (
    rename1`_ A decs = Success _`
    \\ `∃tys id. A = (tys,id)` by metis_tac[PAIR]
    \\ rw[] \\ fs[infertype_prog_inc_def]
    \\ fs[CaseEqs["infer$exc","prod"]] \\ rveq
    \\ drule (CONJUNCT2 infer_d_sound)
    \\ disch_then(qspec_then `ienv_to_tenv tys` mp_tac)
    \\ impl_tac >- (
      drule repl_types_next_id
      \\ simp[init_infer_state_def]
      \\ metis_tac[repl_types_ienv_ok, env_rel_ienv_to_tenv,FST])
    \\ strip_tac
    \\ simp[ienv_to_tenv_extend]
    \\ drule_then drule repl_types_TS_exn_assign
    \\ simp[init_infer_state_def]
    \\ imp_res_tac (CONJUNCT2 infer_d_next_id_mono)
    \\ drule repl_types_next_id
    \\ fs[init_infer_state_def] \\ strip_tac
    \\ simp[GSYM set_ids_UNION]
    \\ disch_then irule
    \\ CONJ_TAC >-
      (match_mp_tac DISJOINT_set_ids>>simp[])
    \\ asm_exists_tac \\ simp[]
    \\ metis_tac[])
  >>
    metis_tac[repl_types_TS_str_assign]
QED

Theorem repl_types_F_thm:
  ∀(ffi:'ffi ffi_state) rs types s env.
    repl_types F (ffi,rs) (types,s,env) ⇒
      EVERY (ref_lookup_ok s.refs) rs ∧
      ∀decs new_t new_s res.
        infertype_prog_inc types decs = Success new_t ∧
        evaluate_decs s env decs = (new_s,res) ⇒
        res ≠ Rerr (Rabort Rtype_error)
Proof
  rpt gen_tac
  \\ strip_tac
  \\ imp_res_tac repl_types_F_repl_types_TS
  \\ drule repl_types_TS_thm
  \\ strip_tac
  \\ rw[]
  \\ rename1`_ A decs = Success _`
  \\ `∃tys id. A = (tys,id)` by metis_tac[PAIR]
  \\ qpat_x_assum`_ = Success _` mp_tac
  \\ simp[infertype_prog_inc_def]
  \\ every_case_tac \\ simp[]
  \\ drule (CONJUNCT2 infer_d_sound)
  \\ disch_then(qspec_then `ienv_to_tenv tys` mp_tac)
  \\ impl_tac >- (
    drule repl_types_next_id
    \\ simp[init_infer_state_def]
    \\ metis_tac[repl_types_ienv_ok, env_rel_ienv_to_tenv,FST])
  \\ strip_tac
  \\ strip_tac
  \\ `FST A = tys` by fs[]
  \\ pop_assum SUBST_ALL_TAC
  \\ first_x_assum drule
  \\ disch_then match_mp_tac
  \\ fs[init_infer_state_def]
  \\ match_mp_tac DISJOINT_set_ids
  \\ simp[set_ids_SUBSET]
QED

Theorem repl_types_set_clock:
  ∀ffi rs t s env.
    repl_types F (ffi,rs) (t,s,env) ⇒
    ∀ck. repl_types F (ffi,rs) (t,s with clock := ck,env)
Proof
  Induct_on ‘repl_types’ \\ rpt conj_tac \\ rpt gen_tac \\ rw []
  >- (* init *)
   (drule evaluatePropsTheory.evaluate_decs_set_clock \\ fs []
    \\ disch_then (qspec_then ‘ck'’ strip_assume_tac)
    \\ irule_at Any repl_types_init \\ fs []
    \\ rpt (first_assum $ irule_at Any))
  >- (* eval *)
   (drule evaluatePropsTheory.evaluate_decs_set_clock \\ fs []
    \\ disch_then (qspec_then ‘ck’ strip_assume_tac)
    \\ irule_at Any repl_types_eval \\ fs []
    \\ rpt (first_assum $ irule_at Any))
  >- (* exn *)
   (drule evaluatePropsTheory.evaluate_decs_set_clock \\ fs []
    \\ disch_then (qspec_then ‘ck’ strip_assume_tac)
    \\ irule_at Any repl_types_exn \\ fs []
    \\ rpt (first_assum $ irule_at Any))
  >- (* exn_assign *)
   (drule evaluatePropsTheory.evaluate_decs_set_clock \\ fs []
    \\ disch_then (qspec_then ‘ck’ strip_assume_tac)
    \\ ‘new_s with <|clock := ck; refs := new_store|> =
        (new_s with clock := ck) with refs := new_store’ by fs []
    \\ asm_rewrite_tac []
    \\ irule_at Any repl_types_exn_assign \\ fs []
    \\ rpt (first_assum $ irule_at Any))
  \\ gvs []
  \\ ‘s with <|clock := ck; refs := new_store|> =
      (s with clock := ck) with refs := new_store’ by fs []
  \\ asm_rewrite_tac []
  \\ irule_at Any repl_types_str_assign \\ fs []
  \\ rpt (first_assum $ irule_at Any)
QED

Triviality INJ_count_ADD:
  INJ f a (count k) ⇒ INJ f a (count (t + k))
Proof
  fs [INJ_DEF] \\ rw [] \\ res_tac \\ fs []
QED

Theorem repl_types_T_F:
  ∀(ffi:'ffi ffi_state) rs types t env1.
    repl_types T (ffi,rs) (types,t,env1) ⇒
    ∃s env fr ft fe l.
      repl_types F (ffi,rs) (types,s,env) ∧
      state_rel l fr ft fe s t ∧
      env_rel fr ft fe env env1 ∧
      EVERY (λ(a,b,loc). loc < l) rs
Proof
  Induct_on ‘repl_types’ \\ rpt conj_tac \\ rpt gen_tac \\ rw []
  >- (* init *)
   (drule evaluate_decs_init \\ rw [] \\ gvs []
    \\ first_assum $ irule_at Any
    \\ first_assum $ irule_at Any
    \\ irule_at Any repl_types_init
    \\ rpt (first_assum $ irule_at Any)
    \\ fs [EVERY_MEM,FORALL_PROD] \\ rw []
    \\ res_tac
    \\ fs [check_ref_types_def,env_rel_def]
    \\ res_tac \\ fs [Once v_rel_cases]
    \\ fs [FLOOKUP_DEF])
  >- (* skip *)
   (‘repl_types F (ffi,rs) (types',s' with clock := s'.clock - ck,env')’
           by (irule_at Any repl_types_set_clock \\ fs [])
    \\ pop_assum $ irule_at Any
    \\ rpt (last_assum $ irule_at $ Pos last)
    \\ fs [state_rel_def,SF SFY_ss]
    \\ rw []
    \\ first_x_assum (qspec_then ‘n’ assume_tac)
    \\ gvs [EL_APPEND1]
    \\ irule INJ_count_ADD \\ fs [])
  >- (* eval *)
   (gvs []
    \\ irule_at Any repl_types_eval
    \\ ntac 2 (first_assum $ irule_at $ Pos hd)
    \\ rename [‘state_rel l fr ft fe s1 s2’,‘env_rel fr ft fe env1 env2’]
    \\ Cases_on ‘evaluate_decs s1 env1 decs’ \\ gvs []
    \\ drule_all evaluate_decs_skip \\ gvs []
    \\ strip_tac
    \\ Cases_on ‘r’ \\ fs [res_rel_def]
    \\ rpt (first_assum $ irule_at $ Pos hd))
  >- (* exn *)
   (gvs []
    \\ irule_at Any repl_types_exn
    \\ ntac 2 (first_assum $ irule_at $ Pos hd)
    \\ rename [‘state_rel l fr ft fe s1 s2’,‘env_rel fr ft fe env1 env2’]
    \\ Cases_on ‘evaluate_decs s1 env1 decs’ \\ gvs []
    \\ drule_all evaluate_decs_skip \\ gvs []
    \\ strip_tac
    \\ Cases_on ‘r’ \\ fs [res_rel_def]
    \\ rename [‘_ (Rerr e1) _’]
    \\ Cases_on ‘e1’ \\ fs [res_rel_def]
    \\ rpt (first_assum $ irule_at $ Pos hd)
    \\ rpt (first_assum $ irule_at $ Pos last)
    \\ irule env_rel_update
    \\ rpt (first_assum $ irule_at $ Pos last))
  >- (* exn_assign *)
   (gvs []
    \\ irule_at Any repl_types_exn_assign
    \\ ntac 2 (first_assum $ irule_at $ Pos hd)
    \\ rename [‘state_rel l fr ft fe s1 s2’,‘env_rel fr ft fe env1 env2’]
    \\ Cases_on ‘evaluate_decs s1 env1 decs’ \\ gvs []
    \\ drule_all evaluate_decs_skip \\ gvs []
    \\ strip_tac
    \\ Cases_on ‘r’ \\ fs [res_rel_def]
    \\ rename [‘_ (Rerr e1) _’]
    \\ Cases_on ‘e1’ \\ fs [res_rel_def]
    \\ rpt (first_assum $ irule_at $ Pos hd)
    \\ first_assum $ irule_at $ Pos last
    \\ irule_at Any env_rel_update
    \\ rpt (first_assum $ irule_at $ Pos hd)
    \\ fs [state_rel_def,store_assign_def]
    \\ fs [EL_LUPDATE,EVERY_MEM] \\ res_tac
    \\ Cases_on ‘EL loc new_s.refs’ \\ fs [store_v_same_type_def]
    \\ res_tac \\ fs []
    \\ first_assum (qspec_then ‘loc’ assume_tac)
    \\ qpat_x_assum ‘FLOOKUP fr loc = SOME loc’ assume_tac \\ fs []
    \\ qpat_x_assum ‘loc < LENGTH q.refs’ assume_tac
    \\ fs [] \\ gvs []
    \\ Cases_on ‘EL loc q.refs’ \\ fs [ref_rel_def]
    \\ strip_tac \\ first_x_assum (qspec_then ‘n’ mp_tac) \\ fs [EL_LUPDATE]
    \\ reverse IF_CASES_TAC \\ fs []
    \\ strip_tac \\ fs []
    \\ ‘FLOOKUP fr1 loc = SOME loc ∧ loc < LENGTH q.refs’ by (res_tac \\ fs [])
    \\ ‘n = loc ⇔ m = loc’ by
     (fs [FLOOKUP_DEF]
      \\ qpat_x_assum ‘INJ ($' fr1) (count (LENGTH q.refs)) _’ mp_tac
      \\ simp_tac (srw_ss()) [INJ_DEF] \\ metis_tac [])
    \\ asm_rewrite_tac []
    \\ rw [] \\ fs [] \\ rw [ref_rel_def]
    \\ fs [FLOOKUP_DEF] \\ gvs [])
  >- (* str_assign *)
   (gvs []
    \\ irule_at Any repl_types_str_assign
    \\ ntac 2 (first_assum $ irule_at $ Pos hd)
    \\ ntac 2 (first_assum $ irule_at $ Pos last)
    \\ gvs [store_assign_def,EVERY_MEM]
    \\ res_tac \\ fs []
    \\ rename [‘state_rel l fr ft fe s1 s2’,‘env_rel fr ft fe env1 env2’]
    \\ fs [state_rel_def]
    \\ qexists_tac ‘t’ \\ fs []
    \\ fs [EL_LUPDATE] \\ res_tac
    \\ Cases_on ‘EL loc s2.refs’ \\ fs [store_v_same_type_def]
    \\ first_assum (qspec_then ‘loc’ assume_tac)
    \\ qpat_x_assum ‘FLOOKUP fr loc = SOME loc’ assume_tac \\ fs []
    \\ gvs [] \\ Cases_on ‘EL loc s1.refs’ \\ fs [ref_rel_def]
    \\ rw []
    >- fs [ref_rel_def,Once v_rel_cases]
    \\ first_x_assum (qspec_then ‘n’ mp_tac) \\ fs []
    \\ rw [] \\ fs [] \\ rw []
    \\ fs [FLOOKUP_DEF] \\ gvs []
    \\ qpat_x_assum ‘INJ ($' fr) (count (LENGTH _)) _’ mp_tac
    \\ simp_tac (srw_ss()) [INJ_DEF] \\ metis_tac [])
QED

Theorem repl_types_thm:
  ∀(ffi:'ffi ffi_state) b rs types s env.
    repl_types b (ffi,rs) (types,s,env) ⇒
      EVERY (ref_lookup_ok s.refs) rs ∧
      ∀decs new_t new_s res.
        infertype_prog_inc types decs = Success new_t ∧
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

val _ = export_theory();
