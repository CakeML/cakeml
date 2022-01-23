(*
  Proofs about how the REPL uses types and the type inferencer
*)
open preamble
open semanticsPropsTheory evaluateTheory semanticPrimitivesTheory
open inferTheory inferSoundTheory typeSoundTheory semanticsTheory
     envRelTheory primSemEnvTheory typeSoundInvariantsTheory
     namespacePropsTheory inferPropsTheory repl_check_and_tweakTheory
open ml_progTheory

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
     repl_types b (ffi,rs) (types,new_s,env)) ∧
[repl_types_exn_assign:]
  (∀ffi rs decs types new_types (s:'ffi semanticPrimitives$state) env e
    new_s name loc new_store b.
     repl_types b (ffi,rs) (types,s,env) ∧
     infertype_prog_inc types decs = Success new_types ∧
     evaluate$evaluate_decs s env decs = (new_s,Rerr (Rraise e)) ∧
     MEM (name,Exn,loc) rs ∧
     store_assign loc (Refv e) new_s.refs = SOME new_store ⇒
     repl_types b (ffi,rs) (types,new_s with refs := new_store,env)) ∧
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
  >- (
    rename1`_ tys decs = Success _`
    \\ Cases_on`tys` \\ fs[infertype_prog_inc_def]
    \\ every_case_tac \\ fs[]
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

Theorem repl_types_TS_thm:
  ∀(ffi:'ffi ffi_state) rs tids tenv s env.
    repl_types_TS (ffi,rs) (tids,tenv,s,env) ⇒
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
  \\ cheat
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
    (* TODO: repl_types needs to use the correct IDs *)
    \\ cheat
    (* \\ irule_at Any repl_types_TS_exn
    \\ CONJ_TAC >-
      (match_mp_tac DISJOINT_set_ids>>simp[init_infer_state_def])
    \\ asm_exists_tac \\ simp[] *))
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
    \\ cheat (* see above *) )
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

Theorem repl_types_thm:
  ∀(ffi:'ffi ffi_state) b rs types s env.
    repl_types b (ffi,rs) (types,s,env) ⇒
      EVERY (ref_lookup_ok s.refs) rs ∧
      ∀decs new_t new_s res.
        infertype_prog_inc types decs = Success new_t ∧
        evaluate_decs s env decs = (new_s,res) ⇒
        res ≠ Rerr (Rabort Rtype_error)
Proof
  cheat (* Magnus: I believe this can be proved using an
           evaluate-simulation proof from repl_types_F_thm *)
QED

val _ = export_theory();
