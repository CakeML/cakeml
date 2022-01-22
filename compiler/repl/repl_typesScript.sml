(*
  Proofs about how the REPL uses types and the type inferencer
*)
open preamble
open semanticsPropsTheory evaluateTheory semanticPrimitivesTheory
open inferTheory inferSoundTheory typeSoundTheory semanticsTheory
     envRelTheory primSemEnvTheory typeSoundInvariantsTheory
     namespacePropsTheory inferPropsTheory
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
  (∀ffi rs decs types (s:'ffi semanticPrimitives$state) env b.
     infertype_prog init_config decs = Success types ∧
     evaluate$evaluate_decs (init_state ffi) init_env decs = (s,Rval env) ∧
     EVERY (check_ref_types types (extend_dec_env env init_env)) rs ⇒
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
     infertype_prog types decs = Success new_types ∧
     evaluate$evaluate_decs s env decs = (new_s,Rval new_env) ⇒
     repl_types b (ffi,rs) (new_types,new_s,extend_dec_env new_env env)) ∧
[repl_types_exn:]
  (∀ffi rs decs types new_types (s:'ffi semanticPrimitives$state) env e new_s b.
     repl_types b (ffi,rs) (types,s,env) ∧
     infertype_prog types decs = Success new_types ∧
     evaluate$evaluate_decs s env decs = (new_s,Rerr (Rraise e)) ⇒
     repl_types b (ffi,rs) (types,new_s,env)) ∧
[repl_types_exn_assign:]
  (∀ffi rs decs types new_types (s:'ffi semanticPrimitives$state) env e
    new_s name loc new_store b.
     repl_types b (ffi,rs) (types,s,env) ∧
     infertype_prog types decs = Success new_types ∧
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

Definition ref_lookup_ok_def:
  ref_lookup_ok refs (name:(string,string) id,ty,loc) =
    ∃v:semanticPrimitives$v.
      store_lookup loc refs = SOME (Refv v) ∧
      (ty = Bool ⇒ v = Boolv T ∨ v = Boolv F) ∧
      (ty = Str ⇒ ∃t. v = Litv (StrLit t))
End

Theorem init_config_tenv_to_ienv:
  init_config = tenv_to_ienv prim_tenv
Proof
  rw[init_config_def, tenv_to_ienv_def]
  \\ EVAL_TAC
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

Theorem repl_types_F_thm:
  ∀(ffi:'ffi ffi_state) rs types s env.
    repl_types F (ffi,rs) (types,s,env) ⇒
      EVERY (ref_lookup_ok s.refs) rs ∧
      ∀decs new_t new_s res.
        infertype_prog types decs = Success new_t ∧
        evaluate_decs s env decs = (new_s,res) ⇒
        res ≠ Rerr (Rabort Rtype_error)
Proof
  Induct_on`repl_types`
  \\ rw[infertype_prog_def, CaseEq"exc", init_infer_state_def] \\ fs[PULL_EXISTS]
  \\ qmatch_asmsub_abbrev_tac`infer_ds _ _ s0`
  >- (
    Cases_on`infer_ds init_config decs s0` \\ fs[] \\ rw[]
    \\ drule (CONJUNCT2 infer_d_sound)
    \\ disch_then (resolve_then Any mp_tac env_rel_init_config)
    \\ impl_tac >- simp[Abbr`s0`] \\ strip_tac
    \\ fs[EVERY_MEM, FORALL_PROD] \\ rw[]
    \\ first_x_assum drule
    \\ rw[check_ref_types_def, ref_lookup_ok_def]
    \\ drule_then drule decs_type_sound \\ simp[]
    \\ qmatch_asmsub_abbrev_tac`type_ds _ _ _ ids`
    \\ resolve_then Any (qspecl_then[`ids`,`ffi`]mp_tac)
         (GSYM init_state_env_thm)
         prim_type_sound_invariants
    \\ impl_tac >- ( simp[Abbr`ids`, Abbr`s0`] \\ EVAL_TAC )
    \\ strip_tac \\ strip_tac
    \\ first_x_assum drule \\ strip_tac
    \\ fs[type_sound_invariant_def]
    \\ fs[type_s_def]
    \\ qmatch_goalsub_rename_tac`store_lookup l s.refs`
    \\ first_x_assum(qspec_then`l`mp_tac)
    \\ fs[type_all_env_def]
    \\ drule_then drule nsAll2_nsLookup1
    \\ fs[typeSystemTheory.extend_dec_tenv_def, extend_dec_ienv_def, init_config_def]
    \\ simp[ienv_to_tenv_def, nsLookup_nsMap,
            primTypesTheory.prim_tenv_def, nsAppend_nsEmpty]
    \\ simp[Once type_v_cases, convert_t_def]
    \\ simp[EVAL``Tref_num = Tarray_num``]
    \\ strip_tac \\ strip_tac
    \\ first_x_assum drule
    \\ Cases_on`v` \\ simp[type_sv_def]
    \\ fs[good_ctMap_def, ctMap_has_bools_def]
    \\ rw[] \\ fs[to_type_def, convert_t_def]
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
    \\ EVAL_TAC )
  \\ cheat
QED

Theorem repl_types_thm:
  ∀(ffi:'ffi ffi_state) b rs types s env.
    repl_types b (ffi,rs) (types,s,env) ⇒
      EVERY (ref_lookup_ok s.refs) rs ∧
      ∀decs new_t new_s res.
        infertype_prog types decs = Success new_t ∧
        evaluate_decs s env decs = (new_s,res) ⇒
        res ≠ Rerr (Rabort Rtype_error)
Proof
  cheat (* Magnus: I believe this can be proved using an
           evaluate-simulation proof from repl_types_F_thm *)
QED

val _ = export_theory();
