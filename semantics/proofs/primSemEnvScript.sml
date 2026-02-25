(*
  Proof about the primitive semantic environment
*)
Theory primSemEnv
Ancestors
  ast evaluate semanticPrimitives semantics evaluate
  semanticPrimitivesProps primTypes typeSystem
  typeSoundInvariants namespace namespaceProps typeSysProps
Libs
  preamble evaluateComputeLib

Theorem prim_sem_env_eq =
  EVAL ``prim_sem_env (ffi:'ffi ffi_state)``

Theorem prim_type_sound_invariants:
  ∀type_ids sem_st prim_env.
    (sem_st,prim_env) = THE (prim_sem_env ffi) ∧
    DISJOINT type_ids {Tlist_num; Tbool_num; Texn_num}
    ⇒
    ?ctMap.
      type_sound_invariant sem_st prim_env ctMap FEMPTY type_ids prim_tenv ∧
      FRANGE ((SND o SND) o_f ctMap) ⊆ prim_type_ids
Proof
  rw[type_sound_invariant_def, prim_sem_env_eq, prim_tenv_def] >>
  gvs [evaluate_decs_def,check_dup_ctors_def,combine_dec_result_def] >>
  qexists_tac`FEMPTY |++ REVERSE [
      (bind_stamp, ([],[],Texn_num));
      (div_stamp, ([],[],Texn_num));
      (chr_stamp, ([],[],Texn_num));
      (subscript_stamp, ([],[],Texn_num));
      (TypeStamp «[]» list_type_num, ([«'a»],[],Tlist_num));
      (TypeStamp «::» list_type_num, ([«'a»],[Tvar «'a»; Tlist (Tvar «'a»)], Tlist_num));
      (TypeStamp «True» bool_type_num, ([],[], Tbool_num));
      (TypeStamp «False» bool_type_num, ([],[], Tbool_num))]` >>
  rw []
  >- (
    simp [tenv_ok_def, tenv_ctor_ok_def, tenv_abbrev_ok_def]>>
    rw[] >>
    rpt (
      irule nsAll_nsBind >>
      rw [check_freevars_def]))
  >- (
    simp [good_ctMap_def, ctMap_ok_def, flookup_fupdate_list] >>
    EVAL_TAC >>
    rw [] >>
    rw [same_type_def] >>
    rw [FEVERY_FUPDATE, check_freevars_def, FEVERY_FEMPTY])
  >- (
    rw [consistent_ctMap_def] >>
    fs [FDOM_FUPDATE_LIST, bool_type_num_def,
        list_type_num_def, subscript_stamp_def, chr_stamp_def, div_stamp_def,
        bind_stamp_def] >>
    simp [DISJOINT_DEF, EXTENSION, IN_FRANGE_FLOOKUP, FLOOKUP_o_f,
         flookup_fupdate_list] >>
    CCONTR_TAC >>
    fs [] >>
    fs [AllCaseEqs()] >>
    rw [] >> fs [])
  >- (
    simp [type_all_env_def, GSYM namespaceTheory.nsEmpty_def,
          GSYM namespaceTheory.nsBind_def] >>
    fs [nsAppend_def,build_tdefs_def,build_constrs_def] >>
    rpt (
      irule nsAll2_nsBind >>
      rw [type_ctor_def, flookup_fupdate_list, bind_stamp_def, div_stamp_def,
          chr_stamp_def, subscript_stamp_def,nsSing_def,GSYM nsBind_def,
          bool_type_num_def, list_type_num_def, GSYM nsEmpty_def]))
  >- simp [type_s_def, store_lookup_def]
  >- (
    simp[SUBSET_DEF]
    \\ ho_match_mp_tac IN_FRANGE_o_f_suff
    \\ ho_match_mp_tac IN_FRANGE_FUPDATE_LIST_suff
    \\ simp[]
    \\ EVAL_TAC
    \\ rpt strip_tac \\ rveq
    \\ EVAL_TAC)
QED
