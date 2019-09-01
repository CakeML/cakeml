(*
  Correctness proof for data_space
*)
open preamble data_spaceTheory dataSemTheory dataPropsTheory;

val _ = new_theory"data_spaceProof";

val _ = temp_bring_to_front_overload"get_vars"{Name="get_vars",Thy="dataSem"};
val _ = temp_bring_to_front_overload"cut_env"{Name="cut_env",Thy="dataSem"};
val _ = temp_bring_to_front_overload"evaluate"{Name="evaluate",Thy="dataSem"};
val _ = temp_bring_to_front_overload"lookup"{Name="lookup",Thy="sptree"};
val _ = temp_bring_to_front_overload"insert"{Name="insert",Thy="sptree"};
val _ = temp_bring_to_front_overload"wf"{Name="wf",Thy="sptree"};

val IMP_sptree_eq = Q.prove(
  `wf x /\ wf y /\ (!a. lookup a x = lookup a y) ==> (x = y)`,
  METIS_TAC [spt_eq_thm]);

val mk_wf_inter = Q.prove(
  `!t1 t2. inter t1 t2 = mk_wf (inter t1 t2)`,
  full_simp_tac(srw_ss())[]);

Theorem get_vars_IMP_LENGTH:
   !xs s l. get_vars xs s = SOME l ==> (LENGTH l = LENGTH xs)
Proof
  Induct \\ fs [get_vars_def] \\ rw [] \\ every_case_tac \\ fs []
  \\ rw [] \\ fs [] \\ res_tac \\ fs []
QED

val case_eq_thms = bvlPropsTheory.case_eq_thms;

val evaluate_compile = Q.prove(
  `!c s res s2 vars l.
     res <> SOME (Rerr(Rabort Rtype_error)) /\ (evaluate (c,s) = (res,s2)) /\
     locals_ok s.locals l ==>
     ?w safe peak.
      (evaluate (compile c, s with locals := l) =
         (res,if res = NONE then s2 with <| locals := w;
                                            safe_for_space := safe;
                                            peak_heap_length := peak |>
                            else s2 with <| safe_for_space := safe;
                                            peak_heap_length := peak |>)) /\
         locals_ok s2.locals w`,
  SIMP_TAC std_ss [compile_def]
  \\ recInduct evaluate_ind \\ REPEAT STRIP_TAC
  \\ fs[evaluate_def,space_def,pMakeSpace_def]
  THEN1 (* Skip *)
   (MAP_EVERY Q.EXISTS_TAC [`l`,`s2.safe_for_space`,`s2.peak_heap_length`]
   \\ rw [state_component_equality])
  THEN1 (* Move *)
   (Cases_on `get_var src s.locals` \\ fs[] \\ SRW_TAC [] []
    \\ fs[get_var_def,lookup_union,set_var_def,locals_ok_def]
    \\ RES_TAC \\ fs[]
    \\ Q.EXISTS_TAC `insert dest x l`
    \\ fs[lookup_insert,state_component_equality]
    \\ METIS_TAC [])
  THEN1 (* Assign *)
   (BasicProvers.TOP_CASE_TAC \\ fs[cut_state_opt_def]
    \\ BasicProvers.CASE_TAC \\ fs[]
    THEN1 (Cases_on `get_vars args s.locals`
      \\ fs[cut_state_opt_def]
      \\ `get_vars args l =
          get_vars args s.locals` by
       (MATCH_MP_TAC EVERY_get_vars
        \\ fs[EVERY_MEM,locals_ok_def]
        \\ REPEAT STRIP_TAC \\ IMP_RES_TAC get_vars_IMP_domain
        \\ fs[domain_lookup])
      \\ fs[] \\ reverse(Cases_on `do_app op x s`)
      \\ fs[] >- (
           imp_res_tac do_app_err >> fs[] >>
           fs [EVAL ``op_requires_names (FFI i)``])
      \\ Cases_on `a` \\ fs[] \\ SRW_TAC [] []
      \\ IMP_RES_TAC do_app_locals \\ fs[set_var_def]
      \\ Q.EXISTS_TAC `insert dest q l`
      \\ fs[set_var_def,locals_ok_def,lookup_insert,state_component_equality]
      \\ METIS_TAC [do_app_const])
    \\ `cut_state x (s with locals := l) = cut_state x s` by
     (fs[cut_state_def]
      \\ Cases_on `cut_env x s.locals` \\ fs[]
      \\ IMP_RES_TAC locals_ok_cut_env \\ fs[] \\ NO_TAC)
    \\ fs[] \\ POP_ASSUM (K ALL_TAC)
    \\ fs[cut_state_def,cut_env_def]
    \\ Cases_on `domain x SUBSET domain s.locals` \\ fs[]
    \\ Q.EXISTS_TAC `s2.locals`
    \\ Q.EXISTS_TAC `s2.safe_for_space`
    \\ Q.EXISTS_TAC `s2.peak_heap_length`
    \\ fs[locals_ok_def]
    \\ SRW_TAC [] [state_component_equality])
  THEN1 (* Tick *)
   (Cases_on `s.clock = 0` \\ fs[] \\ SRW_TAC [] []
    \\ fs[locals_ok_def,call_env_def,
         EVAL ``fromList []``,lookup_def,dec_clock_def,state_component_equality]
    \\ METIS_TAC [])
  THEN1 (* MakeSpace *)
   (Cases_on `cut_env names s.locals` \\ fs[]
    \\ IMP_RES_TAC locals_ok_cut_env
    \\ fs[LET_DEF,add_space_def,
         state_component_equality,locals_ok_def])
  THEN1 (* Raise *)
   (Cases_on `get_var n s.locals` \\ fs[] \\ SRW_TAC [] []
    \\ `jump_exc (s with locals := l) = jump_exc s` by
         fs[jump_exc_def]
    \\ Cases_on `jump_exc s` \\ fs[]
    \\ `get_var n l = SOME x` by
         fs[locals_ok_def,get_var_def]
    \\ fs[]
    \\ srw_tac [] []
    \\ Q.EXISTS_TAC `s2.locals`
    \\ Q.EXISTS_TAC `s2.safe_for_space`
    \\ Q.EXISTS_TAC `s2.peak_heap_length`
    \\ fs[locals_ok_def,state_component_equality])
  THEN1 (* Return *)
   (Cases_on `get_var n s.locals` \\ fs[] \\ SRW_TAC [] []
    \\ `get_var n l = SOME x` by
         fs[locals_ok_def,get_var_def]
    \\ fs[]
    \\ srw_tac [] [call_env_def]
    \\ fs[locals_ok_def,call_env_def,lookup_fromList,
           dec_clock_def,state_component_equality])
  THEN1 (* Seq *)
   (fs[LET_DEF] \\ Cases_on `space c2`
    \\ fs[] THEN1
     (Cases_on `evaluate (c1,s)` \\ fs[]
      \\ Cases_on `c1` \\ fs[pMakeSpace_def]
      THEN1 (fs[evaluate_def])
      \\ Cases_on `q = SOME (Rerr(Rabort Rtype_error))`
      \\ fs[]
      \\ SIMP_TAC std_ss [Once evaluate_def]
      \\ fs[space_def,pMakeSpace_def]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `l`)
      \\ fs[] \\ REPEAT STRIP_TAC
      \\ fs[LET_DEF,Seq_Skip]
      \\ Cases_on `q` \\ fs[] \\ SRW_TAC [] []
      \\ TRY (Q.EXISTS_TAC `w` \\ rw [state_component_equality] \\ NO_TAC)
      \\ qpat_x_assum `∀l. _` drule \\ rw []
      \\ drule_then (qspecl_then [`safe`,`peak`] ASSUME_TAC) evaluate_safe_peak_swap
      \\ qmatch_asmsub_abbrev_tac `evaluate_safe x r'`
      \\ MAP_EVERY Q.EXISTS_TAC [`w'`,`evaluate_safe x r'`,`evaluate_peak x r'`]
      \\ fs [state_fupdcanon]
      \\ rw [])
    \\ PairCases_on `y` \\ fs[]
    \\ Cases_on `evaluate (c1,s)` \\ fs[]
    \\ reverse (Cases_on `c1`) \\ fs[]
    \\ TRY (fs[pMakeSpace_def,space_def]
      \\ SIMP_TAC std_ss [Once evaluate_def,LET_DEF]
      \\ fs[] \\ SRW_TAC [] []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `l`) \\ fs[]
      \\ Cases_on `q = SOME (Rerr(Rabort Rtype_error))`
      \\ fs[] \\ REPEAT STRIP_TAC
      \\ fs[] \\ Cases_on `q`
      \\ fs[] \\ SRW_TAC [] []
      \\ TRY (Q.EXISTS_TAC `w` \\ rw [state_component_equality] \\ NO_TAC)
      \\ qpat_x_assum `∀l. _` drule \\ rw []
      \\ drule_then (qspecl_then [`safe`,`peak`] ASSUME_TAC) evaluate_safe_peak_swap
      \\ qmatch_asmsub_abbrev_tac `evaluate_safe x r'`
      \\ MAP_EVERY Q.EXISTS_TAC [`w'`,`evaluate_safe x r'`,`evaluate_peak x r'`]
      \\ fs [state_fupdcanon] \\ rw [] \\ NO_TAC)
    THEN1 (* MakeSpace *)
     (fs[pMakeSpace_def,space_def,Seq_Skip]
      \\ Cases_on `q = SOME (Rerr(Rabort Rtype_error))` \\ fs[]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `l`) \\ fs[]
      \\ SIMP_TAC std_ss [Once evaluate_def] \\ fs[]
      \\ Cases_on `cut_env s' l` \\ fs[]
      \\ REPEAT STRIP_TAC \\ SRW_TAC [] [] \\ fs[]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `w`) \\ fs[]
      \\ ONCE_REWRITE_TAC [evaluate_def] \\ fs[LET_DEF]
      \\ fs[evaluate_def]
      \\ Cases_on `cut_env y1 w` \\ fs[]
      \\ REPEAT STRIP_TAC
      \\ `cut_env (inter s' y1) l = SOME x'` by
       (fs[cut_env_def] \\ SRW_TAC [] []
        \\ fs[state_component_equality,add_space_def]
        \\ SRW_TAC [] []
        \\ fs[SUBSET_DEF,domain_inter,lookup_inter_alt]
        \\ Cases_on `x IN domain y1` \\ fs[])
        \\ fs[]
      \\ fs[]
      \\ `∃safe peak.
            (add_space (s with locals := l) y0 with locals := x') =
            (add_space (r with locals := w) y0 with <| locals := x';
                                                       safe_for_space := safe;
                                                       peak_heap_length := peak |>)`
         by (fs[state_component_equality,add_space_def]
            \\ SRW_TAC [] [] \\ DECIDE_TAC)
      \\ drule_then (qspecl_then [`safe''`,`peak''`] ASSUME_TAC) evaluate_safe_peak_swap
      \\ qmatch_asmsub_abbrev_tac `evaluate_safe y2 r2`
      \\ fs [state_fupdcanon]
      \\ MAP_EVERY Q.EXISTS_TAC [`w'`,`evaluate_safe y2 r2`,`evaluate_peak y2 r2`]
      \\ rw[Abbr `r2`] \\ METIS_TAC [])
    THEN1 (* Assign *)
     (fs[pMakeSpace_def,space_def] \\ reverse (Cases_on `o0`)
      \\ fs[evaluate_def,cut_state_opt_def] THEN1
       (fs[pMakeSpace_def,space_def,evaluate_def,
            cut_state_opt_def,cut_state_def]
        \\ Cases_on `cut_env x s.locals`
        \\ fs[] \\ SRW_TAC [] []
        \\ IMP_RES_TAC locals_ok_cut_env \\ fs[]
        \\ Cases_on `get_vars l' x'`
        \\ fs [] \\ SRW_TAC [] []
        THEN1
         (reverse(Cases_on `do_app o' x'' (s with locals := x')`)
          \\ fs[] \\ SRW_TAC [] []
          \\ Cases_on `a` \\ fs[] \\ SRW_TAC [] []
          \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `l`) \\ fs[]
          \\ REPEAT STRIP_TAC \\ fs[]
          \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC
               `(set_var n q r').locals`) \\ fs[]
          \\ fs[locals_ok_refl] \\ REPEAT STRIP_TAC
          \\ Cases_on `cut_env y1 (set_var n q r').locals` \\ fs[LET_DEF]
          \\ Q.EXISTS_TAC `w'`
          \\ Q.EXISTS_TAC `safe'`
          \\ Q.EXISTS_TAC `peak'`
          \\ fs[]
          \\ Q.PAT_X_ASSUM `evaluate xxx = yyy` (fn th => SIMP_TAC std_ss [GSYM th])
          \\ `∀s. s with locals := s.locals = s` suffices_by fs []
          \\ fs[state_component_equality,add_space_def])
        \\ fs [] \\ rfs []
        \\ qpat_x_assum `∀l. locals_ok s.locals _ ⇒ _` drule
        \\ rw [])
      \\ Cases_on `op_requires_names o'` \\ fs[] \\ SRW_TAC [] []
      \\ Cases_on `get_vars l' s.locals` \\ fs[] \\ SRW_TAC [] []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `l`) \\ fs[]
      \\ impl_tac >- (rpt strip_tac >> fs[])
      \\ rpt strip_tac
      \\ fs[pMakeSpace_def,space_def]
      \\ fs[evaluate_def,cut_state_opt_def]
      \\ IMP_RES_TAC locals_ok_get_vars \\ fs[]
      \\ reverse (Cases_on `do_app o' x s`) \\ fs[] THEN1
       (IMP_RES_TAC do_app_err \\ fs[]
        \\ srw_tac[][] \\ fs[]
        \\ fs [EVAL ``¬op_requires_names (FFI i)``])
      \\ Cases_on `a`
      \\ IMP_RES_TAC do_app_locals \\ fs[] \\ SRW_TAC [] []
      \\ NTAC 2 (Q.PAT_X_ASSUM `!xx.bbb` (K ALL_TAC))
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `w`) \\ fs[]
      \\ qmatch_asmsub_abbrev_tac `state_safe_for_space_fupd (K SAFE0) _`
      \\ Cases_on `cut_env y1 w`
      \\ fs[LET_DEF,add_space_def,set_var_def]
      \\ `SAFE0 = safe` by fs [state_component_equality]
      \\ fs [] \\ pop_assum (K ALL_TAC)
      \\ qpat_x_assum `Abbrev _` (K ALL_TAC)
      \\ qpat_abbrev_tac `SAFE1 = (r'.safe_for_space ∧ _)`
      \\ qpat_abbrev_tac `SAFE2 = (s.safe_for_space  ∧ _)`
      \\ qpat_abbrev_tac `PEAK1 = (MAX r'.peak_heap_length _)`
      \\ qpat_abbrev_tac `PEAK2 = (MAX s.peak_heap_length  _)`
      \\ qpat_x_assum `cut_env _ _ = _` MP_TAC
      \\ REPEAT STRIP_TAC \\ fs[Once cut_env_def]
      \\ REPEAT STRIP_TAC
      \\ `domain (list_insert l' (delete n y1)) SUBSET domain l` by
       (fs[dataSemTheory.state_component_equality]
        \\ SRW_TAC [] []
        \\ IMP_RES_TAC locals_ok_IMP
        \\ IMP_RES_TAC get_vars_IMP_domain \\ fs[]
        \\ fs[domain_list_insert,SUBSET_DEF]
        \\ REPEAT STRIP_TAC \\ RES_TAC \\ NO_TAC)
      \\ fs[]
      \\ `get_vars l' (inter l (list_insert l' (delete n y1))) = get_vars l' l`
           by (MATCH_MP_TAC EVERY_get_vars
               \\ fs[EVERY_MEM,lookup_inter_alt,
                     domain_list_insert] \\ NO_TAC)
      \\ fs[do_app_def,do_space_alt]
      \\ IF_CASES_TAC >- (
        fs[do_install_def,case_eq_thms]
        \\ pairarg_tac \\ fs[]
        \\ pairarg_tac \\ fs[]
        \\ fs[case_eq_thms] \\ rveq
        \\ fs [] \\ rfs []
        \\ fs[state_component_equality] \\ rveq
        \\ fs[op_space_req_def]
        \\ first_assum(mp_tac o MATCH_MP(REWRITE_RULE[GSYM AND_IMP_INTRO]evaluate_locals))
        \\ disch_then drule
        \\ simp[]
        \\ qpat_abbrev_tac`ll = insert n _ (inter _ _)`
        \\ disch_then(qspec_then`ll`mp_tac)
        \\ impl_tac THEN1
          (UNABBREV_ALL_TAC \\ fs[]
           \\ fs[dataSemTheory.state_component_equality]
           \\ SRW_TAC [] []
           \\ fs[locals_ok_def,lookup_insert,lookup_inter_alt]
           \\ fs[domain_delete,domain_list_insert])
        \\ strip_tac \\ simp[]
        \\ drule_then (qspec_then `v4.safe_for_space` ASSUME_TAC) evaluate_safe_peak_swap
        \\ fs [state_fupdcanon]
        \\ qexists_tac`w`
        \\ qmatch_goalsub_rename_tac `evaluate_safe y2 ss`
        \\ qexists_tac `evaluate_safe y2 ss`
        \\ qexists_tac `evaluate_peak y2 ss`
        \\ fs[]
        \\ Cases_on`res` \\ fs[]
        \\ fs[locals_ok_def])
      \\ IF_CASES_TAC THEN1 fs []
      \\ REV_FULL_SIMP_TAC std_ss []
      \\ fs[consume_space_def]
      \\ `¬op_space_reset o'` by fs[dataLangTheory.op_requires_names_def] \\ fs[]
      \\ Cases_on `s.space < op_space_req o' (LENGTH l')`
      \\ fs[]
      (* \\ `s with space := s.space - op_space_req o' (LENGTH x) = s` *)
      (*    by (fs[] \\ NO_TAC) *)
      \\ fs[]
      \\ `~(op_space_req o' (LENGTH l') + y0 < op_space_req o' (LENGTH l'))`
            by DECIDE_TAC \\ fs[]
      \\ imp_res_tac get_vars_IMP_LENGTH \\ fs []
      \\ fs[]
      \\ fs [do_app_aux_with_locals,do_app_aux_with_space]
      \\ PairCases_on `y`
      \\ fs [] \\ rveq
      \\ fs [state_component_equality]
      \\ rveq \\ fs []
      \\ first_assum(mp_tac o MATCH_MP(REWRITE_RULE[GSYM AND_IMP_INTRO]evaluate_locals))
      \\ disch_then drule
      \\ fs []
      \\ drule_then (qspecl_then [`SAFE2`,`PEAK2`] (CHOOSE_THEN ASSUME_TAC)) do_app_aux_safe_peak_swap
      \\ ONCE_ASM_REWRITE_TAC []
      \\ fs []
      \\ qpat_abbrev_tac`l2 = insert n _ (inter _ _)`
      \\ disch_then(qspec_then`l2`mp_tac)
      \\ impl_tac  >-
          (UNABBREV_ALL_TAC
           \\ fs[locals_ok_def,lookup_insert,lookup_inter_alt]
           \\ fs[domain_delete,domain_list_insert])
      \\ strip_tac
      \\ simp[]
      \\ drule_then (qspecl_then [`safe''`,`peak''`] ASSUME_TAC) evaluate_safe_peak_swap
      \\ fs [state_fupdcanon]
      \\ qexists_tac `w`
      \\ qmatch_asmsub_abbrev_tac `evaluate_safe y2 ss`
      \\ qexists_tac `evaluate_safe y2 ss`
      \\ qexists_tac `evaluate_peak y2 ss`
      \\ Cases_on `res` \\ fs[]
      \\ fs [locals_ok_def])
    THEN1 (* Move *)
     (fs[pMakeSpace_def,space_def]
      \\ SIMP_TAC std_ss [Once evaluate_def,LET_DEF]
      \\ SIMP_TAC std_ss [Once evaluate_def,LET_DEF]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `l`) \\ fs[]
      \\ SIMP_TAC std_ss [Once evaluate_def,LET_DEF]
      \\ POP_ASSUM MP_TAC
      \\ SIMP_TAC std_ss [Once evaluate_def,LET_DEF]
      \\ REPEAT STRIP_TAC \\ Cases_on `get_var n0 s.locals` \\ fs[]
      \\ SRW_TAC [] []
      \\ IMP_RES_TAC locals_ok_get_var \\ fs[]
      \\ Q.PAT_X_ASSUM `!ww.bb==>bbb` (MP_TAC o Q.SPEC `insert n x w`) \\ fs[]
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
       (fs[dataSemTheory.state_component_equality] \\ SRW_TAC [] []
        \\ fs[locals_ok_def,set_var_def,lookup_insert])
      \\ fs[evaluate_def]
      \\ Cases_on `cut_env y1 (insert n x w)` \\ fs[LET_DEF]
      \\ REPEAT STRIP_TAC
      \\ fs[dataSemTheory.state_component_equality,
             add_space_def,set_var_def] \\ SRW_TAC [] []
      \\ `cut_env (insert n0 () (delete n y1)) l =
             SOME (insert n0 x (delete n x'))` by
       (fs[cut_env_def] \\ SRW_TAC [] [] \\ fs[]
        \\ fs[lookup_insert,lookup_inter_alt,lookup_delete]
        THEN1 (fs[get_var_def,domain_lookup])
        THEN1 (fs[SUBSET_DEF] \\ METIS_TAC [])
        \\ MATCH_MP_TAC IMP_sptree_eq \\ fs[wf_insert,wf_delete]
        \\ fs[lookup_insert,lookup_inter_alt,lookup_delete]
        \\ REPEAT STRIP_TAC
        \\ Cases_on `a = n0` THEN1 (fs[get_var_def]) \\ fs[]
        \\ SRW_TAC [] [] \\ fs[]) \\ fs[]
      \\ SIMP_TAC (srw_ss()) [get_var_def]
      \\ qpat_abbrev_tac `ll = insert n _ _`
      \\ qmatch_assum_abbrev_tac`evaluate (y2,s4) = _`
      \\ qmatch_goalsub_abbrev_tac `state_safe_for_space_fupd (K SAFE0) (state_peak_heap_length_fupd (K PEAK0) _)`
      \\ `s with <|locals := ll; space := y0; safe_for_space := SAFE0 ; peak_heap_length := PEAK0 |> =
          s4 with <| locals := ll; safe_for_space := SAFE0 ; peak_heap_length := PEAK0 |>`
         by (UNABBREV_ALL_TAC \\ fs[dataSemTheory.state_component_equality])
      \\ fs[]
      \\ `locals_ok s4.locals ll` by
       (UNABBREV_ALL_TAC \\ fs[dataSemTheory.state_component_equality,locals_ok_def]
        \\ fs[lookup_insert,lookup_delete,cut_env_def]
        \\ Q.PAT_X_ASSUM `xxx = x'` (fn th => fs[GSYM th])
        \\ fs[lookup_insert,lookup_inter_alt,lookup_delete]
        \\ REPEAT STRIP_TAC \\ Cases_on `v=n` \\ fs[]
        \\ Cases_on `v=n0` \\ fs[]
        \\ Q.PAT_X_ASSUM `inter xx tt = yy` MP_TAC
        \\ ONCE_REWRITE_TAC [mk_wf_inter]
        \\ SIMP_TAC std_ss [delete_mk_wf,insert_mk_wf]
        \\ SIMP_TAC std_ss [mk_wf_eq]
        \\ fs[lookup_insert,lookup_inter_alt,lookup_delete]
        \\ REPEAT STRIP_TAC
        \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `n0`) \\ fs[])
      \\ MP_TAC (Q.SPECL [`y2`,`s4`] evaluate_locals)
      \\ fs[] \\ REPEAT STRIP_TAC \\ RES_TAC \\ fs[]
      \\ drule_then (qspecl_then [`SAFE0`,`PEAK0`] ASSUME_TAC) evaluate_safe_peak_swap
      \\ fs [state_fupdcanon]
      \\ Cases_on `res` \\ fs[]
      \\ fs[dataSemTheory.state_component_equality] \\ SRW_TAC [] []
      \\ METIS_TAC [locals_ok_def])
    THEN1 (* Skip *)
     (fs[pMakeSpace_def,space_def]
      \\ SIMP_TAC std_ss [Once evaluate_def,LET_DEF]
      \\ POP_ASSUM (ASSUME_TAC o REWRITE_RULE [evaluate_def])
      \\ fs[] \\ SRW_TAC [] [] \\ POP_ASSUM (K ALL_TAC)
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `l`) \\ fs[]
      \\ SIMP_TAC std_ss [Once evaluate_def,LET_DEF]))
  THEN1 (* If *)
   (Cases_on `get_var n s.locals` \\ fs[]
    \\ IMP_RES_TAC locals_ok_get_var \\ fs[]
    \\ SRW_TAC [] [] \\ fs[])
  THEN1 (* Call *)
   (Cases_on `get_vars args s.locals` \\ fs[]
    \\ IMP_RES_TAC locals_ok_get_vars \\ fs[]
    \\ Cases_on `find_code dest x s.code` \\ fs[]
    \\ Cases_on `x'` \\ fs[]
    \\ Cases_on `ret` \\ fs[] THEN1
     (Cases_on `handler` \\ fs[]
      \\ `call_env q (dec_clock (s with locals := l)) =
          call_env q (dec_clock s)` by
         fs[dataSemTheory.state_component_equality,
             dec_clock_def,call_env_def] \\ fs[]
      \\ Cases_on `s.clock = 0` \\ fs[] \\ SRW_TAC [] []
      THEN1 (fs[ locals_ok_def,call_env_def,EVAL ``fromList []``
               , lookup_def, dec_clock_def]
            \\ Q.EXISTS_TAC `s.safe_for_space`
            \\ rw [state_component_equality])
      \\ MAP_EVERY Q.EXISTS_TAC [`s2.locals`,`s2.safe_for_space`,`s2.peak_heap_length`]
      \\ fs[locals_ok_refl]
      \\ SRW_TAC [] [dataSemTheory.state_component_equality])
    \\ Cases_on `x'` \\ fs[]
    \\ Cases_on `cut_env r' s.locals` \\ fs[]
    \\ IMP_RES_TAC locals_ok_cut_env \\ fs[]
    \\ `call_env q (push_env x' (IS_SOME handler)
          (dec_clock (s with locals := l))) =
        call_env q (push_env x' (IS_SOME handler)
          (dec_clock s))` by
     (Cases_on `handler`
      \\ fs[dataSemTheory.state_component_equality,
             dec_clock_def,call_env_def,push_env_def])
    \\ Cases_on `s.clock = 0` \\ fs[] \\ SRW_TAC [] []
    THEN1 (fs[ locals_ok_def,call_env_def,EVAL ``fromList []``
             , lookup_def, dec_clock_def]
          \\ Q.EXISTS_TAC `s.safe_for_space`
          \\ Q.EXISTS_TAC `s.peak_heap_length`
          \\ rw [state_component_equality])
    \\ fs[] \\ MAP_EVERY Q.EXISTS_TAC [`s2.locals`,`s2.safe_for_space`,`s2.peak_heap_length`]
    \\ rw [locals_ok_refl,with_same_locals,state_component_equality]));

Theorem compile_correct:
   !c s.
      FST (evaluate (c,s)) <> NONE /\
      FST (evaluate (c,s)) <> SOME (Rerr(Rabort Rtype_error)) ==>
      ∃safe peak. evaluate (compile c, s) = (I ## λs. s with <| safe_for_space := safe; peak_heap_length := peak |>)
                                               (evaluate (c,s))
Proof
  REPEAT STRIP_TAC \\ Cases_on `evaluate (c,s)` \\ fs[]
  \\ MP_TAC (Q.SPECL [`c`,`s`] evaluate_compile)
  \\ fs[] \\ REPEAT STRIP_TAC
  \\ POP_ASSUM (MP_TAC o Q.SPECL [`s.locals`])
  \\ fs[locals_ok_refl]
  \\ REPEAT STRIP_TAC \\ fs[with_same_locals]
  \\ METIS_TAC []
QED

Theorem get_code_labels_space:
   ∀x y y0 y1 y2.
   (space x = INL y ⇒ get_code_labels y = get_code_labels x) ∧
   (space x = INR (y0,y1,y2) ⇒ get_code_labels y2 = get_code_labels x)
Proof
  recInduct data_spaceTheory.space_ind
  \\ rw[data_spaceTheory.space_def] \\ simp[]
  \\ fs[CaseEq"sum",CaseEq"dataLang$prog"] \\ rveq \\ fs[data_spaceTheory.space_def]
  \\ fs[data_spaceTheory.pMakeSpace_def]
  \\ every_case_tac \\ fs[data_spaceTheory.pMakeSpace_def,CaseEq"option",data_spaceTheory.space_def]
  \\ rveq \\ fs[]
  \\ every_case_tac \\ fs[data_spaceTheory.pMakeSpace_def,CaseEq"option",data_spaceTheory.space_def]
  \\ Cases_on`space c2` \\ Cases_on`space c3` \\ fs[] \\ TRY(PairCases_on`y`)
  \\ fs[data_spaceTheory.pMakeSpace_def,CaseEq"option",data_spaceTheory.space_def]
  \\ PairCases_on`y'`
  \\ fs[data_spaceTheory.pMakeSpace_def,CaseEq"option",data_spaceTheory.space_def]
QED

Theorem get_code_labels_compile[simp]:
   ∀x. get_code_labels (data_space$compile x) = get_code_labels x
Proof
  rw[data_spaceTheory.compile_def]
  \\ Cases_on`space x`
  \\ simp[data_spaceTheory.pMakeSpace_def]
  \\ TRY (PairCases_on`y`)
  \\ simp[data_spaceTheory.pMakeSpace_def]
  \\ imp_res_tac get_code_labels_space
QED

val _ = export_theory();
