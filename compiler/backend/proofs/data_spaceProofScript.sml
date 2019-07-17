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
     ?w. (evaluate (compile c, s with locals := l) =
            (res,if res = NONE then s2 with locals := w
                               else s2)) /\
         locals_ok s2.locals w`,
  SIMP_TAC std_ss [compile_def]
  \\ recInduct evaluate_ind \\ REPEAT STRIP_TAC
  \\ full_simp_tac(srw_ss())[evaluate_def,space_def,pMakeSpace_def]
  THEN1 (* Skip *)
   (full_simp_tac(srw_ss())[evaluate_def] \\ METIS_TAC [])
  THEN1 (* Move *)
   (Cases_on `get_var src s.locals` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[get_var_def,lookup_union,set_var_def,locals_ok_def]
    \\ RES_TAC \\ full_simp_tac(srw_ss())[]
    \\ Q.EXISTS_TAC `insert dest x l` \\ full_simp_tac(srw_ss())[lookup_insert]
    \\ METIS_TAC [])
  THEN1 (* Assign *)
   (BasicProvers.TOP_CASE_TAC \\ fs[cut_state_opt_def]
    \\ BasicProvers.CASE_TAC \\ fs[]
    THEN1 (Cases_on `get_vars args s.locals`
      \\ full_simp_tac(srw_ss())[cut_state_opt_def]
      \\ `get_vars args l =
          get_vars args s.locals` by
       (MATCH_MP_TAC EVERY_get_vars
        \\ full_simp_tac(srw_ss())[EVERY_MEM,locals_ok_def]
        \\ REPEAT STRIP_TAC \\ IMP_RES_TAC get_vars_IMP_domain
        \\ full_simp_tac(srw_ss())[domain_lookup])
      \\ full_simp_tac(srw_ss())[] \\ reverse(Cases_on `do_app op x s`)
      \\ full_simp_tac(srw_ss())[] >- (
           imp_res_tac do_app_err >> full_simp_tac(srw_ss())[] >>
           fs [EVAL ``op_requires_names (FFI i)``])
      \\ Cases_on `a` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
      \\ IMP_RES_TAC do_app_locals \\ full_simp_tac(srw_ss())[set_var_def]
      \\ Q.EXISTS_TAC `insert dest q l`
      \\ full_simp_tac(srw_ss())[set_var_def,locals_ok_def,lookup_insert]
      \\ METIS_TAC [do_app_const])
    \\ `cut_state x (s with locals := l) = cut_state x s` by
     (full_simp_tac(srw_ss())[cut_state_def]
      \\ Cases_on `cut_env x s.locals` \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC locals_ok_cut_env \\ full_simp_tac(srw_ss())[] \\ NO_TAC)
    \\ full_simp_tac(srw_ss())[] \\ POP_ASSUM (K ALL_TAC)
    \\ full_simp_tac(srw_ss())[cut_state_def,cut_env_def]
    \\ Cases_on `domain x SUBSET domain s.locals` \\ full_simp_tac(srw_ss())[]
    \\ Q.EXISTS_TAC `s2.locals` \\ full_simp_tac(srw_ss())[locals_ok_def]
    \\ SRW_TAC [] [state_component_equality])
  THEN1 (* Tick *)
   (Cases_on `s.clock = 0` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[locals_ok_def,call_env_def,
         EVAL ``fromList []``,lookup_def,dec_clock_def] \\ METIS_TAC [])
  THEN1 (* MakeSpace *)
   (Cases_on `cut_env names s.locals` \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC locals_ok_cut_env
    \\ full_simp_tac(srw_ss())[LET_DEF,add_space_def,
         state_component_equality,locals_ok_def])
  THEN1 (* Raise *)
   (Cases_on `get_var n s.locals` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ `jump_exc (s with locals := l) = jump_exc s` by
         full_simp_tac(srw_ss())[jump_exc_def]
    \\ Cases_on `jump_exc s` \\ full_simp_tac(srw_ss())[]
    \\ `get_var n l = SOME x` by
         full_simp_tac(srw_ss())[locals_ok_def,get_var_def]
    \\ full_simp_tac(srw_ss())[]
    \\ srw_tac [] [] \\ Q.EXISTS_TAC `s2.locals`
    \\ full_simp_tac(srw_ss())[locals_ok_def])
  THEN1 (* Return *)
   (Cases_on `get_var n s.locals` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ `get_var n l = SOME x` by
         full_simp_tac(srw_ss())[locals_ok_def,get_var_def]
    \\ full_simp_tac(srw_ss())[]
    \\ srw_tac [] [call_env_def]
    \\ full_simp_tac(srw_ss())[locals_ok_def,call_env_def,lookup_fromList,
           dec_clock_def])
  THEN1 (* Seq *)
   (full_simp_tac(srw_ss())[LET_DEF] \\ Cases_on `space c2`
    \\ full_simp_tac(srw_ss())[] THEN1
     (Cases_on `evaluate (c1,s)` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `c1` \\ full_simp_tac(srw_ss())[pMakeSpace_def]
      THEN1 (full_simp_tac(srw_ss())[evaluate_def])
      \\ Cases_on `q = SOME (Rerr(Rabort Rtype_error))`
      \\ full_simp_tac(srw_ss())[]
      \\ SIMP_TAC std_ss [Once evaluate_def]
      \\ full_simp_tac(srw_ss())[space_def,pMakeSpace_def]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `l`)
      \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
      \\ full_simp_tac(srw_ss())[LET_DEF,Seq_Skip]
      \\ Cases_on `q` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
      \\ Q.EXISTS_TAC `w` \\ full_simp_tac(srw_ss())[])
    \\ PairCases_on `y` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `evaluate (c1,s)` \\ full_simp_tac(srw_ss())[]
    \\ reverse (Cases_on `c1`) \\ full_simp_tac(srw_ss())[]
    \\ TRY (full_simp_tac(srw_ss())[pMakeSpace_def,space_def]
      \\ SIMP_TAC std_ss [Once evaluate_def,LET_DEF]
      \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `l`) \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `q = SOME (Rerr(Rabort Rtype_error))`
      \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
      \\ full_simp_tac(srw_ss())[] \\ Cases_on `q`
      \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
      \\ Q.EXISTS_TAC `w` \\ full_simp_tac(srw_ss())[] \\ NO_TAC)
    THEN1 (* MakeSpace *)
     (full_simp_tac(srw_ss())[pMakeSpace_def,space_def,Seq_Skip]
      \\ Cases_on `q = SOME (Rerr(Rabort Rtype_error))` \\ full_simp_tac(srw_ss())[]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `l`) \\ full_simp_tac(srw_ss())[]
      \\ SIMP_TAC std_ss [Once evaluate_def] \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `cut_env s' l` \\ full_simp_tac(srw_ss())[]
      \\ REPEAT STRIP_TAC \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `w`) \\ full_simp_tac(srw_ss())[]
      \\ ONCE_REWRITE_TAC [evaluate_def] \\ full_simp_tac(srw_ss())[LET_DEF]
      \\ full_simp_tac(srw_ss())[evaluate_def]
      \\ Cases_on `cut_env y1 w` \\ full_simp_tac(srw_ss())[]
      \\ REPEAT STRIP_TAC
      \\ `cut_env (inter s' y1) l = SOME x'` by
       (full_simp_tac(srw_ss())[cut_env_def] \\ SRW_TAC [] []
        \\ full_simp_tac(srw_ss())[state_component_equality,add_space_def]
        \\ SRW_TAC [] []
        \\ full_simp_tac(srw_ss())[SUBSET_DEF,domain_inter,lookup_inter_alt]
        \\ Cases_on `x IN domain y1` \\ full_simp_tac(srw_ss())[])
        \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[]
      \\ `(add_space (s with locals := l) y0 with locals := x') =
          (add_space (r with locals := w) y0 with locals := x')` by
       (full_simp_tac(srw_ss())[state_component_equality,add_space_def]
        \\ SRW_TAC [] [] \\ DECIDE_TAC)
      \\ full_simp_tac(srw_ss())[] \\ METIS_TAC [])
    THEN1 (* Seq *)
     (full_simp_tac(srw_ss())[pMakeSpace_def]
      \\ SIMP_TAC std_ss [Once evaluate_def,LET_DEF]
      \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `l`) \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `q = SOME (Rerr(Rabort Rtype_error))`
      \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
      \\ full_simp_tac(srw_ss())[] \\ Cases_on `q`
      \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] [] \\ METIS_TAC [])
    THEN1 (* Assign *)
     (full_simp_tac(srw_ss())[pMakeSpace_def,space_def] \\ reverse (Cases_on `o0`)
      \\ full_simp_tac(srw_ss())[evaluate_def,cut_state_opt_def] THEN1
       (full_simp_tac(srw_ss())[pMakeSpace_def,space_def,evaluate_def,
            cut_state_opt_def,cut_state_def]
        \\ Cases_on `cut_env x s.locals`
        \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
        \\ IMP_RES_TAC locals_ok_cut_env \\ full_simp_tac(srw_ss())[]
        \\ Cases_on `get_vars l' x'` \\ full_simp_tac(srw_ss())[]
        \\ SRW_TAC [] []
        \\ reverse(Cases_on `do_app o' x'' (s with locals := x')`)
        \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] [] >- (
             imp_res_tac do_app_err >> full_simp_tac(srw_ss())[] >>
             full_simp_tac(srw_ss())[]>>srw_tac[][]
             \\ fs [call_env_def] \\ qexists_tac `fromList []` \\ fs [locals_ok_def])
        \\ Cases_on `a` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
        \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `l`) \\ full_simp_tac(srw_ss())[]
        \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
        \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC
             `(set_var n q' r').locals`) \\ full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[locals_ok_refl] \\ REPEAT STRIP_TAC
        \\ Cases_on `cut_env y1 (set_var n q' r').locals` \\ full_simp_tac(srw_ss())[LET_DEF]
        \\ Q.EXISTS_TAC `w'` \\ full_simp_tac(srw_ss())[]
        \\ Q.PAT_X_ASSUM `evaluate xxx = yyy` (fn th => SIMP_TAC std_ss [GSYM th])
        \\ AP_TERM_TAC \\ AP_TERM_TAC
        \\ full_simp_tac(srw_ss())[state_component_equality,add_space_def])
      \\ Cases_on `op_requires_names o'` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
      \\ Cases_on `get_vars l' s.locals` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `l`) \\ full_simp_tac(srw_ss())[]
      \\ impl_tac >- (rpt strip_tac >> full_simp_tac(srw_ss())[])
      \\ rpt strip_tac
      \\ full_simp_tac(srw_ss())[pMakeSpace_def,space_def]
      \\ full_simp_tac(srw_ss())[evaluate_def,cut_state_opt_def]
      \\ IMP_RES_TAC locals_ok_get_vars \\ full_simp_tac(srw_ss())[]
      \\ reverse (Cases_on `do_app o' x s`) \\ full_simp_tac(srw_ss())[] THEN1
       (IMP_RES_TAC do_app_err \\ full_simp_tac(srw_ss())[]
        \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
        \\ fs [EVAL ``¬op_requires_names (FFI i)``])
      \\ Cases_on `a`
      \\ IMP_RES_TAC do_app_locals \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
      \\ NTAC 2 (Q.PAT_X_ASSUM `!xx.bbb` (K ALL_TAC))
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `w`) \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `cut_env y1 w`
      \\ full_simp_tac(srw_ss())[LET_DEF,add_space_def,set_var_def]
      \\ POP_ASSUM MP_TAC
      \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[Once cut_env_def]
      \\ REPEAT STRIP_TAC
      \\ `domain (list_insert l' (delete n y1)) SUBSET domain l` by
       (full_simp_tac(srw_ss())[dataSemTheory.state_component_equality]
        \\ SRW_TAC [] []
        \\ IMP_RES_TAC locals_ok_IMP
        \\ IMP_RES_TAC get_vars_IMP_domain \\ full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[domain_list_insert,SUBSET_DEF]
        \\ REPEAT STRIP_TAC \\ RES_TAC \\ NO_TAC)
      \\ full_simp_tac(srw_ss())[]
      \\ `get_vars l' (inter l (list_insert l' (delete n y1))) = get_vars l' l`
           by (MATCH_MP_TAC EVERY_get_vars
               \\ full_simp_tac(srw_ss())[EVERY_MEM,lookup_inter_alt,
                     domain_list_insert] \\ NO_TAC)
      \\ full_simp_tac(srw_ss())[do_app_def,do_space_alt]
      \\ IF_CASES_TAC >- (
        fs[do_install_def,case_eq_thms]
        \\ pairarg_tac \\ fs[]
        \\ fs[case_eq_thms] \\ rveq
        \\ fs[state_component_equality] \\ rveq
        \\ fs[op_space_req_def]
        \\ first_assum(mp_tac o MATCH_MP(REWRITE_RULE[GSYM AND_IMP_INTRO]evaluate_locals))
        \\ disch_then drule
        \\ simp[]
        \\ qpat_abbrev_tac`ll = insert n _ (inter _ _)`
        \\ disch_then(qspec_then`ll`mp_tac)
        \\ impl_tac THEN1
          (UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[]
           \\ full_simp_tac(srw_ss())[dataSemTheory.state_component_equality]
           \\ SRW_TAC [] []
           \\ full_simp_tac(srw_ss())[locals_ok_def,lookup_insert,lookup_inter_alt]
           \\ full_simp_tac(srw_ss())[domain_delete,domain_list_insert])
        \\ strip_tac \\ simp[]
        \\ qexists_tac`w` \\ fs[]
        \\ Cases_on`res` \\ fs[]
        \\ fs[locals_ok_def])
      \\ IF_CASES_TAC THEN1 fs []
      \\ REV_FULL_SIMP_TAC std_ss []
      \\ full_simp_tac(srw_ss())[consume_space_def]
      \\ `¬op_space_reset o'` by fs[dataLangTheory.op_requires_names_def] \\ fs[]
      \\ Cases_on `s.space < op_space_req o' (LENGTH l')`
      \\ full_simp_tac(srw_ss())[]
      (* \\ `s with space := s.space - op_space_req o' (LENGTH x) = s` *)
      (*    by (full_simp_tac(srw_ss())[] \\ NO_TAC) *)
      \\ full_simp_tac(srw_ss())[]
      \\ `~(op_space_req o' (LENGTH l') + y0 < op_space_req o' (LENGTH l'))`
            by DECIDE_TAC \\ full_simp_tac(srw_ss())[]
      \\ imp_res_tac get_vars_IMP_LENGTH \\ fs []
      \\ full_simp_tac(srw_ss())[]
      \\ fs [do_app_aux_with_locals,do_app_aux_with_space]
      \\ PairCases_on `y`
      \\ fs [] \\ rveq
      \\ fs [state_component_equality]
      \\ rveq \\ fs []
      \\ first_assum(mp_tac o MATCH_MP(REWRITE_RULE[GSYM AND_IMP_INTRO]evaluate_locals))
      \\ disch_then drule
      \\ fs []
      \\ qpat_abbrev_tac`l2 = insert n _ (inter _ _)`
      \\ disch_then(qspec_then`l2`mp_tac)
      \\ impl_tac  >-
          (UNABBREV_ALL_TAC
           \\ full_simp_tac(srw_ss())[locals_ok_def,lookup_insert,lookup_inter_alt]
           \\ full_simp_tac(srw_ss())[domain_delete,domain_list_insert])
      \\ strip_tac
      \\ simp[]
      \\ Cases_on `res` \\ full_simp_tac(srw_ss())[]
      \\ fs [state_component_equality]
      \\ METIS_TAC [locals_ok_def])
    THEN1 (* Move *)
     (full_simp_tac(srw_ss())[pMakeSpace_def,space_def]
      \\ SIMP_TAC std_ss [Once evaluate_def,LET_DEF]
      \\ SIMP_TAC std_ss [Once evaluate_def,LET_DEF]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `l`) \\ full_simp_tac(srw_ss())[]
      \\ SIMP_TAC std_ss [Once evaluate_def,LET_DEF]
      \\ POP_ASSUM MP_TAC
      \\ SIMP_TAC std_ss [Once evaluate_def,LET_DEF]
      \\ REPEAT STRIP_TAC \\ Cases_on `get_var n0 s.locals` \\ full_simp_tac(srw_ss())[]
      \\ SRW_TAC [] []
      \\ IMP_RES_TAC locals_ok_get_var \\ full_simp_tac(srw_ss())[]
      \\ Q.PAT_X_ASSUM `!ww.bb==>bbb` (MP_TAC o Q.SPEC `insert n x w`) \\ full_simp_tac(srw_ss())[]
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
       (full_simp_tac(srw_ss())[dataSemTheory.state_component_equality] \\ SRW_TAC [] []
        \\ full_simp_tac(srw_ss())[locals_ok_def,set_var_def,lookup_insert])
      \\ full_simp_tac(srw_ss())[evaluate_def]
      \\ Cases_on `cut_env y1 (insert n x w)` \\ full_simp_tac(srw_ss())[LET_DEF]
      \\ REPEAT STRIP_TAC
      \\ full_simp_tac(srw_ss())[dataSemTheory.state_component_equality,
             add_space_def,set_var_def] \\ SRW_TAC [] []
      \\ `cut_env (insert n0 () (delete n y1)) l =
             SOME (insert n0 x (delete n x'))` by
       (full_simp_tac(srw_ss())[cut_env_def] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[lookup_insert,lookup_inter_alt,lookup_delete]
        THEN1 (full_simp_tac(srw_ss())[get_var_def,domain_lookup])
        THEN1 (full_simp_tac(srw_ss())[SUBSET_DEF] \\ METIS_TAC [])
        \\ MATCH_MP_TAC IMP_sptree_eq \\ full_simp_tac(srw_ss())[wf_insert,wf_delete]
        \\ full_simp_tac(srw_ss())[lookup_insert,lookup_inter_alt,lookup_delete]
        \\ REPEAT STRIP_TAC
        \\ Cases_on `a = n0` THEN1 (full_simp_tac(srw_ss())[get_var_def]) \\ full_simp_tac(srw_ss())[]
        \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]) \\ full_simp_tac(srw_ss())[]
      \\ SIMP_TAC (srw_ss()) [get_var_def]
      \\ qpat_abbrev_tac `ll = insert n _ _`
      \\ qmatch_assum_abbrev_tac`evaluate (y2,s4) = _`
      \\ `s with <|locals := ll; space := y0|> =
          s4 with locals := ll` by (UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[dataSemTheory.state_component_equality]) \\ full_simp_tac(srw_ss())[]
      \\ `locals_ok s4.locals ll` by
       (UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[dataSemTheory.state_component_equality,locals_ok_def]
        \\ full_simp_tac(srw_ss())[lookup_insert,lookup_delete,cut_env_def]
        \\ Q.PAT_X_ASSUM `xxx = x'` (fn th => full_simp_tac(srw_ss())[GSYM th])
        \\ full_simp_tac(srw_ss())[lookup_insert,lookup_inter_alt,lookup_delete]
        \\ REPEAT STRIP_TAC \\ Cases_on `v=n` \\ full_simp_tac(srw_ss())[]
        \\ Cases_on `v=n0` \\ full_simp_tac(srw_ss())[]
        \\ Q.PAT_X_ASSUM `inter xx tt = yy` MP_TAC
        \\ ONCE_REWRITE_TAC [mk_wf_inter]
        \\ SIMP_TAC std_ss [delete_mk_wf,insert_mk_wf]
        \\ SIMP_TAC std_ss [mk_wf_eq]
        \\ full_simp_tac(srw_ss())[lookup_insert,lookup_inter_alt,lookup_delete]
        \\ REPEAT STRIP_TAC
        \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `n0`) \\ full_simp_tac(srw_ss())[])
      \\ MP_TAC (Q.SPECL [`y2`,`s4`] evaluate_locals)
      \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC \\ RES_TAC \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `res` \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[dataSemTheory.state_component_equality] \\ SRW_TAC [] []
      \\ METIS_TAC [locals_ok_def])
    THEN1 (* Skip *)
     (full_simp_tac(srw_ss())[pMakeSpace_def,space_def]
      \\ SIMP_TAC std_ss [Once evaluate_def,LET_DEF]
      \\ POP_ASSUM (ASSUME_TAC o REWRITE_RULE [evaluate_def])
      \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] [] \\ POP_ASSUM (K ALL_TAC)
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `l`) \\ full_simp_tac(srw_ss())[]
      \\ SIMP_TAC std_ss [Once evaluate_def,LET_DEF]))
  THEN1 (* If *)
   (Cases_on `get_var n s.locals` \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC locals_ok_get_var \\ full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
  THEN1 (* Call *)
   (Cases_on `get_vars args s.locals` \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC locals_ok_get_vars \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `find_code dest x s.code` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `x'` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `ret` \\ full_simp_tac(srw_ss())[] THEN1
     (Cases_on `handler` \\ full_simp_tac(srw_ss())[]
      \\ `call_env q (dec_clock (s with locals := l)) =
          call_env q (dec_clock s)` by
         full_simp_tac(srw_ss())[dataSemTheory.state_component_equality,
             dec_clock_def,call_env_def] \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `s.clock = 0` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
      THEN1 (full_simp_tac(srw_ss())[locals_ok_def,call_env_def,EVAL ``fromList []``,lookup_def,
             dec_clock_def] \\ METIS_TAC [])
      \\ Q.EXISTS_TAC `s2.locals` \\ full_simp_tac(srw_ss())[locals_ok_refl]
      \\ SRW_TAC [] [dataSemTheory.state_component_equality])
    \\ Cases_on `x'` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `cut_env r' s.locals` \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC locals_ok_cut_env \\ full_simp_tac(srw_ss())[]
    \\ `call_env q (push_env x' (IS_SOME handler)
          (dec_clock (s with locals := l))) =
        call_env q (push_env x' (IS_SOME handler)
          (dec_clock s))` by
     (Cases_on `handler`
      \\ full_simp_tac(srw_ss())[dataSemTheory.state_component_equality,
             dec_clock_def,call_env_def,push_env_def])
    \\ Cases_on `s.clock = 0` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    THEN1 (full_simp_tac(srw_ss())[locals_ok_def,call_env_def,EVAL ``fromList []``,lookup_def,
           dec_clock_def] \\ METIS_TAC [])
    \\ full_simp_tac(srw_ss())[] \\ METIS_TAC [locals_ok_refl,with_same_locals]));

Theorem compile_correct:
   !c s.
      FST (evaluate (c,s)) <> NONE /\
      FST (evaluate (c,s)) <> SOME (Rerr(Rabort Rtype_error)) ==>
      (evaluate (compile c, s) = evaluate (c,s))
Proof
  REPEAT STRIP_TAC \\ Cases_on `evaluate (c,s)` \\ full_simp_tac(srw_ss())[]
  \\ MP_TAC (Q.SPECL [`c`,`s`] evaluate_compile)
  \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
  \\ POP_ASSUM (MP_TAC o Q.SPECL [`s.locals`])
  \\ full_simp_tac(srw_ss())[locals_ok_refl]
  \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[with_same_locals]
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
