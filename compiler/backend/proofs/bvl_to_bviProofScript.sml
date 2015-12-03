open preamble
     bvlSemTheory bvlPropsTheory
     bvl_to_bviTheory
     bviSemTheory bviPropsTheory;
local open
  bvl_constProofTheory
  bvl_handleProofTheory
in end;

val _ = new_theory"bvl_to_bviProof";

(* value relation *)

val adjust_bv_def = tDefine "adjust_bv" `
  (adjust_bv b (Number i) = Number i) /\
  (adjust_bv b (RefPtr r) = RefPtr (b r)) /\
  (adjust_bv b (CodePtr c) = CodePtr (num_stubs + 2 * c)) /\
  (adjust_bv b (Block tag vs) = Block tag (MAP (adjust_bv b) vs))`
  (WF_REL_TAC `measure (v_size o SND)`
   \\ Induct_on `vs` \\ fs [] \\ SRW_TAC [] [v_size_def]
   \\ RES_TAC \\ FIRST_X_ASSUM (ASSUME_TAC o SPEC_ALL) \\ DECIDE_TAC)

val adjust_bv_ind = theorem"adjust_bv_ind";

val adjust_bv_Unit = Q.store_thm("adjust_bv_Unit[simp]",
  `adjust_bv x Unit = Unit`,
  EVAL_TAC);

val adjust_bv_Boolv = store_thm("adjust_bv_Boolv[simp]",
  ``adjust_bv x (Boolv b) = Boolv b``,
  Cases_on`b`>>EVAL_TAC)

val aux_code_installed_def = Define `
  (aux_code_installed [] t <=> T) /\
  (aux_code_installed ((name,arg_count,body)::rest) t <=>
     (sptree$lookup (num_stubs + 2 * name + 1) t = SOME (arg_count,body)) /\
     aux_code_installed rest t)`

val aux_code_installed_APPEND = prove(
  ``!xs ys.
      aux_code_installed (xs++ys) code ==>
      aux_code_installed xs code /\
      aux_code_installed ys code``,
  Induct \\ fs [APPEND,aux_code_installed_def,FORALL_PROD] \\ METIS_TAC []);

val state_rel_def = Define `
  state_rel (b:num->num) (s:'ffi bvlSem$state) (t:'ffi bviSem$state) <=>
    INJ b (FDOM s.refs) (FDOM t.refs) /\
    (!k. case FLOOKUP s.refs k of
         | NONE => T
         | SOME (ValueArray vs) =>
             (FLOOKUP t.refs (b k) = SOME (ValueArray (MAP (adjust_bv b) vs)))
         | SOME res => (FLOOKUP t.refs (b k) = SOME res)) /\
    (s.ffi = t.ffi) /\
    (∀p. t.global = SOME p ⇒
           p ∉ IMAGE b (FDOM s.refs) ∧
           ∃z. FLOOKUP t.refs p =
                 SOME (ValueArray ((Number(&(SUC(LENGTH s.globals))))::
                                   (MAP (the (Number 0) o OPTION_MAP (adjust_bv b)) s.globals ++
                                    REPLICATE (z - (SUC(LENGTH s.globals))) (Number 0)))) ∧
               SUC(LENGTH s.globals) ≤ z) ∧
    (s.clock = t.clock) /\
    (lookup AllocGlobal_location t.code = SOME AllocGlobal_code) ∧
    (lookup CopyGlobals_location t.code = SOME CopyGlobals_code) ∧
    (* (lookup InitGlobals_location t.code = SOME InitGlobals_code start) ∧ *)
    (!name arity exp.
       (lookup name s.code = SOME (arity,exp)) ==>
       ?n. let (c1,aux1,n1) = compile_exps n [exp] in
             (lookup (num_stubs + 2 * name) t.code = SOME (arity,HD c1)) /\
             aux_code_installed aux1 t.code /\
             bEvery GoodHandleLet [exp])`;

val bv_ok_def = tDefine "bv_ok" `
  (bv_ok refs (RefPtr r) <=> r IN FDOM refs) /\
  (bv_ok refs (Block tag vs) <=> EVERY (bv_ok refs) vs) /\
  (bv_ok refs _ <=> T)`
  (WF_REL_TAC `measure (v_size o SND)`
   \\ Induct_on `vs` \\ fs [] \\ SRW_TAC [] [v_size_def]
   \\ RES_TAC \\ FIRST_X_ASSUM (ASSUME_TAC o SPEC_ALL) \\ DECIDE_TAC)

val bv_ok_ind = theorem"bv_ok_ind";

val bv_ok_SUBSET_IMP = prove(
  ``!refs x refs2.
      bv_ok refs x /\ FDOM refs SUBSET FDOM refs2 ==> bv_ok refs2 x``,
  HO_MATCH_MP_TAC bv_ok_ind \\ fs [bv_ok_def]
  \\ fs [SUBSET_DEF,EVERY_MEM]);

val bv_ok_Unit = Q.store_thm("bv_ok_Unit[simp]",
  `bv_ok refs Unit`,
  EVAL_TAC)

val bv_ok_Boolv = Q.store_thm("bv_ok_Boolv[simp]",
  `bv_ok refs (Boolv b)`,
  EVAL_TAC)

val bv_ok_IMP_adjust_bv_eq = prove(
  ``!b2 a1 b3.
      bv_ok (s5:'ffi bvlSem$state).refs a1 /\
      (!a. a IN FDOM s5.refs ==> b2 a = b3 a) ==>
      (adjust_bv b2 a1 = adjust_bv b3 a1)``,
  HO_MATCH_MP_TAC adjust_bv_ind
  \\ REPEAT STRIP_TAC \\ fs [adjust_bv_def,bv_ok_def]
  \\ fs [MAP_EQ_f,EVERY_MEM]);

val state_ok_def = Define `
  state_ok (s:'ffi bvlSem$state) <=>
    EVERY (\x. case x of NONE => T | SOME v => bv_ok s.refs v) s.globals /\
    !k. case FLOOKUP s.refs k of
        | SOME (ValueArray vs) => EVERY (bv_ok s.refs) vs
        | _ => T`;

(* evaluate preserves state_ok *)

val evaluate_ok_lemma = prove(
  ``(state_ok (dec_clock n s) = state_ok s) /\
    ((dec_clock n s).refs = s.refs)``,
  fs [state_ok_def,bvlSemTheory.dec_clock_def]);

val evaluate_IMP_bv_ok = prove(
  ``(bvlSem$evaluate (xs,env,s) = (res,t)) ==>
    (bv_ok s.refs a1 ==> bv_ok t.refs a1) /\
    (EVERY (bv_ok s.refs) as ==> EVERY (bv_ok t.refs) as)``,
  REPEAT STRIP_TAC \\ fs [EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ IMP_RES_TAC evaluate_refs_SUBSET \\ IMP_RES_TAC bv_ok_SUBSET_IMP);

val v_to_list_ok = Q.prove(
  `∀v x. v_to_list v = SOME x ∧
         bv_ok refs v ⇒
         EVERY (bv_ok refs) x`,
  ho_match_mp_tac v_to_list_ind >>
  simp[v_to_list_def,bv_ok_def] >> rw[] >>
  every_case_tac >> fs[] >> rw[])

val do_app_ok_lemma = prove(
  ``state_ok r /\ EVERY (bv_ok r.refs) a /\
    (do_app op a r = Rval (q,t)) ==>
    state_ok t /\ bv_ok t.refs q``,
  Cases_on `op` \\ fs [bvlSemTheory.do_app_def] \\ BasicProvers.EVERY_CASE_TAC
  \\ TRY (fs [] \\ SRW_TAC [] [bv_ok_def]
    \\ fs [closSemTheory.get_global_def]
    \\ fs [state_ok_def,bv_ok_def] \\ NO_TAC)
  \\ TRY (SRW_TAC [] [] \\ fs [bv_ok_def,EVERY_EL] \\ NO_TAC)
  \\ TRY (SRW_TAC [] [] \\ fs [bv_ok_def,EVERY_MEM] \\ NO_TAC)
  \\ STRIP_TAC \\ fs [LET_THM] \\ rpt BasicProvers.VAR_EQ_TAC THEN1
   (fs [closSemTheory.get_global_def,state_ok_def,EVERY_EL]
    \\ RES_TAC \\ fs [] \\ REPEAT (Q.PAT_ASSUM `!x.bb` (K ALL_TAC))
    \\ REV_FULL_SIMP_TAC std_ss [])
  THEN1
   (SRW_TAC [] [bv_ok_def] \\ fs [LET_DEF,state_ok_def]
    \\ MATCH_MP_TAC IMP_EVERY_LUPDATE \\ fs [])
  THEN1
   (rw[bv_ok_def] \\ fs [state_ok_def] >>
    rw[FLOOKUP_UPDATE] >> fs[EVERY_MEM] >> rw[] >>
    BasicProvers.CASE_TAC >> TRY BasicProvers.CASE_TAC >> rw[] >>
    Q.ISPEC_THEN`r.refs`match_mp_tac bv_ok_SUBSET_IMP >>
    first_x_assum(qspec_then`k`strip_assume_tac)>>rfs[]>>
    simp[] >> res_tac >> fs[] >>
    simp[SUBSET_DEF])
  THEN1
   (rw[bv_ok_def] \\ fs [state_ok_def] >>
    rw[FLOOKUP_UPDATE] >> fs[EVERY_MEM] >> rw[] >>
    rpt BasicProvers.CASE_TAC >> rw[] >>
    Q.ISPEC_THEN`r.refs`match_mp_tac bv_ok_SUBSET_IMP >>
    first_x_assum(qspec_then`k`strip_assume_tac)>>rfs[]>>
    simp[] >> res_tac >> fs[rich_listTheory.REPLICATE_GENLIST,MEM_GENLIST] >>
    simp[SUBSET_DEF])
  THEN1
   (rw[bv_ok_def] \\ fs [state_ok_def] >>
    rw[FLOOKUP_UPDATE] >> fs[EVERY_MEM] >> rw[] >>
    every_case_tac >> rw[] >>
    Q.ISPEC_THEN`r.refs`match_mp_tac bv_ok_SUBSET_IMP >>
    first_x_assum(qspec_then`k`strip_assume_tac)>>rfs[]>>
    simp[] >> res_tac >> fs[] >>
    simp[SUBSET_DEF])
  THEN1 (
    simp[bv_ok_def] >>
    imp_res_tac v_to_list_ok >>
    fs[EVERY_MEM])
  THEN1
   (fs [LET_DEF,state_ok_def]
    \\ SRW_TAC [] [bv_ok_def,FLOOKUP_DEF,EVERY_MEM]
    \\ BasicProvers.EVERY_CASE_TAC
    \\ fs [EVERY_MEM] \\ RES_TAC \\ fs []
    \\ REPEAT STRIP_TAC \\ RES_TAC
    THEN1 (bv_ok_SUBSET_IMP |> Q.ISPEC_THEN `r.refs`MATCH_MP_TAC
           \\ fs [] \\ fs [SUBSET_DEF,FLOOKUP_DEF])
    THEN1 (bv_ok_SUBSET_IMP |> Q.ISPEC_THEN `r.refs`MATCH_MP_TAC
           \\ fs [] \\ fs [SUBSET_DEF,FLOOKUP_DEF])
    \\ Q.PAT_ASSUM `xx = ValueArray l` MP_TAC
    \\ SRW_TAC [] [FAPPLY_FUPDATE_THM] \\ RES_TAC
    THEN1 (bv_ok_SUBSET_IMP |> Q.ISPEC_THEN `r.refs`MATCH_MP_TAC
           \\ fs [] \\ fs [SUBSET_DEF,FLOOKUP_DEF])
    \\ Q.PAT_ASSUM `!k:num. bbb` (MP_TAC o Q.SPEC `k`)
    \\ fs [FLOOKUP_DEF] \\ REPEAT STRIP_TAC
    THEN1 (bv_ok_SUBSET_IMP |> Q.ISPEC_THEN `r.refs`MATCH_MP_TAC
           \\ fs [] \\ fs [SUBSET_DEF,FLOOKUP_DEF]))
  THEN1
   (fs [state_ok_def]
    \\ Q.PAT_ASSUM `!k:num. bbb` (MP_TAC o Q.SPEC `n`) \\ fs []
    \\ fs [EVERY_EL] \\ REPEAT STRIP_TAC \\ RES_TAC
    \\ SRW_TAC [] [] \\ Cases_on `i` \\ fs [])
  THEN1
   (fs [state_ok_def] \\ SRW_TAC [] [] THEN1
     (fs [EVERY_MEM] \\ REPEAT STRIP_TAC
      \\ BasicProvers.EVERY_CASE_TAC
      \\ RES_TAC \\ fs []
      \\ Q.ISPEC_THEN`r.refs`match_mp_tac bv_ok_SUBSET_IMP
      \\ fs [] \\ fs [SUBSET_DEF,FLOOKUP_DEF])
    THEN1
     (fs [FLOOKUP_UPDATE] \\ Cases_on `k = n` \\ fs [] THEN1
       (MATCH_MP_TAC IMP_EVERY_LUPDATE \\ REPEAT STRIP_TAC
        THEN1 (bv_ok_SUBSET_IMP |> Q.ISPEC_THEN `r.refs`MATCH_MP_TAC
          \\ fs [] \\ fs [SUBSET_DEF,FLOOKUP_DEF])
        \\ Q.PAT_ASSUM `!k:num. bbb` (MP_TAC o Q.SPEC `n`) \\ fs []
        \\ fs [EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC
        \\ Q.ISPEC_THEN`r.refs`match_mp_tac bv_ok_SUBSET_IMP
        \\ fs [] \\ fs [SUBSET_DEF,FLOOKUP_DEF])
      \\ Q.PAT_ASSUM `!k:num. bbb` (MP_TAC o Q.SPEC `k`) \\ fs []
      \\ BasicProvers.EVERY_CASE_TAC
      \\ fs [EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC
      \\ Q.ISPEC_THEN`r.refs`match_mp_tac bv_ok_SUBSET_IMP
      \\ fs [] \\ fs [SUBSET_DEF,FLOOKUP_DEF]))
  THEN1 (
    fs[state_ok_def] \\ rw[] >-
     (fs [EVERY_MEM] \\ REPEAT STRIP_TAC
      \\ BasicProvers.EVERY_CASE_TAC
      \\ RES_TAC \\ fs []
      \\ Q.ISPEC_THEN`r.refs`match_mp_tac bv_ok_SUBSET_IMP
      \\ fs [] \\ fs [SUBSET_DEF,FLOOKUP_DEF])
    \\ simp[FLOOKUP_UPDATE] >> rw[] >>
    BasicProvers.CASE_TAC >>
    BasicProvers.CASE_TAC >>
    first_x_assum(qspec_then`k`mp_tac) >> rw[] >>
    fs [EVERY_MEM] \\ REPEAT STRIP_TAC
    \\ RES_TAC \\ fs []
    \\ Q.ISPEC_THEN`r.refs`match_mp_tac bv_ok_SUBSET_IMP
    \\ fs [] \\ fs [SUBSET_DEF,FLOOKUP_DEF]));

val do_app_ok = prove(
  ``state_ok r /\ EVERY (bv_ok r.refs) a /\
    (do_app op a r = Rval (q,t)) ==>
    state_ok t /\ bv_ok t.refs q /\
    (EVERY (bv_ok r.refs) env ==> EVERY (bv_ok t.refs) env)``,
  STRIP_TAC \\ IMP_RES_TAC do_app_ok_lemma \\ fs []
  \\ fs [EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ IMP_RES_TAC do_app_refs_SUBSET
  \\ IMP_RES_TAC bv_ok_SUBSET_IMP);

val evaluate_ok = prove(
  ``!xs env s res t.
      (evaluate (xs,env,s) = (res,t)) /\
      state_ok s /\ EVERY (bv_ok s.refs) env ==>
      state_ok t /\
      (case res of
       | Rval vs => EVERY (bv_ok t.refs) vs
       | Rerr(Rraise v) => bv_ok t.refs v
       | _ => T) /\
      EVERY (bv_ok t.refs) env``,
  recInduct bvlSemTheory.evaluate_ind \\ REPEAT STRIP_TAC \\ fs [bvlSemTheory.evaluate_def]
  \\ SRW_TAC [] []
  \\ BasicProvers.EVERY_CASE_TAC \\ fs [evaluate_ok_lemma]
  \\ SRW_TAC [] [] \\ REV_FULL_SIMP_TAC std_ss []
  \\ BasicProvers.EVERY_CASE_TAC \\ fs [evaluate_ok_lemma]
  \\ SRW_TAC [] [] \\ REV_FULL_SIMP_TAC std_ss []
  \\ BasicProvers.EVERY_CASE_TAC \\ fs [evaluate_ok_lemma]
  \\ SRW_TAC [] [] \\ REV_FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC evaluate_SING \\ fs []
  \\ BasicProvers.EVERY_CASE_TAC \\ fs [evaluate_ok_lemma]
  \\ SRW_TAC [] [] \\ REV_FULL_SIMP_TAC std_ss []
  \\ BasicProvers.EVERY_CASE_TAC \\ fs [evaluate_ok_lemma]
  \\ SRW_TAC [] [] \\ REV_FULL_SIMP_TAC std_ss []
  \\ TRY (fs [EVERY_EL] \\ NO_TAC)
  \\ IMP_RES_TAC evaluate_IMP_bv_ok
  \\ IMP_RES_TAC do_app_ok
  \\ REPEAT (Q.PAT_ASSUM `!xx.bb` (K ALL_TAC))
  \\ imp_res_tac bvlPropsTheory.do_app_err \\ fs[]
  \\ IMP_RES_TAC find_code_EVERY_IMP \\ fs [rich_listTheory.EVERY_REVERSE]
  \\ IMP_RES_TAC evaluate_IMP_bv_ok \\ fs [evaluate_ok_lemma]
  \\ fs [state_ok_def]);

(* semantics lemmas *)

val evaluate_MAP_Var = prove(
  ``!l env vs b s.
      EVERY isVar l /\ (get_vars (MAP destVar l) env = SOME vs) ==>
        (evaluate (MAP (Var o destVar) l,MAP (adjust_bv b) env,s) =
          (Rval (MAP (adjust_bv b) vs),s))``,
  Induct THEN1 (EVAL_TAC \\ SRW_TAC [] [])
  \\ Cases \\ fs [isVar_def,destVar_def,get_vars_def]
  \\ Cases_on `l` \\ fs [bviSemTheory.evaluate_def,get_vars_def,EL_MAP]
  \\ Cases_on `h` \\ fs [isVar_def,destVar_def]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `n' < LENGTH env` \\ fs []
  \\ Cases_on `get_vars (MAP destVar t) env` \\ fs []
  \\ Q.PAT_ASSUM `!xx.bb` (MP_TAC o Q.SPEC `env`) \\ fs []
  \\ SRW_TAC [] [] \\ fs [EL_MAP]) |> INST_TYPE[alpha|->``:'ffi``];

val evaluate_MAP_Var2 = prove(
  ``!args.
      bVarBound (LENGTH vs) args /\ EVERY isVar args ==>
      ?ts.
        bviSem$evaluate (MAP (Var o destVar) args,vs ++ env,s) = (Rval ts,s) /\
        evaluate (MAP (Var o destVar) args,vs,s) = (Rval ts,s)``,
  Induct \\ fs [MAP,bviSemTheory.evaluate_def] \\ Cases \\ fs [isVar_def]
  \\ Cases_on `args` \\ fs [MAP,bviSemTheory.evaluate_def,destVar_def,bVarBound_def]
  \\ REPEAT STRIP_TAC
  \\ `n < LENGTH vs + LENGTH env` by DECIDE_TAC \\ fs []
  \\ fs [rich_listTheory.EL_APPEND1]) |> SPEC_ALL |> INST_TYPE[alpha|->``:'ffi``];

val bEval_bVarBound = prove(
  ``!xs vs s env.
      bVarBound (LENGTH vs) xs ==>
      (bvlSem$evaluate (xs,vs ++ env,s) = evaluate (xs,vs,s))``,
  recInduct bvlSemTheory.evaluate_ind \\ REPEAT STRIP_TAC
  \\ fs [bvlSemTheory.evaluate_def,bVarBound_def]
  \\ TRY (BasicProvers.EVERY_CASE_TAC \\ fs [ADD1] \\ NO_TAC)
  THEN1 (`n < LENGTH env + LENGTH env'` by DECIDE_TAC
         \\ fs [rich_listTheory.EL_APPEND1])
  THEN1 (BasicProvers.EVERY_CASE_TAC \\ fs []
         \\ FIRST_X_ASSUM MATCH_MP_TAC \\ IMP_RES_TAC bvlPropsTheory.evaluate_IMP_LENGTH
         \\ fs [AC ADD_COMM ADD_ASSOC]));

val iEval_def = bviSemTheory.evaluate_def;

(* correctness of stubs *)

val bEvalOp_def = bvlSemTheory.do_app_def;
val iEvalOp_def = bviSemTheory.do_app_def;

val evaluate_CopyGlobals_code = Q.prove(
  `∀n l1 s.
   lookup CopyGlobals_location s.code = SOME (3,SND CopyGlobals_code) ∧
   FLOOKUP s.refs p = SOME (ValueArray ls) ∧
   FLOOKUP s.refs p1 = SOME (ValueArray l1) ∧
   p ≠ p1 ∧
   n < LENGTH ls ∧ n < LENGTH l1
   ⇒
   ∃c.
     evaluate ([SND CopyGlobals_code],
               [RefPtr p1; RefPtr p; Number &n],
               inc_clock c s) =
     (Rval [Unit], s with refs := s.refs |+ (p1, ValueArray (TAKE (SUC n) ls ++ DROP (SUC n) l1)))`,
  Induct >> rw[] >> rw[CopyGlobals_code_def] >>
  rw[iEval_def,iEvalOp_def,do_app_aux_def,bEvalOp_def,bvl_to_bvi_id,small_enough_int_def,bvl_to_bvi_with_refs] >- (
    qexists_tac`0`>>simp[inc_clock_ZERO,state_component_equality] >>
    rpt AP_TERM_TAC >>
    simp[LIST_EQ_REWRITE,EL_LUPDATE] >>
    rw[] >> simp[EL_APPEND2,EL_DROP] >>
    Cases_on`ls`>>fs[]) >>
  simp[find_code_def] >>
  simp[Once inc_clock_def] >>
  qpat_abbrev_tac`l2 = LUPDATE x y z` >>
  qpat_abbrev_tac`rf = s.refs |+ X` >>
  first_x_assum(qspecl_then[`l2`,`s with refs := rf`]mp_tac) >>
  discharge_hyps >- (
    simp[Abbr`rf`,FLOOKUP_UPDATE] >>
    simp[Abbr`l2`] ) >>
  strip_tac >>
  qexists_tac`c+1` >>
  simp[Once inc_clock_def] >>
  qpat_abbrev_tac`ss = dec_clock 1 Z` >>
  `ss = inc_clock c (s with refs := rf)` by (
    simp[Abbr`ss`] >> EVAL_TAC >>
    simp[state_component_equality] ) >>
  simp[Abbr`ss`] >>
  `&SUC n - 1 = &n` by (
    simp[ADD1] >> intLib.COOPER_TAC ) >>
  simp[state_component_equality] >>
  simp[Abbr`rf`,fmap_eq_flookup,FLOOKUP_UPDATE] >>
  rw[] >>
  simp[LIST_EQ_REWRITE,Abbr`l2`] >> rw[] >>
  Cases_on`x < SUC n` >> simp[EL_APPEND1,EL_TAKE] >>
  simp[EL_APPEND2,EL_DROP,EL_LUPDATE] >>
  Cases_on`x = SUC n` >> simp[EL_APPEND1,EL_TAKE,EL_APPEND2,EL_DROP])
  |> Q.GEN`ls`;

val evaluate_AllocGlobal_code = Q.prove(
  `s.global = SOME p ∧
   FLOOKUP s.refs p = SOME (ValueArray (Number(&(SUC n))::ls)) ∧ n ≤ LENGTH ls ∧
   lookup CopyGlobals_location s.code = SOME (3,SND CopyGlobals_code)
   ⇒
   ∃p1 c.
     (p1 ≠ p ⇒ p1 ∉ FDOM s.refs) ∧
     evaluate ([SND AllocGlobal_code],[],inc_clock c s) =
       (Rval [Unit],
        s with <| global := SOME p1; refs := s.refs
          |+ (p, ValueArray ((Number(&(SUC(n+1))))::ls))
          |+ (p1, ValueArray ((Number(&(SUC(n+1))))::
                              if n < LENGTH ls then ls
                              else ls ++ (REPLICATE (SUC(LENGTH ls)) (Number 0))))|>)`,
  strip_tac >>
  simp[AllocGlobal_code_def,iEval_def,iEvalOp_def,do_app_aux_def,small_enough_int_def,
       Once inc_clock_def,bEvalOp_def,bvl_to_bvi_id,bvl_to_bvi_with_refs,FLOOKUP_UPDATE,
       find_code_def] >>
  IF_CASES_TAC >> simp[] >- (
    Q.LIST_EXISTS_TAC[`p`,`0`] >>
    simp[state_component_equality] >>
    EVAL_TAC >>
    simp[fmap_eq_flookup,FLOOKUP_UPDATE] >>
    rw[] >> simp[] >> intLib.COOPER_TAC) >>
  `(λptr. ptr ≠ p ∧ ptr ∉ FDOM s.refs) = (λptr. ptr ∉ FDOM s.refs)` by (
    simp[FUN_EQ_THM] >> fs[FLOOKUP_DEF] >> metis_tac[]) >> simp[] >>
  qpat_abbrev_tac`p1 = LEAST ptr. ptr ∉ FDOM s.refs` >>
  qexists_tac`p1` >>
  `p1 ∉ FDOM s.refs` by (
    rpt strip_tac >> fs[FLOOKUP_DEF] >>
    metis_tac[LEAST_NOTIN_FDOM] ) >>
  simp[LUPDATE_def] >>
  qpat_abbrev_tac`l1 = REPLICATE _ _` >>
  qpat_abbrev_tac`rf = s.refs |+ _ |+ _` >>
  qspecl_then[`Number(1+ &SUC n)::ls`,`n`,`l1`,`s with <| global := SOME p1; refs := rf|>`]mp_tac evaluate_CopyGlobals_code >>
  discharge_hyps >- (
    simp[Abbr`rf`,FLOOKUP_UPDATE] >>
    IF_CASES_TAC >> simp[] >- (
      fs[FLOOKUP_DEF] >> metis_tac[LEAST_NOTIN_FDOM] ) >>
    simp[Abbr`l1`,LENGTH_REPLICATE] ) >>
  strip_tac >>
  qexists_tac`c+1` >>
  simp[] >>
  qpat_abbrev_tac`ss = dec_clock 1 Z` >>
  `ss = inc_clock c (s with <| global := SOME p1; refs := rf|>)` by (
    simp[Abbr`ss`] >> EVAL_TAC >>
    simp[state_component_equality] ) >>
  simp[Abbr`ss`] >>
  `&SUC n - 1 = &n` by (Cases_on`n`>>fs[]>>simp[ADD1]>>intLib.COOPER_TAC) >> fs[] >>
  simp[Abbr`rf`,fmap_eq_flookup,FLOOKUP_UPDATE,state_component_equality] >>
  rw[] >> simp[] >> TRY(intLib.COOPER_TAC) >>
  `n = LENGTH ls`by decide_tac >>
  `2 * (LENGTH ls + 1) = LENGTH ls + LENGTH ls + 2` by DECIDE_TAC >>
  simp[Abbr`l1`,DROP_REPLICATE,ADD1])

(* compiler correctness *)

val bEval_def = bvlSemTheory.evaluate_def;
val iEval_append = bviPropsTheory.evaluate_APPEND;

val compile_exps_Var_list = prove(
  ``!l n. EVERY isVar l ==> (compile_exps n l = (MAP (Var o destVar) l ,[],n))``,
  Induct \\ fs [EVERY_DEF,compile_exps_def] \\ Cases \\ fs [isVar_def]
  \\ Cases_on `l` \\ fs [compile_exps_def,destVar_def,LET_DEF]);

val compile_int_thm = prove(
  ``!i env s. evaluate ([compile_int i],env,s) = (Rval [Number i],s)``,
  STRIP_TAC \\ completeInduct_on `Num (ABS i)`
  \\ REPEAT STRIP_TAC \\ fs [PULL_FORALL] \\ POP_ASSUM (K ALL_TAC)
  \\ reverse (Cases_on `i`) \\ fs [] THEN1 EVAL_TAC
  \\ (ONCE_REWRITE_TAC [compile_int_def] \\ fs [LET_DEF]
    \\ SRW_TAC [] [] THEN1
     (`n <= 1073741823` by DECIDE_TAC
      \\ fs [evaluate_def,bviSemTheory.do_app_def,do_app_aux_def,small_enough_int_def])
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`&(n DIV 1000000000)`,`env`,`s`])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1 (fs [integerTheory.INT_ABS_NUM,DIV_LT_X] \\ intLib.COOPER_TAC)
    \\ REPEAT STRIP_TAC \\ fs []
    \\ `n MOD 1000000000 < 1000000000` by fs [MOD_LESS]
    \\ `n MOD 1000000000 <= 1073741823` by DECIDE_TAC
    \\ fs [evaluate_def,bviSemTheory.do_app_def,do_app_aux_def,small_enough_int_def,bvlSemTheory.do_app_def]
    \\ fs [bvl_to_bvi_id]
    \\ STRIP_ASSUME_TAC
         (MATCH_MP DIVISION (DECIDE ``0 < 1000000000:num``) |> Q.SPEC `n`)
    \\ intLib.COOPER_TAC));

val iEval_bVarBound = Q.prove(
  `!(n:num) xs n vs (t:'ffi bvlSem$state) (s:'ffi bviSem$state) env.
     bVarBound (LENGTH vs) xs /\ bEvery GoodHandleLet xs ==>
     (evaluate (FST (compile_exps n xs),vs ++ env,s) =
      evaluate (FST (compile_exps n xs),vs,s))`,
  recInduct bVarBound_ind \\ REPEAT STRIP_TAC
  \\ fs [iEval_def,bVarBound_def,compile_exps_def] \\ SRW_TAC [] []
  \\ fs [bEvery_def,GoodHandleLet_def] \\ SRW_TAC [] []
  THEN1 (FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n1`,`vs`]) \\ fs []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n`,`vs`]) \\ fs []
    \\ IMP_RES_TAC compile_exps_SING \\ SRW_TAC [] []
    \\ ONCE_REWRITE_TAC [bviPropsTheory.evaluate_CONS] \\ fs [])
  THEN1 (fs [rich_listTheory.EL_APPEND1])
  THEN1 (`F` by DECIDE_TAC)
  THEN1 (IMP_RES_TAC compile_exps_SING \\ SRW_TAC [] []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n2`,`vs`]) \\ fs []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n1`,`vs`]) \\ fs []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n`,`vs`]) \\ fs []
    \\ fs [iEval_def])
  THEN1 (IMP_RES_TAC compile_exps_SING \\ SRW_TAC [] [] \\ fs [iEval_def]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n1`]) \\ fs []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n`,`vs`]) \\ fs []
    \\ REPEAT STRIP_TAC
    \\ Cases_on `evaluate (c1,vs,s)` \\ fs []
    \\ Cases_on `q` \\ fs []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`a ++ vs`]) \\ fs []
    \\ IMP_RES_TAC bviPropsTheory.evaluate_IMP_LENGTH \\ IMP_RES_TAC compile_exps_LENGTH
    \\ REPEAT STRIP_TAC \\ POP_ASSUM MATCH_MP_TAC
    \\ fs [AC ADD_COMM ADD_ASSOC])
  \\ TRY (IMP_RES_TAC compile_exps_SING \\ SRW_TAC [] []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n`,`vs`]) \\ fs []
    \\ fs [iEval_def] \\ NO_TAC)
  THEN1
   (FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n`,`vs`]) \\ fs []
    \\ Cases_on `op` \\ fs [compile_op_def,iEval_def,compile_int_thm]
    \\ simp[iEval_def]
    \\ simp[iEval_append,iEval_def,compile_int_thm]
    \\ BasicProvers.EVERY_CASE_TAC \\ fs [iEval_def,compile_int_thm])
  \\ fs [iEval_def]
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n2`]) \\ fs []
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n`,`vs`]) \\ fs []
  \\ REPEAT STRIP_TAC \\ fs []
  \\ IMP_RES_TAC compile_exps_SING \\ SRW_TAC [] []
  \\ fs [markerTheory.Abbrev_def] \\ SRW_TAC [] []
  \\ Cases_on `x1` \\ fs [GoodHandleLet_def,destLet_def]
  \\ SRW_TAC [] [] \\ fs [compile_exps_def]
  \\ REV_FULL_SIMP_TAC std_ss [LET_DEF]
  \\ fs [iEval_def]
  \\ Q.PAT_ASSUM `!xx yy. bb = bbb` (ASSUME_TAC o Q.SPECL [`s`,`env`])
  \\ IMP_RES_TAC compile_exps_Var_list \\ fs [] \\ SRW_TAC [] []
  \\ fs [bVarBound_def]
  \\ (evaluate_MAP_Var2 |> MP_TAC) \\ fs []
  \\ REPEAT STRIP_TAC \\ fs []
  \\ Cases_on `find_code (SOME (num_stubs + 2 * n3 + 1)) ts s.code` \\ fs []
  \\ Cases_on `x` \\ fs [] \\ Cases_on `s.clock = 0` \\ fs []
  \\ Cases_on `evaluate ([r],q,dec_clock 1 s)` \\ fs []
  \\ Cases_on `q'` \\ fs []
  \\ Cases_on `e'` \\ fs []
  \\ ONCE_REWRITE_TAC [APPEND |> SPEC_ALL |> CONJUNCT2 |> GSYM]
  \\ FIRST_X_ASSUM MATCH_MP_TAC \\ fs [ADD1]);

val v_to_list_adjust = Q.prove(
  `∀x. v_to_list (adjust_bv f x) = OPTION_MAP (MAP (adjust_bv f)) (v_to_list x)`,
  ho_match_mp_tac v_to_list_ind >>
  simp[v_to_list_def,adjust_bv_def] >> rw[] >>
  Cases_on`v_to_list x`>>fs[]);

val do_app_adjust = Q.prove(
  `state_rel b2 s5 t2 /\
   (!i. op <> Const i) /\ (op <> Ref) /\ (op ≠ RefByte) ∧ (op ≠ RefArray) ∧
   (∀n. op ≠ Global n) ∧ (∀n. op ≠ SetGlobal n) ∧ (op ≠ AllocGlobal) ∧
   (do_app op (REVERSE a) s5 = Rval (q,r)) /\ EVERY (bv_ok s5.refs) (REVERSE a) ==>
   ?t3. (do_app op (MAP (adjust_bv b2) (REVERSE a)) t2 =
          Rval (adjust_bv b2 q,t3)) /\
        state_rel b2 r t3`,
  SIMP_TAC std_ss [Once bEvalOp_def,iEvalOp_def,do_app_aux_def]
  \\ Cases_on `op` \\ fs []
  THEN1 (* Cons *)
   (fs [bEvalOp_def]
    \\ SRW_TAC [] [adjust_bv_def,MAP_EQ_f,bvl_to_bvi_id]
    \\ SRW_TAC [] [adjust_bv_def,MAP_EQ_f,bvl_to_bvi_id])
  THEN1 (* El *)
   (BasicProvers.EVERY_CASE_TAC \\ fs [adjust_bv_def,bEvalOp_def]
    \\ every_case_tac >> fs[]
    \\ SRW_TAC [] []
    \\ fs [adjust_bv_def,MAP_EQ_f,bvl_to_bvi_id,
         bEvalOp_def,EL_MAP] \\ SRW_TAC [] [])
  THEN1 (* LengthBlock *)
   (BasicProvers.EVERY_CASE_TAC \\ fs [adjust_bv_def,bEvalOp_def]
    \\ SRW_TAC [] [] \\ fs[adjust_bv_def,bvl_to_bvi_id])
  THEN1 (* Length *) (
    every_case_tac >> fs[] >> rw[] >> fs[bEvalOp_def] >>
    every_case_tac >> fs[] >> rw[] >> fs[adjust_bv_def,bvl_to_bvi_id] >- (
      fs[state_rel_def,bvi_to_bvl_def] >> rw[] >>
      last_x_assum(qspec_then`n`mp_tac) >> rw[]) >>
    spose_not_then strip_assume_tac >> rw[] >>
    fs[bvi_to_bvl_def,state_rel_def] >>
    last_x_assum(qspec_then`n`mp_tac) >> rw[])
  THEN1 (* LengthByte *) (
    every_case_tac >> fs[] >> rw[] >> fs[bEvalOp_def] >>
    every_case_tac >> fs[] >> rw[] >> fs[adjust_bv_def,bvl_to_bvi_id] >- (
      fs[state_rel_def,bvi_to_bvl_def] >> rw[] >>
      last_x_assum(qspec_then`n`mp_tac) >> rw[]) >>
    spose_not_then strip_assume_tac >> rw[] >>
    fs[bvi_to_bvl_def,state_rel_def] >>
    last_x_assum(qspec_then`n`mp_tac) >> rw[])
  THEN1 (* DerefByte *) (
    Cases_on`REVERSE a`>>fs[]>>
    Cases_on`t`>>fs[]>>
    Cases_on`h'`>>fs[]>>
    Cases_on`h`>>fs[]>>
    Cases_on`t'`>>fs[]>>
    simp[bEvalOp_def,adjust_bv_def] >>
    simp[] >> rw[] >>
    every_case_tac >> fs[] >>rw[] >> rw[adjust_bv_def,bvl_to_bvi_id] >>
    fs[state_rel_def] >>
    last_x_assum(qspec_then`n`mp_tac) >> simp[] >>
    spose_not_then strip_assume_tac >> fs[])
  THEN1 (* UpdateByte *) (
    Cases_on`REVERSE a`>>fs[]>>
    Cases_on`t`>>fs[]>>
    Cases_on`t'`>>fs[]>>
    Cases_on`h''`>>fs[]>>
    Cases_on`h'`>>fs[]>>
    Cases_on`h`>>fs[]>>
    Cases_on`t`>>fs[]>>
    simp[bEvalOp_def,adjust_bv_def] >>
    simp[] >> rw[] >>
    every_case_tac >> fs[] >>rw[] >>
    rw[adjust_bv_def,bvl_to_bvi_with_refs,bvl_to_bvi_id] >>
    fs[state_rel_def] >>
    TRY (
      last_x_assum(qspec_then`n`mp_tac) >> simp[] >>
      spose_not_then strip_assume_tac >> rpt var_eq_tac >> fs[] >>
      NO_TAC) >>
    simp[bvi_to_bvl_def] >>
    conj_asm1_tac >- (
      simp[INJ_INSERT] >>
      conj_tac >- (
        rator_x_assum`INJ`mp_tac >>
        simp[INJ_DEF] ) >>
      `n ∈ FDOM s5.refs` by fs[FLOOKUP_DEF] >>
      metis_tac[INJ_DEF]) >>
    simp[FLOOKUP_UPDATE] >>
    rw[] >- (
      last_x_assum(qspec_then`k`mp_tac) >> simp[] ) >>
    fs[bv_ok_def] >>
    TRY (
      qexists_tac`array_size`>>simp[]>>
      rw[] >> fs[FLOOKUP_DEF] >> NO_TAC) >>
    TRY (
      BasicProvers.CASE_TAC >>
      `k ∈ FDOM s5.refs ∧ n ∈ FDOM s5.refs` by fs[FLOOKUP_DEF] >>
      metis_tac[INJ_DEF]) >>
    METIS_TAC[])
  THEN1 (* FromList *) (
    Cases_on`REVERSE a`>>fs[]>>
    Cases_on`t`>>fs[] >>
    simp[bEvalOp_def,v_to_list_adjust] >>
    Cases_on`v_to_list h`>>simp[] >> strip_tac >>
    rpt var_eq_tac >> simp[bvl_to_bvi_id,adjust_bv_def] >>
    srw_tac[ETA_ss][])
  THEN1 (* TagLenEq *) (
    every_case_tac >> fs[bEvalOp_def,adjust_bv_def] >>
    rw[] >> rw[bvl_to_bvi_id])
  THEN1 (* TagEq *)
    (BasicProvers.EVERY_CASE_TAC \\ fs [adjust_bv_def,bEvalOp_def]
     \\ SRW_TAC [] []
     \\ simp[bvl_to_bvi_id])
  THEN1 (* BlockCmp *) (
    every_case_tac >> fs[bEvalOp_def,adjust_bv_def] >>
    rw[] >> simp[bvl_to_bvi_id])
  THEN1 (* IsBlock *)
   (BasicProvers.EVERY_CASE_TAC \\ fs [adjust_bv_def,bEvalOp_def]
    \\ SRW_TAC [] []
    \\ simp[bvl_to_bvi_id])
  THEN1 (* Deref *)
   (Cases_on `REVERSE a` \\ fs []
    \\ Cases_on `t` \\ fs []
    \\ Cases_on `h'` \\ fs []
    \\ Cases_on `h` \\ fs []
    \\ Cases_on `t'` \\ fs []
    \\ Cases_on `FLOOKUP s5.refs n` \\ fs []
    \\ Cases_on `x` \\ fs []
    \\ REPEAT STRIP_TAC \\ SRW_TAC [] [adjust_bv_def]
    \\ fs [bEvalOp_def]
    \\ Q.EXISTS_TAC `t2` \\ fs []
    \\ `FLOOKUP t2.refs (b2 n) = SOME(ValueArray(MAP (adjust_bv b2) l))` by (
        fs [state_rel_def] >>
        last_x_assum(qspec_then`n`mp_tac) >>
        simp[] )
    \\ simp[]
    \\ IF_CASES_TAC >> fs[] >> fs[]
    \\ `Num i < LENGTH l` by METIS_TAC[integerTheory.INT_OF_NUM,integerTheory.INT_LT]
    \\ simp[EL_MAP,bvl_to_bvi_id])
  THEN1 (* Update *)
   (Cases_on `REVERSE a` \\ fs []
    \\ Cases_on `t` \\ fs []
    \\ Cases_on `t'` \\ fs []
    \\ Cases_on `h'` \\ fs []
    \\ Cases_on `h` \\ fs []
    \\ Cases_on `t` \\ fs []
    \\ Cases_on `FLOOKUP s5.refs n` \\ fs []
    \\ Cases_on `x` \\ fs []
    \\ REPEAT STRIP_TAC \\ SRW_TAC [] [adjust_bv_def]
    \\ fs [bEvalOp_def] \\ SIMP_TAC std_ss [Once bvi_to_bvl_def] \\ fs []
    \\ `FLOOKUP t2.refs (b2 n) =
        SOME (ValueArray (MAP (adjust_bv b2) l))` by ALL_TAC THEN1
     (fs [state_rel_def,bvl_to_bvi_def,bvi_to_bvl_def]
      \\ last_x_assum (MP_TAC o Q.SPEC `n`) \\ fs [])
    \\ simp[]
    \\ IF_CASES_TAC >> fs[] >> fs[]
    \\ rpt var_eq_tac \\ simp[]
    \\ simp[bvl_to_bvi_with_refs,bvl_to_bvi_id]
    \\ fs [state_rel_def,bvl_to_bvi_def,bvi_to_bvl_def]
    \\ fs [FLOOKUP_UPDATE]
    \\ conj_tac >- fs [FLOOKUP_DEF,ABSORPTION_RWT]
    \\ rw[] \\ fs[LUPDATE_MAP,bv_ok_def]
    THEN1 (
      BasicProvers.CASE_TAC >>
      fs[FLOOKUP_DEF,INJ_DEF] >>
      METIS_TAC[] ) >>
    res_tac >> METIS_TAC[])
  THEN1 (* Label *)
   (BasicProvers.EVERY_CASE_TAC \\ fs [bEvalOp_def,bvl_to_bvi_id]
    \\ SRW_TAC [] [] \\ fs [adjust_bv_def])
  THEN1 (* FFI *) (
    Cases_on`REVERSE a`>>fs[]>>
    Cases_on`h`>>fs[]>>
    Cases_on`t`>>fs[]>>
    simp[bEvalOp_def,adjust_bv_def] >>
    rw[] >>
    qmatch_assum_rename_tac`bv_ok s5.refs (RefPtr k)` >>
    Cases_on`FLOOKUP s5.refs k`>>fs[]>>
    Cases_on`x`>>fs[]>>
    `FLOOKUP t2.refs (b2 k) = SOME (ByteArray l)` by (
      fs[state_rel_def] >>
      last_x_assum(qspec_then`k`mp_tac) >> simp[] ) >>
    simp[] >>
    simp[Once bvi_to_bvl_def] >>
    `s5.ffi = t2.ffi` by fs[state_rel_def] >>
    BasicProvers.CASE_TAC >> fs[] >>
    every_case_tac >> fs[] >> rw[] >>
    simp[bvl_to_bvi_with_refs,bvl_to_bvi_with_ffi,bvl_to_bvi_id] >>
    simp[bvi_to_bvl_def] >>
    fs[state_rel_def] >>
    conj_tac >- (
      fs[FLOOKUP_DEF] >>
      simp[ABSORPTION_RWT] ) >>
    simp[FLOOKUP_UPDATE] >> rw[] >>
    fs[bv_ok_def] >>
    TRY BasicProvers.CASE_TAC >>
    fs[FLOOKUP_DEF] >>
    METIS_TAC[INJ_DEF])
  THEN1 (* Equal *) (
    simp[bEvalOp_def] >>
    Cases_on`REVERSE a`>>fs[] >>
    Cases_on`t`>>fs[] >>
    Cases_on`t'`>>fs[] >>
    Cases_on`h'`>>fs[] >>
    Cases_on`h`>>fs[] >>
    strip_tac >> rpt var_eq_tac >>
    simp[adjust_bv_def,bvl_to_bvi_id] >>
    fs[state_rel_def,bv_ok_def] >>
    METIS_TAC[INJ_DEF] )
  \\ (* Add, Sub, Mult, Div, Mod, Less, ... *)
   (REPEAT STRIP_TAC
    \\ Cases_on `REVERSE a` \\ fs [] \\ Cases_on `t` \\ fs []
    \\ Cases_on `h'` \\ fs [] \\ Cases_on `h` \\ fs []
    \\ Cases_on `t'` \\ fs [] \\ SRW_TAC [] []
    \\ fs [bEvalOp_def,adjust_bv_def,bvl_to_bvi_id]
    \\ every_case_tac >> fs[bvl_to_bvi_id] >> rw[]
    \\ EVAL_TAC )) |> INST_TYPE[alpha|->``:'ffi``];

val compile_exps_correct = Q.prove(
  `!xs env (s1:'ffi bvlSem$state) n res s2 t1 n2 ys aux b1.
     (evaluate (xs,env,s1) = (res,s2)) /\ res <> Rerr(Rabort Rtype_error) /\
     (compile_exps n xs = (ys,aux,n2)) /\
     state_rel b1 s1 t1 /\
     state_ok s1 /\ EVERY (bv_ok s1.refs) env /\
     aux_code_installed aux t1.code /\
     bEvery GoodHandleLet xs /\ IS_SOME t1.global
     ==>
     ?t2 b2 c.
        (evaluate (ys,MAP (adjust_bv b2) env,inc_clock c t1) =
           (map_result (MAP (adjust_bv b2)) (adjust_bv b2) res,t2)) /\
        state_rel b2 s2 t2 /\
        (MAP (adjust_bv b1) env = MAP (adjust_bv b2) env) /\
        (!a. a IN FDOM s1.refs ==> (b1 a = b2 a))`,
  SIMP_TAC std_ss []
  \\ recInduct bvlSemTheory.evaluate_ind \\ REPEAT STRIP_TAC
  \\ fs [bEval_def,compile_exps_def,iEval_def,bEvery_def,GoodHandleLet_def]
  THEN1 (* NIL *)
   (SRW_TAC [] [iEval_def]
    \\ Q.LIST_EXISTS_TAC [`b1`,`0`] \\ fs [inc_clock_ZERO])
  THEN1 (* CONS *)
   (`?c1 aux1 n1. compile_exps n [x] = (c1,aux1,n1)` by METIS_TAC [PAIR]
    \\ `?c2 aux2 n2. compile_exps n1 (y::xs) = (c2,aux2,n2)` by METIS_TAC [PAIR]
    \\ fs [LET_DEF] \\ SRW_TAC [] [] \\ fs [PULL_FORALL]
    \\ `?res5 s5. evaluate ([x],env,s) = (res5,s5)` by METIS_TAC [PAIR]
    \\ `?res6 s6. evaluate (y::xs,env,s5) = (res6,s6)` by METIS_TAC [PAIR]
    \\ IMP_RES_TAC evaluate_ok \\ fs []
    \\ IMP_RES_TAC aux_code_installed_APPEND \\ SRW_TAC [] []
    \\ fs [] \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `n`) \\ fs []
    \\ reverse (Cases_on `res5`) \\ fs [] \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`t1`,`b1`]) \\ fs []
    \\ rpt var_eq_tac
    \\ TRY (discharge_hyps >- (spose_not_then strip_assume_tac >> fs[]))
    \\ TRY (REPEAT STRIP_TAC \\ IMP_RES_TAC compile_exps_LENGTH
      \\ `?d. c1 = [d]` by (Cases_on `c1` \\ fs [LENGTH_NIL])
      \\ SIMP_TAC std_ss [Once bviPropsTheory.evaluate_CONS] \\ fs []
      \\ SIMP_TAC std_ss [Once bviPropsTheory.evaluate_CONS] \\ fs [GSYM PULL_FORALL]
      \\ Q.LIST_EXISTS_TAC [`t2`,`b2`,`c`] \\ fs [] \\ NO_TAC)
    \\ REPEAT STRIP_TAC
    \\ Q.PAT_ASSUM `!nn mm. bbb` (MP_TAC o Q.SPEC `n1`) \\ fs []
    \\ `res6 <> Rerr(Rabort Rtype_error)` by (REPEAT STRIP_TAC \\ fs []) \\ fs []
    \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC compile_exps_LENGTH
    \\ `?d. c1 = [d]` by (Cases_on `c1` \\ fs [LENGTH_NIL]) \\ fs []
    \\ `aux_code_installed aux2 t2.code` by
     (fs [GSYM PULL_FORALL]
      \\ IMP_RES_TAC evaluate_code_const \\ fs [inc_clock_def])
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`b2`]) \\ fs []
    \\ `s2 = s6` by (BasicProvers.EVERY_CASE_TAC \\ fs [])
    \\ discharge_hyps >- metis_tac[evaluate_global_mono,inc_clock_global]
    \\ REPEAT STRIP_TAC \\ fs [GSYM PULL_FORALL]
    \\ Q.MATCH_ASSUM_RENAME_TAC
        `evaluate (c2,MAP (adjust_bv b3) env,inc_clock c4 t2) =
           (map_result (MAP (adjust_bv b3)) (adjust_bv b3) res6,t3)`
    \\ IMP_RES_TAC evaluate_inv_clock
    \\ fs [inc_clock_ADD]
    \\ ONCE_REWRITE_TAC [bviPropsTheory.evaluate_CONS] \\ fs []
    \\ REV_FULL_SIMP_TAC std_ss []
    \\ Q.LIST_EXISTS_TAC [`t3`,`b3`,`c4 + c`] \\ fs []
    \\ Cases_on `res6` \\ fs []
    \\ Q.PAT_ASSUM `xx = res` (ASSUME_TAC o GSYM) \\ fs []
    \\ IMP_RES_TAC evaluate_refs_SUBSET \\ fs [SUBSET_DEF]
    \\ IMP_RES_TAC bvlPropsTheory.evaluate_SING \\ fs []
    \\ MATCH_MP_TAC bv_ok_IMP_adjust_bv_eq \\ fs [])
  THEN1 (* Var *)
   (Cases_on `n < LENGTH env` \\ fs [] \\ SRW_TAC [] []
    \\ fs [iEval_def] \\ Q.LIST_EXISTS_TAC [`b1`,`0`]
    \\ fs [inc_clock_ZERO,EL_MAP])
  THEN1 (* If *)
   (Q.ABBREV_TAC `n4 = n2` \\ POP_ASSUM (K ALL_TAC)
    \\ `?c1 aux1 n1. compile_exps n [x1] = (c1,aux1,n1)` by METIS_TAC [PAIR]
    \\ `?c2 aux2 n2. compile_exps n1 [x2] = (c2,aux2,n2)` by METIS_TAC [PAIR]
    \\ `?c3 aux3 n3. compile_exps n2 [x3] = (c3,aux3,n3)` by METIS_TAC [PAIR]
    \\ fs [LET_DEF] \\ SRW_TAC [] [] \\ fs [PULL_FORALL]
    \\ `?res5 s5. evaluate ([x1],env,s) = (res5,s5)` by METIS_TAC [PAIR]
    \\ IMP_RES_TAC evaluate_ok \\ fs []
    \\ IMP_RES_TAC aux_code_installed_APPEND \\ SRW_TAC [] []
    \\ fs [] \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `n`) \\ fs []
    \\ reverse (Cases_on `res5`) \\ fs [] \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`t1`,`b1`]) \\ fs []
    \\ IMP_RES_TAC aux_code_installed_APPEND \\ fs [GSYM PULL_FORALL]
    \\ TRY (
      discharge_hyps >- (rpt strip_tac >> fs[])
      \\ REPEAT STRIP_TAC \\ IMP_RES_TAC compile_exps_LENGTH
      \\ `?d. c1 = [d]` by (Cases_on `c1` \\ fs [LENGTH_NIL])
      \\ SIMP_TAC std_ss [Once iEval_def] \\ fs []
      \\ Q.LIST_EXISTS_TAC [`t2`,`b2`,`c`] \\ fs []
      \\ rw[] \\ NO_TAC)
    \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC bvlPropsTheory.evaluate_SING \\ fs []
    \\ Cases_on `d1 = Boolv T` \\ fs []
    THEN1
     (IMP_RES_TAC compile_exps_LENGTH
      \\ `?d. c1 = [d]` by (Cases_on `c1` \\ fs [LENGTH_NIL])
      \\ SIMP_TAC std_ss [Once iEval_def] \\ fs []
      \\ `?d2. c2 = [d2]` by (Cases_on `c2` \\ fs [LENGTH_NIL]) \\ fs []
      \\ Q.PAT_ASSUM `!nn mm. bbb` (MP_TAC o Q.SPEC `n1`) \\ fs []
      \\ `aux_code_installed aux2 t2.code` by
       (fs [GSYM PULL_FORALL]
        \\ IMP_RES_TAC evaluate_code_const \\ fs [inc_clock_def])
      \\ REPEAT STRIP_TAC
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`b2`]) \\ fs []
      \\ discharge_hyps >- metis_tac[evaluate_global_mono,inc_clock_global]
      \\ REPEAT STRIP_TAC \\ fs [GSYM PULL_FORALL]
      \\ IMP_RES_TAC evaluate_inv_clock \\ fs [inc_clock_ADD]
      \\ REV_FULL_SIMP_TAC std_ss []
      \\ Q.LIST_EXISTS_TAC [`t2'`,`b2'`,`c' + c`] \\ fs []
      \\ fs [adjust_bv_def]
      \\ IMP_RES_TAC evaluate_refs_SUBSET \\ fs [SUBSET_DEF])
    \\ Cases_on `d1 = Boolv F` \\ fs []
    THEN1
     (IMP_RES_TAC compile_exps_LENGTH
      \\ `?d. c1 = [d]` by (Cases_on `c1` \\ fs [LENGTH_NIL])
      \\ SIMP_TAC std_ss [Once iEval_def] \\ fs []
      \\ `?d3. c3 = [d3]` by (Cases_on `c3` \\ fs [LENGTH_NIL]) \\ fs []
      \\ Q.PAT_ASSUM `!nn mm. bbb` (MP_TAC o Q.SPEC `n2`) \\ fs []
      \\ `aux_code_installed aux3 t2.code` by
       (fs [GSYM PULL_FORALL]
        \\ IMP_RES_TAC evaluate_code_const \\ fs [inc_clock_def])
      \\ REPEAT STRIP_TAC
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`b2`]) \\ fs []
      \\ discharge_hyps >- metis_tac[evaluate_global_mono,inc_clock_global]
      \\ REPEAT STRIP_TAC \\ fs [GSYM PULL_FORALL]
      \\ IMP_RES_TAC evaluate_inv_clock \\ fs [inc_clock_ADD]
      \\ REV_FULL_SIMP_TAC std_ss []
      \\ Q.LIST_EXISTS_TAC [`t2'`,`b2'`,`c' + c`] \\ fs []
      \\ fs [adjust_bv_def]
      \\ IMP_RES_TAC evaluate_refs_SUBSET \\ fs [SUBSET_DEF]))
  THEN1 (* Let *)
   (`?c1 aux1 n1. compile_exps n xs = (c1,aux1,n1)` by METIS_TAC [PAIR]
    \\ `?c2 aux2 n2. compile_exps n1 [x2] = (c2,aux2,n2)` by METIS_TAC [PAIR]
    \\ fs [LET_DEF] \\ SRW_TAC [] [] \\ fs [PULL_FORALL]
    \\ `?res5 s5. evaluate (xs,env,s) = (res5,s5)` by METIS_TAC [PAIR]
    \\ IMP_RES_TAC evaluate_ok \\ fs []
    \\ IMP_RES_TAC aux_code_installed_APPEND \\ SRW_TAC [] []
    \\ fs [] \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `n`) \\ fs []
    \\ reverse (Cases_on `res5`) \\ fs [] \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`t1`,`b1`]) \\ fs []
    \\ TRY (
      discharge_hyps >- (rpt strip_tac >> fs[])
      \\ REPEAT STRIP_TAC \\ IMP_RES_TAC compile_exps_LENGTH
      \\ `?d. c2 = [d]` by (Cases_on `c2` \\ fs [LENGTH_NIL])
      \\ SIMP_TAC std_ss [Once iEval_def] \\ fs []
      \\ Q.LIST_EXISTS_TAC [`t2`,`b2`,`c`] \\ fs []
      \\ rw [] \\ NO_TAC)
    \\ REPEAT STRIP_TAC
    \\ Q.MATCH_ASSUM_RENAME_TAC `evaluate ([x2],a ++ env,s5) = (res6,s6)`
    \\ Q.PAT_ASSUM `!nn mm. bbb` (MP_TAC o Q.SPEC `n1`) \\ fs []
    \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC compile_exps_LENGTH
    \\ `?d. c2 = [d]` by (Cases_on `c2` \\ fs [LENGTH_NIL]) \\ fs []
    \\ `aux_code_installed aux2 t2.code` by
     (fs [GSYM PULL_FORALL]
      \\ IMP_RES_TAC evaluate_code_const \\ fs [inc_clock_def])
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`b2`]) \\ fs []
    \\ discharge_hyps >- metis_tac[evaluate_global_mono,inc_clock_global]
    \\ REPEAT STRIP_TAC \\ fs [GSYM PULL_FORALL]
    \\ Q.MATCH_ASSUM_RENAME_TAC
        `evaluate ([d],MAP (adjust_bv b3) a ++
                    MAP (adjust_bv b3) env,inc_clock c4 t2) =
           (map_result (MAP (adjust_bv b3)) (adjust_bv b3) res6,t3)`
    \\ IMP_RES_TAC evaluate_inv_clock
    \\ fs [inc_clock_ADD]
    \\ ONCE_REWRITE_TAC [iEval_def] \\ fs []
    \\ fs [MAP_APPEND_MAP_EQ]
    \\ REV_FULL_SIMP_TAC std_ss []
    \\ Q.LIST_EXISTS_TAC [`t3`,`b3`,`c4 + c`] \\ fs []
    \\ IMP_RES_TAC evaluate_refs_SUBSET \\ fs [SUBSET_DEF])
  THEN1 (* Raise *)
   (`?c1 aux1 n1. compile_exps n [x1] = (c1,aux1,n1)` by METIS_TAC [PAIR]
    \\ fs [LET_DEF] \\ SRW_TAC [] [] \\ fs [PULL_FORALL]
    \\ IMP_RES_TAC compile_exps_LENGTH
    \\ `?d. c1 = [d]` by (Cases_on `c1` \\ fs [LENGTH_NIL]) \\ fs []
    \\ SRW_TAC [] []
    \\ `?res5 s5. evaluate ([x1],env,s) = (res5,s5)` by METIS_TAC [PAIR]
    \\ reverse (Cases_on `res5`) \\ fs [] \\ REPEAT STRIP_TAC
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `n`) \\ fs []
    \\ TRY (SRW_TAC [] [] \\ fs []
      \\ REPEAT STRIP_TAC \\ RES_TAC
      \\ Q.LIST_EXISTS_TAC [`t2`,`b2`,`c`] \\ fs []
      \\ SIMP_TAC std_ss [Once bviPropsTheory.evaluate_CONS] \\ fs []
      \\ fs [iEval_def] \\ NO_TAC)
    \\ REPEAT STRIP_TAC \\ RES_TAC \\ fs [iEval_def]
    \\ Q.LIST_EXISTS_TAC [`t2`,`b2`,`c`] \\ fs [] \\ SRW_TAC [] []
    \\ IMP_RES_TAC bvlPropsTheory.evaluate_SING \\ SRW_TAC [] [])
  THEN1 (* Handle *)
   (Cases_on `x1` \\ fs [GoodHandleLet_def,destLet_def] \\ fs [LET_DEF]
    \\ fs [compile_exps_Var_list]
    \\ `?c2 aux2 n2. compile_exps n [e] = (c2,aux2,n2)` by METIS_TAC [PAIR]
    \\ `?c3 aux3 n3. compile_exps n2' [x2] = (c3,aux3,n3)` by METIS_TAC [PAIR]
    \\ fs [] \\ SRW_TAC [] [] \\ fs [bEval_def]
    \\ Q.ISPECL_THEN[`s1`,`l`]mp_tac (Q.GEN`s`evaluate_Var_list) \\ fs[]
    \\ STRIP_TAC \\ fs []
    \\ `evaluate ([e],vs ++ env,s1) = evaluate ([e],vs,s1)` by ALL_TAC
    THEN1 (MATCH_MP_TAC bEval_bVarBound \\ fs [])
    \\ fs [] \\ POP_ASSUM (K ALL_TAC)
    \\ Cases_on `evaluate ([e],vs,s1)` \\ fs []
    \\ `?d2. c2 = [d2]` by
           (IMP_RES_TAC compile_exps_LENGTH \\ Cases_on `c2` \\ fs [LENGTH_NIL])
    \\ `?d3. c3 = [d3]` by
           (IMP_RES_TAC compile_exps_LENGTH \\ Cases_on `c3` \\ fs [LENGTH_NIL])
    \\ fs [] \\ NTAC 2 (POP_ASSUM (K ALL_TAC))
    \\ (Cases_on `q`) \\ fs []
    THEN1 (* Result case *)
     (SRW_TAC [] [] \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `n`)
      \\ fs [compile_exps_def,compile_exps_Var_list,LET_DEF]
      \\ STRIP_TAC \\ POP_ASSUM (Q.SPECL_THEN [`t1`,`b1`]mp_tac)
      \\ fs []
      \\ IMP_RES_TAC aux_code_installed_APPEND \\ fs []
      \\ IMP_RES_TAC aux_code_installed_APPEND \\ fs []
      \\ REPEAT STRIP_TAC
      \\ fs [] \\ SRW_TAC [] []
      \\ fs [aux_code_installed_def,iEval_def,find_code_def]
      \\ IMP_RES_TAC (GEN_ALL evaluate_MAP_Var) \\ fs []
      \\ `evaluate ([d2],MAP (adjust_bv b2) vs ++ MAP (adjust_bv b2) env,
            inc_clock c t1) =
          evaluate ([d2],MAP (adjust_bv b2) vs,inc_clock c t1)` by ALL_TAC THEN1
       (Q.SPECL_THEN[`n`,`[e]`,`n`,`MAP (adjust_bv b2) vs`,`t`]mp_tac iEval_bVarBound
        \\ fs [bEvery_def]
        \\ REPEAT STRIP_TAC \\ fs [])
      \\ fs [] \\ POP_ASSUM (K ALL_TAC)
      \\ Q.LIST_EXISTS_TAC [`t2`,`b2`,`c + 1`] \\ fs []
      \\ `dec_clock 1 (inc_clock (c + 1) t1) = inc_clock c t1` by
        (EVAL_TAC \\ fs [bviSemTheory.state_component_equality] \\ DECIDE_TAC) \\ fs [])
    \\ (Cases_on`e'`) \\ fs[]
    THEN1 (* Raise case *)
     (SRW_TAC [] [] \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `n`)
      \\ fs [compile_exps_def,compile_exps_Var_list,LET_DEF]
      \\ STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPECL [`t1`,`b1`])
      \\ fs []
      \\ IMP_RES_TAC aux_code_installed_APPEND \\ fs []
      \\ IMP_RES_TAC aux_code_installed_APPEND \\ fs []
      \\ REPEAT STRIP_TAC
      \\ fs [] \\ SRW_TAC [] []
      \\ fs [aux_code_installed_def,iEval_def,find_code_def]
      \\ IMP_RES_TAC (GEN_ALL evaluate_MAP_Var) \\ fs []
      \\ `evaluate ([d2],MAP (adjust_bv b2) vs ++ MAP (adjust_bv b2) env,
            inc_clock c t1) =
          evaluate ([d2],MAP (adjust_bv b2) vs,inc_clock c t1)` by ALL_TAC THEN1
       ((iEval_bVarBound |> SPEC_ALL |> Q.INST [`xs`|->`[e]`,
           `vs`|->`MAP (adjust_bv b2) vs`]
           |> Q.GENL [`env`,`s`] |> MP_TAC) \\ fs [bEvery_def]
        \\ REPEAT STRIP_TAC \\ fs [])
      \\ fs [] \\ POP_ASSUM (K ALL_TAC)
      \\ Q.PAT_ASSUM `!nn mm nn1. bbb` (MP_TAC o Q.SPEC `n2'`) \\ fs []
      \\ REPEAT STRIP_TAC
      \\ POP_ASSUM (MP_TAC o Q.SPECL [`t2`,`b2`]) \\ fs []
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
       (IMP_RES_TAC evaluate_ok \\ fs [] \\ REV_FULL_SIMP_TAC std_ss []
        \\ IMP_RES_TAC aux_code_installed_APPEND \\ fs []
        \\ IMP_RES_TAC aux_code_installed_APPEND \\ fs []
        \\ IMP_RES_TAC evaluate_code_const
        \\ imp_res_tac evaluate_global_mono
        \\ fs [inc_clock_def]
        \\ `EVERY (bv_ok r.refs) env` by ALL_TAC \\ fs []
        \\ fs [EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC
        \\ IMP_RES_TAC evaluate_refs_SUBSET
        \\ IMP_RES_TAC bv_ok_SUBSET_IMP)
      \\ REPEAT STRIP_TAC
      \\ Q.LIST_EXISTS_TAC [`t2'`,`b2'`,`c' + c + 1`] \\ fs []
      \\ `dec_clock 1 (inc_clock (c' + c + 1) t1) = inc_clock (c' + c) t1` by
        (EVAL_TAC \\ fs [bviSemTheory.state_component_equality] \\ DECIDE_TAC) \\ fs []
      \\ IMP_RES_TAC evaluate_inv_clock \\ fs [inc_clock_ADD]
      \\ `MAP (adjust_bv b2) vs = MAP (adjust_bv b2') vs` by ALL_TAC THEN1
       (fs [MAP_EQ_f] \\ REPEAT STRIP_TAC
        \\ MATCH_MP_TAC (bv_ok_IMP_adjust_bv_eq |> GEN_ALL)
        \\ Q.EXISTS_TAC `r` \\ fs []
        \\ IMP_RES_TAC evaluate_ok \\ fs [] \\ REV_FULL_SIMP_TAC std_ss []
        \\ fs [EVERY_MEM] \\ RES_TAC)
      \\ fs [] \\ IMP_RES_TAC evaluate_refs_SUBSET \\ fs [SUBSET_DEF])
    THEN1 (* abort case *)
     (SRW_TAC [] [] \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `n`)
      \\ fs [compile_exps_def,compile_exps_Var_list,LET_DEF]
      \\ STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPECL [`t1`,`b1`])
      \\ fs []
      \\ IMP_RES_TAC aux_code_installed_APPEND \\ fs []
      \\ IMP_RES_TAC aux_code_installed_APPEND \\ fs []
      \\ REPEAT STRIP_TAC
      \\ fs [] \\ SRW_TAC [] []
      \\ fs [aux_code_installed_def,iEval_def,find_code_def]
      \\ IMP_RES_TAC (GEN_ALL evaluate_MAP_Var) \\ fs []
      \\ `evaluate ([d2],MAP (adjust_bv b2) vs ++ MAP (adjust_bv b2) env,
            inc_clock c t1) =
          evaluate ([d2],MAP (adjust_bv b2) vs,inc_clock c t1)` by ALL_TAC THEN1
       ((iEval_bVarBound |> SPEC_ALL |> Q.INST [`xs`|->`[e]`,
           `vs`|->`MAP (adjust_bv b2) vs`]
           |> Q.GENL [`env`,`s`] |> MP_TAC) \\ fs [bEvery_def]
        \\ REPEAT STRIP_TAC \\ fs [])
      \\ fs [] \\ POP_ASSUM (K ALL_TAC)
      \\ Q.LIST_EXISTS_TAC [`t2`,`b2`,`c + 1`] \\ fs []
      \\ `dec_clock 1 (inc_clock (c + 1) t1) = inc_clock c t1` by
        (EVAL_TAC \\ fs [bviSemTheory.state_component_equality] \\ DECIDE_TAC) \\ fs []))
  THEN1 (* Op *)
   (`?c1 aux1 n1. compile_exps n xs = (c1,aux1,n1)` by METIS_TAC [PAIR]
    \\ fs [LET_DEF] \\ SRW_TAC [] [] \\ fs [PULL_FORALL]
    \\ `?res5 s5. evaluate (xs,env,s) = (res5,s5)` by METIS_TAC [PAIR]
    \\ fs [] \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `n`) \\ fs []
    \\ reverse (Cases_on `res5`) \\ fs [] \\ SRW_TAC [] []
    \\ first_x_assum (MP_TAC o Q.SPECL [`t1`,`b1`]) \\ fs []
    THEN1 (
      REPEAT STRIP_TAC \\ IMP_RES_TAC compile_exps_LENGTH \\ fs [iEval_def]
      \\ Q.LIST_EXISTS_TAC [`t2`,`b2`] \\ fs []
      \\ Cases_on `op` \\ fs [compile_op_def,iEval_def,compile_int_thm,iEval_append]
      \\ qexists_tac`c`>>simp[]>>
         every_case_tac \\ fs [iEval_def,compile_int_thm])
    \\ REPEAT STRIP_TAC \\ Cases_on `do_app op (REVERSE a) s5` \\ fs []
    \\ TRY(
      rw[] >>
      CHANGED_TAC(imp_res_tac bvlPropsTheory.do_app_err))
    \\ fs [GSYM PULL_FORALL]
    \\ Cases_on`a'`>>fs[]\\rw[]
    \\ Cases_on `?i. op = Const i` \\ fs [] THEN1
     (CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `b2`
      \\ CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `c`
      \\ fs [] \\ fs [compile_op_def] \\ Cases_on `c1`
      \\ fs [compile_int_thm,bEvalOp_def,iEval_def]
      \\ Cases_on `REVERSE a` \\ fs [iEval_def,iEvalOp_def]
      \\ fs [EVAL ``do_app_aux (Const 0) [] t2``]
      \\ SRW_TAC [] [adjust_bv_def])
    \\ Cases_on `op = Ref` \\ fs [] THEN1
     (fs [compile_op_def,iEval_def]
      \\ Q.ABBREV_TAC `b3 = ((LEAST ptr. ptr NOTIN FDOM s5.refs) =+
           (LEAST ptr. ptr NOTIN FDOM (bvi_to_bvl t2).refs)) b2`
      \\ CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `b3`
      \\ CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `c`
      \\ fs [iEvalOp_def,do_app_aux_def,bEvalOp_def,LET_DEF]
      \\ Q.ABBREV_TAC `x = (LEAST ptr. ptr NOTIN FDOM s5.refs)`
      \\ Q.ABBREV_TAC `y = LEAST ptr. ptr NOTIN FDOM (bvi_to_bvl t2).refs`
      \\ `~(x IN FDOM s5.refs)` by ALL_TAC THEN1
       (`?p. (\ptr. ptr NOTIN FDOM s5.refs) p` by
          (SIMP_TAC std_ss [] \\ METIS_TAC [NUM_NOT_IN_FDOM])
        \\ IMP_RES_TAC whileTheory.LEAST_INTRO \\ fs []
        \\ REV_FULL_SIMP_TAC std_ss [])
      \\ `~(y IN FDOM t2.refs)` by ALL_TAC THEN1
       (`?p. (\ptr. ptr NOTIN FDOM t2.refs) p` by
          (SIMP_TAC std_ss [] \\ METIS_TAC [NUM_NOT_IN_FDOM])
        \\ IMP_RES_TAC whileTheory.LEAST_INTRO \\ fs [bvi_to_bvl_def]
        \\ REV_FULL_SIMP_TAC (srw_ss()) [bvi_to_bvl_def])
      \\ fs []
      \\ SRW_TAC [] [adjust_bv_def]
      \\ `MAP (adjust_bv b3) env = MAP (adjust_bv b2) env` by ALL_TAC THEN1
       (fs [MAP_EQ_f] \\ REPEAT STRIP_TAC
        \\ MATCH_MP_TAC bv_ok_IMP_adjust_bv_eq
        \\ fs [EVERY_MEM] \\ RES_TAC
        \\ IMP_RES_TAC evaluate_refs_SUBSET
        \\ REPEAT STRIP_TAC THEN1 METIS_TAC [bv_ok_SUBSET_IMP]
        \\ Q.UNABBREV_TAC `b3` \\ fs [APPLY_UPDATE_THM]
        \\ SRW_TAC [] [] \\ fs [])
      \\ `MAP (adjust_bv b3) a = MAP (adjust_bv b2) a` by ALL_TAC THEN1
       (fs [MAP_EQ_f] \\ REPEAT STRIP_TAC
        \\ MATCH_MP_TAC bv_ok_IMP_adjust_bv_eq
        \\ IMP_RES_TAC evaluate_ok \\ REV_FULL_SIMP_TAC std_ss [] \\ fs []
        \\ fs [EVERY_MEM] \\ RES_TAC
        \\ Q.UNABBREV_TAC `b3` \\ fs [APPLY_UPDATE_THM]
        \\ SRW_TAC [] [] \\ fs [])
      \\ `MAP (OPTION_MAP (adjust_bv b2)) s5.globals =
          MAP (OPTION_MAP (adjust_bv b3)) s5.globals` by ALL_TAC THEN1
       (fs [MAP_EQ_f] \\ REPEAT STRIP_TAC
        \\ Cases_on `e` \\ fs []
        \\ MATCH_MP_TAC bv_ok_IMP_adjust_bv_eq
        \\ IMP_RES_TAC evaluate_ok \\ REV_FULL_SIMP_TAC std_ss [] \\ fs []
        \\ fs [state_ok_def,EVERY_MEM] \\ RES_TAC \\ fs []
        \\ Q.UNABBREV_TAC `b3` \\ fs [APPLY_UPDATE_THM]
        \\ SRW_TAC [] [] \\ fs [])
      \\ fs [] \\ STRIP_TAC
      THEN1 (UNABBREV_ALL_TAC \\ fs [APPLY_UPDATE_THM])
      \\ reverse STRIP_TAC THEN1
       (REPEAT STRIP_TAC \\ UNABBREV_ALL_TAC \\ fs [APPLY_UPDATE_THM]
        \\ SRW_TAC [] []
        \\ IMP_RES_TAC evaluate_refs_SUBSET \\ fs [SUBSET_DEF] \\ RES_TAC)
      \\ simp[bvl_to_bvi_with_refs,bvl_to_bvi_id]
      \\ fs [state_rel_def,bvl_to_bvi_def,bvi_to_bvl_def,FLOOKUP_UPDATE]
      \\ STRIP_TAC
      THEN1 (Q.UNABBREV_TAC `b3` \\ MATCH_MP_TAC INJ_EXTEND \\ fs [])
      \\ rw[MAP_REVERSE] \\ fs[]
      \\ TRY ( fs[Abbr`b3`,APPLY_UPDATE_THM] \\ NO_TAC)
      \\ TRY ( simp[Abbr`b3`,APPLY_UPDATE_THM] >> rw[] >> NO_TAC)
      \\ TRY ( fs[FLOOKUP_DEF] >> NO_TAC)
      \\ TRY ( qexists_tac`z`>>simp[]>>
        simp[GSYM MAP_MAP_o] >> rw[] >>
        simp[Abbr`b3`,APPLY_UPDATE_THM] >> rw[] >> NO_TAC)
      \\ Cases_on `FLOOKUP s5.refs k = NONE` \\ fs [rich_listTheory.MAP_REVERSE]
      \\ (`b3 k <> y` by ALL_TAC THEN1
       (fs[] \\ Q.UNABBREV_TAC `b3` \\ fs [APPLY_UPDATE_THM,FLOOKUP_DEF]
        \\ fs [INJ_DEF] \\ RES_TAC \\ REPEAT STRIP_TAC \\ fs []))
      \\ (`b3 k = b2 k` by ALL_TAC
           THEN1 (Q.UNABBREV_TAC `b3` \\ fs [APPLY_UPDATE_THM,FLOOKUP_DEF]))
      THEN1 ( fs[FLOOKUP_DEF] >> METIS_TAC[INJ_DEF] )
      \\ fs [] \\ Cases_on `FLOOKUP s5.refs k` \\ fs []
      \\ ntac 3 (Q.PAT_ASSUM `!k. bbb` MP_TAC)
      \\ Q.PAT_ASSUM `!k. bbb` (MP_TAC o Q.SPEC `k`) \\ fs []
      \\ Cases_on `x'` \\ fs [] \\ REPEAT STRIP_TAC
      \\ fs [MAP_EQ_f] \\ REPEAT STRIP_TAC
      \\ MATCH_MP_TAC bv_ok_IMP_adjust_bv_eq
      \\ IMP_RES_TAC evaluate_ok \\ REV_FULL_SIMP_TAC std_ss [] \\ fs []
      \\ fs [state_ok_def]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `k`) \\ fs []
      \\ fs [EVERY_MEM] \\ REPEAT STRIP_TAC
      \\ Q.UNABBREV_TAC `b3` \\ fs [APPLY_UPDATE_THM]
      \\ SRW_TAC [] [] \\ fs [])
    \\ Cases_on `op = RefArray` \\ fs[] THEN1
     (fs [compile_op_def,iEval_def]
      \\ Q.ABBREV_TAC `b3 = ((LEAST ptr. ptr NOTIN FDOM s5.refs) =+
           (LEAST ptr. ptr NOTIN FDOM (bvi_to_bvl t2).refs)) b2`
      \\ CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `b3`
      \\ CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `c`
      \\ fs [iEvalOp_def,do_app_aux_def,bEvalOp_def,LET_DEF]
      \\ Q.ABBREV_TAC `x = (LEAST ptr. ptr NOTIN FDOM s5.refs)`
      \\ Q.ABBREV_TAC `y = LEAST ptr. ptr NOTIN FDOM (bvi_to_bvl t2).refs`
      \\ `~(x IN FDOM s5.refs)` by ALL_TAC THEN1
       (`?p. (\ptr. ptr NOTIN FDOM s5.refs) p` by
          (SIMP_TAC std_ss [] \\ METIS_TAC [NUM_NOT_IN_FDOM])
        \\ IMP_RES_TAC whileTheory.LEAST_INTRO \\ fs []
        \\ REV_FULL_SIMP_TAC std_ss [])
      \\ `~(y IN FDOM t2.refs)` by ALL_TAC THEN1
       (`?p. (\ptr. ptr NOTIN FDOM t2.refs) p` by
          (SIMP_TAC std_ss [] \\ METIS_TAC [NUM_NOT_IN_FDOM])
        \\ IMP_RES_TAC whileTheory.LEAST_INTRO \\ fs [bvi_to_bvl_def]
        \\ REV_FULL_SIMP_TAC (srw_ss()) [bvi_to_bvl_def])
      \\ fs []
      \\ SRW_TAC [] [adjust_bv_def]
      \\ `MAP (adjust_bv b3) env = MAP (adjust_bv b2) env` by ALL_TAC THEN1
       (fs [MAP_EQ_f] \\ REPEAT STRIP_TAC
        \\ MATCH_MP_TAC bv_ok_IMP_adjust_bv_eq
        \\ fs [EVERY_MEM] \\ RES_TAC
        \\ IMP_RES_TAC evaluate_refs_SUBSET
        \\ REPEAT STRIP_TAC THEN1 METIS_TAC [bv_ok_SUBSET_IMP]
        \\ Q.UNABBREV_TAC `b3` \\ fs [APPLY_UPDATE_THM]
        \\ SRW_TAC [] [] \\ fs [])
      \\ `MAP (adjust_bv b3) a = MAP (adjust_bv b2) a` by ALL_TAC THEN1
       (fs [MAP_EQ_f] \\ REPEAT STRIP_TAC
        \\ MATCH_MP_TAC bv_ok_IMP_adjust_bv_eq
        \\ IMP_RES_TAC evaluate_ok \\ REV_FULL_SIMP_TAC std_ss [] \\ fs []
        \\ fs [EVERY_MEM] \\ RES_TAC
        \\ Q.UNABBREV_TAC `b3` \\ fs [APPLY_UPDATE_THM]
        \\ SRW_TAC [] [] \\ fs [])
      \\ `MAP (OPTION_MAP (adjust_bv b2)) s5.globals =
          MAP (OPTION_MAP (adjust_bv b3)) s5.globals` by ALL_TAC THEN1
       (fs [MAP_EQ_f] \\ REPEAT STRIP_TAC
        \\ Cases_on `e` \\ fs []
        \\ MATCH_MP_TAC bv_ok_IMP_adjust_bv_eq
        \\ IMP_RES_TAC evaluate_ok \\ REV_FULL_SIMP_TAC std_ss [] \\ fs []
        \\ fs [state_ok_def,EVERY_MEM] \\ RES_TAC \\ fs []
        \\ Q.UNABBREV_TAC `b3` \\ fs [APPLY_UPDATE_THM]
        \\ SRW_TAC [] [] \\ fs [])
      \\ fs []
      \\ Cases_on`REVERSE a`>>fs[]
      \\ Cases_on`t`>>fs[]
      \\ Cases_on`h`>>fs[]
      \\ Cases_on`t'`>>fs[]
      \\ Cases_on`0 ≤ i` >>fs[]
      \\ Cases_on`a`>>fs[adjust_bv_def]
      \\ STRIP_TAC THEN1 (
        rpt var_eq_tac >>
        simp[Abbr`b3`,adjust_bv_def,APPLY_UPDATE_THM] )
      \\ reverse STRIP_TAC THEN1
       (REPEAT STRIP_TAC \\ UNABBREV_ALL_TAC \\ fs [APPLY_UPDATE_THM]
        \\ SRW_TAC [] []
        \\ IMP_RES_TAC evaluate_refs_SUBSET \\ fs [SUBSET_DEF] \\ RES_TAC)
      \\ simp[bvl_to_bvi_with_refs,bvl_to_bvi_id]
      \\ fs [state_rel_def,bvl_to_bvi_def,bvi_to_bvl_def,FLOOKUP_UPDATE]
      \\ rpt var_eq_tac \\ simp[]
      \\ STRIP_TAC
      THEN1 (Q.UNABBREV_TAC `b3` \\ MATCH_MP_TAC INJ_EXTEND \\ fs [])
      \\ simp[FLOOKUP_UPDATE]
      \\ rw[MAP_REVERSE] \\ fs[]
      \\ TRY ( fs[Abbr`b3`,APPLY_UPDATE_THM] \\ NO_TAC)
      \\ TRY ( simp[Abbr`b3`,APPLY_UPDATE_THM] >> rw[] >> NO_TAC)
      \\ TRY ( fs[FLOOKUP_DEF] >> NO_TAC)
      \\ TRY (
        qexists_tac`z`>>simp[]>>
        simp[GSYM MAP_MAP_o] >> rw[] >>
        simp[Abbr`b3`,APPLY_UPDATE_THM] >> rw[] >> NO_TAC)
      \\ simp[map_replicate]
      \\ Cases_on `FLOOKUP s5.refs k = NONE` \\ fs [rich_listTheory.MAP_REVERSE]
      \\ (`b3 k <> y` by ALL_TAC THEN1
       (fs[] \\ Q.UNABBREV_TAC `b3` \\ fs [APPLY_UPDATE_THM,FLOOKUP_DEF]
        \\ fs [INJ_DEF] \\ RES_TAC \\ REPEAT STRIP_TAC \\ fs []))
      \\ (`b3 k = b2 k` by ALL_TAC
           THEN1 (Q.UNABBREV_TAC `b3` \\ fs [APPLY_UPDATE_THM,FLOOKUP_DEF]))
      THEN1 ( fs[FLOOKUP_DEF] >> METIS_TAC[INJ_DEF] )
      \\ fs [] \\ Cases_on `FLOOKUP s5.refs k` \\ fs []
      \\ ntac 3 (Q.PAT_ASSUM `!k. bbb` MP_TAC)
      \\ Q.PAT_ASSUM `!k. bbb` (MP_TAC o Q.SPEC `k`) \\ fs []
      \\ Cases_on `x'` \\ fs [] \\ REPEAT STRIP_TAC
      \\ fs [MAP_EQ_f] \\ REPEAT STRIP_TAC
      \\ MATCH_MP_TAC bv_ok_IMP_adjust_bv_eq
      \\ IMP_RES_TAC evaluate_ok \\ REV_FULL_SIMP_TAC std_ss [] \\ fs []
      \\ fs [state_ok_def]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `k`) \\ fs []
      \\ fs [EVERY_MEM] \\ REPEAT STRIP_TAC
      \\ Q.UNABBREV_TAC `b3` \\ fs [APPLY_UPDATE_THM]
      \\ SRW_TAC [] [] \\ fs [])
    \\ Cases_on`op = RefByte` \\ fs[] THEN1
     (fs [compile_op_def,iEval_def]
      \\ Q.ABBREV_TAC `b3 = ((LEAST ptr. ptr NOTIN FDOM s5.refs) =+
           (LEAST ptr. ptr NOTIN FDOM (bvi_to_bvl t2).refs)) b2`
      \\ CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `b3`
      \\ CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `c`
      \\ fs [iEvalOp_def,do_app_aux_def,bEvalOp_def,LET_DEF]
      \\ Q.ABBREV_TAC `x = (LEAST ptr. ptr NOTIN FDOM s5.refs)`
      \\ Q.ABBREV_TAC `y = LEAST ptr. ptr NOTIN FDOM (bvi_to_bvl t2).refs`
      \\ `~(x IN FDOM s5.refs)` by ALL_TAC THEN1
       (`?p. (\ptr. ptr NOTIN FDOM s5.refs) p` by
          (SIMP_TAC std_ss [] \\ METIS_TAC [NUM_NOT_IN_FDOM])
        \\ IMP_RES_TAC whileTheory.LEAST_INTRO \\ fs []
        \\ REV_FULL_SIMP_TAC std_ss [])
      \\ `~(y IN FDOM t2.refs)` by ALL_TAC THEN1
       (`?p. (\ptr. ptr NOTIN FDOM t2.refs) p` by
          (SIMP_TAC std_ss [] \\ METIS_TAC [NUM_NOT_IN_FDOM])
        \\ IMP_RES_TAC whileTheory.LEAST_INTRO \\ fs [bvi_to_bvl_def]
        \\ REV_FULL_SIMP_TAC (srw_ss()) [bvi_to_bvl_def])
      \\ fs []
      \\ SRW_TAC [] [adjust_bv_def]
      \\ `MAP (adjust_bv b3) env = MAP (adjust_bv b2) env` by ALL_TAC THEN1
       (fs [MAP_EQ_f] \\ REPEAT STRIP_TAC
        \\ MATCH_MP_TAC bv_ok_IMP_adjust_bv_eq
        \\ fs [EVERY_MEM] \\ RES_TAC
        \\ IMP_RES_TAC evaluate_refs_SUBSET
        \\ REPEAT STRIP_TAC THEN1 METIS_TAC [bv_ok_SUBSET_IMP]
        \\ Q.UNABBREV_TAC `b3` \\ fs [APPLY_UPDATE_THM]
        \\ SRW_TAC [] [] \\ fs [])
      \\ `MAP (adjust_bv b3) a = MAP (adjust_bv b2) a` by ALL_TAC THEN1
       (fs [MAP_EQ_f] \\ REPEAT STRIP_TAC
        \\ MATCH_MP_TAC bv_ok_IMP_adjust_bv_eq
        \\ IMP_RES_TAC evaluate_ok \\ REV_FULL_SIMP_TAC std_ss [] \\ fs []
        \\ fs [EVERY_MEM] \\ RES_TAC
        \\ Q.UNABBREV_TAC `b3` \\ fs [APPLY_UPDATE_THM]
        \\ SRW_TAC [] [] \\ fs [])
      \\ `MAP (OPTION_MAP (adjust_bv b2)) s5.globals =
          MAP (OPTION_MAP (adjust_bv b3)) s5.globals` by ALL_TAC THEN1
       (fs [MAP_EQ_f] \\ REPEAT STRIP_TAC
        \\ Cases_on `e` \\ fs []
        \\ MATCH_MP_TAC bv_ok_IMP_adjust_bv_eq
        \\ IMP_RES_TAC evaluate_ok \\ REV_FULL_SIMP_TAC std_ss [] \\ fs []
        \\ fs [state_ok_def,EVERY_MEM] \\ RES_TAC \\ fs []
        \\ Q.UNABBREV_TAC `b3` \\ fs [APPLY_UPDATE_THM]
        \\ SRW_TAC [] [] \\ fs [])
      \\ fs []
      \\ Cases_on`REVERSE a`>>fs[]
      \\ Cases_on`t`>>fs[]
      \\ Cases_on`h'`>>fs[]
      \\ Cases_on`h`>>fs[]
      \\ Cases_on`t'`>>fs[]
      \\ qpat_assum`X = Rval Y`mp_tac
      \\ IF_CASES_TAC \\ fs[] \\ strip_tac \\ rpt var_eq_tac
      \\ Cases_on`a`>>fs[adjust_bv_def]
      \\ STRIP_TAC THEN1 (
        rpt var_eq_tac >>
        simp[Abbr`b3`,adjust_bv_def,APPLY_UPDATE_THM] )
      \\ reverse STRIP_TAC THEN1
       (REPEAT STRIP_TAC \\ UNABBREV_ALL_TAC \\ fs [APPLY_UPDATE_THM]
        \\ SRW_TAC [] []
        \\ IMP_RES_TAC evaluate_refs_SUBSET \\ fs [SUBSET_DEF] \\ RES_TAC)
      \\ simp[bvl_to_bvi_with_refs,bvl_to_bvi_id]
      \\ fs [state_rel_def,bvl_to_bvi_def,bvi_to_bvl_def,FLOOKUP_UPDATE]
      \\ rpt var_eq_tac \\ simp[]
      \\ STRIP_TAC
      THEN1 (Q.UNABBREV_TAC `b3` \\ MATCH_MP_TAC INJ_EXTEND \\ fs [])
      \\ rw[MAP_REVERSE] \\ fs[]
      \\ TRY ( fs[Abbr`b3`,APPLY_UPDATE_THM] \\ NO_TAC)
      \\ TRY ( simp[Abbr`b3`,APPLY_UPDATE_THM] >> rw[] >> NO_TAC)
      \\ TRY ( fs[FLOOKUP_DEF] >> NO_TAC)
      \\ TRY (
        qexists_tac`z`>>simp[]>>
        simp[GSYM MAP_MAP_o] >> rw[] >>
        simp[Abbr`b3`,APPLY_UPDATE_THM] >> rw[] >>
        NO_TAC)
      \\ TRY (
        qmatch_rename_tac`t2.global ≠ SOME p` >>
        fs[FLOOKUP_DEF] >> METIS_TAC[])
      \\ Cases_on `FLOOKUP s5.refs k = NONE` \\ fs [rich_listTheory.MAP_REVERSE]
      \\ (`b3 k <> y` by ALL_TAC THEN1
       (fs[] \\ Q.UNABBREV_TAC `b3` \\ fs [APPLY_UPDATE_THM,FLOOKUP_DEF]
        \\ fs [INJ_DEF] \\ RES_TAC \\ REPEAT STRIP_TAC \\ fs []))
      \\ (`b3 k = b2 k` by ALL_TAC
           THEN1 (Q.UNABBREV_TAC `b3` \\ fs [APPLY_UPDATE_THM,FLOOKUP_DEF]))
      THEN1 ( fs[FLOOKUP_DEF] >> METIS_TAC[INJ_DEF] )
      \\ fs [] \\ Cases_on `FLOOKUP s5.refs k` \\ fs []
      \\ ntac 3 (Q.PAT_ASSUM `!k. bbb` MP_TAC)
      \\ Q.PAT_ASSUM `!k. bbb` (MP_TAC o Q.SPEC `k`) \\ fs []
      \\ Cases_on `x'` \\ fs [] \\ REPEAT STRIP_TAC
      \\ fs [MAP_EQ_f] \\ REPEAT STRIP_TAC
      \\ MATCH_MP_TAC bv_ok_IMP_adjust_bv_eq
      \\ IMP_RES_TAC evaluate_ok \\ REV_FULL_SIMP_TAC std_ss [] \\ fs []
      \\ fs [state_ok_def]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `k`) \\ fs []
      \\ fs [EVERY_MEM] \\ REPEAT STRIP_TAC
      \\ Q.UNABBREV_TAC `b3` \\ fs [APPLY_UPDATE_THM]
      \\ SRW_TAC [] [] \\ fs [])
    \\ Cases_on`∃n. op = Global n` \\ fs[] THEN1 (
         simp[compile_op_def] >>
         fs[bEvalOp_def] >>
         Cases_on`REVERSE a`>>fs[] >>
         imp_res_tac evaluate_IMP_LENGTH >>
         fs[LENGTH_NIL] >>
         simp[iEval_def,compile_int_thm] >>
         Q.LIST_EXISTS_TAC[`t2`,`b2`,`c`] >>
         simp[iEvalOp_def,do_app_aux_def] >>
         BasicProvers.CASE_TAC >> fs[] >>
         simp[bEvalOp_def] >>
         fs[closSemTheory.get_global_def] >>
         imp_res_tac bvlPropsTheory.evaluate_IMP_LENGTH >> fs[LENGTH_NIL] >>
         fs[bEval_def] >> rpt var_eq_tac >>
         fs[iEval_def] >> rpt var_eq_tac >>
         last_x_assum mp_tac >>
         simp[Once state_rel_def] >> strip_tac >>
         simp[LENGTH_REPLICATE,ADD1] >>
         simp[EL_CONS,PRE_SUB1] >>
         reverse IF_CASES_TAC >>
         every_case_tac >> fsrw_tac[ARITH_ss][] >>
         rpt var_eq_tac >>
         simp[EL_APPEND1,EL_MAP,libTheory.the_def,bvl_to_bvi_with_clock,bvl_to_bvi_id] >>
         MATCH_MP_TAC (GEN_ALL bv_ok_IMP_adjust_bv_eq) >>
         qexists_tac`r`>>simp[] >>
         fs[state_ok_def,EVERY_MEM,MEM_EL,PULL_EXISTS] >>
         first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
         simp[])
    \\ Cases_on`∃n. op = SetGlobal n` \\ fs[] THEN1 (
         simp[compile_op_def] >>
         fs[bEvalOp_def] >>
         Cases_on`REVERSE a`>>fs[] >>
         Cases_on`t`>>fs[] >> rw[] >>
         imp_res_tac evaluate_IMP_LENGTH >>
         Cases_on`c1`>>fs[LENGTH_NIL] >> rw[] >>
         every_case_tac >> fs[] >> rw[] >>
         simp[iEval_def] >>
         CONV_TAC(RESORT_EXISTS_CONV(List.rev)) >>
         Q.LIST_EXISTS_TAC[`c`,`b2`] >>
         simp[compile_int_thm] >>
         simp[iEvalOp_def,do_app_aux_def] >>
         imp_res_tac evaluate_global_mono >>
         BasicProvers.CASE_TAC >> fs[] >>
         simp[bEvalOp_def] >>
         rator_x_assum`state_rel`mp_tac >>
         simp[Once state_rel_def] >> strip_tac >>
         simp[ADD1,LENGTH_REPLICATE] >>
         reverse IF_CASES_TAC >>
         fsrw_tac[ARITH_ss][closSemTheory.get_global_def] >>
         simp[bvl_to_bvi_with_refs,bvl_to_bvi_id,LUPDATE_def,GSYM ADD1] >>
         simp[ADD1,LUPDATE_APPEND1] >>
         fs[state_rel_def] >>
         simp[FLOOKUP_UPDATE] >>
         conj_tac >- fs[INJ_DEF] >>
         rw[] >- ( fs[FLOOKUP_DEF] >> rw[] >> METIS_TAC[] ) >>
         qexists_tac`z` >> simp[ADD1,LUPDATE_MAP] >>
         simp[libTheory.the_def])
    \\ Cases_on`op = AllocGlobal` \\ fs[] THEN1 (
         simp[compile_op_def] >>
         fs[bEvalOp_def] >>
         Cases_on`REVERSE a`>>fs[]>>rw[]>>
         imp_res_tac evaluate_IMP_LENGTH >>
         fs[LENGTH_NIL] >> rw[] >>
         rw[iEval_def] >>
         simp[Once inc_clock_def] >>
         simp[find_code_def] >>
         `lookup AllocGlobal_location t1.code = SOME(0,SND AllocGlobal_code)` by (
           fs[state_rel_def] >> simp[AllocGlobal_code_def] ) >>
         simp[] >>
         let
           val th = (Q.ISPEC`inc_clock c (t1:'ffi bviSem$state)`(Q.GEN`s`evaluate_AllocGlobal_code))
         in
         Q.SUBGOAL_THEN `∃p n ls. ^(fst(dest_imp(concl th)))` assume_tac
         THEN1 (
           fs[state_rel_def,REPLICATE_NIL] >>
           simp[Once inc_clock_def] >>
           simp[CopyGlobals_code_def] >>
           Cases_on`t1.global`>>fs[])
         end >>
         rpt(pop_assum CHOOSE_TAC) >>
         first_assum(mp_tac o MATCH_MP evaluate_AllocGlobal_code) >>
         disch_then(qx_choosel_then[`p1`,`ck`]strip_assume_tac) >>
         CONV_TAC(RESORT_EXISTS_CONV(List.rev)) >>
         Q.LIST_EXISTS_TAC[`c+ck+1`,`b2`] >>
         simp[Once inc_clock_def] >>
         `dec_clock 1 (inc_clock (c + (ck+1)) t1) =
          inc_clock ck (inc_clock c t1)` by (
           EVAL_TAC >> simp[state_component_equality] ) >>
         simp[] >>
         ntac 2 (pop_assum kall_tac) >>
         fs[iEval_def] >> var_eq_tac >>
         fs[state_rel_def,LENGTH_REPLICATE,FLOOKUP_UPDATE] >>
         conj_tac >- fs[INJ_DEF] >>
         conj_tac >- (
           gen_tac >>
           Cases_on`FLOOKUP s5.refs k`>>simp[]>>
           `p ≠ b2 k` by ( fs[FLOOKUP_DEF] >> METIS_TAC[]) >>
           `p1 ≠ b2 k` by (
             fs[INJ_DEF,FLOOKUP_DEF] >>
             METIS_TAC[] ) >>
           simp[] >>
           rpt(first_x_assum(qspec_then`k`mp_tac)) >>
           simp[] ) >>
         conj_tac >- (
           fs[FLOOKUP_DEF] >> metis_tac[INJ_DEF]) >>
         IF_CASES_TAC >- (
           qexists_tac`z'`>>simp[libTheory.the_def]>>
           simp[LIST_EQ_REWRITE,LENGTH_REPLICATE,EL_REPLICATE] >>
           Cases >> simp[EL_REPLICATE] ) >>
         qexists_tac`z' * 2`>>simp[libTheory.the_def] >>
         simp[LIST_EQ_REWRITE,LENGTH_REPLICATE,REPLICATE_APPEND] >>
         Cases >> simp[EL_REPLICATE])
    \\ `compile_op op c1 = Op op c1` by
      (Cases_on `op` \\ fs [compile_op_def] \\ NO_TAC)
    \\ fs [iEval_def]
    \\ CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `b2`
    \\ CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `c`
    \\ `EVERY (bv_ok s5.refs) (REVERSE a)` by ALL_TAC
    THEN1 (IMP_RES_TAC evaluate_ok \\ fs [rich_listTheory.EVERY_REVERSE])
    \\ MP_TAC do_app_adjust \\ fs [] \\ REPEAT STRIP_TAC \\ fs [rich_listTheory.MAP_REVERSE])
  THEN1 (* Tick *)
   (`?c1 aux1 n1. compile_exps n [x] = (c1,aux1,n1)` by METIS_TAC [PAIR]
    \\ fs [LET_DEF] \\ SRW_TAC [] [] \\ fs [PULL_FORALL]
    \\ IMP_RES_TAC compile_exps_LENGTH
    \\ `?d. c1 = [d]` by (Cases_on `c1` \\ fs [LENGTH_NIL]) \\ fs []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `n`) \\ fs []
    \\ SRW_TAC [] [iEval_def]
    \\ Cases_on `s.clock = 0` \\ fs [] THEN1
     (SRW_TAC [] [] \\ Q.LIST_EXISTS_TAC [`t1`,`b1`,`0`]
      \\ fs [inc_clock_ZERO] \\ fs [state_rel_def]) \\ fs []
    \\ `t1.clock <> 0 /\ !c. (inc_clock c t1).clock <> 0` by
      (EVAL_TAC \\ fs [state_rel_def] \\ DECIDE_TAC) \\ fs []
    \\ REV_FULL_SIMP_TAC std_ss [dec_clock_inv_clock1]
    \\ `(dec_clock 1 s).refs = s.refs` by EVAL_TAC \\ fs []
    \\ Q.PAT_ASSUM `!xx yy. bbb` (MP_TAC o Q.SPECL [`dec_clock 1 t1`,`b1`])
    \\ REV_FULL_SIMP_TAC std_ss [dec_clock_inv_clock1]
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1 (fs [evaluate_ok_lemma]
           \\ fs [state_rel_def,dec_clock_def,bvlSemTheory.dec_clock_def]
           \\ metis_tac[])
    \\ fs [GSYM PULL_FORALL])
  THEN1 (* Call *)
   (`?c1 aux1 n1. compile_exps n xs = (c1,aux1,n1)` by METIS_TAC [PAIR]
    \\ fs [LET_DEF] \\ SRW_TAC [] [] \\ fs [PULL_FORALL]
    \\ `?res5 s5. evaluate (xs,env,s1) = (res5,s5)` by METIS_TAC [PAIR]
    \\ fs [] \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `n`) \\ fs []
    \\ reverse (Cases_on `res5`) \\ fs [] \\ SRW_TAC [] []
    \\ first_x_assum (MP_TAC o Q.SPECL [`t1`,`b1`]) \\ fs []
    \\ TRY (REPEAT STRIP_TAC \\ IMP_RES_TAC compile_exps_LENGTH \\ fs [iEval_def]
      \\ Q.LIST_EXISTS_TAC [`t2`,`b2`,`c`] \\ fs [] \\ NO_TAC)
    \\ fs [GSYM PULL_FORALL] \\ REPEAT STRIP_TAC
    \\ fs [iEval_def]
    \\ Cases_on `find_code dest a s5.code` \\ fs [] \\ Cases_on `x` \\ fs []
    \\ Cases_on `s5.clock < ticks + 1` \\ fs [] THEN1
     (Q.LIST_EXISTS_TAC [`t2 with clock := 0`,`b2`,`c`] \\ fs []
      \\ SRW_TAC [] []
      \\ TRY (fs [state_rel_def] \\ qexists_tac`array_size'` \\ simp[])
      \\ `t2.clock < ticks + 1` by (fs [state_rel_def] \\ rfs [])
      \\ fs []
      \\ reverse (Cases_on `dest`)
      \\ fs [bvlSemTheory.find_code_def,find_code_def]
      THEN1
       (Cases_on `lookup x s5.code` \\ fs []
        \\ Cases_on `x'` \\ fs [] \\ SRW_TAC [] []
        \\ fs [state_rel_def] \\ RES_TAC
        \\ `?x1 x2 x3. compile_exps n' [r] = (x1,x2,x3)` by METIS_TAC [PAIR]
        \\ fs [LET_DEF])
      \\ `?x1 l1. a = SNOC x1 l1` by METIS_TAC [SNOC_CASES]
      \\ fs [] \\ Cases_on `x1` \\ fs [adjust_bv_def]
      \\ Cases_on `lookup n' s5.code` \\ fs []
      \\ Cases_on `x` \\ fs [] \\ SRW_TAC [] []
      \\ fs [state_rel_def] \\ RES_TAC
      \\ `?x1 x2 x3. compile_exps n'' [r] = (x1,x2,x3)` by METIS_TAC [PAIR]
      \\ fs [LET_DEF])
    \\ Q.MATCH_ASSUM_RENAME_TAC `find_code dest a s5.code = SOME (args,body)`
    \\ `?n7. let (c7,aux7,n8) = compile_exps n7 [body] in
               (find_code (case dest of NONE => NONE | SOME n => SOME (num_stubs + 2 * n))
                 (MAP (adjust_bv b2) a) t2.code =
                 SOME (MAP (adjust_bv b2) args,HD c7)) /\
               aux_code_installed aux7 t2.code /\
               bEvery GoodHandleLet [body]` by ALL_TAC THEN1
     (reverse (Cases_on `dest`) \\ fs [state_rel_def,find_code_def]
      THEN1 (Cases_on `lookup x s5.code` \\ fs [] \\ Cases_on `x'` \\ fs []
        \\ SRW_TAC [] []
        \\ FIRST_X_ASSUM (qspecl_then
             [`x`,`LENGTH a`,`body`]mp_tac) \\ fs []
        \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `n'` \\ fs []
        \\ `?c2 aux2 n2. compile_exps n' [body] = (c2,aux2,n2)` by METIS_TAC [PAIR]
        \\ fs [LET_DEF])
      \\ `?a1 a2. a = SNOC a1 a2` by METIS_TAC [SNOC_CASES]
      \\ fs [] \\ Cases_on `a1` \\ fs []
      \\ FULL_SIMP_TAC std_ss [GSYM SNOC_APPEND,FRONT_SNOC]
      \\ Cases_on `lookup n' s5.code` \\ fs [] \\ Cases_on `x` \\ fs []
      \\ SRW_TAC [] []
      \\ Q.PAT_ASSUM `!x1 x2. bbb` (MP_TAC o Q.SPECL [`n'`]) \\ fs []
      \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `n''`
      \\ `?c2 aux2 n2. compile_exps n'' [body] = (c2,aux2,n2)` by METIS_TAC [PAIR]
      \\ fs [LET_DEF,adjust_bv_def])
    \\ `?c7 aux7 n8. compile_exps n7 [body] = (c7,aux7,n8)` by METIS_TAC [PAIR]
    \\ fs [LET_DEF]
    \\ `¬(t2.clock < ticks + 1)` by (fs [state_rel_def] \\ REV_FULL_SIMP_TAC std_ss [])
    \\ fs [] \\ IMP_RES_TAC compile_exps_LENGTH
    \\ `?d. c7 = [d]` by (Cases_on `c7` \\ fs [LENGTH_NIL]) \\ fs []
    \\ Q.PAT_ASSUM `!nn mm. bbb` (MP_TAC o Q.SPEC `n7`) \\ fs []
    \\ STRIP_TAC
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`dec_clock (ticks + 1) t2`,`b2`]) \\ fs []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (`(dec_clock (ticks + 1) t2).code = t2.code` by (EVAL_TAC \\ fs [])
      \\ `(dec_clock (ticks + 1) t2).refs = t2.refs` by (EVAL_TAC \\ fs [])
      \\ IMP_RES_TAC evaluate_ok
      \\ fs [evaluate_ok_lemma] \\ REV_FULL_SIMP_TAC std_ss []
      \\ STRIP_TAC THEN1
        (fs [state_rel_def,dec_clock_def,bvlSemTheory.dec_clock_def] >>
         METIS_TAC[])
      \\ IMP_RES_TAC find_code_EVERY_IMP
      \\ imp_res_tac evaluate_global_mono
      \\ fs[])
    \\ STRIP_TAC
    \\ Q.LIST_EXISTS_TAC [`t2'`,`b2'`,`c' + c`] \\ fs []
    \\ IMP_RES_TAC evaluate_inv_clock
    \\ fs [inc_clock_ADD]
    \\ REV_FULL_SIMP_TAC std_ss []
    \\ `MAP (adjust_bv b2') env = MAP (adjust_bv b2) env` by
     (fs [MAP_EQ_f] \\ REPEAT STRIP_TAC
      \\ MATCH_MP_TAC (bv_ok_IMP_adjust_bv_eq |> GEN_ALL)
      \\ Q.EXISTS_TAC `s5` \\ fs [bvlSemTheory.dec_clock_def]
      \\ IMP_RES_TAC evaluate_refs_SUBSET
      \\ IMP_RES_TAC bv_ok_SUBSET_IMP \\ fs [EVERY_MEM] \\ NO_TAC)
    \\ `(inc_clock c' t2).code = t2.code` by (EVAL_TAC \\ fs []) \\ fs []
    \\ `¬((inc_clock c' t2).clock < ticks + 1)` by (fs [inc_clock_def] \\ decide_tac)
    \\ fs []
    \\ REV_FULL_SIMP_TAC std_ss [dec_clock_inv_clock]
    \\ fs [bvlSemTheory.dec_clock_def]
    \\ IMP_RES_TAC evaluate_refs_SUBSET \\ fs [SUBSET_DEF]
    \\ Cases_on `res` \\ fs []
    \\ Cases_on`e` \\ fs[]));

val _ = save_thm("compile_exps_correct",compile_exps_correct);

(* composed compiler correctness *)

val MAP_FST_optimise = Q.store_thm("MAP_FST_optimise[simp]",
  `MAP FST (optimise prog) = MAP FST prog`,
  simp[optimise_def,MAP_MAP_o,o_DEF,UNCURRY,ETA_AX]);

val ALOOKUP_optimise_lookup = Q.store_thm("ALOOKUP_optimise_lookup",
  `lookup n ls = SOME (a,b) ⇒
   ALOOKUP (optimise (toAList ls)) n = SOME (a,HD(compile a [compile_exp b]))`,
  rw[] >>
  Cases_on`ALOOKUP (optimise (toAList ls)) n` >- (
    imp_res_tac ALOOKUP_FAILS >>
    `¬MEM n (MAP FST (optimise (toAList ls)))` by METIS_TAC[MEM_MAP,FST,PAIR] >>
    fs[toAList_domain] >>
    METIS_TAC[domain_lookup] ) >>
  imp_res_tac ALOOKUP_MEM >>
  fs[optimise_def,MEM_MAP,PULL_EXISTS,EXISTS_PROD,MEM_toAList] >> fs[]);

val optimise_evaluate = Q.store_thm("optimise_evaluate",
  `∀xs env s res s'.
     evaluate (xs,env,s) = (res,s') ∧
     res ≠ Rerr (Rabort Rtype_error) ⇒
     evaluate (xs,env,s with code := fromAList (optimise (toAList s.code))) =
       (res,s' with code := fromAList (optimise (toAList s.code)))`,
  recInduct bvlSemTheory.evaluate_ind >>
  rw[bvlSemTheory.evaluate_def] >>
  TRY (
    qcase_tac`Boolv T = HD _` >>
    BasicProvers.CASE_TAC >> fs[] >>
    BasicProvers.CASE_TAC >> fs[] >>
    rpt(IF_CASES_TAC >> fs[]) >>
    TRY(qpat_assum`_ = HD _`(assume_tac o SYM))>>fs[]>>
    every_case_tac >> fs[] >> rpt var_eq_tac >> fs[] >> rfs[] >>
    imp_res_tac bvlPropsTheory.evaluate_code >> fs[] >>
    TRY(qpat_assum`_ = HD _`(assume_tac o SYM))>>fs[] ) >>
  TRY (
    qcase_tac`bvlSem$do_app` >>
    every_case_tac >> fs[] >> rpt var_eq_tac >> fs[] >> rfs[] >>
    imp_res_tac bvlPropsTheory.evaluate_code >> fs[] >>
    imp_res_tac bvlPropsTheory.do_app_with_code >>
    imp_res_tac bvlPropsTheory.do_app_with_code_err >>
    fs[domain_fromAList] >>
    fs[SUBSET_DEF,toAList_domain] >>
    qmatch_assum_rename_tac`bvlSem$do_app op _ z = _` >>
    rpt(first_x_assum(qspec_then`z.code`mp_tac)) >> simp[] >>
    NO_TAC) >>
  every_case_tac >> fs[] >> rpt var_eq_tac >> fs[] >> rfs[] >>
  imp_res_tac bvlPropsTheory.evaluate_code >> fs[] >>
  Cases_on`dest`>>fs[find_code_def]>>
  every_case_tac>>fs[]>>rw[]>>
  fs[lookup_fromAList] >>
  imp_res_tac ALOOKUP_optimise_lookup >> fs[] >>
  rpt var_eq_tac >>
  qmatch_assum_abbrev_tac`bvlSem$evaluate (zxs,zenv,zs) = (_,_ with code := _)` >>
  qspecl_then[`zxs`,`zenv`,`zs`]mp_tac bvl_constProofTheory.compile_exps_thm >>
  simp[Abbr`zxs`,bvl_constTheory.compile_exps_def] >> strip_tac >>
  unabbrev_all_tac >>
  simp[bvl_handleTheory.compile_HD_SING] >>
  drule bvl_handleProofTheory.compile_correct >>
  simp[LENGTH_FRONT,PRE_SUB1]);

val fromAList_optimise = Q.prove(
  `fromAList (optimise p) =
   map (λ(a,e). (a, HD (compile a [compile_exp e]))) (fromAList p)`,
  simp[map_fromAList,optimise_def] >>
  rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
  simp[FUN_EQ_THM,UNCURRY]);

val optimise_semantics = Q.store_thm("optimise_semantics",
  `semantics ffi0 (fromAList prog) start ≠ Fail ⇒
   semantics ffi0 (fromAList (optimise prog)) start =
   semantics ffi0 (fromAList prog) start`,
  simp[bvlSemTheory.semantics_def] >>
  IF_CASES_TAC >> fs[] >>
  `∀k. evaluate ([Call 0 (SOME start) []],[],initial_state ffi0 (fromAList (optimise prog)) k) =
    let (r,s) = bvlSem$evaluate ([Call 0 (SOME start) []],[],initial_state ffi0 (fromAList prog) k) in
      (r, s with code := fromAList (optimise (toAList s.code)))` by (
    gen_tac >> simp[] >>
    qmatch_abbrev_tac`_ = (_ (bvlSem$evaluate (xs,env,s)))` >>
    Q.ISPECL_THEN[`xs`,`env`,`s`]mp_tac optimise_evaluate >>
    Cases_on`evaluate (xs,env,s)` >>
    simp[Abbr`s`] >>
    discharge_hyps >- METIS_TAC[FST] >>
    fs[fromAList_optimise,fromAList_toAList,wf_fromAList] >>
    fs[GSYM fromAList_optimise] >>
    imp_res_tac bvlPropsTheory.evaluate_code >>
    fs[bvlSemTheory.state_component_equality] >>
    fs[fromAList_optimise,fromAList_toAList,wf_fromAList] ) >>
  simp[] >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  fs[UNCURRY,LET_THM] >>
  reverse conj_tac >- (
    simp_tac(srw_ss()++QUANT_INST_ss[pair_default_qp])[] ) >>
  gen_tac >> strip_tac >> var_eq_tac >>
  asm_simp_tac(srw_ss()++QUANT_INST_ss[pair_default_qp])[] >>
  reverse conj_tac >- METIS_TAC[] >>
  gen_tac >> strip_tac >>
  qmatch_assum_abbrev_tac`FST (bvlSem$evaluate (e1,v1,s1)) ≠ Rerr _` >>
  qpat_assum`_ ≠ _`mp_tac >>
  qmatch_assum_abbrev_tac`FST (bvlSem$evaluate (e1,v1,s2)) ≠ _` >>
  strip_tac >>
  qmatch_assum_rename_tac`Abbrev(s1 = _ _ _ k1)` >>
  qmatch_assum_rename_tac`Abbrev(s2 = _ _ _ k2)` >>
  qspecl_then[`k1`,`k2`]mp_tac LESS_EQ_CASES >>
  simp[LESS_EQ_EXISTS] >>
  qspecl_then[`e1`,`v1`,`s1`]mp_tac bvlPropsTheory.evaluate_add_clock >>
  simp_tac(srw_ss()++QUANT_INST_ss[pair_default_qp])[] >> simp[] >>
  qspecl_then[`e1`,`v1`,`s2`]mp_tac bvlPropsTheory.evaluate_add_clock >>
  simp_tac(srw_ss()++QUANT_INST_ss[pair_default_qp])[] >> simp[] >>
  simp[bvlPropsTheory.inc_clock_def] >>
  simp[Abbr`s1`,Abbr`s2`] >>
  rw[] >>
  rpt(first_x_assum(qspec_then`p`mp_tac))>>
  fsrw_tac[ARITH_ss][]);

val compile_single_evaluate = Q.store_thm("compile_single_evaluate",
  `evaluate ([Call 0 (SOME start) []],[],s1) = (res,s2) ∧
   state_rel b1 s1 t1 ∧ IS_SOME t1.global ∧ state_ok s1 ∧
   res ≠ Rerr (Rabort Rtype_error)
   ⇒
   ∃ck b2 t2.
     evaluate ([Call 0 (SOME (num_stubs + 2 * start))[] NONE],[],inc_clock ck t1) =
       (map_result (MAP (adjust_bv b2)) (adjust_bv b2) res,t2) ∧
     state_rel b2 s2 t2`,
  rw[] >>
  fs[bvlSemTheory.evaluate_def] >>
  fs[find_code_def] >>
  every_case_tac >> fs[] >>
  rw[bviSemTheory.evaluate_def,find_code_def] >>
  first_assum(drule o last o CONJUNCTS o CONV_RULE(REWR_CONV state_rel_def)) >>
  simp[] >> strip_tac >> split_pair_tac >> fs[] >- (
    qpat_assum`0n = _`(assume_tac o SYM) >> simp[] >>
    `t1.clock = 0` by fs[state_rel_def] >> simp[] >>
    simp[inc_clock_def] >>
    qexists_tac`0`>>simp[]>>
    qexists_tac`b1` >>
    fs[state_rel_def] ) >>
  `t1.clock ≠ 0` by fs[state_rel_def] >> simp[] >>
  drule compile_exps_correct >> simp[] >>
  disch_then drule >>
  `state_rel b1 (dec_clock 1 s1) (dec_clock 1 t1)` by (
    fs[state_rel_def,bvlSemTheory.dec_clock_def,bviSemTheory.dec_clock_def] ) >>
  disch_then drule >>
  discharge_hyps >- (
    fs[bvlSemTheory.dec_clock_def,bviSemTheory.dec_clock_def] >>
    fs[state_ok_def] ) >>
  strip_tac >>
  imp_res_tac compile_exps_SING >> var_eq_tac >> simp[] >>
  qexists_tac`c` >>
  `dec_clock 1 (inc_clock c t1) = inc_clock c (dec_clock 1 t1)` by (
    EVAL_TAC >> simp[state_component_equality] ) >>
  simp[] >>
  Cases_on`res`>>simp[] >- METIS_TAC[] >>
  Cases_on`e`>>simp[] >> METIS_TAC[]);

val bvi_stubs_evaluate = Q.store_thm("bvi_stubs_evaluate",
  `∀start ffi0 code k. 0 < k ∧ num_stubs ≤ start ⇒
  let t0 = <| global := SOME 0; ffi := ffi0; clock := k; code := fromAList (bvi_stubs start ++ code);
              refs := FEMPTY |+ (0,ValueArray [Number 1]) |> in
   evaluate ([Call 0 (SOME InitGlobals_location) [] NONE],[],initial_state ffi0 (fromAList (bvi_stubs start ++ code)) (k+1)) =
   evaluate ([Call 0 (SOME start) [] NONE],[],t0)`,
  rw[bviSemTheory.evaluate_def,find_code_def,lookup_fromAList,ALOOKUP_APPEND] >>
  rw[Once bvi_stubs_def] >>
  TRY (pop_assum(assume_tac o CONV_RULE EVAL)>>fs[]>>NO_TAC) >>
  simp[InitGlobals_code_def] >>
  simp[bviSemTheory.evaluate_def,bviSemTheory.do_app_def,bviSemTheory.do_app_aux_def,small_enough_int_def] >>
  simp[bvlSemTheory.do_app_def,find_code_def,lookup_fromAList,ALOOKUP_APPEND] >>
  reverse BasicProvers.CASE_TAC >- (
    `F` suffices_by rw[] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[bvi_stubs_def] >>
    qpat_assum`num_stubs ≤ _`mp_tac >>
    rpt var_eq_tac >> EVAL_TAC ) >>
  BasicProvers.CASE_TAC >- (
    simp[Abbr`t0`] >>
    simp[lookup_fromAList,ALOOKUP_APPEND] >>
    simp[bviSemTheory.state_component_equality] >>
    unabbrev_all_tac >> EVAL_TAC >> simp[]) >>
  Cases_on`x`>>simp[] >>
  reverse IF_CASES_TAC >> fs[] >- (
    simp[Abbr`t0`,lookup_fromAList,ALOOKUP_APPEND] >>
    simp[bviSemTheory.state_component_equality] >>
    unabbrev_all_tac >> EVAL_TAC >> simp[] ) >>
  simp[] >>
  var_eq_tac >>
  simp[Once bviSemTheory.dec_clock_def] >>
  fs[bvl_to_bvi_def,bvi_to_bvl_def,bviSemTheory.dec_clock_def,bviSemTheory.initial_state_def] >>
  simp[Abbr`t0`,lookup_fromAList,ALOOKUP_APPEND] >>
  REWRITE_TAC[ONE,REPLICATE] >> simp[] >>
  BasicProvers.CASE_TAC >> simp[] >>
  BasicProvers.CASE_TAC >> simp[] >>
  BasicProvers.CASE_TAC >> simp[]);

val sorted_lt_append =
  Q.ISPEC`prim_rec$<`SORTED_APPEND
  |> SIMP_RULE std_ss [transitive_LESS]

val compile_exps_aux_sorted = Q.store_thm("compile_exps_aux_sorted",
  `∀n es c aux n1. compile_exps n es = (c,aux,n1) ⇒
   SORTED $< (MAP FST aux) ∧ EVERY (between n n1) (MAP FST aux) ∧ n ≤ n1`,
   ho_match_mp_tac compile_exps_ind >>
   simp[compile_exps_def] >> rw[] >>
   rpt (split_pair_tac >> fs[]) >> rw[] >>
   rpt ((sorted_lt_append |> match_mp_tac) >> fs[] >> rw[] ) >>
   fs[EVERY_MEM,between_def] >>
   rw[] >> res_tac >> decide_tac);

val aux_code_installed_sublist = Q.store_thm("aux_code_installed_sublist",
  `∀aux ls.
    IS_SUBLIST ls (MAP (λ(k,args,p). (num_stubs + 2 * k + 1,args,p)) aux) ∧ ALL_DISTINCT (MAP FST ls) ⇒
    aux_code_installed aux (fromAList ls)`,
  Induct >> simp[aux_code_installed_def] >>
  qx_gen_tac`p`>>PairCases_on`p`>>
  Cases >> simp[IS_SUBLIST] >> strip_tac >- (
    simp[aux_code_installed_def,lookup_fromAList] >>
    first_x_assum match_mp_tac >>
    var_eq_tac >> fs[] >>
    fs[IS_SUBLIST_APPEND,IS_PREFIX_APPEND] >>
    CONV_TAC SWAP_EXISTS_CONV >>
    qexists_tac`l`>>simp[] ) >>
  simp[aux_code_installed_def,lookup_fromAList] >>
  reverse conj_tac >- (
    first_x_assum match_mp_tac >> fs[] >>
    fs[IS_SUBLIST_APPEND] >>
    CONV_TAC SWAP_EXISTS_CONV >>
    qexists_tac`l'`>>simp[] ) >>
  fs[IS_SUBLIST_APPEND] >>
  PairCases_on`h` >>
  simp[ALOOKUP_APPEND] >>
  var_eq_tac >> fs[] >>
  fs[ALL_DISTINCT_APPEND] >>
  BasicProvers.CASE_TAC >>
  imp_res_tac ALOOKUP_MEM >>
  fs[MEM_MAP,PULL_EXISTS,EXISTS_PROD] >>
  METIS_TAC[PAIR])

val compile_list_distinct_locs = Q.store_thm("compile_list_distinct_locs",
  `∀n prog code n'.
     ALL_DISTINCT (MAP FST prog) ∧
     compile_list n prog = (code,n') ⇒
     ALL_DISTINCT (MAP FST code) ∧
     EVERY (between (num_stubs + 2 * n) (num_stubs + 2 * n')) (FILTER (λn. ODD (n - num_stubs)) (MAP FST code)) ∧
     FILTER (λn. EVEN (n - num_stubs)) (MAP FST code) = MAP (λn. num_stubs + 2 * n) (MAP FST prog) ∧
     (* redundant, but useful *) EVERY ($<= num_stubs) (MAP FST code) ∧
     n ≤ n'`,
  Induct_on`prog`>>simp[compile_list_def]>>
  qx_gen_tac`p`>>PairCases_on`p`>>
  rpt gen_tac >> strip_tac >>
  split_pair_tac >> fs[] >>
  split_pair_tac >> fs[] >>
  fs[compile_single_def,LET_THM] >>
  split_pair_tac >> fs[] >>
  imp_res_tac compile_exps_aux_sorted >>
  rpt var_eq_tac >>
  first_x_assum drule >> strip_tac >>
  simp[] >>
  simp[MAP_MAP_o,o_DEF,UNCURRY] >>
  simp[EVERY_MAP] >>
  reverse conj_tac >- (
    reverse conj_tac >- (
      simp[FILTER_APPEND] >>
      reverse IF_CASES_TAC >- METIS_TAC[EVEN_EXISTS] >>
      simp[FILTER_MAP,o_DEF] >>
      simp[MAP_MAP_o,o_DEF,UNCURRY,FILTER_EQ_NIL] >>
      simp[EVERY_MEM] >>
      METIS_TAC[EVEN_ODD,ODD_EXISTS,ADD1] ) >>
    fsrw_tac[ARITH_ss][EVERY_FILTER,between_def,EVERY_MAP] >>
    fs[EVERY_MEM] >> rw[] >> res_tac >>
    fsrw_tac[ARITH_ss][] >>
    METIS_TAC[EVEN_ODD,EVEN_EXISTS] ) >>
  simp[ALL_DISTINCT_APPEND] >>
  reverse conj_tac >- (
    fs[EVERY_MEM,PULL_EXISTS,MEM_MAP,EXISTS_PROD] >>
    rw[] >> spose_not_then strip_assume_tac >>
    res_tac >> fs[between_def] >- (
      fs[MEM_FILTER,MEM_MAP,PULL_EXISTS,EXISTS_PROD] >>
      res_tac >> fsrw_tac[ARITH_ss][] >>
      pop_assum mp_tac >> simp[] >>
      pop_assum mp_tac >> simp[] >>
      METIS_TAC[ODD_EXISTS,ADD1] ) >>
    qmatch_assum_abbrev_tac`l1 = l2` >>
    qmatch_assum_abbrev_tac`MEM x l3` >>
    `MEM (FST x) l1` by (
      unabbrev_all_tac >>
      simp[MEM_FILTER,MEM_MAP,EXISTS_PROD] >>
      METIS_TAC[EVEN_EXISTS] ) >>
    `MEM (FST x) l2` by METIS_TAC[] >>
    pop_assum mp_tac >>
    unabbrev_all_tac >> simp[MEM_MAP,EXISTS_PROD] >>
    METIS_TAC[EQ_MULT_LCANCEL,DECIDE``2 ≠ 0n``] ) >>
  reverse conj_tac >- (
    simp[MEM_MAP,EXISTS_PROD] >>
    spose_not_then strip_assume_tac >> fs[] >>
    qmatch_assum_rename_tac`2 * a + num_stubs = 2 * b + (num_stubs + 1)` >>
    `2 * a = 2 * b + 1` by decide_tac >>
    METIS_TAC[EVEN_ODD,EVEN_EXISTS,ODD_EXISTS,ADD1] ) >>
  qmatch_abbrev_tac`ALL_DISTINCT (MAP f aux)` >>
  `∃g. MAP f aux = MAP g (MAP FST aux) ∧
       (∀x y. g x = g y ⇒ x = y)` by (
    simp[MAP_EQ_f,MAP_MAP_o,Abbr`f`] >>
    simp[FORALL_PROD,GSYM SKOLEM_THM,PULL_FORALL] >>
    qexists_tac`λx. 2 * x + num_stubs + 1` >> simp[]) >>
  first_assum(CHANGED_TAC o SUBST1_TAC) >>
  MATCH_MP_TAC ALL_DISTINCT_MAP_INJ >>
  conj_tac >- METIS_TAC[] >>
  irule SORTED_ALL_DISTINCT >>
  METIS_TAC[irreflexive_def,prim_recTheory.LESS_REFL,transitive_LESS]);

val compile_list_imp = Q.prove(
  `∀n prog code n' name arity exp.
     compile_list n prog = (code,n') ∧
     ALOOKUP prog name = SOME (arity,exp) ⇒
     ∃n0 c aux n1.
     compile_exps n0 [exp] = ([c],aux,n1) ∧
     ALOOKUP code (2 * name + num_stubs) = SOME (arity,c) ∧
     IS_SUBLIST code (MAP (λ(k,args,p). (num_stubs + 2 * k + 1,args,p)) aux)`,
  Induct_on`prog` >> simp[] >>
  qx_gen_tac`p`>>PairCases_on`p`>>
  simp[compile_list_def] >>
  rpt gen_tac >> strip_tac >>
  split_pair_tac >> fs[] >>
  split_pair_tac >> fs[] >>
  rpt var_eq_tac >>
  fs[compile_single_def,LET_THM] >>
  split_pair_tac >> fs[] >>
  rpt var_eq_tac >>
  BasicProvers.FULL_CASE_TAC >- (
    fs[] >> rpt var_eq_tac >>
    imp_res_tac compile_exps_SING >> var_eq_tac >>
    asm_exists_tac >> simp[] >>
    conj_tac >- (
      simp[ALOOKUP_APPEND] >>
      BasicProvers.CASE_TAC >>
      imp_res_tac ALOOKUP_MEM >>
      fs[MEM_MAP,EXISTS_PROD,PULL_EXISTS] >>
      qmatch_assum_rename_tac`2 * a + num_stubs = 2 * b + (num_stubs + 1)` >>
      `2 * a = 2 * b + 1` by decide_tac >>
      METIS_TAC[EVEN_ODD,EVEN_EXISTS,ODD_EXISTS,ADD1] ) >>
    MATCH_MP_TAC IS_PREFIX_IS_SUBLIST >>
    simp[IS_PREFIX_APPEND] ) >>
  first_x_assum drule >>
  disch_then drule >> strip_tac >>
  asm_exists_tac >> simp[] >>
  conj_tac >- (
    simp[ALOOKUP_APPEND] >>
    BasicProvers.CASE_TAC >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,EXISTS_PROD,PULL_EXISTS] >>
    qmatch_assum_rename_tac`2 * a + num_stubs = 2 * b + (num_stubs + 1)` >>
    `2 * a = 2 * b + 1` by decide_tac >>
    METIS_TAC[EVEN_ODD,EVEN_EXISTS,ODD_EXISTS,ADD1] ) >>
  fs[IS_SUBLIST_APPEND] >>
  imp_res_tac compile_exps_SING >> fs[] >>
  rpt var_eq_tac >>
  fsrw_tac[ARITH_ss][] >>
  METIS_TAC[APPEND_ASSOC]);

val compile_prog_evaluate = Q.store_thm("compile_prog_evaluate",
  `compile_prog start n prog = (start', prog', n') ∧
   evaluate ([Call 0 (SOME start) []],[],initial_state ffi0 (fromAList prog) k) = (r,s) ∧
   0 < k ∧
   ALL_DISTINCT (MAP FST prog) ∧
   bEvery GoodHandleLet (MAP (SND o SND) prog) ∧
   r ≠ Rerr (Rabort Rtype_error)
   ⇒
   ∃ck b2 s2.
   evaluate ([Call 0 (SOME start') [] NONE],[],initial_state ffi0 (fromAList prog') (k+ck)) =
     (map_result (MAP (adjust_bv b2)) (adjust_bv b2) r,s2) ∧
   state_rel b2 s s2`,
  rw[compile_prog_def,LET_THM] >>
  split_pair_tac >> fs[] >> var_eq_tac >>
  `num_stubs ≤ num_stubs + 2 * start` by simp[] >>
  drule (GEN_ALL compile_single_evaluate) >>
  simp[state_ok_def] >>
  qspecl_then[`num_stubs + 2 * start`,`ffi0`,`code`]
    (fn tmp =>
      disch_then(fn th => subterm (mp_tac o C SPEC th o #2 o boolSyntax.dest_let) (concl tmp)))
    bvi_stubs_evaluate >>
  simp[Once state_rel_def,FLOOKUP_UPDATE] >>
  discharge_hyps >- (
    conj_tac >- (
      qexists_tac`1`>>simp[]>>EVAL_TAC ) >>
    rpt var_eq_tac >>
    simp[lookup_fromAList,ALOOKUP_APPEND] >>
    simp[bvi_stubs_def] >>
    IF_CASES_TAC >> simp[] >- (
      `F` suffices_by rw[] >> pop_assum mp_tac >> EVAL_TAC ) >>
    rpt gen_tac >> strip_tac >>
    rpt (
      IF_CASES_TAC >- (
        `F` suffices_by rw[] >> pop_assum mp_tac >> EVAL_TAC >> decide_tac)) >>
    simp[] >>
    imp_res_tac compile_list_imp >>
    qmatch_assum_rename_tac`compile_exps nn _ = _` >>
    qexists_tac`nn` >> simp[] >>
    reverse conj_tac >- (
      imp_res_tac ALOOKUP_MEM >>
      rator_x_assum`bEvery`mp_tac >>
      simp[Once bEvery_EVERY] >>
      simp[EVERY_MEM,MEM_MAP,PULL_EXISTS,EXISTS_PROD] >>
      METIS_TAC[] ) >>
    match_mp_tac aux_code_installed_sublist >>
    conj_tac >- (
      fs[IS_SUBLIST_APPEND] >>
      METIS_TAC[CONS_APPEND,APPEND_ASSOC] ) >>
    imp_res_tac compile_list_distinct_locs >>
    simp[] >> rw[] >> (TRY (EVAL_TAC >> NO_TAC)) >>
    spose_not_then strip_assume_tac >> fs[EVERY_MEM] >>
    res_tac >> pop_assum mp_tac >> EVAL_TAC ) >>
  strip_tac >>
  `0 < ck + k` by simp[] >>
  drule (GEN_ALL bvi_stubs_evaluate) >>
  disch_then drule >>
  disch_then(qspecl_then[`ffi0`,`code`]mp_tac) >>
  simp[] >>
  rpt var_eq_tac >>
  fsrw_tac[ARITH_ss][inc_clock_def] >>
  PROVE_TAC[ADD_ASSOC,ADD_COMM]);

val compile_prog_semantics = Q.store_thm("compile_prog_semantics",
  `compile_prog start n prog = (start', prog', n') ∧
   ALL_DISTINCT (MAP FST prog) ∧
   bEvery GoodHandleLet (MAP (SND o SND) prog) ∧
   semantics ffi0 (fromAList prog) start ≠ Fail
   ⇒
   semantics ffi0 (fromAList prog') start' =
   semantics ffi0 (fromAList prog) start`,
  simp[GSYM AND_IMP_INTRO] >> ntac 3 strip_tac >>
  simp[bvlSemTheory.semantics_def] >>
  IF_CASES_TAC >> fs[] >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  conj_tac >- (
    qx_gen_tac`ffi'` >> strip_tac >>
    drule (GEN_ALL compile_prog_evaluate) >>
    disch_then drule >> simp[] >>
    discharge_hyps_keep >- (
      conj_tac >- (
        Cases_on`k`>>simp[] >>
        fs[bvlSemTheory.evaluate_def] >>
        every_case_tac >> fs[] ) >>
      strip_tac >> fs[] >>
      METIS_TAC[FST] ) >>
    strip_tac >>
    `s.ffi = s2.ffi` by fs[state_rel_def] >>
    simp[bviSemTheory.semantics_def] >>
    IF_CASES_TAC >> fs[] >- (
      qmatch_assum_abbrev_tac`FST q = _` >>
      Cases_on`q`>>fs[markerTheory.Abbrev_def] >>
      pop_assum(assume_tac o SYM) >>
      imp_res_tac bviPropsTheory.evaluate_add_clock >> rfs[] >>
      qspecl_then[`ck+k`,`k'`]strip_assume_tac LESS_EQ_CASES >>
      fs[LESS_EQ_EXISTS] >>
      qmatch_assum_rename_tac`_ = _ + (ex:num)` >>
      rpt var_eq_tac >> rfs[] >>
      rpt(first_x_assum(qspec_then`ex`mp_tac)) >>
      simp[inc_clock_def] >>
      fsrw_tac[ARITH_ss][]) >>
    DEEP_INTRO_TAC some_intro >> simp[] >>
    conj_tac >- (
      qx_gen_tac`ffi` >> strip_tac >>
      imp_res_tac bviPropsTheory.evaluate_add_clock >>
      qspecl_then[`ck+k`,`k'`]strip_assume_tac LESS_EQ_CASES >>
      fs[LESS_EQ_EXISTS] >>
      qmatch_assum_rename_tac`_ = _ + (ex:num)` >>
      rpt var_eq_tac >> rfs[] >>
      rpt(first_x_assum(qspec_then`ex`mp_tac)) >>
      simp[inc_clock_def] >>
      fsrw_tac[ARITH_ss][]) >>
    simp_tac(srw_ss()++QUANT_INST_ss[pair_default_qp])[] >>
    qexists_tac`ck+k`>>simp[]) >>
  strip_tac >>
  simp[bviSemTheory.semantics_def] >>
  IF_CASES_TAC >> fs[] >- (
    last_x_assum(qspec_then`k`strip_assume_tac) >>
    qmatch_assum_abbrev_tac`FST q ≠ _` >>
    Cases_on`q`>>fs[markerTheory.Abbrev_def] >>
    pop_assum(assume_tac o SYM) >>
    drule (GEN_ALL compile_prog_evaluate) >>
    disch_then drule >> simp[] >>
    conj_tac >- (
      Cases_on`k`>>simp[] >>
      fs[bviSemTheory.evaluate_def] >>
      every_case_tac >> fs[] >>
      fs[compile_prog_def,LET_THM] >>
      split_pair_tac >> fs[] >> rpt var_eq_tac >>
      fs[find_code_def,lookup_fromAList,ALOOKUP_APPEND,bvi_stubs_def] >>
      every_case_tac >> fs[] >>
      TRY(rpt(qpat_assum`_ = _`mp_tac) >> EVAL_TAC >> NO_TAC) >>
      fs[InitGlobals_code_def]) >>
    spose_not_then strip_assume_tac >>
    qmatch_assum_abbrev_tac`FST q = _` >>
    Cases_on`q`>>fs[markerTheory.Abbrev_def] >>
    pop_assum(assume_tac o SYM) >>
    imp_res_tac bviPropsTheory.evaluate_add_clock >> rfs[] >>
    first_x_assum(qspec_then`ck`mp_tac) >>
    simp[inc_clock_def]) >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  conj_tac >- (
    spose_not_then strip_assume_tac >>
    fsrw_tac[QUANT_INST_ss[pair_default_qp]][] >>
    last_x_assum(qspec_then`k`strip_assume_tac) >>
    qmatch_assum_abbrev_tac`FST q = _` >>
    Cases_on`q`>>fs[markerTheory.Abbrev_def] >>
    pop_assum(assume_tac o SYM) >>
    drule (GEN_ALL compile_prog_evaluate) >>
    disch_then drule >> simp[] >>
    conj_tac >- (
      Cases_on`k`>>simp[] >>
      fs[bviSemTheory.evaluate_def] >>
      every_case_tac >> fs[]) >>
    spose_not_then strip_assume_tac >>
    imp_res_tac evaluate_add_clock >>
    first_x_assum(qspec_then`ck`mp_tac) >>
    simp[inc_clock_def] ) >>
  strip_tac >>
  qmatch_abbrev_tac`build_lprefix_lub l1 = build_lprefix_lub l2` >>
  `(lprefix_chain l1 ∧ lprefix_chain l2) ∧ equiv_lprefix_chain l1 l2`
    suffices_by metis_tac[build_lprefix_lub_thm,lprefix_lub_new_chain,unique_lprefix_lub] >>
  conj_asm1_tac >- (
    UNABBREV_ALL_TAC >>
    conj_tac >>
    Ho_Rewrite.ONCE_REWRITE_TAC[GSYM o_DEF] >>
    REWRITE_TAC[IMAGE_COMPOSE] >>
    match_mp_tac prefix_chain_lprefix_chain >>
    simp[prefix_chain_def,PULL_EXISTS] >>
    qx_genl_tac[`k1`,`k2`] >>
    qspecl_then[`k1`,`k2`]mp_tac LESS_EQ_CASES >>
    metis_tac[
      LESS_EQ_EXISTS,
      bviPropsTheory.initial_state_with_simp,
      bvlPropsTheory.initial_state_with_simp,
      bviPropsTheory.evaluate_add_to_clock_io_events_mono
        |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["s"]))
        |> Q.SPEC`s with clock := k`
        |> SIMP_RULE (srw_ss())[bviPropsTheory.inc_clock_def],
      bvlPropsTheory.evaluate_add_to_clock_io_events_mono
        |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["s"]))
        |> Q.SPEC`s with clock := k`
        |> SIMP_RULE (srw_ss())[bvlPropsTheory.inc_clock_def]]) >>
  simp[equiv_lprefix_chain_thm] >>
  unabbrev_all_tac >> simp[PULL_EXISTS] >>
  ntac 2 (pop_assum kall_tac) >>
  simp[LNTH_fromList,PULL_EXISTS] >>
  simp[GSYM FORALL_AND_THM] >>
  rpt gen_tac >>
  drule (GEN_ALL compile_prog_evaluate) >>
  fsrw_tac[QUANT_INST_ss[pair_default_qp]][] >>
  disch_then(qspecl_then[`k`,`ffi0`]mp_tac)>>simp[]>>
  Cases_on`k=0`>>simp[]>-(
    fs[bviSemTheory.evaluate_def,bvlSemTheory.evaluate_def]>>
    every_case_tac >> fs[] >>
    simp[GSYM IMP_CONJ_THM] >> strip_tac >>
    conj_tac >> qexists_tac`0`>>simp[])>>
  strip_tac >>
  qmatch_assum_abbrev_tac`state_rel _ (SND p1) (SND p2)` >>
  Cases_on`p1`>>Cases_on`p2`>>fs[markerTheory.Abbrev_def] >>
  ntac 2 (pop_assum(mp_tac o SYM)) >> ntac 2 strip_tac >> fs[] >>
  qmatch_assum_rename_tac`state_rel _ p1 p2` >>
  `p1.ffi = p2.ffi` by fs[state_rel_def] >>
  reverse conj_tac >> rw[]
  >- ( qexists_tac`ck+k` >> fs[] ) >>
  qexists_tac`k` >> fs[] >>
  qmatch_assum_abbrev_tac`_ < (LENGTH (_ ffi))` >>
  `ffi.io_events ≼ p2.ffi.io_events` by (
    qunabbrev_tac`ffi` >>
    metis_tac[
      bviPropsTheory.initial_state_with_simp,
      bviPropsTheory.evaluate_add_to_clock_io_events_mono
        |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["s"]))
        |> Q.SPEC`s with clock := k`
        |> SIMP_RULE(srw_ss())[bviPropsTheory.inc_clock_def],
      SND,ADD_SYM]) >>
  fs[IS_PREFIX_APPEND] >> simp[EL_APPEND1]);

val compile_semantics = Q.store_thm("compile_semantics",
  `compile start n prog = (start', prog', n') ∧
   bEvery GoodHandleLet (MAP (SND o SND) prog) ∧
   ALL_DISTINCT (MAP FST prog) ∧
   semantics ffi0 (fromAList prog) start ≠ Fail
   ⇒
   semantics ffi0 (fromAList prog') start' =
   semantics ffi0 (fromAList prog) start`,
  rw[compile_def] >>
  `bEvery GoodHandleLet (MAP (SND o SND) (optimise prog))` by cheat >>
  METIS_TAC[optimise_semantics,MAP_FST_optimise,compile_prog_semantics]);

val _ = export_theory();
