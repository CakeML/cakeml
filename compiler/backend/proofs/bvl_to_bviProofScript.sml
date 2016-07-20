open preamble
     bvlSemTheory bvlPropsTheory
     bvl_to_bviTheory
     bviSemTheory bviPropsTheory;
local open
  bvl_constProofTheory
  bvl_handleProofTheory
  bvi_letProofTheory
in end;

val _ = new_theory"bvl_to_bviProof";

(* TODO: move *)

val SNOC_REPLICATE = store_thm("SNOC_REPLICATE",
  ``!n x. SNOC x (REPLICATE n x) = REPLICATE (SUC n) x``,
  Induct \\ fs [REPLICATE]);

val REVERSE_REPLICATE = store_thm("REVERSE_REPLICATE",
  ``!n x. REVERSE (REPLICATE n x) = REPLICATE n x``,
  Induct \\ fs [REPLICATE] \\ fs [GSYM REPLICATE,GSYM SNOC_REPLICATE]);

(* --- *)

(* value relation *)

val adjust_bv_def = tDefine "adjust_bv" `
  (adjust_bv b (Number i) = Number i) /\
  (adjust_bv b (Word64 w) = Word64 w) /\
  (adjust_bv b (RefPtr r) = RefPtr (b r)) /\
  (adjust_bv b (CodePtr c) = CodePtr (num_stubs + 2 * c)) /\
  (adjust_bv b (Block tag vs) = Block tag (MAP (adjust_bv b) vs))`
  (WF_REL_TAC `measure (v_size o SND)`
   \\ Induct_on `vs` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] [v_size_def]
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
     (sptree$lookup (num_stubs + 2 * name + 1) t =
        SOME (arg_count,bvi_let$compile_exp body)) /\
     aux_code_installed rest t)`

val aux_code_installed_APPEND = prove(
  ``!xs ys.
      aux_code_installed (xs++ys) code ==>
      aux_code_installed xs code /\
      aux_code_installed ys code``,
  Induct \\ full_simp_tac(srw_ss())[APPEND,aux_code_installed_def,FORALL_PROD] \\ METIS_TAC []);

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
   \\ Induct_on `vs` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] [v_size_def]
   \\ RES_TAC \\ FIRST_X_ASSUM (ASSUME_TAC o SPEC_ALL) \\ DECIDE_TAC)

val bv_ok_ind = theorem"bv_ok_ind";

val bv_ok_SUBSET_IMP = prove(
  ``!refs x refs2.
      bv_ok refs x /\ FDOM refs SUBSET FDOM refs2 ==> bv_ok refs2 x``,
  HO_MATCH_MP_TAC bv_ok_ind \\ full_simp_tac(srw_ss())[bv_ok_def]
  \\ full_simp_tac(srw_ss())[SUBSET_DEF,EVERY_MEM]);

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
  \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[adjust_bv_def,bv_ok_def]
  \\ full_simp_tac(srw_ss())[MAP_EQ_f,EVERY_MEM]);

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
  full_simp_tac(srw_ss())[state_ok_def,bvlSemTheory.dec_clock_def]);

val evaluate_IMP_bv_ok = prove(
  ``(bvlSem$evaluate (xs,env,s) = (res,t)) ==>
    (bv_ok s.refs a1 ==> bv_ok t.refs a1) /\
    (EVERY (bv_ok s.refs) as ==> EVERY (bv_ok t.refs) as)``,
  REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ IMP_RES_TAC evaluate_refs_SUBSET \\ IMP_RES_TAC bv_ok_SUBSET_IMP);

val v_to_list_ok = Q.prove(
  `∀v x. v_to_list v = SOME x ∧
         bv_ok refs v ⇒
         EVERY (bv_ok refs) x`,
  ho_match_mp_tac v_to_list_ind >>
  simp[v_to_list_def,bv_ok_def] >> srw_tac[][] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][])

val do_app_ok_lemma = prove(
  ``state_ok r /\ EVERY (bv_ok r.refs) a /\
    (do_app op a r = Rval (q,t)) ==>
    state_ok t /\ bv_ok t.refs q``,
  Cases_on `op` \\ full_simp_tac(srw_ss())[bvlSemTheory.do_app_def] \\ BasicProvers.EVERY_CASE_TAC
  \\ TRY (full_simp_tac(srw_ss())[] \\ SRW_TAC [] [bv_ok_def]
    \\ full_simp_tac(srw_ss())[closSemTheory.get_global_def]
    \\ full_simp_tac(srw_ss())[state_ok_def,bv_ok_def] \\ NO_TAC)
  \\ TRY (SRW_TAC [] [] \\ full_simp_tac(srw_ss())[bv_ok_def,EVERY_EL] \\ NO_TAC)
  \\ TRY (SRW_TAC [] [] \\ full_simp_tac(srw_ss())[bv_ok_def,EVERY_MEM] \\ NO_TAC)
  \\ STRIP_TAC \\ full_simp_tac(srw_ss())[LET_THM] \\ rpt BasicProvers.VAR_EQ_TAC THEN1
   (full_simp_tac(srw_ss())[closSemTheory.get_global_def,state_ok_def,EVERY_EL]
    \\ RES_TAC \\ full_simp_tac(srw_ss())[] \\ REPEAT (Q.PAT_ASSUM `!x.bb` (K ALL_TAC))
    \\ REV_FULL_SIMP_TAC std_ss [])
  THEN1
   (SRW_TAC [] [bv_ok_def] \\ full_simp_tac(srw_ss())[LET_DEF,state_ok_def]
    \\ MATCH_MP_TAC IMP_EVERY_LUPDATE \\ full_simp_tac(srw_ss())[])
  THEN1
   (srw_tac[][bv_ok_def] \\ full_simp_tac(srw_ss())[state_ok_def] >>
    srw_tac[][FLOOKUP_UPDATE] >> full_simp_tac(srw_ss())[EVERY_MEM] >> srw_tac[][] >>
    BasicProvers.CASE_TAC >> TRY BasicProvers.CASE_TAC >> srw_tac[][] >>
    Q.ISPEC_THEN`r.refs`match_mp_tac bv_ok_SUBSET_IMP >>
    first_x_assum(qspec_then`k`strip_assume_tac)>>rev_full_simp_tac(srw_ss())[]>>
    simp[] >> res_tac >> full_simp_tac(srw_ss())[] >>
    simp[SUBSET_DEF])
  THEN1
   (srw_tac[][bv_ok_def] \\ full_simp_tac(srw_ss())[state_ok_def] >>
    srw_tac[][FLOOKUP_UPDATE] >> full_simp_tac(srw_ss())[EVERY_MEM] >> srw_tac[][] >>
    rpt BasicProvers.CASE_TAC >> srw_tac[][] >>
    Q.ISPEC_THEN`r.refs`match_mp_tac bv_ok_SUBSET_IMP >>
    first_x_assum(qspec_then`k`strip_assume_tac)>>rev_full_simp_tac(srw_ss())[]>>
    simp[] >> res_tac >> full_simp_tac(srw_ss())[rich_listTheory.REPLICATE_GENLIST,MEM_GENLIST] >>
    simp[SUBSET_DEF])
  THEN1
   (srw_tac[][bv_ok_def] \\ full_simp_tac(srw_ss())[state_ok_def] >>
    srw_tac[][FLOOKUP_UPDATE] >> full_simp_tac(srw_ss())[EVERY_MEM] >> srw_tac[][] >>
    every_case_tac >> srw_tac[][] >>
    Q.ISPEC_THEN`r.refs`match_mp_tac bv_ok_SUBSET_IMP >>
    first_x_assum(qspec_then`k`strip_assume_tac)>>rev_full_simp_tac(srw_ss())[]>>
    simp[] >> res_tac >> full_simp_tac(srw_ss())[] >>
    simp[SUBSET_DEF])
  THEN1 (
    simp[bv_ok_def] >>
    imp_res_tac v_to_list_ok >>
    full_simp_tac(srw_ss())[EVERY_MEM])
  THEN1
   (full_simp_tac(srw_ss())[LET_DEF,state_ok_def]
    \\ SRW_TAC [] [bv_ok_def,FLOOKUP_DEF,EVERY_MEM]
    \\ BasicProvers.EVERY_CASE_TAC
    \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ RES_TAC \\ full_simp_tac(srw_ss())[]
    \\ REPEAT STRIP_TAC \\ RES_TAC
    THEN1 (bv_ok_SUBSET_IMP |> Q.ISPEC_THEN `r.refs`MATCH_MP_TAC
           \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[SUBSET_DEF,FLOOKUP_DEF])
    THEN1 (bv_ok_SUBSET_IMP |> Q.ISPEC_THEN `r.refs`MATCH_MP_TAC
           \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[SUBSET_DEF,FLOOKUP_DEF])
    \\ Q.PAT_ASSUM `xx = ValueArray l` MP_TAC
    \\ SRW_TAC [] [FAPPLY_FUPDATE_THM] \\ RES_TAC
    THEN1 (bv_ok_SUBSET_IMP |> Q.ISPEC_THEN `r.refs`MATCH_MP_TAC
           \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[SUBSET_DEF,FLOOKUP_DEF])
    \\ Q.PAT_ASSUM `!k:num. bbb` (MP_TAC o Q.SPEC `k`)
    \\ full_simp_tac(srw_ss())[FLOOKUP_DEF] \\ REPEAT STRIP_TAC
    THEN1 (bv_ok_SUBSET_IMP |> Q.ISPEC_THEN `r.refs`MATCH_MP_TAC
           \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[SUBSET_DEF,FLOOKUP_DEF]))
  THEN1
   (full_simp_tac(srw_ss())[state_ok_def]
    \\ Q.PAT_ASSUM `!k:num. bbb` (MP_TAC o Q.SPEC `n`) \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[EVERY_EL] \\ REPEAT STRIP_TAC \\ RES_TAC
    \\ SRW_TAC [] [] \\ Cases_on `i` \\ full_simp_tac(srw_ss())[])
  THEN1
   (full_simp_tac(srw_ss())[state_ok_def] \\ SRW_TAC [] [] THEN1
     (full_simp_tac(srw_ss())[EVERY_MEM] \\ REPEAT STRIP_TAC
      \\ BasicProvers.EVERY_CASE_TAC
      \\ RES_TAC \\ full_simp_tac(srw_ss())[]
      \\ Q.ISPEC_THEN`r.refs`match_mp_tac bv_ok_SUBSET_IMP
      \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[SUBSET_DEF,FLOOKUP_DEF])
    THEN1
     (full_simp_tac(srw_ss())[FLOOKUP_UPDATE] \\ Cases_on `k = n` \\ full_simp_tac(srw_ss())[] THEN1
       (MATCH_MP_TAC IMP_EVERY_LUPDATE \\ REPEAT STRIP_TAC
        THEN1 (bv_ok_SUBSET_IMP |> Q.ISPEC_THEN `r.refs`MATCH_MP_TAC
          \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[SUBSET_DEF,FLOOKUP_DEF])
        \\ Q.PAT_ASSUM `!k:num. bbb` (MP_TAC o Q.SPEC `n`) \\ full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC
        \\ Q.ISPEC_THEN`r.refs`match_mp_tac bv_ok_SUBSET_IMP
        \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[SUBSET_DEF,FLOOKUP_DEF])
      \\ Q.PAT_ASSUM `!k:num. bbb` (MP_TAC o Q.SPEC `k`) \\ full_simp_tac(srw_ss())[]
      \\ BasicProvers.EVERY_CASE_TAC
      \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC
      \\ Q.ISPEC_THEN`r.refs`match_mp_tac bv_ok_SUBSET_IMP
      \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[SUBSET_DEF,FLOOKUP_DEF]))
  THEN1 (
    full_simp_tac(srw_ss())[state_ok_def] \\ srw_tac[][] >-
     (full_simp_tac(srw_ss())[EVERY_MEM] \\ REPEAT STRIP_TAC
      \\ BasicProvers.EVERY_CASE_TAC
      \\ RES_TAC \\ full_simp_tac(srw_ss())[]
      \\ Q.ISPEC_THEN`r.refs`match_mp_tac bv_ok_SUBSET_IMP
      \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[SUBSET_DEF,FLOOKUP_DEF])
    \\ simp[FLOOKUP_UPDATE] >> srw_tac[][] >>
    BasicProvers.CASE_TAC >>
    BasicProvers.CASE_TAC >>
    first_x_assum(qspec_then`k`mp_tac) >> srw_tac[][] >>
    full_simp_tac(srw_ss())[EVERY_MEM] \\ REPEAT STRIP_TAC
    \\ RES_TAC \\ full_simp_tac(srw_ss())[]
    \\ Q.ISPEC_THEN`r.refs`match_mp_tac bv_ok_SUBSET_IMP
    \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[SUBSET_DEF,FLOOKUP_DEF]));

val do_app_ok = prove(
  ``state_ok r /\ EVERY (bv_ok r.refs) a /\
    (do_app op a r = Rval (q,t)) ==>
    state_ok t /\ bv_ok t.refs q /\
    (EVERY (bv_ok r.refs) env ==> EVERY (bv_ok t.refs) env)``,
  STRIP_TAC \\ IMP_RES_TAC do_app_ok_lemma \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC
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
  recInduct bvlSemTheory.evaluate_ind \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[bvlSemTheory.evaluate_def]
  \\ SRW_TAC [] []
  \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[evaluate_ok_lemma]
  \\ SRW_TAC [] [] \\ REV_FULL_SIMP_TAC std_ss []
  \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[evaluate_ok_lemma]
  \\ SRW_TAC [] [] \\ REV_FULL_SIMP_TAC std_ss []
  \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[evaluate_ok_lemma]
  \\ SRW_TAC [] [] \\ REV_FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC evaluate_SING \\ full_simp_tac(srw_ss())[]
  \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[evaluate_ok_lemma]
  \\ SRW_TAC [] [] \\ REV_FULL_SIMP_TAC std_ss []
  \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[evaluate_ok_lemma]
  \\ SRW_TAC [] [] \\ REV_FULL_SIMP_TAC std_ss []
  \\ TRY (full_simp_tac(srw_ss())[EVERY_EL] \\ NO_TAC)
  \\ IMP_RES_TAC evaluate_IMP_bv_ok
  \\ IMP_RES_TAC do_app_ok
  \\ REPEAT (Q.PAT_ASSUM `!xx.bb` (K ALL_TAC))
  \\ imp_res_tac bvlPropsTheory.do_app_err \\ full_simp_tac(srw_ss())[]
  \\ IMP_RES_TAC find_code_EVERY_IMP \\ full_simp_tac(srw_ss())[rich_listTheory.EVERY_REVERSE]
  \\ IMP_RES_TAC evaluate_IMP_bv_ok \\ full_simp_tac(srw_ss())[evaluate_ok_lemma]
  \\ full_simp_tac(srw_ss())[state_ok_def]);

(* semantics lemmas *)

val evaluate_MAP_Var = prove(
  ``!l env vs b s.
      EVERY isVar l /\ (get_vars (MAP destVar l) env = SOME vs) ==>
        (evaluate (MAP (Var o destVar) l,MAP (adjust_bv b) env,s) =
          (Rval (MAP (adjust_bv b) vs),s))``,
  Induct THEN1 (EVAL_TAC \\ SRW_TAC [] [])
  \\ Cases \\ full_simp_tac(srw_ss())[isVar_def,destVar_def,get_vars_def]
  \\ Cases_on `l` \\ full_simp_tac(srw_ss())[bviSemTheory.evaluate_def,get_vars_def,EL_MAP]
  \\ Cases_on `h` \\ full_simp_tac(srw_ss())[isVar_def,destVar_def]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `n' < LENGTH env` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `get_vars (MAP destVar t) env` \\ full_simp_tac(srw_ss())[]
  \\ Q.PAT_ASSUM `!xx.bb` (MP_TAC o Q.SPEC `env`) \\ full_simp_tac(srw_ss())[]
  \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[EL_MAP]) |> INST_TYPE[alpha|->``:'ffi``];

val evaluate_MAP_Var2 = prove(
  ``!args.
      bVarBound (LENGTH vs) args /\ EVERY isVar args ==>
      ?ts.
        bviSem$evaluate (MAP (Var o destVar) args,vs ++ env,s) = (Rval ts,s) /\
        evaluate (MAP (Var o destVar) args,vs,s) = (Rval ts,s)``,
  Induct \\ full_simp_tac(srw_ss())[MAP,bviSemTheory.evaluate_def] \\ Cases \\ full_simp_tac(srw_ss())[isVar_def]
  \\ Cases_on `args` \\ full_simp_tac(srw_ss())[MAP,bviSemTheory.evaluate_def,destVar_def,bVarBound_def]
  \\ REPEAT STRIP_TAC
  \\ `n < LENGTH vs + LENGTH env` by DECIDE_TAC \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[rich_listTheory.EL_APPEND1]) |> SPEC_ALL |> INST_TYPE[alpha|->``:'ffi``];

val bEval_bVarBound = prove(
  ``!xs vs s env.
      bVarBound (LENGTH vs) xs ==>
      (bvlSem$evaluate (xs,vs ++ env,s) = evaluate (xs,vs,s))``,
  recInduct bvlSemTheory.evaluate_ind \\ REPEAT STRIP_TAC
  \\ full_simp_tac(srw_ss())[bvlSemTheory.evaluate_def,bVarBound_def]
  \\ TRY (BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[ADD1] \\ NO_TAC)
  THEN1 (`n < LENGTH env + LENGTH env'` by DECIDE_TAC
         \\ full_simp_tac(srw_ss())[rich_listTheory.EL_APPEND1])
  THEN1 (BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[]
         \\ FIRST_X_ASSUM MATCH_MP_TAC \\ IMP_RES_TAC bvlPropsTheory.evaluate_IMP_LENGTH
         \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC]));

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
  Induct >> srw_tac[][] >> srw_tac[][CopyGlobals_code_def] >>
  srw_tac[][iEval_def,iEvalOp_def,do_app_aux_def,bEvalOp_def,bvl_to_bvi_id,small_enough_int_def,bvl_to_bvi_with_refs] >- (
    qexists_tac`0`>>simp[inc_clock_ZERO,state_component_equality] >>
    rpt AP_TERM_TAC >>
    simp[LIST_EQ_REWRITE,EL_LUPDATE] >>
    srw_tac[][] >> simp[EL_APPEND2,EL_DROP] >>
    Cases_on`ls`>>full_simp_tac(srw_ss())[]) >>
  simp[find_code_def] >>
  simp[Once inc_clock_def] >>
  qpat_abbrev_tac`l2 = LUPDATE x y z` >>
  qpat_abbrev_tac`rf = s.refs |+ X` >>
  first_x_assum(qspecl_then[`l2`,`s with refs := rf`]mp_tac) >>
  impl_tac >- (
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
  srw_tac[][] >>
  simp[LIST_EQ_REWRITE,Abbr`l2`] >> srw_tac[][] >>
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
    srw_tac[][] >> simp[] >> intLib.COOPER_TAC) >>
  `(λptr. ptr ≠ p ∧ ptr ∉ FDOM s.refs) = (λptr. ptr ∉ FDOM s.refs)` by (
    simp[FUN_EQ_THM] >> full_simp_tac(srw_ss())[FLOOKUP_DEF] >> metis_tac[]) >> simp[] >>
  qpat_abbrev_tac`p1 = LEAST ptr. ptr ∉ FDOM s.refs` >>
  qexists_tac`p1` >>
  `p1 ∉ FDOM s.refs` by (
    rpt strip_tac >> full_simp_tac(srw_ss())[FLOOKUP_DEF] >>
    metis_tac[LEAST_NOTIN_FDOM] ) >>
  simp[LUPDATE_def] >>
  qpat_abbrev_tac`l1 = REPLICATE _ _` >>
  qpat_abbrev_tac`rf = s.refs |+ _ |+ _` >>
  qspecl_then[`Number(1+ &SUC n)::ls`,`n`,`l1`,`s with <| global := SOME p1; refs := rf|>`]mp_tac evaluate_CopyGlobals_code >>
  impl_tac >- (
    simp[Abbr`rf`,FLOOKUP_UPDATE] >>
    IF_CASES_TAC >> simp[] >- (
      full_simp_tac(srw_ss())[FLOOKUP_DEF] >> metis_tac[LEAST_NOTIN_FDOM] ) >>
    simp[Abbr`l1`,LENGTH_REPLICATE] ) >>
  strip_tac >>
  qexists_tac`c+1` >>
  simp[] >>
  qpat_abbrev_tac`ss = dec_clock 1 Z` >>
  `ss = inc_clock c (s with <| global := SOME p1; refs := rf|>)` by (
    simp[Abbr`ss`] >> EVAL_TAC >>
    simp[state_component_equality] ) >>
  simp[Abbr`ss`] >>
  `&SUC n - 1 = &n` by (Cases_on`n`>>full_simp_tac(srw_ss())[]>>simp[ADD1]>>intLib.COOPER_TAC) >> full_simp_tac(srw_ss())[] >>
  simp[Abbr`rf`,fmap_eq_flookup,FLOOKUP_UPDATE,state_component_equality] >>
  srw_tac[][] >> simp[] >> TRY(intLib.COOPER_TAC) >>
  `n = LENGTH ls`by decide_tac >>
  `2 * (LENGTH ls + 1) = LENGTH ls + LENGTH ls + 2` by DECIDE_TAC >>
  simp[Abbr`l1`,DROP_REPLICATE,ADD1])

(* compiler correctness *)

val bEval_def = bvlSemTheory.evaluate_def;
val iEval_append = bviPropsTheory.evaluate_APPEND;

val compile_exps_Var_list = prove(
  ``!l n. EVERY isVar l ==> (compile_exps n l = (MAP (Var o destVar) l ,[],n))``,
  Induct \\ full_simp_tac(srw_ss())[EVERY_DEF,compile_exps_def] \\ Cases \\ full_simp_tac(srw_ss())[isVar_def]
  \\ Cases_on `l` \\ full_simp_tac(srw_ss())[compile_exps_def,destVar_def,LET_DEF]);

val compile_int_thm = prove(
  ``!i env s. evaluate ([compile_int i],env,s) = (Rval [Number i],s)``,
  STRIP_TAC \\ completeInduct_on `Num (ABS i)`
  \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[PULL_FORALL] \\ POP_ASSUM (K ALL_TAC)
  \\ reverse (Cases_on `i`) \\ full_simp_tac(srw_ss())[] THEN1 EVAL_TAC
  \\ (ONCE_REWRITE_TAC [compile_int_def] \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ SRW_TAC [] [] THEN1
     (`n <= 268435457` by DECIDE_TAC
      \\ full_simp_tac(srw_ss())[evaluate_def,bviSemTheory.do_app_def,do_app_aux_def,small_enough_int_def])
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`&(n DIV 268435457)`,`env`,`s`])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1 (full_simp_tac(srw_ss())[integerTheory.INT_ABS_NUM,DIV_LT_X] \\ intLib.COOPER_TAC)
    \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
    \\ `n MOD 268435457 < 268435457` by full_simp_tac(srw_ss())[MOD_LESS]
    \\ `n MOD 268435457 <= 268435457` by DECIDE_TAC
    \\ full_simp_tac(srw_ss())[evaluate_def,bviSemTheory.do_app_def,do_app_aux_def,small_enough_int_def,bvlSemTheory.do_app_def]
    \\ full_simp_tac(srw_ss())[bvl_to_bvi_id]
    \\ STRIP_ASSUME_TAC
         (MATCH_MP DIVISION (DECIDE ``0 < 268435457:num``) |> Q.SPEC `n`)
    \\ intLib.COOPER_TAC));

val iEval_bVarBound = Q.prove(
  `!(n:num) xs n vs (t:'ffi bvlSem$state) (s:'ffi bviSem$state) env.
     bVarBound (LENGTH vs) xs /\ bEvery GoodHandleLet xs ==>
     (evaluate (FST (compile_exps n xs),vs ++ env,s) =
      evaluate (FST (compile_exps n xs),vs,s))`,
  recInduct bVarBound_ind \\ REPEAT STRIP_TAC
  \\ full_simp_tac(srw_ss())[iEval_def,bVarBound_def,compile_exps_def] \\ SRW_TAC [] []
  \\ full_simp_tac(srw_ss())[bEvery_def,GoodHandleLet_def] \\ SRW_TAC [] []
  THEN1 (FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n1`,`vs`]) \\ full_simp_tac(srw_ss())[]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n`,`vs`]) \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC compile_exps_SING \\ SRW_TAC [] []
    \\ ONCE_REWRITE_TAC [bviPropsTheory.evaluate_CONS] \\ full_simp_tac(srw_ss())[])
  THEN1 (full_simp_tac(srw_ss())[rich_listTheory.EL_APPEND1])
  THEN1 (`F` by DECIDE_TAC)
  THEN1 (IMP_RES_TAC compile_exps_SING \\ SRW_TAC [] []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n2`,`vs`]) \\ full_simp_tac(srw_ss())[]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n1`,`vs`]) \\ full_simp_tac(srw_ss())[]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n`,`vs`]) \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[iEval_def])
  THEN1 (IMP_RES_TAC compile_exps_SING \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[iEval_def]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n1`]) \\ full_simp_tac(srw_ss())[]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n`,`vs`]) \\ full_simp_tac(srw_ss())[]
    \\ REPEAT STRIP_TAC
    \\ Cases_on `evaluate (c1,vs,s)` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `q` \\ full_simp_tac(srw_ss())[]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`a ++ vs`]) \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC bviPropsTheory.evaluate_IMP_LENGTH \\ IMP_RES_TAC compile_exps_LENGTH
    \\ REPEAT STRIP_TAC \\ POP_ASSUM MATCH_MP_TAC
    \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC])
  \\ TRY (IMP_RES_TAC compile_exps_SING \\ SRW_TAC [] []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n`,`vs`]) \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[iEval_def] \\ NO_TAC)
  THEN1
   (FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n`,`vs`]) \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `op` \\ full_simp_tac(srw_ss())[compile_op_def,iEval_def,compile_int_thm]
    \\ simp[iEval_def]
    \\ simp[iEval_append,iEval_def,compile_int_thm]
    \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[iEval_def,compile_int_thm])
  \\ full_simp_tac(srw_ss())[iEval_def]
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n2`]) \\ full_simp_tac(srw_ss())[]
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n`,`vs`]) \\ full_simp_tac(srw_ss())[]
  \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
  \\ IMP_RES_TAC compile_exps_SING \\ SRW_TAC [] []
  \\ full_simp_tac(srw_ss())[markerTheory.Abbrev_def] \\ SRW_TAC [] []
  \\ Cases_on `x1` \\ full_simp_tac(srw_ss())[GoodHandleLet_def,destLet_def]
  \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[compile_exps_def]
  \\ REV_FULL_SIMP_TAC std_ss [LET_DEF]
  \\ full_simp_tac(srw_ss())[iEval_def]
  \\ Q.PAT_ASSUM `!xx yy. bb = bbb` (ASSUME_TAC o Q.SPECL [`s`,`env`])
  \\ IMP_RES_TAC compile_exps_Var_list \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
  \\ full_simp_tac(srw_ss())[bVarBound_def]
  \\ (evaluate_MAP_Var2 |> MP_TAC) \\ full_simp_tac(srw_ss())[]
  \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `find_code (SOME (num_stubs + 2 * n3 + 1)) ts s.code` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `x` \\ full_simp_tac(srw_ss())[] \\ Cases_on `s.clock = 0` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `evaluate ([r],q,dec_clock 1 s)` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `q'` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `e'` \\ full_simp_tac(srw_ss())[]
  \\ ONCE_REWRITE_TAC [APPEND |> SPEC_ALL |> CONJUNCT2 |> GSYM]
  \\ FIRST_X_ASSUM MATCH_MP_TAC \\ full_simp_tac(srw_ss())[ADD1]);

val v_to_list_adjust = Q.prove(
  `∀x. v_to_list (adjust_bv f x) = OPTION_MAP (MAP (adjust_bv f)) (v_to_list x)`,
  ho_match_mp_tac v_to_list_ind >>
  simp[v_to_list_def,adjust_bv_def] >> srw_tac[][] >>
  Cases_on`v_to_list x`>>full_simp_tac(srw_ss())[]);

val do_app_adjust = Q.prove(
  `state_rel b2 s5 t2 /\
   (!i. op <> Const i) /\ (op <> Ref) /\ (op ≠ RefByte) ∧ (op ≠ RefArray) ∧
   (∀n. op ≠ Global n) ∧ (∀n. op ≠ SetGlobal n) ∧ (op ≠ AllocGlobal) ∧
   (do_app op (REVERSE a) s5 = Rval (q,r)) /\ EVERY (bv_ok s5.refs) (REVERSE a) ==>
   ?t3. (do_app op (MAP (adjust_bv b2) (REVERSE a)) t2 =
          Rval (adjust_bv b2 q,t3)) /\
        state_rel b2 r t3`,
  SIMP_TAC std_ss [Once bEvalOp_def,iEvalOp_def,do_app_aux_def]
  \\ Cases_on `op` \\ full_simp_tac(srw_ss())[]
  THEN1 (* Cons *)
   (full_simp_tac(srw_ss())[bEvalOp_def]
    \\ SRW_TAC [] [adjust_bv_def,MAP_EQ_f,bvl_to_bvi_id]
    \\ SRW_TAC [] [adjust_bv_def,MAP_EQ_f,bvl_to_bvi_id])
  THEN1 (* El *)
   (BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[adjust_bv_def,bEvalOp_def]
    \\ every_case_tac >> full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[adjust_bv_def,MAP_EQ_f,bvl_to_bvi_id,
         bEvalOp_def,EL_MAP] \\ SRW_TAC [] [])
  THEN1 (* LengthBlock *)
   (BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[adjust_bv_def,bEvalOp_def]
    \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[adjust_bv_def,bvl_to_bvi_id])
  THEN1 (* Length *) (
    every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[bEvalOp_def] >>
    every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[adjust_bv_def,bvl_to_bvi_id] >- (
      full_simp_tac(srw_ss())[state_rel_def,bvi_to_bvl_def] >> srw_tac[][] >>
      last_x_assum(qspec_then`n`mp_tac) >> srw_tac[][]) >>
    spose_not_then strip_assume_tac >> srw_tac[][] >>
    full_simp_tac(srw_ss())[bvi_to_bvl_def,state_rel_def] >>
    last_x_assum(qspec_then`n`mp_tac) >> srw_tac[][])
  THEN1 (* LengthByte *) (
    every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[bEvalOp_def] >>
    every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[adjust_bv_def,bvl_to_bvi_id] >- (
      full_simp_tac(srw_ss())[state_rel_def,bvi_to_bvl_def] >> srw_tac[][] >>
      last_x_assum(qspec_then`n`mp_tac) >> srw_tac[][]) >>
    spose_not_then strip_assume_tac >> srw_tac[][] >>
    full_simp_tac(srw_ss())[bvi_to_bvl_def,state_rel_def] >>
    last_x_assum(qspec_then`n`mp_tac) >> srw_tac[][])
  THEN1 (* DerefByte *) (
    Cases_on`REVERSE a`>>full_simp_tac(srw_ss())[]>>
    Cases_on`t`>>full_simp_tac(srw_ss())[]>>
    Cases_on`h'`>>full_simp_tac(srw_ss())[]>>
    Cases_on`h`>>full_simp_tac(srw_ss())[]>>
    Cases_on`t'`>>full_simp_tac(srw_ss())[]>>
    simp[bEvalOp_def,adjust_bv_def] >>
    simp[] >> srw_tac[][] >>
    every_case_tac >> full_simp_tac(srw_ss())[] >>srw_tac[][] >> srw_tac[][adjust_bv_def,bvl_to_bvi_id] >>
    full_simp_tac(srw_ss())[state_rel_def] >>
    last_x_assum(qspec_then`n`mp_tac) >> simp[] >>
    spose_not_then strip_assume_tac >> full_simp_tac(srw_ss())[])
  THEN1 (* UpdateByte *) (
    Cases_on`REVERSE a`>>full_simp_tac(srw_ss())[]>>
    Cases_on`t`>>full_simp_tac(srw_ss())[]>>
    Cases_on`t'`>>full_simp_tac(srw_ss())[]>>
    Cases_on`h''`>>full_simp_tac(srw_ss())[]>>
    Cases_on`h'`>>full_simp_tac(srw_ss())[]>>
    Cases_on`h`>>full_simp_tac(srw_ss())[]>>
    Cases_on`t`>>full_simp_tac(srw_ss())[]>>
    simp[bEvalOp_def,adjust_bv_def] >>
    simp[] >> srw_tac[][] >>
    every_case_tac >> full_simp_tac(srw_ss())[] >>srw_tac[][] >>
    srw_tac[][adjust_bv_def,bvl_to_bvi_with_refs,bvl_to_bvi_id] >>
    full_simp_tac(srw_ss())[state_rel_def] >>
    TRY (
      last_x_assum(qspec_then`n`mp_tac) >> simp[] >>
      spose_not_then strip_assume_tac >> rpt var_eq_tac >> full_simp_tac(srw_ss())[] >>
      NO_TAC) >>
    simp[bvi_to_bvl_def] >>
    conj_asm1_tac >- (
      simp[INJ_INSERT] >>
      conj_tac >- (
        rator_x_assum`INJ`mp_tac >>
        simp[INJ_DEF] ) >>
      `n ∈ FDOM s5.refs` by full_simp_tac(srw_ss())[FLOOKUP_DEF] >>
      metis_tac[INJ_DEF]) >>
    simp[FLOOKUP_UPDATE] >>
    srw_tac[][] >- (
      last_x_assum(qspec_then`k`mp_tac) >> simp[] ) >>
    full_simp_tac(srw_ss())[bv_ok_def] >>
    TRY (
      qexists_tac`array_size`>>simp[]>>
      srw_tac[][] >> full_simp_tac(srw_ss())[FLOOKUP_DEF] >> NO_TAC) >>
    TRY (
      BasicProvers.CASE_TAC >>
      `k ∈ FDOM s5.refs ∧ n ∈ FDOM s5.refs` by full_simp_tac(srw_ss())[FLOOKUP_DEF] >>
      metis_tac[INJ_DEF]) >>
    METIS_TAC[])
  THEN1 (* FromList *) (
    Cases_on`REVERSE a`>>full_simp_tac(srw_ss())[]>>
    Cases_on`t`>>full_simp_tac(srw_ss())[] >>
    simp[bEvalOp_def,v_to_list_adjust] >>
    Cases_on`v_to_list h`>>simp[] >> strip_tac >>
    rpt var_eq_tac >> simp[bvl_to_bvi_id,adjust_bv_def] >>
    srw_tac[ETA_ss][])
  THEN1 (* TagLenEq *) (
    every_case_tac >> full_simp_tac(srw_ss())[bEvalOp_def,adjust_bv_def] >>
    srw_tac[][] >> srw_tac[][bvl_to_bvi_id])
  THEN1 (* TagEq *)
    (BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[adjust_bv_def,bEvalOp_def]
     \\ SRW_TAC [] []
     \\ simp[bvl_to_bvi_id])
  THEN1 (* BlockCmp *) (
    every_case_tac >> full_simp_tac(srw_ss())[bEvalOp_def,adjust_bv_def] >>
    srw_tac[][] >> simp[bvl_to_bvi_id])
  THEN1 (* IsBlock *)
   (BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[adjust_bv_def,bEvalOp_def]
    \\ SRW_TAC [] []
    \\ simp[bvl_to_bvi_id])
  THEN1 (* Deref *)
   (Cases_on `REVERSE a` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `t` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `h'` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `h` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `t'` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `FLOOKUP s5.refs n` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `x` \\ full_simp_tac(srw_ss())[]
    \\ REPEAT STRIP_TAC \\ SRW_TAC [] [adjust_bv_def]
    \\ full_simp_tac(srw_ss())[bEvalOp_def]
    \\ Q.EXISTS_TAC `t2` \\ full_simp_tac(srw_ss())[]
    \\ `FLOOKUP t2.refs (b2 n) = SOME(ValueArray(MAP (adjust_bv b2) l))` by (
        full_simp_tac(srw_ss())[state_rel_def] >>
        last_x_assum(qspec_then`n`mp_tac) >>
        simp[] )
    \\ simp[]
    \\ IF_CASES_TAC >> full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[]
    \\ `Num i < LENGTH l` by METIS_TAC[integerTheory.INT_OF_NUM,integerTheory.INT_LT]
    \\ simp[EL_MAP,bvl_to_bvi_id])
  THEN1 (* Update *)
   (Cases_on `REVERSE a` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `t` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `t'` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `h'` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `h` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `t` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `FLOOKUP s5.refs n` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `x` \\ full_simp_tac(srw_ss())[]
    \\ REPEAT STRIP_TAC \\ SRW_TAC [] [adjust_bv_def]
    \\ full_simp_tac(srw_ss())[bEvalOp_def] \\ SIMP_TAC std_ss [Once bvi_to_bvl_def] \\ full_simp_tac(srw_ss())[]
    \\ `FLOOKUP t2.refs (b2 n) =
        SOME (ValueArray (MAP (adjust_bv b2) l))` by ALL_TAC THEN1
     (full_simp_tac(srw_ss())[state_rel_def,bvl_to_bvi_def,bvi_to_bvl_def]
      \\ last_x_assum (MP_TAC o Q.SPEC `n`) \\ full_simp_tac(srw_ss())[])
    \\ simp[]
    \\ IF_CASES_TAC >> full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[]
    \\ rpt var_eq_tac \\ simp[]
    \\ simp[bvl_to_bvi_with_refs,bvl_to_bvi_id]
    \\ full_simp_tac(srw_ss())[state_rel_def,bvl_to_bvi_def,bvi_to_bvl_def]
    \\ full_simp_tac(srw_ss())[FLOOKUP_UPDATE]
    \\ conj_tac >- full_simp_tac(srw_ss())[FLOOKUP_DEF,ABSORPTION_RWT]
    \\ srw_tac[][] \\ full_simp_tac(srw_ss())[LUPDATE_MAP,bv_ok_def]
    THEN1 (
      BasicProvers.CASE_TAC >>
      full_simp_tac(srw_ss())[FLOOKUP_DEF,INJ_DEF] >>
      METIS_TAC[] ) >>
    res_tac >> METIS_TAC[])
  THEN1 (* Label *)
   (BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[bEvalOp_def,bvl_to_bvi_id]
    \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[adjust_bv_def])
  THEN1 (* FFI *) (
    Cases_on`REVERSE a`>>full_simp_tac(srw_ss())[]>>
    Cases_on`h`>>full_simp_tac(srw_ss())[]>>
    Cases_on`t`>>full_simp_tac(srw_ss())[]>>
    simp[bEvalOp_def,adjust_bv_def] >>
    srw_tac[][] >>
    qmatch_assum_rename_tac`bv_ok s5.refs (RefPtr k)` >>
    Cases_on`FLOOKUP s5.refs k`>>full_simp_tac(srw_ss())[]>>
    Cases_on`x`>>full_simp_tac(srw_ss())[]>>
    `FLOOKUP t2.refs (b2 k) = SOME (ByteArray l)` by (
      full_simp_tac(srw_ss())[state_rel_def] >>
      last_x_assum(qspec_then`k`mp_tac) >> simp[] ) >>
    simp[] >>
    simp[Once bvi_to_bvl_def] >>
    `s5.ffi = t2.ffi` by full_simp_tac(srw_ss())[state_rel_def] >>
    BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
    every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    simp[bvl_to_bvi_with_refs,bvl_to_bvi_with_ffi,bvl_to_bvi_id] >>
    simp[bvi_to_bvl_def] >>
    full_simp_tac(srw_ss())[state_rel_def] >>
    conj_tac >- (
      full_simp_tac(srw_ss())[FLOOKUP_DEF] >>
      simp[ABSORPTION_RWT] ) >>
    simp[FLOOKUP_UPDATE] >> srw_tac[][] >>
    full_simp_tac(srw_ss())[bv_ok_def] >>
    TRY BasicProvers.CASE_TAC >>
    full_simp_tac(srw_ss())[FLOOKUP_DEF,bvl_to_bvi_def] >>
    METIS_TAC[INJ_DEF])
  THEN1 (* Equal *) (
    simp[bEvalOp_def] >>
    Cases_on`REVERSE a`>>full_simp_tac(srw_ss())[] >>
    Cases_on`t`>>full_simp_tac(srw_ss())[] >>
    Cases_on`t'`>>full_simp_tac(srw_ss())[] >>
    Cases_on`h'`>>full_simp_tac(srw_ss())[] >>
    Cases_on`h`>>full_simp_tac(srw_ss())[] >>
    strip_tac >> rpt var_eq_tac >>
    simp[adjust_bv_def,bvl_to_bvi_id] >>
    full_simp_tac(srw_ss())[state_rel_def,bv_ok_def] >>
    METIS_TAC[INJ_DEF] )
  \\ (* Add, Sub, Mult, Div, Mod, Less, ... *)
   (REPEAT STRIP_TAC
    \\ Cases_on `REVERSE a` \\ full_simp_tac(srw_ss())[]
    \\ TRY(Cases_on `t` \\ full_simp_tac(srw_ss())[])
    \\ TRY (Cases_on`w` \\ fs[])
    \\ TRY(Cases_on `h'` \\ full_simp_tac(srw_ss())[])
    \\ TRY(Cases_on `h` \\ full_simp_tac(srw_ss())[])
    \\ TRY(Cases_on `t'` \\ full_simp_tac(srw_ss())[]) \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[bEvalOp_def,adjust_bv_def,bvl_to_bvi_id]
    \\ every_case_tac >> full_simp_tac(srw_ss())[bvl_to_bvi_id] >> srw_tac[][]
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
  \\ full_simp_tac(srw_ss())[bEval_def,compile_exps_def,iEval_def,bEvery_def,GoodHandleLet_def]
  THEN1 (* NIL *)
   (SRW_TAC [] [iEval_def]
    \\ Q.LIST_EXISTS_TAC [`b1`,`0`] \\ full_simp_tac(srw_ss())[inc_clock_ZERO])
  THEN1 (* CONS *)
   (`?c1 aux1 n1. compile_exps n [x] = (c1,aux1,n1)` by METIS_TAC [PAIR]
    \\ `?c2 aux2 n2. compile_exps n1 (y::xs) = (c2,aux2,n2)` by METIS_TAC [PAIR]
    \\ full_simp_tac(srw_ss())[LET_DEF] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[PULL_FORALL]
    \\ `?res5 s5. evaluate ([x],env,s) = (res5,s5)` by METIS_TAC [PAIR]
    \\ `?res6 s6. evaluate (y::xs,env,s5) = (res6,s6)` by METIS_TAC [PAIR]
    \\ IMP_RES_TAC evaluate_ok \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC aux_code_installed_APPEND \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[] \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `n`) \\ full_simp_tac(srw_ss())[]
    \\ reverse (Cases_on `res5`) \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`t1`,`b1`]) \\ full_simp_tac(srw_ss())[]
    \\ rpt var_eq_tac
    \\ TRY (impl_tac >- (spose_not_then strip_assume_tac >> full_simp_tac(srw_ss())[]))
    \\ TRY (REPEAT STRIP_TAC \\ IMP_RES_TAC compile_exps_LENGTH
      \\ `?d. c1 = [d]` by (Cases_on `c1` \\ full_simp_tac(srw_ss())[LENGTH_NIL])
      \\ SIMP_TAC std_ss [Once bviPropsTheory.evaluate_CONS] \\ full_simp_tac(srw_ss())[]
      \\ SIMP_TAC std_ss [Once bviPropsTheory.evaluate_CONS] \\ full_simp_tac(srw_ss())[GSYM PULL_FORALL]
      \\ Q.LIST_EXISTS_TAC [`t2`,`b2`,`c`] \\ full_simp_tac(srw_ss())[] \\ NO_TAC)
    \\ REPEAT STRIP_TAC
    \\ Q.PAT_ASSUM `!nn mm. bbb` (MP_TAC o Q.SPEC `n1`) \\ full_simp_tac(srw_ss())[]
    \\ `res6 <> Rerr(Rabort Rtype_error)` by (REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]) \\ full_simp_tac(srw_ss())[]
    \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC compile_exps_LENGTH
    \\ `?d. c1 = [d]` by (Cases_on `c1` \\ full_simp_tac(srw_ss())[LENGTH_NIL]) \\ full_simp_tac(srw_ss())[]
    \\ `aux_code_installed aux2 t2.code` by
     (full_simp_tac(srw_ss())[GSYM PULL_FORALL]
      \\ IMP_RES_TAC evaluate_code_const \\ full_simp_tac(srw_ss())[inc_clock_def])
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`b2`]) \\ full_simp_tac(srw_ss())[]
    \\ `s2 = s6` by (BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[])
    \\ impl_tac >- metis_tac[evaluate_global_mono,inc_clock_global]
    \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[GSYM PULL_FORALL]
    \\ Q.MATCH_ASSUM_RENAME_TAC
        `evaluate (c2,MAP (adjust_bv b3) env,inc_clock c4 t2) =
           (map_result (MAP (adjust_bv b3)) (adjust_bv b3) res6,t3)`
    \\ IMP_RES_TAC evaluate_inv_clock
    \\ full_simp_tac(srw_ss())[inc_clock_ADD]
    \\ ONCE_REWRITE_TAC [bviPropsTheory.evaluate_CONS] \\ full_simp_tac(srw_ss())[]
    \\ REV_FULL_SIMP_TAC std_ss []
    \\ Q.LIST_EXISTS_TAC [`t3`,`b3`,`c4 + c`] \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `res6` \\ full_simp_tac(srw_ss())[]
    \\ Q.PAT_ASSUM `xx = res` (ASSUME_TAC o GSYM) \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC evaluate_refs_SUBSET \\ full_simp_tac(srw_ss())[SUBSET_DEF]
    \\ IMP_RES_TAC bvlPropsTheory.evaluate_SING \\ full_simp_tac(srw_ss())[]
    \\ MATCH_MP_TAC bv_ok_IMP_adjust_bv_eq \\ full_simp_tac(srw_ss())[])
  THEN1 (* Var *)
   (Cases_on `n < LENGTH env` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[iEval_def] \\ Q.LIST_EXISTS_TAC [`b1`,`0`]
    \\ full_simp_tac(srw_ss())[inc_clock_ZERO,EL_MAP])
  THEN1 (* If *)
   (Q.ABBREV_TAC `n4 = n2` \\ POP_ASSUM (K ALL_TAC)
    \\ `?c1 aux1 n1. compile_exps n [x1] = (c1,aux1,n1)` by METIS_TAC [PAIR]
    \\ `?c2 aux2 n2. compile_exps n1 [x2] = (c2,aux2,n2)` by METIS_TAC [PAIR]
    \\ `?c3 aux3 n3. compile_exps n2 [x3] = (c3,aux3,n3)` by METIS_TAC [PAIR]
    \\ full_simp_tac(srw_ss())[LET_DEF] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[PULL_FORALL]
    \\ `?res5 s5. evaluate ([x1],env,s) = (res5,s5)` by METIS_TAC [PAIR]
    \\ IMP_RES_TAC evaluate_ok \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC aux_code_installed_APPEND \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[] \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `n`) \\ full_simp_tac(srw_ss())[]
    \\ reverse (Cases_on `res5`) \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`t1`,`b1`]) \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC aux_code_installed_APPEND \\ full_simp_tac(srw_ss())[GSYM PULL_FORALL]
    \\ TRY (
      impl_tac >- (rpt strip_tac >> full_simp_tac(srw_ss())[])
      \\ REPEAT STRIP_TAC \\ IMP_RES_TAC compile_exps_LENGTH
      \\ `?d. c1 = [d]` by (Cases_on `c1` \\ full_simp_tac(srw_ss())[LENGTH_NIL])
      \\ SIMP_TAC std_ss [Once iEval_def] \\ full_simp_tac(srw_ss())[]
      \\ Q.LIST_EXISTS_TAC [`t2`,`b2`,`c`] \\ full_simp_tac(srw_ss())[]
      \\ srw_tac[][] \\ NO_TAC)
    \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC bvlPropsTheory.evaluate_SING \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `d1 = Boolv T` \\ full_simp_tac(srw_ss())[]
    THEN1
     (IMP_RES_TAC compile_exps_LENGTH
      \\ `?d. c1 = [d]` by (Cases_on `c1` \\ full_simp_tac(srw_ss())[LENGTH_NIL])
      \\ SIMP_TAC std_ss [Once iEval_def] \\ full_simp_tac(srw_ss())[]
      \\ `?d2. c2 = [d2]` by (Cases_on `c2` \\ full_simp_tac(srw_ss())[LENGTH_NIL]) \\ full_simp_tac(srw_ss())[]
      \\ Q.PAT_ASSUM `!nn mm. bbb` (MP_TAC o Q.SPEC `n1`) \\ full_simp_tac(srw_ss())[]
      \\ `aux_code_installed aux2 t2.code` by
       (full_simp_tac(srw_ss())[GSYM PULL_FORALL]
        \\ IMP_RES_TAC evaluate_code_const \\ full_simp_tac(srw_ss())[inc_clock_def])
      \\ REPEAT STRIP_TAC
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`b2`]) \\ full_simp_tac(srw_ss())[]
      \\ impl_tac >- metis_tac[evaluate_global_mono,inc_clock_global]
      \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[GSYM PULL_FORALL]
      \\ IMP_RES_TAC evaluate_inv_clock \\ full_simp_tac(srw_ss())[inc_clock_ADD]
      \\ REV_FULL_SIMP_TAC std_ss []
      \\ Q.LIST_EXISTS_TAC [`t2'`,`b2'`,`c' + c`] \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[adjust_bv_def]
      \\ IMP_RES_TAC evaluate_refs_SUBSET \\ full_simp_tac(srw_ss())[SUBSET_DEF])
    \\ Cases_on `d1 = Boolv F` \\ full_simp_tac(srw_ss())[]
    THEN1
     (IMP_RES_TAC compile_exps_LENGTH
      \\ `?d. c1 = [d]` by (Cases_on `c1` \\ full_simp_tac(srw_ss())[LENGTH_NIL])
      \\ SIMP_TAC std_ss [Once iEval_def] \\ full_simp_tac(srw_ss())[]
      \\ `?d3. c3 = [d3]` by (Cases_on `c3` \\ full_simp_tac(srw_ss())[LENGTH_NIL]) \\ full_simp_tac(srw_ss())[]
      \\ Q.PAT_ASSUM `!nn mm. bbb` (MP_TAC o Q.SPEC `n2`) \\ full_simp_tac(srw_ss())[]
      \\ `aux_code_installed aux3 t2.code` by
       (full_simp_tac(srw_ss())[GSYM PULL_FORALL]
        \\ IMP_RES_TAC evaluate_code_const \\ full_simp_tac(srw_ss())[inc_clock_def])
      \\ REPEAT STRIP_TAC
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`b2`]) \\ full_simp_tac(srw_ss())[]
      \\ impl_tac >- metis_tac[evaluate_global_mono,inc_clock_global]
      \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[GSYM PULL_FORALL]
      \\ IMP_RES_TAC evaluate_inv_clock \\ full_simp_tac(srw_ss())[inc_clock_ADD]
      \\ REV_FULL_SIMP_TAC std_ss []
      \\ Q.LIST_EXISTS_TAC [`t2'`,`b2'`,`c' + c`] \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[adjust_bv_def]
      \\ IMP_RES_TAC evaluate_refs_SUBSET \\ full_simp_tac(srw_ss())[SUBSET_DEF]))
  THEN1 (* Let *)
   (`?c1 aux1 n1. compile_exps n xs = (c1,aux1,n1)` by METIS_TAC [PAIR]
    \\ `?c2 aux2 n2. compile_exps n1 [x2] = (c2,aux2,n2)` by METIS_TAC [PAIR]
    \\ full_simp_tac(srw_ss())[LET_DEF] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[PULL_FORALL]
    \\ `?res5 s5. evaluate (xs,env,s) = (res5,s5)` by METIS_TAC [PAIR]
    \\ IMP_RES_TAC evaluate_ok \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC aux_code_installed_APPEND \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[] \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `n`) \\ full_simp_tac(srw_ss())[]
    \\ reverse (Cases_on `res5`) \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`t1`,`b1`]) \\ full_simp_tac(srw_ss())[]
    \\ TRY (
      impl_tac >- (rpt strip_tac >> full_simp_tac(srw_ss())[])
      \\ REPEAT STRIP_TAC \\ IMP_RES_TAC compile_exps_LENGTH
      \\ `?d. c2 = [d]` by (Cases_on `c2` \\ full_simp_tac(srw_ss())[LENGTH_NIL])
      \\ SIMP_TAC std_ss [Once iEval_def] \\ full_simp_tac(srw_ss())[]
      \\ Q.LIST_EXISTS_TAC [`t2`,`b2`,`c`] \\ full_simp_tac(srw_ss())[]
      \\ srw_tac[][] \\ NO_TAC)
    \\ REPEAT STRIP_TAC
    \\ Q.MATCH_ASSUM_RENAME_TAC `evaluate ([x2],a ++ env,s5) = (res6,s6)`
    \\ Q.PAT_ASSUM `!nn mm. bbb` (MP_TAC o Q.SPEC `n1`) \\ full_simp_tac(srw_ss())[]
    \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC compile_exps_LENGTH
    \\ `?d. c2 = [d]` by (Cases_on `c2` \\ full_simp_tac(srw_ss())[LENGTH_NIL]) \\ full_simp_tac(srw_ss())[]
    \\ `aux_code_installed aux2 t2.code` by
     (full_simp_tac(srw_ss())[GSYM PULL_FORALL]
      \\ IMP_RES_TAC evaluate_code_const \\ full_simp_tac(srw_ss())[inc_clock_def])
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`b2`]) \\ full_simp_tac(srw_ss())[]
    \\ impl_tac >- metis_tac[evaluate_global_mono,inc_clock_global]
    \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[GSYM PULL_FORALL]
    \\ Q.MATCH_ASSUM_RENAME_TAC
        `evaluate ([d],MAP (adjust_bv b3) a ++
                    MAP (adjust_bv b3) env,inc_clock c4 t2) =
           (map_result (MAP (adjust_bv b3)) (adjust_bv b3) res6,t3)`
    \\ IMP_RES_TAC evaluate_inv_clock
    \\ full_simp_tac(srw_ss())[inc_clock_ADD]
    \\ ONCE_REWRITE_TAC [iEval_def] \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[MAP_APPEND_MAP_EQ]
    \\ REV_FULL_SIMP_TAC std_ss []
    \\ Q.LIST_EXISTS_TAC [`t3`,`b3`,`c4 + c`] \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC evaluate_refs_SUBSET \\ full_simp_tac(srw_ss())[SUBSET_DEF])
  THEN1 (* Raise *)
   (`?c1 aux1 n1. compile_exps n [x1] = (c1,aux1,n1)` by METIS_TAC [PAIR]
    \\ full_simp_tac(srw_ss())[LET_DEF] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[PULL_FORALL]
    \\ IMP_RES_TAC compile_exps_LENGTH
    \\ `?d. c1 = [d]` by (Cases_on `c1` \\ full_simp_tac(srw_ss())[LENGTH_NIL]) \\ full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] []
    \\ `?res5 s5. evaluate ([x1],env,s) = (res5,s5)` by METIS_TAC [PAIR]
    \\ reverse (Cases_on `res5`) \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `n`) \\ full_simp_tac(srw_ss())[]
    \\ TRY (SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]
      \\ REPEAT STRIP_TAC \\ RES_TAC
      \\ Q.LIST_EXISTS_TAC [`t2`,`b2`,`c`] \\ full_simp_tac(srw_ss())[]
      \\ SIMP_TAC std_ss [Once bviPropsTheory.evaluate_CONS] \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[iEval_def] \\ NO_TAC)
    \\ REPEAT STRIP_TAC \\ RES_TAC \\ full_simp_tac(srw_ss())[iEval_def]
    \\ Q.LIST_EXISTS_TAC [`t2`,`b2`,`c`] \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ IMP_RES_TAC bvlPropsTheory.evaluate_SING \\ SRW_TAC [] [])
  THEN1 (* Handle *)
   (Cases_on `x1` \\ full_simp_tac(srw_ss())[GoodHandleLet_def,destLet_def]
    \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ full_simp_tac(srw_ss())[compile_exps_Var_list]
    \\ `?c2 aux2 n2. compile_exps n [e] = (c2,aux2,n2)` by METIS_TAC [PAIR]
    \\ `?c3 aux3 n3. compile_exps n2' [x2] = (c3,aux3,n3)` by METIS_TAC [PAIR]
    \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ full_simp_tac(srw_ss())[bEval_def]
    \\ Q.ISPECL_THEN[`s1`,`l`]mp_tac (Q.GEN`s`evaluate_Var_list)
    \\ full_simp_tac(srw_ss())[]
    \\ STRIP_TAC \\ full_simp_tac(srw_ss())[]
    \\ `evaluate ([e],vs ++ env,s1) = evaluate ([e],vs,s1)` by ALL_TAC
    THEN1 (MATCH_MP_TAC bEval_bVarBound \\ full_simp_tac(srw_ss())[])
    \\ full_simp_tac(srw_ss())[] \\ POP_ASSUM (K ALL_TAC)
    \\ Cases_on `evaluate ([e],vs,s1)` \\ full_simp_tac(srw_ss())[]
    \\ `?d2. c2 = [d2]` by
           (IMP_RES_TAC compile_exps_LENGTH \\ Cases_on `c2`
            \\ full_simp_tac(srw_ss())[LENGTH_NIL])
    \\ `?d3. c3 = [d3]` by
           (IMP_RES_TAC compile_exps_LENGTH \\ Cases_on `c3`
            \\ full_simp_tac(srw_ss())[LENGTH_NIL])
    \\ full_simp_tac(srw_ss())[] \\ NTAC 2 (POP_ASSUM (K ALL_TAC))
    \\ (Cases_on `q`) \\ full_simp_tac(srw_ss())[]
    THEN1 (* Result case *)
     (SRW_TAC [] [] \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `n`)
      \\ full_simp_tac(srw_ss())[compile_exps_def,compile_exps_Var_list,LET_DEF]
      \\ STRIP_TAC \\ POP_ASSUM (Q.SPECL_THEN [`t1`,`b1`]mp_tac)
      \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC aux_code_installed_APPEND \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC aux_code_installed_APPEND \\ full_simp_tac(srw_ss())[]
      \\ REPEAT STRIP_TAC
      \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
      \\ full_simp_tac(srw_ss())[aux_code_installed_def,iEval_def,find_code_def]
      \\ IMP_RES_TAC (GEN_ALL evaluate_MAP_Var) \\ full_simp_tac(srw_ss())[]
      \\ `evaluate ([d2],MAP (adjust_bv b2) vs ++ MAP (adjust_bv b2) env,
            inc_clock c t1) =
          evaluate ([d2],MAP (adjust_bv b2) vs,inc_clock c t1)` by ALL_TAC THEN1
       (Q.SPECL_THEN[`n`,`[e]`,`n`,`MAP (adjust_bv b2) vs`,`t`]mp_tac iEval_bVarBound
        \\ full_simp_tac(srw_ss())[bEvery_def]
        \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[])
      \\ full_simp_tac(srw_ss())[] \\ POP_ASSUM (K ALL_TAC)
      \\ Q.LIST_EXISTS_TAC [`t2`,`b2`,`c + 1`] \\ full_simp_tac(srw_ss())[]
      \\ `dec_clock 1 (inc_clock (c + 1) t1) = inc_clock c t1` by
        (EVAL_TAC \\ full_simp_tac(srw_ss())[bviSemTheory.state_component_equality]
         \\ DECIDE_TAC) \\ full_simp_tac(srw_ss())[]
      \\ drule bvi_letProofTheory.evaluate_compile_exp \\ fs[])
    \\ (Cases_on`e'`) \\ full_simp_tac(srw_ss())[]
    THEN1 (* Raise case *)
     (SRW_TAC [] [] \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `n`)
      \\ full_simp_tac(srw_ss())[compile_exps_def,compile_exps_Var_list,LET_DEF]
      \\ STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPECL [`t1`,`b1`])
      \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC aux_code_installed_APPEND \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC aux_code_installed_APPEND \\ full_simp_tac(srw_ss())[]
      \\ REPEAT STRIP_TAC
      \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
      \\ full_simp_tac(srw_ss())[aux_code_installed_def,iEval_def,find_code_def]
      \\ IMP_RES_TAC (GEN_ALL evaluate_MAP_Var) \\ full_simp_tac(srw_ss())[]
      \\ `evaluate ([d2],MAP (adjust_bv b2) vs ++ MAP (adjust_bv b2) env,
            inc_clock c t1) =
          evaluate ([d2],MAP (adjust_bv b2) vs,inc_clock c t1)` by ALL_TAC THEN1
       ((iEval_bVarBound |> SPEC_ALL |> Q.INST [`xs`|->`[e]`,
           `vs`|->`MAP (adjust_bv b2) vs`]
           |> Q.GENL [`env`,`s`] |> MP_TAC) \\ full_simp_tac(srw_ss())[bEvery_def]
        \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[])
      \\ full_simp_tac(srw_ss())[] \\ POP_ASSUM (K ALL_TAC)
      \\ Q.PAT_ASSUM `!nn mm nn1. bbb` (MP_TAC o Q.SPEC `n2'`)
      \\ full_simp_tac(srw_ss())[]
      \\ REPEAT STRIP_TAC
      \\ POP_ASSUM (MP_TAC o Q.SPECL [`t2`,`b2`]) \\ full_simp_tac(srw_ss())[]
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
       (IMP_RES_TAC evaluate_ok \\ full_simp_tac(srw_ss())[]
        \\ REV_FULL_SIMP_TAC std_ss []
        \\ IMP_RES_TAC aux_code_installed_APPEND \\ full_simp_tac(srw_ss())[]
        \\ IMP_RES_TAC aux_code_installed_APPEND \\ full_simp_tac(srw_ss())[]
        \\ IMP_RES_TAC evaluate_code_const
        \\ imp_res_tac evaluate_global_mono
        \\ full_simp_tac(srw_ss())[inc_clock_def]
        \\ `EVERY (bv_ok r.refs) env` by ALL_TAC \\ full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ REPEAT STRIP_TAC \\ RES_TAC
        \\ IMP_RES_TAC evaluate_refs_SUBSET
        \\ IMP_RES_TAC bv_ok_SUBSET_IMP)
      \\ REPEAT STRIP_TAC
      \\ Q.LIST_EXISTS_TAC [`t2'`,`b2'`,`c' + c + 1`] \\ full_simp_tac(srw_ss())[]
      \\ `dec_clock 1 (inc_clock (c' + c + 1) t1) = inc_clock (c' + c) t1` by
        (EVAL_TAC \\ full_simp_tac(srw_ss())[bviSemTheory.state_component_equality]
         \\ DECIDE_TAC) \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC evaluate_inv_clock \\ full_simp_tac(srw_ss())[inc_clock_ADD]
      \\ `MAP (adjust_bv b2) vs = MAP (adjust_bv b2') vs` by ALL_TAC THEN1
       (full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
        \\ MATCH_MP_TAC (bv_ok_IMP_adjust_bv_eq |> GEN_ALL)
        \\ Q.EXISTS_TAC `r` \\ full_simp_tac(srw_ss())[]
        \\ IMP_RES_TAC evaluate_ok \\ full_simp_tac(srw_ss())[]
        \\ REV_FULL_SIMP_TAC std_ss []
        \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ RES_TAC)
      \\ full_simp_tac(srw_ss())[] \\ IMP_RES_TAC evaluate_refs_SUBSET
      \\ full_simp_tac(srw_ss())[SUBSET_DEF]
      \\ qpat_assum `!n. _ = _` (qspec_then `c'` assume_tac)
      \\ drule bvi_letProofTheory.evaluate_compile_exp \\ fs[])
    THEN1 (* abort case *)
     (SRW_TAC [] [] \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `n`)
      \\ full_simp_tac(srw_ss())[compile_exps_def,compile_exps_Var_list,LET_DEF]
      \\ STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPECL [`t1`,`b1`])
      \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC aux_code_installed_APPEND \\ full_simp_tac(srw_ss())[]
      \\ IMP_RES_TAC aux_code_installed_APPEND \\ full_simp_tac(srw_ss())[]
      \\ REPEAT STRIP_TAC
      \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
      \\ full_simp_tac(srw_ss())[aux_code_installed_def,iEval_def,find_code_def]
      \\ IMP_RES_TAC (GEN_ALL evaluate_MAP_Var) \\ full_simp_tac(srw_ss())[]
      \\ `evaluate ([d2],MAP (adjust_bv b2) vs ++ MAP (adjust_bv b2) env,
            inc_clock c t1) =
          evaluate ([d2],MAP (adjust_bv b2) vs,inc_clock c t1)` by ALL_TAC THEN1
       ((iEval_bVarBound |> SPEC_ALL |> Q.INST [`xs`|->`[e]`,
           `vs`|->`MAP (adjust_bv b2) vs`]
           |> Q.GENL [`env`,`s`] |> MP_TAC) \\ full_simp_tac(srw_ss())[bEvery_def]
        \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[])
      \\ full_simp_tac(srw_ss())[] \\ POP_ASSUM (K ALL_TAC)
      \\ Q.LIST_EXISTS_TAC [`t2`,`b2`,`c + 1`] \\ full_simp_tac(srw_ss())[]
      \\ `dec_clock 1 (inc_clock (c + 1) t1) = inc_clock c t1` by
        (EVAL_TAC \\ full_simp_tac(srw_ss())[bviSemTheory.state_component_equality]
         \\ DECIDE_TAC) \\ full_simp_tac(srw_ss())[]
      \\ drule bvi_letProofTheory.evaluate_compile_exp \\ fs[]))
  THEN1 (* Op *)
   (`?c1 aux1 n1. compile_exps n xs = (c1,aux1,n1)` by METIS_TAC [PAIR]
    \\ full_simp_tac(srw_ss())[LET_DEF] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[PULL_FORALL]
    \\ `?res5 s5. evaluate (xs,env,s) = (res5,s5)` by METIS_TAC [PAIR]
    \\ full_simp_tac(srw_ss())[] \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `n`) \\ full_simp_tac(srw_ss())[]
    \\ reverse (Cases_on `res5`) \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ first_x_assum (MP_TAC o Q.SPECL [`t1`,`b1`]) \\ full_simp_tac(srw_ss())[]
    THEN1 (
      REPEAT STRIP_TAC \\ IMP_RES_TAC compile_exps_LENGTH \\ full_simp_tac(srw_ss())[iEval_def]
      \\ Q.LIST_EXISTS_TAC [`t2`,`b2`] \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `op` \\ full_simp_tac(srw_ss())[compile_op_def,iEval_def,compile_int_thm,iEval_append]
      \\ qexists_tac`c`>>simp[]>>
         every_case_tac \\ full_simp_tac(srw_ss())[iEval_def,compile_int_thm])
    \\ REPEAT STRIP_TAC \\ Cases_on `do_app op (REVERSE a) s5` \\ full_simp_tac(srw_ss())[]
    \\ TRY(
      srw_tac[][] >>
      CHANGED_TAC(imp_res_tac bvlPropsTheory.do_app_err))
    \\ full_simp_tac(srw_ss())[GSYM PULL_FORALL]
    \\ Cases_on`a'`>>full_simp_tac(srw_ss())[]\\srw_tac[][]
    \\ Cases_on `?i. op = Const i` \\ full_simp_tac(srw_ss())[] THEN1
     (CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `b2`
      \\ CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `c`
      \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[compile_op_def] \\ Cases_on `c1`
      \\ full_simp_tac(srw_ss())[compile_int_thm,bEvalOp_def,iEval_def]
      \\ Cases_on `REVERSE a` \\ full_simp_tac(srw_ss())[iEval_def,iEvalOp_def]
      \\ full_simp_tac(srw_ss())[EVAL ``do_app_aux (Const 0) [] t2``]
      \\ SRW_TAC [] [adjust_bv_def])
    \\ Cases_on `op = Ref` \\ full_simp_tac(srw_ss())[] THEN1
     (full_simp_tac(srw_ss())[compile_op_def,iEval_def]
      \\ Q.ABBREV_TAC `b3 = ((LEAST ptr. ptr NOTIN FDOM s5.refs) =+
           (LEAST ptr. ptr NOTIN FDOM (bvi_to_bvl t2).refs)) b2`
      \\ CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `b3`
      \\ CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `c`
      \\ full_simp_tac(srw_ss())[iEvalOp_def,do_app_aux_def,bEvalOp_def,LET_DEF]
      \\ Q.ABBREV_TAC `x = (LEAST ptr. ptr NOTIN FDOM s5.refs)`
      \\ Q.ABBREV_TAC `y = LEAST ptr. ptr NOTIN FDOM (bvi_to_bvl t2).refs`
      \\ `~(x IN FDOM s5.refs)` by ALL_TAC THEN1
       (`?p. (\ptr. ptr NOTIN FDOM s5.refs) p` by
          (SIMP_TAC std_ss [] \\ METIS_TAC [NUM_NOT_IN_FDOM])
        \\ IMP_RES_TAC whileTheory.LEAST_INTRO \\ full_simp_tac(srw_ss())[]
        \\ REV_FULL_SIMP_TAC std_ss [])
      \\ `~(y IN FDOM t2.refs)` by ALL_TAC THEN1
       (`?p. (\ptr. ptr NOTIN FDOM t2.refs) p` by
          (SIMP_TAC std_ss [] \\ METIS_TAC [NUM_NOT_IN_FDOM])
        \\ IMP_RES_TAC whileTheory.LEAST_INTRO \\ full_simp_tac(srw_ss())[bvi_to_bvl_def]
        \\ REV_FULL_SIMP_TAC (srw_ss()) [bvi_to_bvl_def])
      \\ full_simp_tac(srw_ss())[]
      \\ SRW_TAC [] [adjust_bv_def]
      \\ `MAP (adjust_bv b3) env = MAP (adjust_bv b2) env` by ALL_TAC THEN1
       (full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
        \\ MATCH_MP_TAC bv_ok_IMP_adjust_bv_eq
        \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ RES_TAC
        \\ IMP_RES_TAC evaluate_refs_SUBSET
        \\ REPEAT STRIP_TAC THEN1 METIS_TAC [bv_ok_SUBSET_IMP]
        \\ Q.UNABBREV_TAC `b3` \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
        \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
      \\ `MAP (adjust_bv b3) a = MAP (adjust_bv b2) a` by ALL_TAC THEN1
       (full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
        \\ MATCH_MP_TAC bv_ok_IMP_adjust_bv_eq
        \\ IMP_RES_TAC evaluate_ok \\ REV_FULL_SIMP_TAC std_ss [] \\ full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ RES_TAC
        \\ Q.UNABBREV_TAC `b3` \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
        \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
      \\ `MAP (OPTION_MAP (adjust_bv b2)) s5.globals =
          MAP (OPTION_MAP (adjust_bv b3)) s5.globals` by ALL_TAC THEN1
       (full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
        \\ Cases_on `e` \\ full_simp_tac(srw_ss())[]
        \\ MATCH_MP_TAC bv_ok_IMP_adjust_bv_eq
        \\ IMP_RES_TAC evaluate_ok \\ REV_FULL_SIMP_TAC std_ss [] \\ full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[state_ok_def,EVERY_MEM] \\ RES_TAC \\ full_simp_tac(srw_ss())[]
        \\ Q.UNABBREV_TAC `b3` \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
        \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
      \\ full_simp_tac(srw_ss())[] \\ STRIP_TAC
      THEN1 (UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM])
      \\ reverse STRIP_TAC THEN1
       (REPEAT STRIP_TAC \\ UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
        \\ SRW_TAC [] []
        \\ IMP_RES_TAC evaluate_refs_SUBSET \\ full_simp_tac(srw_ss())[SUBSET_DEF] \\ RES_TAC)
      \\ simp[bvl_to_bvi_with_refs,bvl_to_bvi_id]
      \\ full_simp_tac(srw_ss())[state_rel_def,bvl_to_bvi_def,bvi_to_bvl_def,FLOOKUP_UPDATE]
      \\ STRIP_TAC
      THEN1 (Q.UNABBREV_TAC `b3` \\ MATCH_MP_TAC INJ_EXTEND \\ full_simp_tac(srw_ss())[])
      \\ srw_tac[][MAP_REVERSE] \\ full_simp_tac(srw_ss())[]
      \\ TRY ( full_simp_tac(srw_ss())[Abbr`b3`,APPLY_UPDATE_THM] \\ NO_TAC)
      \\ TRY ( simp[Abbr`b3`,APPLY_UPDATE_THM] >> srw_tac[][] >> NO_TAC)
      \\ TRY ( full_simp_tac(srw_ss())[FLOOKUP_DEF] >> NO_TAC)
      \\ TRY ( qexists_tac`z`>>simp[]>>
        simp[GSYM MAP_MAP_o] >> srw_tac[][] >>
        simp[Abbr`b3`,APPLY_UPDATE_THM] >> srw_tac[][] >> NO_TAC)
      \\ Cases_on `FLOOKUP s5.refs k = NONE` \\ full_simp_tac(srw_ss())[rich_listTheory.MAP_REVERSE]
      \\ (`b3 k <> y` by ALL_TAC THEN1
       (full_simp_tac(srw_ss())[] \\ Q.UNABBREV_TAC `b3` \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM,FLOOKUP_DEF]
        \\ full_simp_tac(srw_ss())[INJ_DEF] \\ RES_TAC \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]))
      \\ (`b3 k = b2 k` by ALL_TAC
           THEN1 (Q.UNABBREV_TAC `b3` \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM,FLOOKUP_DEF]))
      THEN1 ( full_simp_tac(srw_ss())[FLOOKUP_DEF] >> METIS_TAC[INJ_DEF] )
      \\ full_simp_tac(srw_ss())[] \\ Cases_on `FLOOKUP s5.refs k` \\ full_simp_tac(srw_ss())[]
      \\ ntac 3 (Q.PAT_ASSUM `!k. bbb` MP_TAC)
      \\ Q.PAT_ASSUM `!k. bbb` (MP_TAC o Q.SPEC `k`) \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `x'` \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
      \\ full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
      \\ MATCH_MP_TAC bv_ok_IMP_adjust_bv_eq
      \\ IMP_RES_TAC evaluate_ok \\ REV_FULL_SIMP_TAC std_ss [] \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[state_ok_def]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `k`) \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ REPEAT STRIP_TAC
      \\ Q.UNABBREV_TAC `b3` \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
      \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
    \\ Cases_on `op = RefArray` \\ full_simp_tac(srw_ss())[] THEN1
     (full_simp_tac(srw_ss())[compile_op_def,iEval_def]
      \\ Q.ABBREV_TAC `b3 = ((LEAST ptr. ptr NOTIN FDOM s5.refs) =+
           (LEAST ptr. ptr NOTIN FDOM (bvi_to_bvl t2).refs)) b2`
      \\ CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `b3`
      \\ CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `c`
      \\ full_simp_tac(srw_ss())[iEvalOp_def,do_app_aux_def,bEvalOp_def,LET_DEF]
      \\ Q.ABBREV_TAC `x = (LEAST ptr. ptr NOTIN FDOM s5.refs)`
      \\ Q.ABBREV_TAC `y = LEAST ptr. ptr NOTIN FDOM (bvi_to_bvl t2).refs`
      \\ `~(x IN FDOM s5.refs)` by ALL_TAC THEN1
       (`?p. (\ptr. ptr NOTIN FDOM s5.refs) p` by
          (SIMP_TAC std_ss [] \\ METIS_TAC [NUM_NOT_IN_FDOM])
        \\ IMP_RES_TAC whileTheory.LEAST_INTRO \\ full_simp_tac(srw_ss())[]
        \\ REV_FULL_SIMP_TAC std_ss [])
      \\ `~(y IN FDOM t2.refs)` by ALL_TAC THEN1
       (`?p. (\ptr. ptr NOTIN FDOM t2.refs) p` by
          (SIMP_TAC std_ss [] \\ METIS_TAC [NUM_NOT_IN_FDOM])
        \\ IMP_RES_TAC whileTheory.LEAST_INTRO \\ full_simp_tac(srw_ss())[bvi_to_bvl_def]
        \\ REV_FULL_SIMP_TAC (srw_ss()) [bvi_to_bvl_def])
      \\ full_simp_tac(srw_ss())[]
      \\ SRW_TAC [] [adjust_bv_def]
      \\ `MAP (adjust_bv b3) env = MAP (adjust_bv b2) env` by ALL_TAC THEN1
       (full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
        \\ MATCH_MP_TAC bv_ok_IMP_adjust_bv_eq
        \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ RES_TAC
        \\ IMP_RES_TAC evaluate_refs_SUBSET
        \\ REPEAT STRIP_TAC THEN1 METIS_TAC [bv_ok_SUBSET_IMP]
        \\ Q.UNABBREV_TAC `b3` \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
        \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
      \\ `MAP (adjust_bv b3) a = MAP (adjust_bv b2) a` by ALL_TAC THEN1
       (full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
        \\ MATCH_MP_TAC bv_ok_IMP_adjust_bv_eq
        \\ IMP_RES_TAC evaluate_ok \\ REV_FULL_SIMP_TAC std_ss [] \\ full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ RES_TAC
        \\ Q.UNABBREV_TAC `b3` \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
        \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
      \\ `MAP (OPTION_MAP (adjust_bv b2)) s5.globals =
          MAP (OPTION_MAP (adjust_bv b3)) s5.globals` by ALL_TAC THEN1
       (full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
        \\ Cases_on `e` \\ full_simp_tac(srw_ss())[]
        \\ MATCH_MP_TAC bv_ok_IMP_adjust_bv_eq
        \\ IMP_RES_TAC evaluate_ok \\ REV_FULL_SIMP_TAC std_ss [] \\ full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[state_ok_def,EVERY_MEM] \\ RES_TAC \\ full_simp_tac(srw_ss())[]
        \\ Q.UNABBREV_TAC `b3` \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
        \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
      \\ full_simp_tac(srw_ss())[]
      \\ Cases_on`REVERSE a`>>full_simp_tac(srw_ss())[]
      \\ Cases_on`t`>>full_simp_tac(srw_ss())[]
      \\ Cases_on`h`>>full_simp_tac(srw_ss())[]
      \\ Cases_on`t'`>>full_simp_tac(srw_ss())[]
      \\ Cases_on`0 ≤ i` >>full_simp_tac(srw_ss())[]
      \\ Cases_on`a`>>full_simp_tac(srw_ss())[adjust_bv_def]
      \\ STRIP_TAC THEN1 (
        rpt var_eq_tac >>
        simp[Abbr`b3`,adjust_bv_def,APPLY_UPDATE_THM] )
      \\ reverse STRIP_TAC THEN1
       (REPEAT STRIP_TAC \\ UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
        \\ SRW_TAC [] []
        \\ IMP_RES_TAC evaluate_refs_SUBSET \\ full_simp_tac(srw_ss())[SUBSET_DEF] \\ RES_TAC)
      \\ simp[bvl_to_bvi_with_refs,bvl_to_bvi_id]
      \\ full_simp_tac(srw_ss())[state_rel_def,bvl_to_bvi_def,bvi_to_bvl_def,FLOOKUP_UPDATE]
      \\ rpt var_eq_tac \\ simp[]
      \\ STRIP_TAC
      THEN1 (Q.UNABBREV_TAC `b3` \\ MATCH_MP_TAC INJ_EXTEND \\ full_simp_tac(srw_ss())[])
      \\ simp[FLOOKUP_UPDATE]
      \\ srw_tac[][MAP_REVERSE] \\ full_simp_tac(srw_ss())[]
      \\ TRY ( full_simp_tac(srw_ss())[Abbr`b3`,APPLY_UPDATE_THM] \\ NO_TAC)
      \\ TRY ( simp[Abbr`b3`,APPLY_UPDATE_THM] >> srw_tac[][] >> NO_TAC)
      \\ TRY ( full_simp_tac(srw_ss())[FLOOKUP_DEF] >> NO_TAC)
      \\ TRY (
        qexists_tac`z`>>simp[]>>
        simp[GSYM MAP_MAP_o] >> srw_tac[][] >>
        simp[Abbr`b3`,APPLY_UPDATE_THM] >> srw_tac[][] >> NO_TAC)
      \\ simp[map_replicate]
      \\ Cases_on `FLOOKUP s5.refs k = NONE` \\ full_simp_tac(srw_ss())[rich_listTheory.MAP_REVERSE]
      \\ (`b3 k <> y` by ALL_TAC THEN1
       (full_simp_tac(srw_ss())[] \\ Q.UNABBREV_TAC `b3` \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM,FLOOKUP_DEF]
        \\ full_simp_tac(srw_ss())[INJ_DEF] \\ RES_TAC \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]))
      \\ (`b3 k = b2 k` by ALL_TAC
           THEN1 (Q.UNABBREV_TAC `b3` \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM,FLOOKUP_DEF]))
      THEN1 ( full_simp_tac(srw_ss())[FLOOKUP_DEF] >> METIS_TAC[INJ_DEF] )
      \\ full_simp_tac(srw_ss())[] \\ Cases_on `FLOOKUP s5.refs k` \\ full_simp_tac(srw_ss())[]
      \\ ntac 3 (Q.PAT_ASSUM `!k. bbb` MP_TAC)
      \\ Q.PAT_ASSUM `!k. bbb` (MP_TAC o Q.SPEC `k`) \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `x'` \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
      \\ full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
      \\ MATCH_MP_TAC bv_ok_IMP_adjust_bv_eq
      \\ IMP_RES_TAC evaluate_ok \\ REV_FULL_SIMP_TAC std_ss [] \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[state_ok_def]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `k`) \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ REPEAT STRIP_TAC
      \\ Q.UNABBREV_TAC `b3` \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
      \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
    \\ Cases_on`op = RefByte` \\ full_simp_tac(srw_ss())[] THEN1
     (full_simp_tac(srw_ss())[compile_op_def,iEval_def]
      \\ Q.ABBREV_TAC `b3 = ((LEAST ptr. ptr NOTIN FDOM s5.refs) =+
           (LEAST ptr. ptr NOTIN FDOM (bvi_to_bvl t2).refs)) b2`
      \\ CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `b3`
      \\ CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `c`
      \\ full_simp_tac(srw_ss())[iEvalOp_def,do_app_aux_def,bEvalOp_def,LET_DEF]
      \\ Q.ABBREV_TAC `x = (LEAST ptr. ptr NOTIN FDOM s5.refs)`
      \\ Q.ABBREV_TAC `y = LEAST ptr. ptr NOTIN FDOM (bvi_to_bvl t2).refs`
      \\ `~(x IN FDOM s5.refs)` by ALL_TAC THEN1
       (`?p. (\ptr. ptr NOTIN FDOM s5.refs) p` by
          (SIMP_TAC std_ss [] \\ METIS_TAC [NUM_NOT_IN_FDOM])
        \\ IMP_RES_TAC whileTheory.LEAST_INTRO \\ full_simp_tac(srw_ss())[]
        \\ REV_FULL_SIMP_TAC std_ss [])
      \\ `~(y IN FDOM t2.refs)` by ALL_TAC THEN1
       (`?p. (\ptr. ptr NOTIN FDOM t2.refs) p` by
          (SIMP_TAC std_ss [] \\ METIS_TAC [NUM_NOT_IN_FDOM])
        \\ IMP_RES_TAC whileTheory.LEAST_INTRO \\ full_simp_tac(srw_ss())[bvi_to_bvl_def]
        \\ REV_FULL_SIMP_TAC (srw_ss()) [bvi_to_bvl_def])
      \\ full_simp_tac(srw_ss())[]
      \\ SRW_TAC [] [adjust_bv_def]
      \\ `MAP (adjust_bv b3) env = MAP (adjust_bv b2) env` by ALL_TAC THEN1
       (full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
        \\ MATCH_MP_TAC bv_ok_IMP_adjust_bv_eq
        \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ RES_TAC
        \\ IMP_RES_TAC evaluate_refs_SUBSET
        \\ REPEAT STRIP_TAC THEN1 METIS_TAC [bv_ok_SUBSET_IMP]
        \\ Q.UNABBREV_TAC `b3` \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
        \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
      \\ `MAP (adjust_bv b3) a = MAP (adjust_bv b2) a` by ALL_TAC THEN1
       (full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
        \\ MATCH_MP_TAC bv_ok_IMP_adjust_bv_eq
        \\ IMP_RES_TAC evaluate_ok \\ REV_FULL_SIMP_TAC std_ss [] \\ full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ RES_TAC
        \\ Q.UNABBREV_TAC `b3` \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
        \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
      \\ `MAP (OPTION_MAP (adjust_bv b2)) s5.globals =
          MAP (OPTION_MAP (adjust_bv b3)) s5.globals` by ALL_TAC THEN1
       (full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
        \\ Cases_on `e` \\ full_simp_tac(srw_ss())[]
        \\ MATCH_MP_TAC bv_ok_IMP_adjust_bv_eq
        \\ IMP_RES_TAC evaluate_ok \\ REV_FULL_SIMP_TAC std_ss [] \\ full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[state_ok_def,EVERY_MEM] \\ RES_TAC \\ full_simp_tac(srw_ss())[]
        \\ Q.UNABBREV_TAC `b3` \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
        \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
      \\ full_simp_tac(srw_ss())[]
      \\ Cases_on`REVERSE a`>>full_simp_tac(srw_ss())[]
      \\ Cases_on`t`>>full_simp_tac(srw_ss())[]
      \\ Cases_on`h'`>>full_simp_tac(srw_ss())[]
      \\ Cases_on`h`>>full_simp_tac(srw_ss())[]
      \\ Cases_on`t'`>>full_simp_tac(srw_ss())[]
      \\ qpat_assum`X = Rval Y`mp_tac
      \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[] \\ strip_tac \\ rpt var_eq_tac
      \\ Cases_on`a`>>full_simp_tac(srw_ss())[adjust_bv_def]
      \\ STRIP_TAC THEN1 (
        rpt var_eq_tac >>
        simp[Abbr`b3`,adjust_bv_def,APPLY_UPDATE_THM] )
      \\ reverse STRIP_TAC THEN1
       (REPEAT STRIP_TAC \\ UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
        \\ SRW_TAC [] []
        \\ IMP_RES_TAC evaluate_refs_SUBSET \\ full_simp_tac(srw_ss())[SUBSET_DEF] \\ RES_TAC)
      \\ simp[bvl_to_bvi_with_refs,bvl_to_bvi_id]
      \\ full_simp_tac(srw_ss())[state_rel_def,bvl_to_bvi_def,bvi_to_bvl_def,FLOOKUP_UPDATE]
      \\ rpt var_eq_tac \\ simp[]
      \\ STRIP_TAC
      THEN1 (Q.UNABBREV_TAC `b3` \\ MATCH_MP_TAC INJ_EXTEND \\ full_simp_tac(srw_ss())[])
      \\ srw_tac[][MAP_REVERSE] \\ full_simp_tac(srw_ss())[]
      \\ TRY ( full_simp_tac(srw_ss())[Abbr`b3`,APPLY_UPDATE_THM] \\ NO_TAC)
      \\ TRY ( simp[Abbr`b3`,APPLY_UPDATE_THM] >> srw_tac[][] >> NO_TAC)
      \\ TRY ( full_simp_tac(srw_ss())[FLOOKUP_DEF] >> NO_TAC)
      \\ TRY (
        qexists_tac`z`>>simp[]>>
        simp[GSYM MAP_MAP_o] >> srw_tac[][] >>
        simp[Abbr`b3`,APPLY_UPDATE_THM] >> srw_tac[][] >>
        NO_TAC)
      \\ TRY (
        qmatch_rename_tac`t2.global ≠ SOME p` >>
        full_simp_tac(srw_ss())[FLOOKUP_DEF] >> METIS_TAC[])
      \\ Cases_on `FLOOKUP s5.refs k = NONE` \\ full_simp_tac(srw_ss())[rich_listTheory.MAP_REVERSE]
      \\ (`b3 k <> y` by ALL_TAC THEN1
       (full_simp_tac(srw_ss())[] \\ Q.UNABBREV_TAC `b3` \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM,FLOOKUP_DEF]
        \\ full_simp_tac(srw_ss())[INJ_DEF] \\ RES_TAC \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]))
      \\ (`b3 k = b2 k` by ALL_TAC
           THEN1 (Q.UNABBREV_TAC `b3` \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM,FLOOKUP_DEF]))
      THEN1 ( full_simp_tac(srw_ss())[FLOOKUP_DEF] >> METIS_TAC[INJ_DEF] )
      \\ full_simp_tac(srw_ss())[] \\ Cases_on `FLOOKUP s5.refs k` \\ full_simp_tac(srw_ss())[]
      \\ ntac 3 (Q.PAT_ASSUM `!k. bbb` MP_TAC)
      \\ Q.PAT_ASSUM `!k. bbb` (MP_TAC o Q.SPEC `k`) \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `x'` \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
      \\ full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
      \\ MATCH_MP_TAC bv_ok_IMP_adjust_bv_eq
      \\ IMP_RES_TAC evaluate_ok \\ REV_FULL_SIMP_TAC std_ss [] \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[state_ok_def]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `k`) \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ REPEAT STRIP_TAC
      \\ Q.UNABBREV_TAC `b3` \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
      \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[])
    \\ Cases_on`∃n. op = Global n` \\ full_simp_tac(srw_ss())[] THEN1 (
         simp[compile_op_def] >>
         full_simp_tac(srw_ss())[bEvalOp_def] >>
         Cases_on`REVERSE a`>>full_simp_tac(srw_ss())[] >>
         imp_res_tac evaluate_IMP_LENGTH >>
         full_simp_tac(srw_ss())[LENGTH_NIL] >>
         simp[iEval_def,compile_int_thm] >>
         Q.LIST_EXISTS_TAC[`t2`,`b2`,`c`] >>
         simp[iEvalOp_def,do_app_aux_def] >>
         BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
         simp[bEvalOp_def] >>
         full_simp_tac(srw_ss())[closSemTheory.get_global_def] >>
         imp_res_tac bvlPropsTheory.evaluate_IMP_LENGTH >> full_simp_tac(srw_ss())[LENGTH_NIL] >>
         full_simp_tac(srw_ss())[bEval_def] >> rpt var_eq_tac >>
         full_simp_tac(srw_ss())[iEval_def] >> rpt var_eq_tac >>
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
         full_simp_tac(srw_ss())[state_ok_def,EVERY_MEM,MEM_EL,PULL_EXISTS] >>
         first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
         simp[])
    \\ Cases_on`∃n. op = SetGlobal n` \\ full_simp_tac(srw_ss())[] THEN1 (
         simp[compile_op_def] >>
         full_simp_tac(srw_ss())[bEvalOp_def] >>
         Cases_on`REVERSE a`>>full_simp_tac(srw_ss())[] >>
         Cases_on`t`>>full_simp_tac(srw_ss())[] >> srw_tac[][] >>
         imp_res_tac evaluate_IMP_LENGTH >>
         Cases_on`c1`>>full_simp_tac(srw_ss())[LENGTH_NIL] >> srw_tac[][] >>
         every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
         simp[iEval_def] >>
         CONV_TAC(RESORT_EXISTS_CONV(List.rev)) >>
         Q.LIST_EXISTS_TAC[`c`,`b2`] >>
         simp[compile_int_thm] >>
         simp[iEvalOp_def,do_app_aux_def] >>
         imp_res_tac evaluate_global_mono >>
         BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
         simp[bEvalOp_def] >>
         rator_x_assum`state_rel`mp_tac >>
         simp[Once state_rel_def] >> strip_tac >>
         simp[ADD1,LENGTH_REPLICATE] >>
         reverse IF_CASES_TAC >>
         fsrw_tac[ARITH_ss][closSemTheory.get_global_def] >>
         simp[bvl_to_bvi_with_refs,bvl_to_bvi_id,LUPDATE_def,GSYM ADD1] >>
         simp[ADD1,LUPDATE_APPEND1] >>
         full_simp_tac(srw_ss())[state_rel_def] >>
         simp[FLOOKUP_UPDATE] >>
         conj_tac >- full_simp_tac(srw_ss())[INJ_DEF] >>
         srw_tac[][] >- ( full_simp_tac(srw_ss())[FLOOKUP_DEF] >> srw_tac[][] >> METIS_TAC[] ) >>
         qexists_tac`z` >> simp[ADD1,LUPDATE_MAP] >>
         simp[libTheory.the_def])
    \\ Cases_on`op = AllocGlobal` \\ full_simp_tac(srw_ss())[] THEN1 (
         simp[compile_op_def] >>
         full_simp_tac(srw_ss())[bEvalOp_def] >>
         Cases_on`REVERSE a`>>full_simp_tac(srw_ss())[]>>srw_tac[][]>>
         imp_res_tac evaluate_IMP_LENGTH >>
         full_simp_tac(srw_ss())[LENGTH_NIL] >> srw_tac[][] >>
         srw_tac[][iEval_def] >>
         simp[Once inc_clock_def] >>
         simp[find_code_def] >>
         `lookup AllocGlobal_location t1.code = SOME(0,SND AllocGlobal_code)` by (
           full_simp_tac(srw_ss())[state_rel_def] >> simp[AllocGlobal_code_def] ) >>
         simp[] >>
         let
           val th = (Q.ISPEC`inc_clock c (t1:'ffi bviSem$state)`(Q.GEN`s`evaluate_AllocGlobal_code))
         in
         Q.SUBGOAL_THEN `∃p n ls. ^(fst(dest_imp(concl th)))` assume_tac
         THEN1 (
           full_simp_tac(srw_ss())[state_rel_def,REPLICATE_NIL] >>
           simp[Once inc_clock_def] >>
           simp[CopyGlobals_code_def] >>
           Cases_on`t1.global`>>full_simp_tac(srw_ss())[])
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
         full_simp_tac(srw_ss())[iEval_def] >> var_eq_tac >>
         full_simp_tac(srw_ss())[state_rel_def,LENGTH_REPLICATE,FLOOKUP_UPDATE] >>
         conj_tac >- full_simp_tac(srw_ss())[INJ_DEF] >>
         conj_tac >- (
           gen_tac >>
           Cases_on`FLOOKUP s5.refs k`>>simp[]>>
           `p ≠ b2 k` by ( full_simp_tac(srw_ss())[FLOOKUP_DEF] >> METIS_TAC[]) >>
           `p1 ≠ b2 k` by (
             full_simp_tac(srw_ss())[INJ_DEF,FLOOKUP_DEF] >>
             METIS_TAC[] ) >>
           simp[] >>
           rpt(first_x_assum(qspec_then`k`mp_tac)) >>
           simp[] ) >>
         conj_tac >- (
           full_simp_tac(srw_ss())[FLOOKUP_DEF] >> metis_tac[INJ_DEF]) >>
         IF_CASES_TAC >- (
           qexists_tac`z'`>>simp[libTheory.the_def]>>
           simp[LIST_EQ_REWRITE,LENGTH_REPLICATE,EL_REPLICATE] >>
           Cases >> simp[EL_REPLICATE] ) >>
         qexists_tac`z' * 2`>>simp[libTheory.the_def] >>
         simp[LIST_EQ_REWRITE,LENGTH_REPLICATE,REPLICATE_APPEND] >>
         Cases >> simp[EL_REPLICATE])
    \\ `compile_op op c1 = Op op c1` by
      (Cases_on `op` \\ full_simp_tac(srw_ss())[compile_op_def] \\ NO_TAC)
    \\ full_simp_tac(srw_ss())[iEval_def]
    \\ CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `b2`
    \\ CONV_TAC SWAP_EXISTS_CONV \\ Q.EXISTS_TAC `c`
    \\ `EVERY (bv_ok s5.refs) (REVERSE a)` by ALL_TAC
    THEN1 (IMP_RES_TAC evaluate_ok \\ full_simp_tac(srw_ss())[rich_listTheory.EVERY_REVERSE])
    \\ MP_TAC do_app_adjust \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[rich_listTheory.MAP_REVERSE])
  THEN1 (* Tick *)
   (`?c1 aux1 n1. compile_exps n [x] = (c1,aux1,n1)` by METIS_TAC [PAIR]
    \\ full_simp_tac(srw_ss())[LET_DEF] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[PULL_FORALL]
    \\ IMP_RES_TAC compile_exps_LENGTH
    \\ `?d. c1 = [d]` by (Cases_on `c1` \\ full_simp_tac(srw_ss())[LENGTH_NIL]) \\ full_simp_tac(srw_ss())[]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `n`) \\ full_simp_tac(srw_ss())[]
    \\ SRW_TAC [] [iEval_def]
    \\ Cases_on `s.clock = 0` \\ full_simp_tac(srw_ss())[] THEN1
     (SRW_TAC [] [] \\ Q.LIST_EXISTS_TAC [`t1`,`b1`,`0`]
      \\ full_simp_tac(srw_ss())[inc_clock_ZERO] \\ full_simp_tac(srw_ss())[state_rel_def]) \\ full_simp_tac(srw_ss())[]
    \\ `t1.clock <> 0 /\ !c. (inc_clock c t1).clock <> 0` by
      (EVAL_TAC \\ full_simp_tac(srw_ss())[state_rel_def] \\ DECIDE_TAC) \\ full_simp_tac(srw_ss())[]
    \\ REV_FULL_SIMP_TAC std_ss [dec_clock_inv_clock1]
    \\ `(dec_clock 1 s).refs = s.refs` by EVAL_TAC \\ full_simp_tac(srw_ss())[]
    \\ Q.PAT_ASSUM `!xx yy. bbb` (MP_TAC o Q.SPECL [`dec_clock 1 t1`,`b1`])
    \\ REV_FULL_SIMP_TAC std_ss [dec_clock_inv_clock1]
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1 (full_simp_tac(srw_ss())[evaluate_ok_lemma]
           \\ full_simp_tac(srw_ss())[state_rel_def,dec_clock_def,bvlSemTheory.dec_clock_def]
           \\ metis_tac[])
    \\ full_simp_tac(srw_ss())[GSYM PULL_FORALL])
  THEN1 (* Call *)
   (`?c1 aux1 n1. compile_exps n xs = (c1,aux1,n1)` by METIS_TAC [PAIR]
    \\ full_simp_tac(srw_ss())[LET_DEF] \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[PULL_FORALL]
    \\ `?res5 s5. evaluate (xs,env,s1) = (res5,s5)` by METIS_TAC [PAIR]
    \\ full_simp_tac(srw_ss())[] \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `n`) \\ full_simp_tac(srw_ss())[]
    \\ reverse (Cases_on `res5`) \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
    \\ first_x_assum (MP_TAC o Q.SPECL [`t1`,`b1`]) \\ full_simp_tac(srw_ss())[]
    \\ TRY (REPEAT STRIP_TAC \\ IMP_RES_TAC compile_exps_LENGTH \\ full_simp_tac(srw_ss())[iEval_def]
      \\ Q.LIST_EXISTS_TAC [`t2`,`b2`,`c`] \\ full_simp_tac(srw_ss())[] \\ NO_TAC)
    \\ full_simp_tac(srw_ss())[GSYM PULL_FORALL] \\ REPEAT STRIP_TAC
    \\ full_simp_tac(srw_ss())[iEval_def]
    \\ Cases_on `find_code dest a s5.code` \\ full_simp_tac(srw_ss())[] \\ Cases_on `x` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `s5.clock < ticks + 1` \\ full_simp_tac(srw_ss())[] THEN1
     (Q.LIST_EXISTS_TAC [`t2 with clock := 0`,`b2`,`c`] \\ full_simp_tac(srw_ss())[]
      \\ SRW_TAC [] []
      \\ TRY (full_simp_tac(srw_ss())[state_rel_def] \\ qexists_tac`array_size'` \\ simp[])
      \\ `t2.clock < ticks + 1` by (full_simp_tac(srw_ss())[state_rel_def] \\ rev_full_simp_tac(srw_ss())[])
      \\ full_simp_tac(srw_ss())[]
      \\ reverse (Cases_on `dest`)
      \\ full_simp_tac(srw_ss())[bvlSemTheory.find_code_def,find_code_def]
      THEN1
       (Cases_on `lookup x s5.code` \\ full_simp_tac(srw_ss())[]
        \\ Cases_on `x'` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
        \\ full_simp_tac(srw_ss())[state_rel_def] \\ RES_TAC
        \\ `?x1 x2 x3. compile_exps n' [r] = (x1,x2,x3)` by METIS_TAC [PAIR]
        \\ full_simp_tac(srw_ss())[LET_DEF])
      \\ `?x1 l1. a = SNOC x1 l1` by METIS_TAC [SNOC_CASES]
      \\ full_simp_tac(srw_ss())[] \\ Cases_on `x1` \\ full_simp_tac(srw_ss())[adjust_bv_def]
      \\ Cases_on `lookup n' s5.code` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `x` \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] []
      \\ full_simp_tac(srw_ss())[state_rel_def] \\ RES_TAC
      \\ `?x1 x2 x3. compile_exps n'' [r] = (x1,x2,x3)` by METIS_TAC [PAIR]
      \\ full_simp_tac(srw_ss())[LET_DEF])
    \\ Q.MATCH_ASSUM_RENAME_TAC `find_code dest a s5.code = SOME (args,body)`
    \\ `?n7. let (c7,aux7,n8) = compile_exps n7 [body] in
               (find_code (case dest of NONE => NONE | SOME n => SOME (num_stubs + 2 * n))
                 (MAP (adjust_bv b2) a) t2.code =
                 SOME (MAP (adjust_bv b2) args,HD c7)) /\
               aux_code_installed aux7 t2.code /\
               bEvery GoodHandleLet [body]` by ALL_TAC THEN1
     (reverse (Cases_on `dest`) \\ full_simp_tac(srw_ss())[state_rel_def,find_code_def]
      THEN1 (Cases_on `lookup x s5.code` \\ full_simp_tac(srw_ss())[] \\ Cases_on `x'` \\ full_simp_tac(srw_ss())[]
        \\ SRW_TAC [] []
        \\ FIRST_X_ASSUM (qspecl_then
             [`x`,`LENGTH a`,`body`]mp_tac) \\ full_simp_tac(srw_ss())[]
        \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `n'` \\ full_simp_tac(srw_ss())[]
        \\ `?c2 aux2 n2. compile_exps n' [body] = (c2,aux2,n2)` by METIS_TAC [PAIR]
        \\ full_simp_tac(srw_ss())[LET_DEF])
      \\ `?a1 a2. a = SNOC a1 a2` by METIS_TAC [SNOC_CASES]
      \\ full_simp_tac(srw_ss())[] \\ Cases_on `a1` \\ full_simp_tac(srw_ss())[]
      \\ FULL_SIMP_TAC std_ss [GSYM SNOC_APPEND,FRONT_SNOC]
      \\ Cases_on `lookup n' s5.code` \\ full_simp_tac(srw_ss())[] \\ Cases_on `x` \\ full_simp_tac(srw_ss())[]
      \\ SRW_TAC [] []
      \\ Q.PAT_ASSUM `!x1 x2. bbb` (MP_TAC o Q.SPECL [`n'`]) \\ full_simp_tac(srw_ss())[]
      \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `n''`
      \\ `?c2 aux2 n2. compile_exps n'' [body] = (c2,aux2,n2)` by METIS_TAC [PAIR]
      \\ full_simp_tac(srw_ss())[LET_DEF,adjust_bv_def])
    \\ `?c7 aux7 n8. compile_exps n7 [body] = (c7,aux7,n8)` by METIS_TAC [PAIR]
    \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ `¬(t2.clock < ticks + 1)` by (full_simp_tac(srw_ss())[state_rel_def] \\ REV_FULL_SIMP_TAC std_ss [])
    \\ full_simp_tac(srw_ss())[] \\ IMP_RES_TAC compile_exps_LENGTH
    \\ `?d. c7 = [d]` by (Cases_on `c7` \\ full_simp_tac(srw_ss())[LENGTH_NIL]) \\ full_simp_tac(srw_ss())[]
    \\ Q.PAT_ASSUM `!nn mm. bbb` (MP_TAC o Q.SPEC `n7`) \\ full_simp_tac(srw_ss())[]
    \\ STRIP_TAC
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`dec_clock (ticks + 1) t2`,`b2`]) \\ full_simp_tac(srw_ss())[]
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (`(dec_clock (ticks + 1) t2).code = t2.code` by (EVAL_TAC \\ full_simp_tac(srw_ss())[])
      \\ `(dec_clock (ticks + 1) t2).refs = t2.refs` by (EVAL_TAC \\ full_simp_tac(srw_ss())[])
      \\ IMP_RES_TAC evaluate_ok
      \\ full_simp_tac(srw_ss())[evaluate_ok_lemma] \\ REV_FULL_SIMP_TAC std_ss []
      \\ STRIP_TAC THEN1
        (full_simp_tac(srw_ss())[state_rel_def,dec_clock_def,bvlSemTheory.dec_clock_def] >>
         METIS_TAC[])
      \\ IMP_RES_TAC find_code_EVERY_IMP
      \\ imp_res_tac evaluate_global_mono
      \\ full_simp_tac(srw_ss())[])
    \\ STRIP_TAC
    \\ Q.LIST_EXISTS_TAC [`t2'`,`b2'`,`c' + c`] \\ full_simp_tac(srw_ss())[]
    \\ IMP_RES_TAC evaluate_inv_clock
    \\ full_simp_tac(srw_ss())[inc_clock_ADD]
    \\ REV_FULL_SIMP_TAC std_ss []
    \\ `MAP (adjust_bv b2') env = MAP (adjust_bv b2) env` by
     (full_simp_tac(srw_ss())[MAP_EQ_f] \\ REPEAT STRIP_TAC
      \\ MATCH_MP_TAC (bv_ok_IMP_adjust_bv_eq |> GEN_ALL)
      \\ Q.EXISTS_TAC `s5` \\ full_simp_tac(srw_ss())[bvlSemTheory.dec_clock_def]
      \\ IMP_RES_TAC evaluate_refs_SUBSET
      \\ IMP_RES_TAC bv_ok_SUBSET_IMP \\ full_simp_tac(srw_ss())[EVERY_MEM] \\ NO_TAC)
    \\ `(inc_clock c' t2).code = t2.code` by (EVAL_TAC \\ full_simp_tac(srw_ss())[]) \\ full_simp_tac(srw_ss())[]
    \\ `¬((inc_clock c' t2).clock < ticks + 1)` by (full_simp_tac(srw_ss())[inc_clock_def] \\ decide_tac)
    \\ full_simp_tac(srw_ss())[]
    \\ REV_FULL_SIMP_TAC std_ss [dec_clock_inv_clock]
    \\ full_simp_tac(srw_ss())[bvlSemTheory.dec_clock_def]
    \\ IMP_RES_TAC evaluate_refs_SUBSET \\ full_simp_tac(srw_ss())[SUBSET_DEF]
    \\ Cases_on `res` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on`e` \\ full_simp_tac(srw_ss())[]));

val _ = save_thm("compile_exps_correct",compile_exps_correct);

(* composed compiler correctness *)

val MAP_FST_optimise = Q.store_thm("MAP_FST_optimise[simp]",
  `MAP FST (optimise prog) = MAP FST prog`,
  simp[optimise_def,MAP_MAP_o,o_DEF,UNCURRY,ETA_AX]);

val ALOOKUP_optimise_lookup = Q.store_thm("ALOOKUP_optimise_lookup",
  `lookup n ls = SOME (a,b) ⇒
   ALOOKUP (optimise (toAList ls)) n =
     SOME (a,bvl_handle$compile_exp a (bvl_const$compile_exp b))`,
  srw_tac[][] >>
  Cases_on`ALOOKUP (optimise (toAList ls)) n` >- (
    imp_res_tac ALOOKUP_FAILS >>
    `¬MEM n (MAP FST (optimise (toAList ls)))` by METIS_TAC[MEM_MAP,FST,PAIR] >>
    full_simp_tac(srw_ss())[toAList_domain] >>
    METIS_TAC[domain_lookup] ) >>
  imp_res_tac ALOOKUP_MEM >>
  fs [optimise_def,MEM_MAP,PULL_EXISTS,EXISTS_PROD,MEM_toAList] >>
  full_simp_tac(srw_ss())[]);

val evaluate_IMP_optimise = store_thm("evaluate_IMP_optimise",
  ``evaluate ([r],zenv,zs) = (res,s') /\ res <> Rerr (Rabort Rtype_error) /\
    LENGTH zenv = q ==>
    evaluate ([bvl_handle$compile_exp q
                (bvl_const$compile_exp r)],zenv,zs) = (res,s')``,
  rw [] \\ match_mp_tac bvl_handleProofTheory.compile_correct \\ fs []
  \\ drule (GEN_ALL bvl_constProofTheory.evaluate_compile_exp) \\ fs []);

val optimise_evaluate = Q.store_thm("optimise_evaluate",
  `∀xs env s res s'.
     evaluate (xs,env,s) = (res,s') ∧
     res ≠ Rerr (Rabort Rtype_error) ⇒
     evaluate (xs,env,s with code := fromAList (optimise (toAList s.code))) =
       (res,s' with code := fromAList (optimise (toAList s.code)))`,
  recInduct bvlSemTheory.evaluate_ind >>
  srw_tac[][bvlSemTheory.evaluate_def] >>
  TRY (
    rename1`Boolv T = HD _` >>
    BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
    BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
    rpt(IF_CASES_TAC >> full_simp_tac(srw_ss())[]) >>
    TRY(qpat_assum`_ = HD _`(assume_tac o SYM))>>full_simp_tac(srw_ss())[]>>
    every_case_tac >> full_simp_tac(srw_ss())[] >> rpt var_eq_tac >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
    imp_res_tac bvlPropsTheory.evaluate_code >> full_simp_tac(srw_ss())[] >>
    TRY(qpat_assum`_ = HD _`(assume_tac o SYM))>>full_simp_tac(srw_ss())[] ) >>
  TRY (
    rename1`bvlSem$do_app` >>
    every_case_tac >> full_simp_tac(srw_ss())[] >> rpt var_eq_tac >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
    imp_res_tac bvlPropsTheory.evaluate_code >> full_simp_tac(srw_ss())[] >>
    imp_res_tac bvlPropsTheory.do_app_with_code >>
    imp_res_tac bvlPropsTheory.do_app_with_code_err >>
    full_simp_tac(srw_ss())[domain_fromAList] >>
    full_simp_tac(srw_ss())[SUBSET_DEF,toAList_domain] >>
    qmatch_assum_rename_tac`bvlSem$do_app op _ z = _` >>
    rpt(first_x_assum(qspec_then`z.code`mp_tac)) >> simp[] >>
    NO_TAC) >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> rpt var_eq_tac >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
  imp_res_tac bvlPropsTheory.evaluate_code >> full_simp_tac(srw_ss())[] >>
  Cases_on`dest`>>full_simp_tac(srw_ss())[find_code_def]>>
  every_case_tac>>full_simp_tac(srw_ss())[]>>srw_tac[][]>>
  full_simp_tac(srw_ss())[lookup_fromAList] >>
  imp_res_tac ALOOKUP_optimise_lookup >> full_simp_tac(srw_ss())[] >>
  rpt var_eq_tac
  \\ qmatch_assum_abbrev_tac`bvlSem$evaluate (zxs,zenv,zs) = (_,_ with code := _)`
  \\ match_mp_tac evaluate_IMP_optimise
  \\ unabbrev_all_tac \\ fs []
  \\ `?x1 x2. a = SNOC x1 x2` by metis_tac [SNOC_CASES]
  \\ rw []\\ full_simp_tac std_ss [FRONT_SNOC,LAST_SNOC,LENGTH_SNOC,ADD1]);

val fromAList_optimise = Q.prove(
  `fromAList (optimise p) =
   map (λ(a,e). (a, bvl_handle$compile_exp a
                   (bvl_const$compile_exp e))) (fromAList p)`,
  simp[map_fromAList,optimise_def] >>
  rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
  simp[FUN_EQ_THM,UNCURRY]);

val optimise_semantics = Q.store_thm("optimise_semantics",
  `semantics ffi0 (fromAList prog) start ≠ Fail ⇒
   semantics ffi0 (fromAList (optimise prog)) start =
   semantics ffi0 (fromAList prog) start`,
  simp[bvlSemTheory.semantics_def] >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
  `∀k. evaluate ([Call 0 (SOME start) []],[],initial_state ffi0 (fromAList (optimise prog)) k) =
    let (r,s) = bvlSem$evaluate ([Call 0 (SOME start) []],[],initial_state ffi0 (fromAList prog) k) in
      (r, s with code := fromAList (optimise (toAList s.code)))` by (
    gen_tac >> simp[] >>
    qmatch_abbrev_tac`_ = (_ (bvlSem$evaluate (xs,env,s)))` >>
    Q.ISPECL_THEN[`xs`,`env`,`s`]mp_tac optimise_evaluate >>
    Cases_on`evaluate (xs,env,s)` >>
    simp[Abbr`s`] >>
    impl_tac >- METIS_TAC[FST] >>
    full_simp_tac(srw_ss())[fromAList_optimise,fromAList_toAList,wf_fromAList] >>
    full_simp_tac(srw_ss())[GSYM fromAList_optimise] >>
    imp_res_tac bvlPropsTheory.evaluate_code >>
    full_simp_tac(srw_ss())[bvlSemTheory.state_component_equality] >>
    full_simp_tac(srw_ss())[fromAList_optimise,fromAList_toAList,wf_fromAList] ) >>
  simp[] >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  full_simp_tac(srw_ss())[UNCURRY,LET_THM] >>
  reverse conj_tac >- (
    simp_tac(srw_ss()++QUANT_INST_ss[pair_default_qp])[] ) >>
  gen_tac >> strip_tac >> var_eq_tac >>
  asm_simp_tac(srw_ss()++QUANT_INST_ss[pair_default_qp])[] >>
  reverse conj_tac >- METIS_TAC[] >>
  gen_tac >> strip_tac >>
  strip_tac >> full_simp_tac(srw_ss())[] >>
  qpat_abbrev_tac`abb2 = bvlSem$evaluate _` >>
  qpat_abbrev_tac`abb1 = bvlSem$evaluate _` >>
  qmatch_assum_abbrev_tac`Abbrev(abb2 = evaluate (e1,v1,s1))` >>
  qmatch_assum_abbrev_tac`Abbrev(abb1 = evaluate (e1,v1,s2))` >>
  map_every qunabbrev_tac[`abb1`,`abb2`] >>
  qmatch_assum_rename_tac`Abbrev(s1 = _ _ _ k1)` >>
  qmatch_assum_rename_tac`Abbrev(s2 = _ _ _ k2)` >>
  (fn g => subterm(fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g) >> full_simp_tac(srw_ss())[] >>
  (fn g => subterm(fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g) >> full_simp_tac(srw_ss())[] >>
  Q.ISPECL_THEN[`e1`,`v1`,`s1`]mp_tac bvlPropsTheory.evaluate_add_to_clock_io_events_mono >>
  disch_then(qspec_then`k2`mp_tac) >>
  Q.ISPECL_THEN[`e1`,`v1`,`s2`]mp_tac bvlPropsTheory.evaluate_add_to_clock_io_events_mono >>
  disch_then(qspec_then`k1`mp_tac) >>
  simp[bvlPropsTheory.inc_clock_def,Abbr`s1`,Abbr`s2`] >>
  ntac 2 strip_tac >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  imp_res_tac bvlPropsTheory.evaluate_add_clock >>
  rpt(first_x_assum (fn th => mp_tac th >> impl_tac >- (strip_tac >> full_simp_tac(srw_ss())[]))) >>
  simp[bvlPropsTheory.inc_clock_def] >>
  TRY (
    disch_then(qspec_then`k1`strip_assume_tac) >>
    disch_then(qspec_then`k2`strip_assume_tac) >>
    fsrw_tac[ARITH_ss][bvlSemTheory.state_component_equality] ) >>
  TRY (
    qexists_tac`k1` >>
    spose_not_then strip_assume_tac >> full_simp_tac(srw_ss())[] >> NO_TAC) >>
  TRY (
    qexists_tac`k2` >>
    spose_not_then strip_assume_tac >> fsrw_tac[ARITH_ss][] >>
    rev_full_simp_tac(srw_ss())[] >> NO_TAC) >>
  srw_tac[][] >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[]);

val compile_single_evaluate = Q.store_thm("compile_single_evaluate",
  `evaluate ([Call 0 (SOME start) []],[],s1) = (res,s2) ∧
   state_rel b1 s1 t1 ∧ IS_SOME t1.global ∧ state_ok s1 ∧
   res ≠ Rerr (Rabort Rtype_error)
   ⇒
   ∃ck b2 t2.
     evaluate ([Call 0 (SOME (num_stubs + 2 * start))[] NONE],[],inc_clock ck t1) =
       (map_result (MAP (adjust_bv b2)) (adjust_bv b2) res,t2) ∧
     state_rel b2 s2 t2`,
  srw_tac[][] >>
  full_simp_tac(srw_ss())[bvlSemTheory.evaluate_def] >>
  full_simp_tac(srw_ss())[find_code_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >>
  srw_tac[][bviSemTheory.evaluate_def,find_code_def] >>
  first_assum(drule o last o CONJUNCTS o CONV_RULE(REWR_CONV state_rel_def)) >>
  simp[] >> strip_tac >> pairarg_tac >> full_simp_tac(srw_ss())[] >- (
    qpat_assum`0n = _`(assume_tac o SYM) >> simp[] >>
    `t1.clock = 0` by full_simp_tac(srw_ss())[state_rel_def] >> simp[] >>
    simp[inc_clock_def] >>
    qexists_tac`0`>>simp[]>>
    qexists_tac`b1` >>
    full_simp_tac(srw_ss())[state_rel_def] ) >>
  `t1.clock ≠ 0` by full_simp_tac(srw_ss())[state_rel_def] >> simp[] >>
  drule compile_exps_correct >> simp[] >>
  disch_then drule >>
  `state_rel b1 (dec_clock 1 s1) (dec_clock 1 t1)` by (
    full_simp_tac(srw_ss())[state_rel_def,bvlSemTheory.dec_clock_def,bviSemTheory.dec_clock_def] ) >>
  disch_then drule >>
  impl_tac >- (
    full_simp_tac(srw_ss())[bvlSemTheory.dec_clock_def,bviSemTheory.dec_clock_def] >>
    full_simp_tac(srw_ss())[state_ok_def] ) >>
  strip_tac >>
  imp_res_tac compile_exps_SING >> var_eq_tac >> simp[] >>
  qexists_tac`c` >>
  `dec_clock 1 (inc_clock c t1) = inc_clock c (dec_clock 1 t1)` by (
    EVAL_TAC >> simp[state_component_equality] ) >>
  simp[] >>
  Cases_on`res`>>simp[] >- METIS_TAC[] >>
  Cases_on`e`>>simp[] >> METIS_TAC[]);

val evaluate_REPLICATE_0 = prove(
  ``!n. evaluate (REPLICATE n (Op (Const 0) []),env,s) =
          (Rval (REPLICATE n (Number 0)),s)``,
  Induct \\ fs [evaluate_def,REPLICATE]
  \\ once_rewrite_tac [evaluate_CONS]
  \\ fs [evaluate_def,REPLICATE,do_app_def,do_app_aux_def]
  \\ fs [EVAL ``small_enough_int 0``]);

val bvi_stubs_evaluate = Q.store_thm("bvi_stubs_evaluate",
  `∀kk start ffi0 code k.
     0 < k ∧ num_stubs ≤ start ⇒
  let t0 = <| global := SOME 0
            ; ffi := ffi0
            ; clock := k
            ; code := fromAList (stubs start kk ++ code);
              refs := FEMPTY |+ (0,ValueArray ([Number 1] ++
                             REPLICATE kk (Number 0))) |> in
      evaluate ([Call 0 (SOME InitGlobals_location) [] NONE],[],
        initial_state ffi0 (fromAList (stubs start kk ++ code)) (k+1)) =
   let (r,s) = evaluate ([Call 0 (SOME start) [] NONE],[],t0) in
     ((case r of Rerr(Rraise v) => Rval [v] | _ => r), s)`,
  srw_tac[][bviSemTheory.evaluate_def,find_code_def,lookup_fromAList,ALOOKUP_APPEND] >>
  srw_tac[][Once stubs_def] >>
  TRY (pop_assum(assume_tac o CONV_RULE EVAL)>>full_simp_tac(srw_ss())[]>>NO_TAC) >>
  simp[InitGlobals_code_def] >>
  simp[bviSemTheory.evaluate_def,bviSemTheory.do_app_def,bviSemTheory.do_app_aux_def,small_enough_int_def] >>
  once_rewrite_tac [evaluate_SNOC |> REWRITE_RULE [SNOC_APPEND]] >>
  simp[bviSemTheory.evaluate_def,bviSemTheory.do_app_def,bviSemTheory.do_app_aux_def,small_enough_int_def,evaluate_REPLICATE_0] >>
  simp[bvlSemTheory.do_app_def,find_code_def,lookup_fromAList,ALOOKUP_APPEND] >>
  reverse BasicProvers.CASE_TAC >- (
    `F` suffices_by srw_tac[][] >>
    imp_res_tac ALOOKUP_MEM >>
    full_simp_tac(srw_ss())[stubs_def] >>
    qpat_assum`num_stubs ≤ _`mp_tac >>
    rpt var_eq_tac >> EVAL_TAC ) >>
  BasicProvers.CASE_TAC >- (
    full_simp_tac(srw_ss())[Abbr`t0`] >>
    full_simp_tac(srw_ss())[lookup_fromAList,ALOOKUP_APPEND] >>
    rpt var_eq_tac >>
    simp[bviSemTheory.state_component_equality] >>
    unabbrev_all_tac \\ fs [REVERSE_APPEND,REVERSE_REPLICATE] >>
    EVAL_TAC >> simp[]) >>
  Cases_on`x`>>simp[] >>
  reverse IF_CASES_TAC >> full_simp_tac(srw_ss())[] >- (
    full_simp_tac(srw_ss())[Abbr`t0`,lookup_fromAList,ALOOKUP_APPEND] >>
    rpt var_eq_tac >>
    simp[bviSemTheory.state_component_equality] >>
    unabbrev_all_tac >> fs [REVERSE_APPEND,REVERSE_REPLICATE] >>
    EVAL_TAC >> simp[]) >>
  simp[] >>
  var_eq_tac >>
  simp[Once bviSemTheory.dec_clock_def] >>
  full_simp_tac(srw_ss())[bvl_to_bvi_def,bvi_to_bvl_def,bviSemTheory.dec_clock_def,bviSemTheory.initial_state_def] >>
  full_simp_tac(srw_ss())[Abbr`t0`,lookup_fromAList,ALOOKUP_APPEND] >>
  REV_FULL_SIMP_TAC(srw_ss()++ARITH_ss)[] >>
  REWRITE_TAC[ONE,REPLICATE] >> simp[] >>
  BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
  BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
  rpt var_eq_tac >> full_simp_tac(srw_ss())[] >>
  BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
  rfs [] \\ fs [REVERSE_APPEND] \\ rfs [REVERSE_REPLICATE] \\ fs [] >>
  rpt var_eq_tac >> full_simp_tac(srw_ss())[]);

val sorted_lt_append =
  Q.ISPEC`prim_rec$<`SORTED_APPEND
  |> SIMP_RULE std_ss [transitive_LESS]

val compile_exps_aux_sorted = Q.store_thm("compile_exps_aux_sorted",
  `∀n es c aux n1. compile_exps n es = (c,aux,n1) ⇒
   SORTED $< (MAP FST aux) ∧ EVERY (between n n1) (MAP FST aux) ∧ n ≤ n1`,
   ho_match_mp_tac compile_exps_ind >>
   simp[compile_exps_def] >> srw_tac[][] >>
   rpt (pairarg_tac >> full_simp_tac(srw_ss())[]) >> srw_tac[][] >>
   rpt ((sorted_lt_append |> match_mp_tac) >> full_simp_tac(srw_ss())[] >> srw_tac[][] ) >>
   full_simp_tac(srw_ss())[EVERY_MEM,between_def] >>
   srw_tac[][] >> res_tac >> decide_tac);

val aux_code_installed_sublist = Q.store_thm("aux_code_installed_sublist",
  `∀aux ls.
    IS_SUBLIST ls (MAP (λ(k,args,p).
      (num_stubs + 2 * k + 1,args,bvi_let$compile_exp p)) aux) ∧
    ALL_DISTINCT (MAP FST ls) ⇒
    aux_code_installed aux (fromAList ls)`,
  Induct >> simp[aux_code_installed_def] >>
  qx_gen_tac`p`>>PairCases_on`p`>>
  Cases >> simp[IS_SUBLIST] >> strip_tac >- (
    simp[aux_code_installed_def,lookup_fromAList] >>
    first_x_assum match_mp_tac >>
    var_eq_tac >> full_simp_tac(srw_ss())[] >>
    full_simp_tac(srw_ss())[IS_SUBLIST_APPEND,IS_PREFIX_APPEND] >>
    CONV_TAC SWAP_EXISTS_CONV >>
    qexists_tac`l`>>simp[] ) >>
  simp[aux_code_installed_def,lookup_fromAList] >>
  reverse conj_tac >- (
    first_x_assum match_mp_tac >> full_simp_tac(srw_ss())[] >>
    full_simp_tac(srw_ss())[IS_SUBLIST_APPEND] >>
    CONV_TAC SWAP_EXISTS_CONV >>
    qexists_tac`l'`>>simp[] ) >>
  full_simp_tac(srw_ss())[IS_SUBLIST_APPEND] >>
  PairCases_on`h` >>
  simp[ALOOKUP_APPEND] >>
  var_eq_tac >> full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[ALL_DISTINCT_APPEND] >>
  BasicProvers.CASE_TAC >>
  imp_res_tac ALOOKUP_MEM >>
  full_simp_tac(srw_ss())[MEM_MAP,PULL_EXISTS,EXISTS_PROD] >>
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
  pairarg_tac >> full_simp_tac(srw_ss())[] >>
  pairarg_tac >> full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[compile_single_def,LET_THM] >>
  pairarg_tac >> full_simp_tac(srw_ss())[] >>
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
    full_simp_tac(srw_ss())[EVERY_MEM] >> srw_tac[][] >> res_tac >>
    fsrw_tac[ARITH_ss][] >>
    METIS_TAC[EVEN_ODD,EVEN_EXISTS] ) >>
  simp[ALL_DISTINCT_APPEND] >>
  reverse conj_tac >- (
    full_simp_tac(srw_ss())[EVERY_MEM,PULL_EXISTS,MEM_MAP,EXISTS_PROD] >>
    srw_tac[][] >> spose_not_then strip_assume_tac >>
    res_tac >> full_simp_tac(srw_ss())[between_def] >- (
      full_simp_tac(srw_ss())[MEM_FILTER,MEM_MAP,PULL_EXISTS,EXISTS_PROD] >>
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
    spose_not_then strip_assume_tac >> full_simp_tac(srw_ss())[] >>
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
     IS_SUBLIST code (MAP (λ(k,args,p). (num_stubs + 2 * k + 1,args,bvi_let$compile_exp p)) aux)`,
  Induct_on`prog` >> simp[] >>
  qx_gen_tac`p`>>PairCases_on`p`>>
  simp[compile_list_def] >>
  rpt gen_tac >> strip_tac >>
  pairarg_tac >> full_simp_tac(srw_ss())[] >>
  pairarg_tac >> full_simp_tac(srw_ss())[] >>
  rpt var_eq_tac >>
  full_simp_tac(srw_ss())[compile_single_def,LET_THM] >>
  pairarg_tac >> full_simp_tac(srw_ss())[] >>
  rpt var_eq_tac >>
  BasicProvers.FULL_CASE_TAC >- (
    full_simp_tac(srw_ss())[] >> rpt var_eq_tac >>
    imp_res_tac compile_exps_SING >> var_eq_tac >>
    asm_exists_tac >> simp[] >>
    conj_tac >- (
      simp[ALOOKUP_APPEND] >>
      BasicProvers.CASE_TAC >>
      imp_res_tac ALOOKUP_MEM >>
      full_simp_tac(srw_ss())[MEM_MAP,EXISTS_PROD,PULL_EXISTS] >>
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
    full_simp_tac(srw_ss())[MEM_MAP,EXISTS_PROD,PULL_EXISTS] >>
    qmatch_assum_rename_tac`2 * a + num_stubs = 2 * b + (num_stubs + 1)` >>
    `2 * a = 2 * b + 1` by decide_tac >>
    METIS_TAC[EVEN_ODD,EVEN_EXISTS,ODD_EXISTS,ADD1] ) >>
  full_simp_tac(srw_ss())[IS_SUBLIST_APPEND] >>
  imp_res_tac compile_exps_SING >> full_simp_tac(srw_ss())[] >>
  rpt var_eq_tac >>
  fsrw_tac[ARITH_ss][] >>
  METIS_TAC[APPEND_ASSOC]);

val compile_prog_evaluate = Q.store_thm("compile_prog_evaluate",
  `compile_prog start n prog = (start', prog', n') ∧
   evaluate ([Call 0 (SOME start) []],[],
             initial_state ffi0 (fromAList prog) k) = (r,s) ∧
   0 < k ∧
   ALL_DISTINCT (MAP FST prog) ∧
   bEvery GoodHandleLet (MAP (SND o SND) prog) ∧
   r ≠ Rerr (Rabort Rtype_error)
   ⇒
   ∃ck b2 s2.
   evaluate ([Call 0 (SOME start') [] NONE],[],initial_state ffi0 (fromAList prog') (k+ck)) =
     (map_result (MAP (adjust_bv b2)) (adjust_bv b2) (case r of Rerr(Rraise v) => Rval [v] | _ => r),s2) ∧
   state_rel b2 s s2`,
  srw_tac[][compile_prog_def,LET_THM] >>
  pairarg_tac >> full_simp_tac(srw_ss())[] >> var_eq_tac >>
  `num_stubs ≤ num_stubs + 2 * start` by simp[] >>
  drule (GEN_ALL compile_single_evaluate) >>
  simp[state_ok_def] >>
  qabbrev_tac `kk = alloc_glob_count (MAP (λ(_,_,p). p) prog)` >>
  qspecl_then[`kk`,
       `num_stubs + 2 * start`,`ffi0`,`code`]
    (fn tmp =>
      disch_then(fn th => subterm (mp_tac o C SPEC th o #2 o boolSyntax.dest_let) (concl tmp)))
    bvi_stubs_evaluate >>
  simp[Once state_rel_def,FLOOKUP_UPDATE] >>
  impl_tac >- (
    conj_tac >- (qexists_tac`kk+1`>>simp[]>>EVAL_TAC) >>
    rpt var_eq_tac >>
    simp[lookup_fromAList,ALOOKUP_APPEND] >>
    simp[stubs_def] >>
    IF_CASES_TAC >> simp[] >- (
      `F` suffices_by srw_tac[][] >> pop_assum mp_tac >> EVAL_TAC ) >>
    rpt gen_tac >> strip_tac >>
    rpt (
      IF_CASES_TAC >- (
        `F` suffices_by srw_tac[][] >> pop_assum mp_tac >> EVAL_TAC >> decide_tac)) >>
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
      full_simp_tac(srw_ss())[IS_SUBLIST_APPEND] >>
      METIS_TAC[CONS_APPEND,APPEND_ASSOC] ) >>
    imp_res_tac compile_list_distinct_locs >>
    simp[] >> srw_tac[][] >> (TRY (EVAL_TAC >> NO_TAC)) >>
    spose_not_then strip_assume_tac >> full_simp_tac(srw_ss())[EVERY_MEM] >>
    res_tac >> pop_assum mp_tac >> EVAL_TAC ) >>
  strip_tac >>
  `0 < ck + k` by simp[] >>
  drule (GEN_ALL bvi_stubs_evaluate) >>
  disch_then (qspec_then `kk` mp_tac) >>
  disch_then drule >>
  disch_then(qspecl_then[`ffi0`,`code`]mp_tac) >>
  simp[] >>
  rpt var_eq_tac >>
  fsrw_tac[ARITH_ss][inc_clock_def] >>
  Cases_on`r`>>full_simp_tac(srw_ss())[]>>
  TRY(Cases_on`e`)>>full_simp_tac(srw_ss())[] >>
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
  IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  conj_tac >- (
    gen_tac >> strip_tac >> rveq >> simp[] >>
    simp[bviSemTheory.semantics_def] >>
    IF_CASES_TAC >> full_simp_tac(srw_ss())[] >- (
      first_assum(subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) o concl) >>
      drule bviPropsTheory.evaluate_add_clock >>
      impl_tac >- full_simp_tac(srw_ss())[] >> strip_tac >>
      rator_x_assum`bvlSem$evaluate`kall_tac >>
      last_assum(qspec_then`SUC k'`mp_tac)>>
      (fn g => subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) (#2 g) g) >>
      drule (GEN_ALL compile_prog_evaluate) >>
      disch_then drule >>
      impl_tac >- ( full_simp_tac(srw_ss())[] >> METIS_TAC[FST] ) >>
      strip_tac >>
      strip_tac >>
      first_x_assum(qspec_then`SUC ck`mp_tac) >>
      simp[inc_clock_def] >>
      fsrw_tac[ARITH_ss][ADD1] >>
      CASE_TAC >> simp[] >>
      CASE_TAC >> simp[] >>
      full_simp_tac(srw_ss())[] >> rveq >>
      spose_not_then strip_assume_tac >>
      rveq >> full_simp_tac(srw_ss())[] >>
      Cases_on`a`>>full_simp_tac(srw_ss())[]) >>
    DEEP_INTRO_TAC some_intro >> simp[] >>
    conj_tac >- (
      gen_tac >> strip_tac >> rveq >> full_simp_tac(srw_ss())[] >>
      qmatch_assum_abbrev_tac`bvlSem$evaluate (bxps,[],bs) = _` >>
      qmatch_assum_abbrev_tac`bviSem$evaluate (exps,[],ss) = _` >>
      qspecl_then[`bxps`,`[]`,`bs`]mp_tac bvlPropsTheory.evaluate_add_to_clock_io_events_mono >>
      qspecl_then[`exps`,`[]`,`ss`]mp_tac bviPropsTheory.evaluate_add_to_clock_io_events_mono >>
      simp[bvlPropsTheory.inc_clock_def,bviPropsTheory.inc_clock_def,Abbr`ss`,Abbr`bs`] >>
      ntac 2 strip_tac >>
      Cases_on`s.ffi.final_event`>>full_simp_tac(srw_ss())[] >- (
        Cases_on`s'.ffi.final_event`>>full_simp_tac(srw_ss())[]>-(
          unabbrev_all_tac >>
          drule (GEN_ALL compile_prog_evaluate) >>
          disch_then drule >>
          impl_tac >- (
            simp[] >> spose_not_then strip_assume_tac >> full_simp_tac(srw_ss())[] >>
            full_simp_tac(srw_ss())[bvlSemTheory.evaluate_def] >>
            every_case_tac >> full_simp_tac(srw_ss())[] >> rveq >> full_simp_tac(srw_ss())[] ) >>
          strip_tac >>
          drule bviPropsTheory.evaluate_add_clock >>
          impl_tac >- (
            CASE_TAC >> full_simp_tac(srw_ss())[] >>
            CASE_TAC >> full_simp_tac(srw_ss())[] ) >>
          disch_then(qspec_then`k'`mp_tac)>>simp[bviPropsTheory.inc_clock_def]>>
          rator_x_assum`bviSem$evaluate`mp_tac >>
          drule bviPropsTheory.evaluate_add_clock >>
          impl_tac >- ( strip_tac >> full_simp_tac(srw_ss())[] ) >>
          disch_then(qspec_then`ck+k`mp_tac)>>simp[bviPropsTheory.inc_clock_def]>>
          ntac 3 strip_tac >> rveq >> full_simp_tac(srw_ss())[] >>
          full_simp_tac(srw_ss())[state_component_equality] >>
          full_simp_tac(srw_ss())[state_rel_def] >>
          every_case_tac >> full_simp_tac(srw_ss())[] ) >>
        first_x_assum(qspec_then`k'`strip_assume_tac) >>
        first_assum(subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) o concl) >> full_simp_tac(srw_ss())[] >>
        unabbrev_all_tac >>
        drule (GEN_ALL compile_prog_evaluate) >>
        disch_then drule >>
        impl_tac >- (
          last_x_assum(qspec_then`k+k'`mp_tac)>>
          fsrw_tac[ARITH_ss][] >> strip_tac >>
          spose_not_then strip_assume_tac >> full_simp_tac(srw_ss())[] >>
          rveq >> full_simp_tac(srw_ss())[bvlSemTheory.evaluate_def] >>
          every_case_tac >> full_simp_tac(srw_ss())[] >> rveq >> full_simp_tac(srw_ss())[]) >>
        strip_tac >>
        rator_x_assum`bvlSem$evaluate`mp_tac >>
        drule bvlPropsTheory.evaluate_add_clock >>
        impl_tac >- (strip_tac >> full_simp_tac(srw_ss())[]) >>
        disch_then(qspec_then`k'`mp_tac)>>simp[bvlPropsTheory.inc_clock_def] >>
        first_x_assum(qspec_then`ck+k`mp_tac)>>simp[] >>
        fsrw_tac[ARITH_ss][] >>
        rpt strip_tac >> spose_not_then strip_assume_tac >>
        rveq >> fsrw_tac[ARITH_ss][state_rel_def]) >>
      first_x_assum(qspec_then`SUC k'`strip_assume_tac) >>
      first_assum(subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) o concl) >> full_simp_tac(srw_ss())[] >>
      unabbrev_all_tac >>
      drule (GEN_ALL compile_prog_evaluate) >>
      disch_then drule >>
      impl_tac >- (
        last_x_assum(qspec_then`k+SUC k'`mp_tac)>>
        fsrw_tac[ARITH_ss][] ) >>
      strip_tac >> rveq >>
      fsrw_tac[ARITH_ss][] >>
      reverse(Cases_on`s'.ffi.final_event`)>>full_simp_tac(srw_ss())[]>>rev_full_simp_tac(srw_ss())[]>- (
        first_x_assum(qspec_then`ck+SUC k`mp_tac) >>
        fsrw_tac[ARITH_ss][ADD1] >> strip_tac >>
        full_simp_tac(srw_ss())[state_rel_def] >> rev_full_simp_tac(srw_ss())[] ) >>
      rator_x_assum`bviSem$evaluate`mp_tac >>
      drule bviPropsTheory.evaluate_add_clock >>
      impl_tac >- (strip_tac >> full_simp_tac(srw_ss())[]) >>
      disch_then(qspec_then`ck+SUC k`mp_tac)>>simp[bviPropsTheory.inc_clock_def] >>
      fsrw_tac[ARITH_ss][ADD1] >>
      ntac 2 strip_tac >> rveq >>
      fsrw_tac[ARITH_ss][state_rel_def] >> rev_full_simp_tac(srw_ss())[] ) >>
    qmatch_assum_abbrev_tac`bvlSem$evaluate (bxps,[],bs) = _` >>
    qspecl_then[`bxps`,`[]`,`bs`]mp_tac bvlPropsTheory.evaluate_add_to_clock_io_events_mono >>
    simp[bvlPropsTheory.inc_clock_def,Abbr`bs`] >>
    disch_then(qspec_then`1`strip_assume_tac) >>
    first_assum(subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) o concl) >>
    unabbrev_all_tac >>
    drule (GEN_ALL compile_prog_evaluate) >>
    disch_then drule >> simp[] >>
    impl_tac >- (
      last_x_assum(qspec_then`k+1`mp_tac)>>fsrw_tac[ARITH_ss][] ) >>
    strip_tac >>
    asm_exists_tac >>
    every_case_tac >> full_simp_tac(srw_ss())[] >> rveq >> full_simp_tac(srw_ss())[] >- (
      rator_x_assum`bvlSem$evaluate`mp_tac >>
      drule bvlPropsTheory.evaluate_add_clock >>
      impl_tac >- (strip_tac >> full_simp_tac(srw_ss())[]) >>
      disch_then(qspec_then`1`mp_tac)>>simp[bvlPropsTheory.inc_clock_def] ) >>
    rev_full_simp_tac(srw_ss())[state_rel_def] >> full_simp_tac(srw_ss())[] ) >>
  strip_tac >>
  simp[bviSemTheory.semantics_def] >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[] >- (
    last_x_assum(qspec_then`k`strip_assume_tac) >>
    qmatch_assum_abbrev_tac`FST q ≠ _` >>
    Cases_on`q`>>full_simp_tac(srw_ss())[markerTheory.Abbrev_def] >>
    pop_assum(assume_tac o SYM) >>
    drule (GEN_ALL compile_prog_evaluate) >>
    disch_then drule >> simp[] >>
    conj_tac >- (
      Cases_on`k`>>simp[] >>
      full_simp_tac(srw_ss())[bviSemTheory.evaluate_def] >>
      every_case_tac >> full_simp_tac(srw_ss())[] >>
      full_simp_tac(srw_ss())[compile_prog_def,LET_THM] >>
      pairarg_tac >> full_simp_tac(srw_ss())[] >> rpt var_eq_tac >>
      full_simp_tac(srw_ss())[find_code_def,lookup_fromAList,ALOOKUP_APPEND,stubs_def] >>
      every_case_tac >> full_simp_tac(srw_ss())[] >>
      TRY(rpt(qpat_assum`_ = _`mp_tac) >> EVAL_TAC >> NO_TAC) >>
      full_simp_tac(srw_ss())[InitGlobals_code_def]) >>
    spose_not_then strip_assume_tac >>
    qmatch_assum_abbrev_tac`FST q = _` >>
    Cases_on`q`>>full_simp_tac(srw_ss())[markerTheory.Abbrev_def] >>
    pop_assum(assume_tac o SYM) >>
    imp_res_tac bviPropsTheory.evaluate_add_clock >> rev_full_simp_tac(srw_ss())[] >>
    first_x_assum(qspec_then`ck`mp_tac) >>
    simp[inc_clock_def] >>
    every_case_tac >> full_simp_tac(srw_ss())[] >>
    metis_tac[semanticPrimitivesTheory.abort_nchotomy]) >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  conj_tac >- (
    spose_not_then strip_assume_tac >> srw_tac[][] >>
    fsrw_tac[QUANT_INST_ss[pair_default_qp]][] >>
    last_assum(qspec_then`SUC k`mp_tac) >>
    (fn g => subterm (fn tm => Cases_on`^(assert (can dest_prod o type_of) tm)` g) (#2 g)) >>
    strip_tac >>
    drule (GEN_ALL compile_prog_evaluate) >>
    disch_then drule >>
    impl_tac >- full_simp_tac(srw_ss())[] >>
    strip_tac >>
    qmatch_assum_rename_tac`bvlSem$evaluate(_,[],_ (SUC k)) = (_,rr)` >>
    reverse(Cases_on`rr.ffi.final_event`) >- (
      first_x_assum(qspecl_then[`SUC k`,`FFI_outcome(THE rr.ffi.final_event)`]mp_tac) >>
      simp[] ) >>
    qpat_assum`∀x y. ¬z`mp_tac >> simp[] >>
    qexists_tac`SUC k`>>simp[] >>
    reverse(Cases_on`s.ffi.final_event`)>>full_simp_tac(srw_ss())[]>-(
      rator_x_assum`bviSem$evaluate`mp_tac >>
      qmatch_assum_abbrev_tac`bviSem$evaluate (exps,[],ss) = _` >>
      qspecl_then[`exps`,`[]`,`ss`]mp_tac bviPropsTheory.evaluate_add_to_clock_io_events_mono >>
      disch_then(qspec_then`SUC ck`mp_tac)>>
      fsrw_tac[ARITH_ss][ADD1,bviPropsTheory.inc_clock_def,Abbr`ss`] >>
      rpt strip_tac >> full_simp_tac(srw_ss())[] >>
      full_simp_tac(srw_ss())[state_rel_def] >> rev_full_simp_tac(srw_ss())[] ) >>
    rator_x_assum`bviSem$evaluate`mp_tac >>
    drule bviPropsTheory.evaluate_add_clock >>
    impl_tac >- (strip_tac >> full_simp_tac(srw_ss())[]) >>
    disch_then(qspec_then`SUC ck`mp_tac) >>
    simp[bviPropsTheory.inc_clock_def] >>
    fsrw_tac[ARITH_ss][ADD1] >>
    rpt strip_tac >> full_simp_tac(srw_ss())[]) >>
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
    full_simp_tac(srw_ss())[bviSemTheory.evaluate_def,bvlSemTheory.evaluate_def]>>
    every_case_tac >> full_simp_tac(srw_ss())[] >>
    simp[GSYM IMP_CONJ_THM] >> strip_tac >>
    conj_tac >> qexists_tac`0`>>simp[])>>
  strip_tac >>
  qmatch_assum_abbrev_tac`state_rel _ (SND p1) (SND p2)` >>
  Cases_on`p1`>>Cases_on`p2`>>full_simp_tac(srw_ss())[markerTheory.Abbrev_def] >>
  ntac 2 (pop_assum(mp_tac o SYM)) >> ntac 2 strip_tac >> full_simp_tac(srw_ss())[] >>
  qmatch_assum_rename_tac`state_rel _ p1 p2` >>
  `p1.ffi = p2.ffi` by full_simp_tac(srw_ss())[state_rel_def] >>
  reverse conj_tac >> srw_tac[][]
  >- ( qexists_tac`ck+k` >> full_simp_tac(srw_ss())[] ) >>
  qexists_tac`k` >> full_simp_tac(srw_ss())[] >>
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
  full_simp_tac(srw_ss())[IS_PREFIX_APPEND] >> simp[EL_APPEND1]);

val compile_semantics = Q.store_thm("compile_semantics",
  `compile start n prog = (start', prog', n') ∧
   ALL_DISTINCT (MAP FST prog) ∧
   semantics ffi0 (fromAList prog) start ≠ Fail
   ⇒
   semantics ffi0 (fromAList prog') start' =
   semantics ffi0 (fromAList prog) start`,
  srw_tac[][compile_def]
  \\ drule (GEN_ALL compile_prog_semantics)
  \\ fs [MAP_FST_optimise,bvl_inlineProofTheory.MAP_FST_compile_prog]
  \\ disch_then (qspec_then `ffi0` mp_tac)
  \\ rewrite_tac [GSYM AND_IMP_INTRO]
  \\ impl_tac THEN1
   (simp[optimise_def,MAP_MAP_o,o_DEF,UNCURRY]
    \\ full_simp_tac(srw_ss())[Once bEvery_EVERY,EVERY_MAP]
    \\ full_simp_tac(srw_ss())[EVERY_MEM]
    \\ simp[bvl_handleProofTheory.compile_exp_GoodHandleLet])
  \\ metis_tac [optimise_semantics,
       bvl_inlineProofTheory.compile_prog_semantics]);

val _ = export_theory();
