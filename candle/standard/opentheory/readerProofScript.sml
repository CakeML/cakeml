open preamble readerTheory ml_monadBaseTheory
     holKernelTheory holKernelProofTheory

val _ = new_theory"readerProof";

(* case_eq theorems *)

val exc_case_eq = prove_case_eq_thm{case_def=exc_case_def,nchotomy=exc_nchotomy};
val term_case_eq = prove_case_eq_thm{case_def=holSyntaxTheory.term_case_def,nchotomy=holSyntaxTheory.term_nchotomy};
val option_case_eq = prove_case_eq_thm{case_def=optionTheory.option_case_def,nchotomy=optionTheory.option_nchotomy};
val object_case_eq = prove_case_eq_thm{case_def=readerTheory.object_case_def,nchotomy=readerTheory.object_nchotomy};
val exn_case_eq = prove_case_eq_thm{case_def=holKernelTheory.hol_exn_case_def,nchotomy=holKernelTheory.hol_exn_nchotomy};
val list_case_eq = prove_case_eq_thm{case_def=listTheory.list_case_def,nchotomy=listTheory.list_nchotomy};
val update_case_eq = prove_case_eq_thm{case_def=holSyntaxTheory.update_case_def,nchotomy=holSyntaxTheory.update_nchotomy};
val state_case_eq = prove_case_eq_thm{case_def=readerTheory.state_case_def,nchotomy=readerTheory.state_nchotomy};
val case_eq_thms =
  LIST_CONJ
    [exc_case_eq, term_case_eq, option_case_eq,
     object_case_eq, list_case_eq, pair_case_eq,
     exn_case_eq, update_case_eq, thm_caseeq,
     hol_refs_caseeq,state_case_eq]

(* --- Reader does not raise Clash --- *)

val pop_not_clash = Q.store_thm("pop_not_clash[simp]",
  `pop x y ≠ (Failure (Clash tm),refs)`,
  EVAL_TAC \\ rw[] \\ EVAL_TAC);

val peek_not_clash = Q.store_thm("peek_not_clash[simp]",
  `peek x y <> (Failure (Clash tm),refs)`,
  EVAL_TAC \\ rw [] \\ EVAL_TAC);

val getNum_not_clash = Q.store_thm("getNum_not_clash[simp]",
  `getNum x y ≠ (Failure (Clash tm),refs)`,
  Cases_on`x` \\ EVAL_TAC);

val getVar_not_clash = Q.store_thm("getVar_not_clash[simp]",
  `getVar x y ≠ (Failure (Clash tm),refs)`,
  Cases_on`x` \\ EVAL_TAC);

val getTerm_not_clash = Q.store_thm("getTerm_not_clash[simp]",
  `getTerm x y ≠ (Failure (Clash tm),refs)`,
  Cases_on`x` \\ EVAL_TAC);

val getThm_not_clash = Q.store_thm("getThm_not_clash[simp]",
  `getThm x y ≠ (Failure (Clash tm),refs)`,
  Cases_on`x` \\ EVAL_TAC);

val getType_not_clash = Q.store_thm("getType_not_clash[simp]",
  `getType x y <> (Failure (Clash tm),refs)`,
  Cases_on`x` \\ EVAL_TAC);

val getName_not_clash = Q.store_thm("getName_not_clash[simp]",
  `getName x y <> (Failure (Clash tm),refs)`,
  Cases_on`x` \\ EVAL_TAC
  \\ fs [st_ex_return_def] \\ CASE_TAC \\ fs []);

val getConst_not_clash = Q.store_thm("getConst_not_clash[simp]",
  `getConst x y <> (Failure (Clash tm),refs)`,
  Cases_on`x` \\ EVAL_TAC);

val getList_not_clash = Q.store_thm("getList_not_clash[simp]",
  `getList x y <> (Failure (Clash tm),refs)`,
  Cases_on `x` \\ EVAL_TAC);

val getTypeOp_not_clash = Q.store_thm("getTypeOp_not_clash[simp]",
  `getTypeOp a b <> (Failure (Clash tm),refs)`,
  Cases_on`a` \\ EVAL_TAC);

val getPair_not_clash = Q.store_thm("getPair_not_clash[simp]",
  `getPair a b <> (Failure (Clash tm),refs)`,
  Cases_on `a` \\ EVAL_TAC \\ Cases_on `l` \\ EVAL_TAC
  \\ Cases_on `t` \\ EVAL_TAC \\ Cases_on `t'` \\ EVAL_TAC);

val getCns_not_clash = Q.store_thm("getCns_not_clash[simp]",
  `getCns a b <> (Failure (Clash tm),refs)`,
  Cases_on `a` \\ EVAL_TAC \\ every_case_tac \\ fs []);

val getNvs_not_clash = Q.store_thm("getNvs_not_clash[simp]",
  `getNvs a b <> (Failure (Clash tm),refs)`,
  Cases_on `a` \\ EVAL_TAC \\ every_case_tac \\ fs [] \\ EVAL_TAC
  \\ rpt (pairarg_tac \\ fs [])
  \\ every_case_tac \\ fs [] \\ rw []
  \\ metis_tac [getPair_not_clash, getName_not_clash, getVar_not_clash]);

val getTms_not_clash = Q.store_thm("getTms_not_clash[simp]",
  `getTms a b <> (Failure (Clash tm),refs)`,
  Cases_on `a` \\ EVAL_TAC
  \\ every_case_tac \\ fs [] \\ rpt (pairarg_tac \\ fs [])
  \\ every_case_tac \\ fs [] \\ rw []
  \\ metis_tac [getPair_not_clash, getName_not_clash, getVar_not_clash, getTerm_not_clash]);

val getTys_not_clash = Q.store_thm("getTys_not_clash[simp]",
  `getTys a b <> (Failure (Clash tm),refs)`,
  Cases_on `a` \\ EVAL_TAC
  \\ every_case_tac \\ fs [] \\ rpt (pairarg_tac \\ fs [])
  \\ every_case_tac \\ fs [] \\ rw []
  \\ metis_tac [getName_not_clash, getType_not_clash, getPair_not_clash]);

(* --- Use Candle kernel soundness theorem --- *)

(* TODO replace with actual theorem *)
val readLine_no_clash = Q.store_thm("readLine_no_clash[simp]",
  `readLine line st refs <> (Failure (Clash tm), refs)`,
  cheat
  );

(* Refinement invariant for objects *)
val OBJ_def = tDefine "OBJ" `
  (OBJ defs (List xs)     <=> EVERY (OBJ defs) xs) /\
  (OBJ defs (Type ty)     <=> TYPE defs ty) /\
  (OBJ defs (Var (n, ty)) <=> TYPE defs ty) /\
  (OBJ defs (Term tm)     <=> TERM defs tm) /\
  (OBJ defs (Thm thm)     <=> THM defs thm) /\
  (OBJ defs _             <=> T)`
  (WF_REL_TAC `measure (object_size o SND)`
   \\ Induct \\ rw [object_size_def]
   \\ res_tac \\ fs []);

val READER_STATE_def = Define `
  READER_STATE defs st <=>
    EVERY (THM defs) st.thms /\
    EVERY (OBJ defs) st.stack`

val getNum_thm = Q.store_thm("getNum_thm",
  `STATE defs refs /\
   getNum obj refs = (res, refs')
   ==>
   STATE defs refs'`,
   Cases_on `obj` \\ rw [getNum_def, raise_Fail_def, st_ex_return_def] \\ fs []);

val getName_thm = Q.store_thm("getName_thm",
  `STATE defs refs /\
   getName obj refs = (res, refs')
   ==>
   STATE defs refs'`,
   Cases_on `obj` \\ rw [getName_def, raise_Fail_def, st_ex_return_def] \\ fs []);

val getList_thm = Q.store_thm("getList_thm",
  `STATE defs refs /\
   OBJ defs obj /\
   getList obj refs = (res, refs')
   ==>
   STATE defs refs' /\
   case res of
     Failure _ => T
   | Success ls => EVERY (OBJ defs) ls`,
   Cases_on `obj` \\ rw [getList_def, raise_Fail_def, st_ex_return_def] \\ fs []
   \\ metis_tac [OBJ_def]);

val getTypeOp_thm = Q.store_thm("getTypeOp_thm",
  `STATE defs refs /\
   getTypeOp obj refs = (res, refs')
   ==>
   STATE defs refs'`,
   Cases_on `obj` \\ rw [getTypeOp_def, raise_Fail_def, st_ex_return_def] \\ fs []);

val getType_thm = Q.store_thm("getType_thm",
  `STATE defs refs /\
   OBJ defs obj /\
   getType obj refs = (res, refs')
   ==>
   STATE defs refs' /\
   case res of
     Failure _ => T
   | Success ty => TYPE defs ty`,
   Cases_on `obj` \\ rw [getType_def, raise_Fail_def, st_ex_return_def]
   \\ fs [OBJ_def]);

val getConst_thm = Q.store_thm("getConst_thm",
  `STATE defs refs /\
   getConst obj refs = (res, refs')
   ==>
   STATE defs refs'`,
   Cases_on `obj` \\ rw [getConst_def, raise_Fail_def, st_ex_return_def] \\ fs []);

val getVar_thm = Q.store_thm("getVar_thm",
  `STATE defs refs /\
   OBJ defs obj /\
   getVar obj refs = (res, refs')
   ==>
   STATE defs refs' /\
   case res of
     Failure _ => T
   | Success (_, ty) => TYPE defs ty`,
   Cases_on `obj` \\ rw [getVar_def, raise_Fail_def, st_ex_return_def] \\ fs []
   \\ CASE_TAC \\ fs [OBJ_def]);

val getTerm_thm = Q.store_thm("getTerm_thm",
  `STATE defs refs /\
   OBJ defs obj /\
   getTerm obj refs = (res, refs')
   ==>
   STATE defs refs' /\
   case res of
     Failure _ => T
   | Success tm => TERM defs tm`,
   Cases_on `obj` \\ rw [getTerm_def, raise_Fail_def, st_ex_return_def] \\ fs []
   \\ fs [OBJ_def]);

val getThm_thm = Q.store_thm("getThm_thm",
  `STATE defs refs /\
   OBJ defs obj /\
   getThm obj refs = (res, refs')
   ==>
   STATE defs refs' /\
   case res of
     Failure _ => T
   | Success thm => THM defs thm`,
   Cases_on `obj` \\ rw [getThm_def, raise_Fail_def, st_ex_return_def] \\ fs []
   \\ fs [OBJ_def]);

val pop_thm = Q.store_thm("pop_thm",
  `STATE defs refs /\
   READER_STATE defs st /\
   pop st refs = (res, refs')
   ==>
   STATE defs refs' /\
   case res of
     Failure _ => T
   | Success (a, st') => OBJ defs a /\ READER_STATE defs st'`,
   rw [pop_def, raise_Fail_def, st_ex_return_def]
   \\ every_case_tac \\ fs [READER_STATE_def, state_component_equality]);

val peek_thm = Q.store_thm("peek_thm",
  `STATE defs refs /\
   READER_STATE defs st /\
   peek st refs = (res, refs')
   ==>
   STATE defs refs' /\
   case res of
     Failure _ => T
   | Success obj => OBJ defs obj`,
   rw [peek_def, raise_Fail_def, st_ex_return_def]
   \\ every_case_tac \\ fs []
   \\ fs [READER_STATE_def]);

val push_thm = Q.store_thm("push_thm",
  `READER_STATE defs st /\
   OBJ defs obj
   ==>
   READER_STATE defs (push obj st)`,
  rw [push_def, READER_STATE_def]);

(*val insert_dict_thm = Q.store_thm("insert_dict_thm",*)
  (*`T`, cheat);*)

(*val delete_dict_thm = Q.store_thm("delete_dict_thm",*)
  (*`T`, cheat);*)

val first_EVERY = Q.store_thm("first_EVERY",
  `!Q xs x.
     EVERY P xs /\
     first Q xs = SOME x
     ==>
     P x`,
  recInduct first_ind \\ rw [Once first_def]
  \\ Cases_on `l` \\ fs [] >- fs [Once first_def]
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [first_def]
  \\ fs [bool_case_eq]
  \\ strip_tac \\ fs []
  \\ first_x_assum (qspec_then `x` mp_tac)
  \\ CASE_TAC \\ fs [] >- fs [Once first_def]
  \\ fs [bool_case_eq]
  \\ once_rewrite_tac [first_def] \\ fs [bool_case_eq]
  \\ CASE_TAC \\ fs []
  >-
   (fs [Once first_def]
    \\ fs [case_eq_thms, bool_case_eq, Once first_def])
  \\ fs [Once first_def, case_eq_thms, bool_case_eq]
  \\ fs [Once first_def, case_eq_thms, bool_case_eq]
  \\ fs [Once first_def, case_eq_thms, bool_case_eq]);

val find_axiom_thm = Q.store_thm("find_axiom_thm",
  `EVERY (THM defs) refs.the_axioms /\ (* this is nowhere to be found; can it be assumed? *)
   STATE defs refs /\
   EVERY (TERM defs) ls /\
   TERM defs tm /\
   find_axiom (ls, tm) refs = (res, refs')
   ==>
   STATE defs refs' /\
   case res of
     Failure _ => T
   | Success thm => THM defs thm`,
  fs [find_axiom_def, st_ex_bind_def, st_ex_return_def, raise_Fail_def]
  \\ fs [get_the_axioms_def]
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
  \\ qmatch_asmsub_abbrev_tac `first P`
  \\ Q.ISPECL_THEN [`THM defs`, `P`] mp_tac (GEN_ALL first_EVERY)
  \\ disch_then drule \\ fs []);

val getPair_thm = Q.store_thm("getPair_thm",
  `STATE defs refs /\
   OBJ defs obj /\
   getPair obj refs = (res, refs')
   ==>
   STATE defs refs' /\
   case res of
     Failure _ => T
   | Success (a, b) => OBJ defs a /\ OBJ defs b`,
  Cases_on `obj` \\ rw [getPair_def, st_ex_return_def, raise_Fail_def] \\ fs []
  \\ Cases_on `l` \\ fs [getPair_def, st_ex_return_def, raise_Fail_def] \\ rfs []
  \\ every_case_tac \\ fs []
  \\ Cases_on `t` \\ fs [getPair_def, st_ex_return_def, raise_Fail_def]
  \\ rename1 `x::y::z`
  \\ Cases_on `z` \\ fs [getPair_def, st_ex_return_def, raise_Fail_def]
  \\ fs [OBJ_def]);

val getTys_thm = Q.store_thm("getTys_thm",
  `STATE defs refs /\
   OBJ defs obj /\
   getTys obj refs = (res, refs')
   ==>
   STATE defs refs' /\
   case res of
     Failure _ => T
   | Success (t, ty) => TYPE defs t /\ TYPE defs ty`,
  Cases_on `obj`
  \\ fs [getTys_def, st_ex_bind_def, st_ex_return_def, raise_Fail_def, UNCURRY]
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
  \\ TRY (fs [getPair_def, st_ex_return_def, raise_Fail_def] \\ NO_TAC)
  \\ TRY (PairCases_on `a`) \\ fs []
  \\ TRY (map_every imp_res_tac [getPair_thm, getType_thm, getName_thm] \\ fs [] \\ NO_TAC)
  \\ fs [STATE_def]
  \\ irule mk_vartype_thm
  \\ fs [STATE_def] \\ rfs []);

val getTms_thm = Q.store_thm("getTms_thm",
  `STATE defs refs /\
   OBJ defs obj /\
   getTms obj refs = (res, refs')
   ==>
   STATE defs refs' /\
   case res of
     Failure _ => T
   | Success (tm, var) => TERM defs tm /\ TERM defs var`,
  Cases_on `obj`
  \\ fs [getTms_def, st_ex_bind_def, st_ex_return_def, raise_Fail_def, UNCURRY]
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
  \\ TRY (fs [getPair_def, st_ex_return_def, raise_Fail_def] \\ NO_TAC)
  \\ TRY (PairCases_on `a`) \\ fs []
  \\ TRY (map_every imp_res_tac [getPair_thm, getTerm_thm, getVar_thm] \\ fs [] \\ NO_TAC)
  \\ rename1 `getVar _ _ = (_ v,_)` \\ PairCases_on `v`
  \\ irule mk_var_thm >- (asm_exists_tac \\ fs [])
  \\ map_every imp_res_tac [getPair_thm, getTerm_thm, getVar_thm] \\ fs []);

val getNvs_thm = Q.store_thm("getNvs_thm",
  `STATE defs refs /\
   OBJ defs obj /\
   getNvs obj refs = (res, refs')
   ==>
   STATE defs refs' /\
   case res of
     Failure _ => T
   | Success (v1, v2) => TERM defs v1 /\ TERM defs v2`,
  Cases_on `obj`
  \\ fs [getNvs_def, st_ex_bind_def, st_ex_return_def, raise_Fail_def, UNCURRY]
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
  \\ TRY (fs [getPair_def, st_ex_return_def, raise_Fail_def] \\ NO_TAC)
  \\ TRY (PairCases_on `a`) \\ fs []
  \\ TRY (map_every imp_res_tac [getPair_thm, getName_thm, getVar_thm] \\ fs [] \\ NO_TAC)
  \\ rename1 `getVar _ _ = (_ v,_)` \\ PairCases_on `v`
  \\ irule mk_var_thm
  \\ TRY (asm_exists_tac \\ fs [])
  \\ map_every imp_res_tac [getPair_thm, getName_thm, getVar_thm] \\ fs []);

val getCns_thm = Q.store_thm("getCns_thm",
  `STATE defs refs /\
   TERM defs tm /\
   getCns (tm, _) refs = (res, refs')
   ==>
   STATE defs refs' /\
   case res of
     Failure _ => T
   | Success a => OBJ defs a`,
  rw [getCns_def, st_ex_bind_def, st_ex_return_def, UNCURRY]
  \\ every_case_tac \\ fs [] \\ rw []
  \\ metis_tac [dest_var_thm, OBJ_def]);

(* TODO remove: EQ_MP_thm *)
val EQ_MP_STATE = Q.store_thm("EQ_MP_STATE",
  `STATE defs refs /\
   EQ_MP th1 th2 refs = (res, refs')
   ==>
   STATE defs refs'`,
   Cases_on `th1` \\ Cases_on `th2`
   \\ fs [EQ_MP_def, raise_Fail_def, st_ex_return_def]
   \\ every_case_tac \\ fs [] \\ rw [] \\ fs []);

val readLine_thm = Q.store_thm("readLine_thm",
  `STATE defs refs /\
   READER_STATE defs st /\
   readLine line st refs = (res, refs')
   ==>
   STATE defs refs' /\
   case res of
     Failure _ => T
   | Success st' => READER_STATE defs st'`,

  fs [readLine_def, st_ex_bind_def, st_ex_return_def, raise_Fail_def]
  \\ IF_CASES_TAC \\ fs []
  >- (* version *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ map_every imp_res_tac [getNum_thm, pop_thm] \\ fs [])
  \\ IF_CASES_TAC \\ fs []
  >- (* absTerm *)
    cheat
  \\ IF_CASES_TAC \\ fs []
  >- (* absThm *)
    cheat
  \\ IF_CASES_TAC \\ fs []
  >- (* appTerm *)
   (
    fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms]
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ cheat (* TODO mk_comb *)
   )
  \\ IF_CASES_TAC \\ fs []
  >- (* appThm *)
   (
    fs [case_eq_thms] \\ rw  []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms]
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ cheat (* TODO MK_COMB *)
   )
  \\ IF_CASES_TAC \\ fs []
  >- (* assume *)
   (
    fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ cheat (* TODO ASSUME *)
   )
  \\ IF_CASES_TAC \\ fs []
  >- (* axiom *)
   (
    fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ cheat (* TODO find_axiom *)
   )
  \\ IF_CASES_TAC \\ fs []
  >- (* betaConv *)
   (
    fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ cheat (* TODO BETA *)
   )
  \\ IF_CASES_TAC \\ fs []
  >- (* cons *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ map_every imp_res_tac [pop_thm, getList_thm] \\ fs []
    \\ irule push_thm
    \\ fs [OBJ_def]
    \\ metis_tac [])
  \\ IF_CASES_TAC \\ fs []
  >- (* const *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ map_every imp_res_tac [pop_thm, getName_thm] \\ fs []
    \\ irule push_thm \\ fs [OBJ_def])
  \\ IF_CASES_TAC \\ fs []
  >- (* constTerm *)
   (
    fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ every_case_tac \\ fs [] \\ rw []
    \\ TRY (map_every imp_res_tac [pop_thm, getType_thm, getConst_thm] \\ fs [] \\ NO_TAC)
    \\ TRY (irule push_thm \\ fs [OBJ_def])
    \\ cheat (* TODO *)
   )
  \\ IF_CASES_TAC \\ fs []
  >- (* deductAntysim *)
   (
    fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ cheat (* TODO DEDUCT_ANTISYM_RULE *)
   )
  \\ IF_CASES_TAC \\ fs []
  >- (* def *)
   (fs [case_eq_thms] \\ rw []
    \\ fs [insert_dict_def]
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms, bool_case_eq, COND_RATOR] \\ rw []
    \\ map_every imp_res_tac [pop_thm, peek_thm, getNum_thm] \\ fs []
    \\ fs [READER_STATE_def])
  \\ IF_CASES_TAC \\ fs []
  >- (* defineConst *)
   (
    fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ map_every imp_res_tac [getTerm_thm, pop_thm] \\ fs []
    \\ cheat (* TODO *)
   )
  \\ IF_CASES_TAC \\ fs []
  >- (* defineConstList *)
    cheat
  \\ IF_CASES_TAC \\ fs []
  >- (* defineTypeOp *)
    cheat
  \\ IF_CASES_TAC \\ fs []
  >- (* eqMp *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ map_every imp_res_tac [pop_thm, getThm_thm, EQ_MP_STATE] \\ fs [] \\ rfs []
    \\ irule push_thm \\ fs [OBJ_def]
    \\ metis_tac [EQ_MP_thm])
  \\ IF_CASES_TAC \\ fs []
  >- (* hdTl *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ every_case_tac \\ fs [] \\ rw []
    \\ map_every imp_res_tac [pop_thm, getList_thm] \\ fs []
    \\ irule push_thm >- metis_tac [OBJ_def]
    \\ irule push_thm \\ metis_tac [OBJ_def])
  \\ IF_CASES_TAC \\ fs []
  >- (* nil *)
   (fs [case_eq_thms] \\ rw [] \\ fs []
    \\ irule push_thm \\ fs [OBJ_def])
  \\ IF_CASES_TAC \\ fs []
  >- (* opType *)
   (
    fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (map_every imp_res_tac [pop_thm, getList_thm, getType_thm] \\ fs [] \\ NO_TAC)
    \\ cheat (* TODO *)
   )
  \\ IF_CASES_TAC \\ fs []
  >- (* pop *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ imp_res_tac pop_thm \\ fs [])
  \\ IF_CASES_TAC \\ fs []
  >- (* pragma *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ imp_res_tac pop_thm \\ fs [])
  \\ IF_CASES_TAC \\ fs []
  >- (* proveHyp *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ map_every imp_res_tac [PROVE_HYP_thm, pop_thm, getThm_thm] \\ fs []
    \\ TRY (irule push_thm \\ fs [OBJ_def])
    \\ metis_tac [])
  \\ IF_CASES_TAC \\ fs []
  >- (* ref *)
   (
    fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms, bool_case_eq, COND_RATOR] \\ rw []
    \\ every_case_tac \\ fs [] \\ rw []
    \\ map_every imp_res_tac [pop_thm, getNum_thm] \\ fs []
    \\ irule push_thm \\ fs [OBJ_def]
    \\ cheat (* TODO need to ensure the dict contains OBJ things *)
   )
  \\ IF_CASES_TAC \\ fs []
  >- (* refl *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ map_every imp_res_tac [pop_thm, getTerm_thm, REFL_thm] \\ fs []
    \\ TRY (irule push_thm \\ fs [OBJ_def])
    \\ metis_tac [])
  \\ IF_CASES_TAC \\ fs []
  >- (* remove *)
   (
    fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms, bool_case_eq, COND_RATOR] \\ rw []
    \\ every_case_tac \\ fs [] \\ rw []
    \\ map_every imp_res_tac [pop_thm, getNum_thm] \\ fs []
    \\ irule push_thm \\ fs [OBJ_def]
    \\ cheat (* TODO dicts again *)
   )
  \\ IF_CASES_TAC \\ fs []
  >- (* subst *)
   (
    fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms, bool_case_eq, COND_RATOR] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms, bool_case_eq, COND_RATOR] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms, bool_case_eq, COND_RATOR] \\ rw []
    \\ map_every imp_res_tac [pop_thm, getThm_thm, getPair_thm, getList_thm] \\ fs []
    \\ cheat (* TODO *)
   )
  \\ IF_CASES_TAC \\ fs []
  >- (* sym *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ map_every imp_res_tac [pop_thm, getThm_thm] \\ fs []
    \\ TRY (irule push_thm \\ fs [OBJ_def])
    \\ metis_tac [SYM_thm])
  \\ IF_CASES_TAC \\ fs []
  >- (* thm *)
   (
    fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ cheat (* TODO maps *)
   )
  \\ IF_CASES_TAC \\ fs []
  >- (* trans *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ map_every imp_res_tac [pop_thm, getThm_thm] \\ fs []
    \\ TRY (irule push_thm \\ fs [OBJ_def])
    \\ metis_tac [TRANS_thm])
  \\ IF_CASES_TAC \\ fs []
  >- (* typeOp *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ map_every imp_res_tac [pop_thm, getName_thm] \\ fs []
    \\ irule push_thm \\ fs [OBJ_def])
  \\ IF_CASES_TAC \\ fs []
  >- (* var *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ map_every imp_res_tac [pop_thm, getName_thm, getType_thm] \\ fs []
    \\ irule push_thm \\ fs [OBJ_def])
  \\ IF_CASES_TAC \\ fs []
  >-
   (
    fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ map_every imp_res_tac [pop_thm, getVar_thm] \\ fs []
    \\ rename1 `mk_var v1` \\ PairCases_on `v1` \\ fs [mk_var_def, TERM_def]
    \\ irule push_thm \\ fs [OBJ_def]
    \\ cheat (* TODO Var .. *)
   )
  \\ IF_CASES_TAC \\ fs []
  >- (* varType *)
   (fs [case_eq_thms] \\ rw []
    \\ TRY (pairarg_tac \\ fs []) \\ fs [case_eq_thms] \\ rw []
    \\ map_every imp_res_tac [pop_thm, getName_thm] \\ fs []
    \\ irule push_thm \\ fs []
    \\ fs [OBJ_def, STATE_def]
    \\ irule mk_vartype_thm
    \\ metis_tac [STATE_def, CONTEXT_def])
     (* digits *)
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
  \\ irule push_thm \\ fs [OBJ_def]);

val readLines_thm = Q.store_thm("readLines_thm",
  `!lines st res refs refs'.
     STATE defs refs /\
     READER_STATE defs st /\
     readLines lines st refs = (res, refs')
     ==>
     STATE defs refs' /\
     case res of
       Failure _ => T
     | Success st' => READER_STATE defs st'`,
  recInduct readLines_ind \\ once_rewrite_tac [readLines_def] \\ rw []
  \\ fs [st_ex_return_def, st_ex_bind_def] \\ Cases_on `lls` \\ fs [] \\ rw []
  \\ Cases_on `t` \\ fs []
  \\ TRY
   (fs [Once readLines_def, st_ex_return_def]
    \\ every_case_tac \\ imp_res_tac readLine_thm \\ fs []
    \\ rw [] \\ fs []
    \\ NO_TAC)
  \\ pop_assum mp_tac
  \\ CASE_TAC \\ fs []
  \\ reverse CASE_TAC \\ fs []
  >- (rw [] \\ metis_tac [readLine_thm])
  \\ simp [Once readLines_def, st_ex_bind_def]
  \\ CASE_TAC \\ fs []
  \\ reverse CASE_TAC \\ fs []
  >- (rw [] \\ imp_res_tac readLine_thm \\ fs [])
  \\ strip_tac
  \\ `STATE defs r /\ READER_STATE defs a` by (imp_res_tac readLine_thm \\ fs [])
  \\ first_x_assum drule \\ rveq
  \\ disch_then drule \\ fs [])

val readLines_init_state_thm = Q.store_thm("readLines_init_state_thm",
  `STATE defs refs /\
  readLines lines init_state refs = (res, refs')
  ==>
  STATE defs refs' /\
  case res of
    Failure _ => T
  | Success st' => READER_STATE defs st'`,
  sg `READER_STATE defs init_state`
  >- fs [init_state_def, READER_STATE_def]
  \\ rw []
  \\ metis_tac [readLines_thm]);

val _ = export_theory();

