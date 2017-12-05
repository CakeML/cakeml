open preamble readerTheory ml_monadBaseTheory
     holKernelTheory holKernelProofTheory

val _ = new_theory"readerProof";

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

val _ = export_theory();

