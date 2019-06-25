(*
  Correctness proof for bvl_const
*)
open preamble bvl_constTheory bvlSemTheory bvlPropsTheory;

val _ = new_theory"bvl_constProof";

val v_rel_def = Define `
  v_rel (:'c) (:'ffi) a x y xs ys =
    case a of
    | Var n => LLOOKUP ys n = SOME x
    | Op _ _ => !(s:('c,'ffi) bvlSem$state) env. evaluate ([a],env,s) = (Rval [x],s)
    | _ => F`;

val env_rel_def = Define `
  (env_rel (:'c) (:'ffi) [] e1 e2 = (e1 = e2)) /\
  (env_rel (:'c) (:'ffi) (NONE::rest) (x::e1) (y::e2) <=>
     (x = y) /\ env_rel (:'c) (:'ffi) rest e1 e2) /\
  (env_rel (:'c) (:'ffi) (SOME a::rest) (x::e1) (y::e2) <=>
     v_rel (:'c) (:'ffi) a x y (x::e1) (y::e2) /\ env_rel (:'c) (:'ffi) rest e1 e2) /\
  (env_rel _ _ _ _ _ = F)`

Theorem env_rel_length:
   !ax env env2. env_rel (:'c) (:'ffi) ax env env2 ==> LENGTH env2 = LENGTH env
Proof
  Induct \\ Cases_on `env` \\ Cases_on `env2` \\ fs [env_rel_def]
  \\ Cases \\ fs [env_rel_def]
QED

val env_rel_LLOOKUP_NONE = Q.prove(
  `!ax env env2 n.
      env_rel (:'c) (:'ffi) ax env env2 /\
      (LLOOKUP ax n = NONE \/ LLOOKUP ax n = SOME NONE) ==>
      EL n env2 = EL n env`,
  Induct \\ Cases_on `env` \\ Cases_on `env2` \\ fs [env_rel_def]
  \\ Cases \\ fs [env_rel_def,LLOOKUP_def]
  \\ rw [] \\ fs [] \\ Cases_on `n` \\ fs [EL]);

val env_rel_LOOKUP_SOME = Q.prove(
  `!env env2 ax x n.
      env_rel (:'c) (:'ffi) ax env env2 /\
      LLOOKUP ax n = SOME (SOME x) ==>
      v_rel (:'c) (:'ffi) x (EL n env) (EL n env2) (DROP n env) (DROP n env2)`,
  Induct \\ Cases_on `env2` \\ Cases_on `ax` \\ fs [env_rel_def,LLOOKUP_def]
  \\ rw [] \\ fs [env_rel_def] \\ res_tac \\ fs []
  \\ Cases_on `n` \\ fs [env_rel_def]
  \\ first_x_assum match_mp_tac
  \\ Cases_on `h'` \\ fs [env_rel_def]);

Theorem evaluate_delete_var_Rerr_SING:
   !x s r e env2.
      evaluate ([x],env2,s) = (Rerr e,r) /\
      e <> Rabort Rtype_error ==>
      evaluate ([bvl_const$delete_var x],env2,s) = (Rerr e,r)
Proof
  Cases \\ fs [delete_var_def]
  \\ fs [evaluate_def,do_app_def] \\ rw []
  \\ CCONTR_TAC \\ fs [] \\ rw []
QED

val evaluate_delete_var_Rerr = Q.prove(
  `!xs s r e env2.
      evaluate (xs,env2,s) = (Rerr e,r) /\
      e <> Rabort Rtype_error ==>
      evaluate (MAP bvl_const$delete_var xs,env2,s) = (Rerr e,r)`,
  Induct \\ fs [] \\ once_rewrite_tac [evaluate_CONS]
  \\ rw [] \\ every_case_tac \\ fs [] \\ rw []
  \\ TRY (drule evaluate_delete_var_Rerr_SING \\ fs [])
  \\ res_tac \\ fs []
  \\ Cases_on `h` \\ fs [delete_var_def]
  \\ rw [] \\ fs []
  \\ fs [evaluate_def,do_app_def] \\ rw []
  \\ every_case_tac \\ fs [] \\ rw []);

val evaluate_delete_var_Rval = Q.prove(
  `!xs env2 s a r ax env.
      evaluate (xs,env2,s:('c,'ffi) bvlSem$state) = (Rval a,r) /\
      env_rel (:'c) (:'ffi) ax env env2 ==>
      ?b. evaluate (MAP delete_var xs,env2,s) = (Rval b,r) /\
          env_rel (:'c) (:'ffi) (extract_list xs ++ ax) (a ++ env) (b ++ env2)`,
  Induct \\ fs [env_rel_def,extract_list_def]
  \\ once_rewrite_tac [evaluate_CONS]
  \\ rw [] \\ Cases_on `evaluate ([h],env2,s)` \\ fs []
  THEN1 (imp_res_tac evaluate_IMP_LENGTH \\ Cases_on `a` \\ fs [])
  \\ Cases_on `q` \\ fs []
  \\ Cases_on `?i. h = Var i` \\ fs []
  THEN1
   (rw [] \\ fs [delete_var_def,evaluate_def,do_app_def]
    \\ every_case_tac \\ fs [] \\ rw []
    \\ res_tac \\ fs [extract_def,env_rel_def] \\ rw []
    \\ fs [v_rel_def,LLOOKUP_EQ_EL]
    \\ imp_res_tac evaluate_IMP_LENGTH \\ fs []
    \\ fs [GSYM ADD1,ADD_CLAUSES,EL_APPEND2])
  \\ `delete_var h = h` by (Cases_on `h` \\ fs [delete_var_def]) \\ fs []
  \\ Cases_on `evaluate (xs,env2,r')` \\ fs [] \\ Cases_on `q` \\ fs []
  \\ res_tac \\ fs [] \\ rw []
  \\ Cases_on `extract h xs` \\ fs [env_rel_def]
  \\ imp_res_tac evaluate_SING \\ rw [] \\ fs []
  \\ Cases_on `h` \\ fs [extract_def]
  \\ rename1 `bvl_const$extract (Op opp ll) _ = SOME xx`
  \\ Cases_on `opp` \\ fs [extract_def] \\ rw []
  \\ every_case_tac \\ fs []
  \\ fs [v_rel_def,NULL_EQ,evaluate_def,do_app_def]
  \\ every_case_tac \\ fs []);

Theorem evaluate_EQ_NIL:
   bvlSem$evaluate (xs,env,s) = (Rval [],t) <=> xs = [] /\ s = t
Proof
  mp_tac (Q.SPECL [`xs`,`env`,`s`] evaluate_LENGTH)
  \\ every_case_tac \\ fs []
  \\ rw [] \\ TRY eq_tac \\ fs [] \\ rw [] \\ fs [LENGTH_NIL]
  \\ CCONTR_TAC \\ fs [] \\ fs [evaluate_def]
QED

val dest_simple_eq = prove(
  ``dest_simple h = SOME y <=> (h = Op (Const y) [])``,
  Cases_on `h` \\ fs [dest_simple_def]
  \\ Cases_on `o'` \\ fs [dest_simple_def,NULL_EQ]
  \\ eq_tac \\ rw [] \\ rw []);

val case_op_const_eq = prove(
  ``case_op_const exp = SOME x <=>
  (?op x1 n2. x = (op, x1, n2) /\ (exp = Op op [x1; Op (Const n2) []]))``,
  Cases_on `exp` \\ fs [case_op_const_def, NULL_EQ] \\
  every_case_tac \\
  eq_tac \\ rw []
)

val SmartOp_flip_thm = prove(
    ``(op', x1', x2') = SmartOp_flip op x1 x2 /\
    evaluate ([Op op [x1; x2]], env, s) = (res, s2) /\
    res ≠ Rerr (Rabort Rtype_error) ==>
    evaluate ([Op op' [x1'; x2']], env, s) = (res, s2)``,

    rpt strip_tac \\
    Cases_on `MEM op [Add; Sub; Mult]` THEN1 (
      Cases_on `op` \\ fs [] \\
      Cases_on `dest_simple x1` \\
      fs [SmartOp_flip_def, dest_simple_eq] \\
      fs [dest_simple_eq] \\
      fs [evaluate_def, do_app_def] \\
      fs [case_eq_thms] \\
      rveq \\ fs [] \\ rveq \\ fs [REVERSE] \\ rveq \\ fs [] \\
      intLib.COOPER_TAC
    ) \\
    Cases_on `op` \\
    Cases_on `dest_simple x1` \\
    fs [SmartOp_flip_def]
)

val SmartOp2_thm = prove(
  ``evaluate ([Op op [x1;x2]],env,s) = (res,s2) /\
    res ≠ Rerr (Rabort Rtype_error) ==>
    evaluate ([SmartOp2 (op,x1,x2)],env,s) = (res,s2)``,

  simp [SmartOp2_def] \\
  reverse (Cases_on `op = Equal`)
  THEN1 (
    Cases_on `dest_simple x1` \\ fs [] \\
    Cases_on `dest_simple x2` \\ fs [] \\
    Cases_on `case_op_const x1` \\ fs [] \\
    Cases_on `case_op_const x2` \\ fs [] \\
    fs [dest_simple_eq, case_op_const_eq] \\
    rveq \\
    rw [case_eq_thms] \\
    qpat_x_assum `evaluate _ = _` mp_tac \\

    simp [evaluate_def, do_app_def] \\
    fsrw_tac [DNF_ss] [case_eq_thms] \\
    rw [REVERSE] \\
    imp_res_tac evaluate_SING  \\
    fs [] \\
    intLib.COOPER_TAC
  )

  \\ fs []
  \\ every_case_tac \\ fs []
  \\ fs [dest_simple_eq] \\ rveq
  \\ fs [evaluate_def,do_app_def] \\ rw []
  \\ qpat_x_assum `_ = (res,_)` mp_tac
  \\ CASE_TAC \\ fs []
  \\ Cases_on `q`
  \\ imp_res_tac evaluate_SING \\ fs [do_eq_def]
  \\ TRY (Cases_on `d1`) \\ fs [do_eq_def]
  \\ rw [] \\ fs []
  \\ eq_tac \\ fs []);


Theorem SmartOp_thm:
   evaluate ([Op op xs],env,s) = (res,s2) /\
    res ≠ Rerr (Rabort Rtype_error) ==>
    evaluate ([SmartOp op xs],env,s) = (res,s2)
Proof
  simp [SmartOp_def] \\
  every_case_tac \\
  rename1 `Op op [x1; x2]` \\
  Cases_on `SmartOp_flip op x1 x2` \\
  Cases_on `r` \\
  rename1 `SmartOp_flip op x1 x2 = (op', x1', x2')` \\
  metis_tac [SmartOp_flip_thm, SmartOp2_thm]
QED

Theorem evaluate_env_rel:
   !xs env1 (s1:('c,'ffi) bvlSem$state) ax env2 res s2 ys.
      (evaluate (xs,env1,s1) = (res,s2)) /\
      env_rel (:'c) (:'ffi) ax env1 env2 /\
      res <> Rerr (Rabort Rtype_error) ==>
      (evaluate (compile ax xs,env2,s1) = (res,s2))
Proof
  recInduct evaluate_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [compile_def,evaluate_def,compile_HD_SING]
  THEN1
   (`?y0. compile ax [x] = [y0]` by
     (`LENGTH (compile ax [x]) = LENGTH [x]` by fs [compile_length]
      \\ Cases_on `compile ax [x]` \\ fs [LENGTH_NIL])
    \\ `?y1 ys. compile ax (y::xs) = y1::ys` by
     (`LENGTH (compile ax (y::xs)) = LENGTH (y::xs)` by fs [compile_length]
      \\ Cases_on `compile ax (y::xs)` \\ fs [LENGTH_NIL])
    \\ fs [] \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
    \\ rpt (first_x_assum drule) \\ fs []
    \\ rw [] \\ rpt (first_x_assum drule) \\ fs [] \\ rw []
    \\ fs [evaluate_def])
  THEN1
   (Cases_on `n < LENGTH env` \\ fs [] \\ rw []
    \\ Cases_on `LLOOKUP ax n` \\ fs []
    \\ imp_res_tac env_rel_length
    THEN1 (fs [evaluate_def] \\ metis_tac [env_rel_LLOOKUP_NONE])
    \\ CASE_TAC
    THEN1 (fs [evaluate_def] \\ metis_tac [env_rel_LLOOKUP_NONE])
    \\ CASE_TAC
    \\ drule env_rel_LOOKUP_SOME \\ fs [] \\ fs [v_rel_def]
    \\ disch_then drule \\ fs [] \\ rw []
    \\ fs [evaluate_def]
    \\ fs [LLOOKUP_EQ_EL]
    \\ fs [EL_DROP] \\ rfs [EL_DROP])
  THEN1
   (Cases_on `evaluate ([x1],env,s)` \\ fs []
    \\ Cases_on `q` \\ fs [] \\ rw [] \\ res_tac \\ fs []
    \\ every_case_tac \\ fs []
    \\ imp_res_tac evaluate_SING \\ fs [] \\ rveq \\ fs []
    \\ res_tac \\ fs []
    \\ fs [evaluate_def,compile_HD_SING]
    \\ imp_res_tac (prove(``x = y ==> [x] = [y]``,fs []))
    \\ full_simp_tac std_ss [compile_HD_SING]
    \\ fs [evaluate_def,EVAL ``Bool T``,EVAL ``Bool F``])
  THEN1
   (fs [LET_THM,evaluate_def]
    \\ Cases_on `evaluate (xs,env,s)` \\ fs []
    \\ Cases_on `q` \\ fs [] \\ rw []
    \\ res_tac \\ fs []
    \\ imp_res_tac evaluate_delete_var_Rerr \\ fs []
    \\ drule evaluate_delete_var_Rval \\ fs [compile_HD_SING]
    \\ disch_then drule \\ strip_tac \\ fs [])
  THEN1
   (Cases_on `evaluate ([x1],env,s)` \\ fs []
    \\ Cases_on `q` \\ fs [] \\ rw [] \\ res_tac \\ fs []
    \\ every_case_tac \\ fs [])
  THEN1
   (Cases_on `evaluate ([x1],env,s1)` \\ fs [] \\ Cases_on `q` \\ fs []
    \\ res_tac \\ rw [] \\ Cases_on `e` \\ fs [] \\ rw [] \\ fs []
    \\ first_x_assum match_mp_tac
    \\ fs [env_rel_def])
  \\ TRY (match_mp_tac SmartOp_thm)
  \\ fs [evaluate_def] \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
  \\ res_tac \\ fs [] \\ rw [] \\ fs [] \\ rw [] \\ fs []
QED

val compile_thm = save_thm("compile_thm",
  evaluate_env_rel
  |> Q.SPECL [`xs`,`env`,`s1`,`[]`,`env`] |> GEN_ALL
  |> SIMP_RULE std_ss [env_rel_def])

Theorem evaluate_compile_exp:
   evaluate ([d],env,s) = (r,t) /\
    r <> Rerr (Rabort Rtype_error) ==>
    evaluate ([bvl_const$compile_exp d],env,s) = (r,t)
Proof
  fs [compile_exp_def]
  \\ `LENGTH (compile [] [d]) = LENGTH [d]` by fs [compile_length]
  \\ Cases_on `compile [] [d]` \\ fs [LENGTH_NIL] \\ rw []
  \\ imp_res_tac compile_thm \\ rfs []
QED

Theorem delete_var_code_labels[simp]:
   ∀x. get_code_labels (bvl_const$delete_var x) = get_code_labels x
Proof
  recInduct bvl_constTheory.delete_var_ind
  \\ rw[bvl_constTheory.delete_var_def]
  \\ EVAL_TAC
QED

Theorem dest_simple_SOME_code_labels:
   ∀x y. dest_simple x = SOME y ⇒ get_code_labels x = {}
Proof
  recInduct bvl_constTheory.dest_simple_ind
  \\ rw[NULL_EQ] \\ EVAL_TAC
QED

Theorem SmartOp2_code_labels[simp]:
   get_code_labels (SmartOp2 (op,x1,x2)) =
    closLang$assign_get_code_label op ∪ get_code_labels x1 ∪ get_code_labels x2
Proof
  rw[bvl_constTheory.SmartOp2_def, closLangTheory.assign_get_code_label_def]
  \\ rpt(PURE_CASE_TAC \\ simp[closLangTheory.assign_get_code_label_def])
  \\ imp_res_tac dest_simple_SOME_code_labels \\ fs[]
  \\ fs[bvl_constTheory.case_op_const_def, CaseEq"option", CaseEq"closLang$op", CaseEq"bvl$exp", CaseEq"list", NULL_EQ]
  \\ rveq \\ fs[closLangTheory.assign_get_code_label_def,bvlTheory.Bool_def]
  \\ simp[EXTENSION] \\ metis_tac[]
QED

Theorem SmartOp_code_labels[simp]:
   get_code_labels (SmartOp op xs) = closLang$assign_get_code_label op ∪ BIGUNION (set (MAP get_code_labels xs))
Proof
  rw[bvl_constTheory.SmartOp_def]
  \\ PURE_CASE_TAC \\ simp[]
  \\ PURE_CASE_TAC \\ simp[]
  \\ PURE_CASE_TAC \\ simp[]
  \\ simp[bvl_constTheory.SmartOp_flip_def]
  \\ PURE_TOP_CASE_TAC \\ fs[]
  >- ( rw[EXTENSION] \\ metis_tac[] )
  \\ imp_res_tac dest_simple_SOME_code_labels
  \\ rw[closLangTheory.assign_get_code_label_def]
QED

Theorem MEM_extract_list_code_labels:
   ∀xs x. MEM (SOME x) (extract_list xs) ⇒ get_code_labels x = {}
Proof
  Induct
  \\ rw[bvl_constTheory.extract_list_def]
  \\ res_tac \\ fs[]
  \\ Cases_on`h` \\ fs[bvl_constTheory.extract_def]
  \\ rename1`Op op l`
  \\ Cases_on`op` \\ fs[bvl_constTheory.extract_def] \\ rw[]
  \\ EVAL_TAC
QED

Theorem compile_code_labels:
   ∀x y. BIGUNION (set (MAP get_code_labels (bvl_const$compile x y))) ⊆
         BIGUNION (set (MAP get_code_labels y)) ∪
         BIGUNION (set (MAP (get_code_labels o THE) (FILTER IS_SOME x)))
Proof
  recInduct bvl_constTheory.compile_ind
  \\ rw[bvl_constTheory.compile_def]
  \\ fsrw_tac[DNF_ss][SUBSET_DEF]
  \\ fs[Once(GSYM bvl_constTheory.compile_HD_SING)]
  \\ fsrw_tac[ETA_ss][MAP_MAP_o, o_DEF]
  \\ TRY(metis_tac[])
  >- (
    PURE_CASE_TAC \\ fs[]
    \\ PURE_CASE_TAC \\ fs[]
    \\ rw[]
    \\ asm_exists_tac \\ fs[]
    \\ fs[LLOOKUP_THM]
    \\ fs[MEM_MAP, MEM_FILTER, IS_SOME_EXISTS, PULL_EXISTS]
    \\ simp[MEM_EL, PULL_EXISTS]
    \\ goal_assum(first_assum o mp_then Any mp_tac) \\ simp[]
    \\ PURE_FULL_CASE_TAC \\ fs[] )
  >- (
    rw[]
    \\ last_x_assum drule
    \\ rw[] >- metis_tac[]
    \\ reverse(fs[MEM_MAP, PULL_EXISTS, MEM_FILTER, IS_SOME_EXISTS])
    >- metis_tac[]
    \\ imp_res_tac MEM_extract_list_code_labels
    \\ fs[])
QED

Theorem compile_exp_code_labels:
   ∀e. get_code_labels (bvl_const$compile_exp e) ⊆ get_code_labels e
Proof
  rw[bvl_constTheory.compile_exp_def]
  \\ rw[Once(GSYM bvl_constTheory.compile_HD_SING)]
  \\ specl_args_of_then``bvl_const$compile``compile_code_labels mp_tac
  \\ rw[] \\ fs[Once(GSYM bvl_constTheory.compile_HD_SING)]
QED

val _ = export_theory();
