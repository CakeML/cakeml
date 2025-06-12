(*
  Correctness proof for bvi_let
*)
open preamble bvi_letTheory bviSemTheory bviPropsTheory;

val _ = new_theory"bvi_letProof";

val _ = bring_to_front_overload "compile" {Name = "compile", Thy = "bvi_let"}

Definition v_rel_def:
  v_rel a x y xs ys <=> LLOOKUP ys a = SOME x
End

Definition env_rel_def:
  (env_rel [] d e1 e2 = (e1 = DROP d e2)) /\
  (env_rel (a::rest) d (x::e1) (y::e2) <=>
     v_rel a x y (x::e1) (y::e2) /\ env_rel rest d e1 e2) /\
  (env_rel _ _ _ _ = F)
End

Theorem env_rel_length:
   !ax env env2. env_rel ax d env env2 ==> LENGTH env <= LENGTH env2
Proof
  Induct \\ Cases_on `env` \\ Cases_on `env2` \\ fs [env_rel_def]
  \\ rw [] \\ Cases_on `d` \\ fs []
  \\ imp_res_tac (METIS_PROVE [] ``x=y ==> LENGTH x = LENGTH y``) \\ fs []
QED

Triviality env_rel_LLOOKUP_NONE:
  !ax env env2 n d.
      env_rel ax d env env2 /\
      LLOOKUP ax n = NONE /\
      n < LENGTH env ==>
      n+d < LENGTH env2 /\
      EL (n+d) env2 = EL n env
Proof
  Induct THEN1 (fs [env_rel_def,LLOOKUP_def,EL_DROP])
  \\ Cases_on `env` \\ Cases_on `env2` \\ fs [env_rel_def]
  \\ rw [] \\ Cases_on `n` \\ fs []
  \\ res_tac \\ fs [LLOOKUP_def] \\ rfs [] \\ fs[ADD_CLAUSES]
QED

Triviality env_rel_LOOKUP_SOME:
  !env env2 ax x n d.
      env_rel ax d env env2 /\
      LLOOKUP ax n = SOME x ==>
      v_rel x (EL n env) (EL n env2) (DROP n env) (DROP n env2)
Proof
  Induct \\ Cases_on `env2` \\ Cases_on `ax` \\ fs [env_rel_def,LLOOKUP_def]
  \\ rw [] \\ fs [env_rel_def] \\ res_tac \\ fs []
  \\ Cases_on `n` \\ fs [env_rel_def]
  \\ first_x_assum match_mp_tac
  \\ Cases_on `h'` \\ fs [env_rel_def]
QED

Theorem evaluate_delete_var_Rerr_SING:
   !x s r e env2.
      evaluate ([x],env2,s) = (Rerr e,r) /\
      e <> Rabort Rtype_error ==>
      evaluate ([delete_var x],env2,s) = (Rerr e,r)
Proof
  Cases \\ fs [delete_var_def]
  \\ fs [evaluate_def,do_app_def] \\ rw []
  \\ CCONTR_TAC \\ fs [] \\ rw []
QED

Triviality evaluate_delete_var_Rerr:
  !xs s r e env2.
      evaluate (xs,env2,s) = (Rerr e,r) /\
      e <> Rabort Rtype_error ==>
      evaluate (MAP delete_var xs,env2,s) = (Rerr e,r)
Proof
  Induct \\ fs [] \\ once_rewrite_tac [evaluate_CONS]
  \\ rw [] \\ every_case_tac \\ fs [] \\ rw []
  \\ TRY (drule evaluate_delete_var_Rerr_SING \\ fs [])
  \\ res_tac \\ fs []
  \\ Cases_on `h` \\ fs [delete_var_def]
  \\ rw [] \\ fs [] \\ fs [evaluate_def,do_app_def,do_app_aux_def] \\ rw []
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs [] \\ rw []
  \\ pop_assum mp_tac \\ EVAL_TAC
QED

Triviality evaluate_delete_var_Rval:
  !xs env2 s a r ax env d.
      evaluate (xs,env2,s:('c,'ffi) bviSem$state) = (Rval a,r) /\
      env_rel ax d env env2 ==>
      ?b. evaluate (MAP delete_var xs,env2,s) = (Rval b,r) /\
          env_rel (extract_list xs ++ ax) d (a ++ env) (b ++ env2)
Proof
  Induct \\ fs [env_rel_def,extract_list_def]
  \\ once_rewrite_tac [evaluate_CONS]
  \\ rw [] \\ Cases_on `evaluate ([h],env2,s)` \\ fs []
  THEN1 (imp_res_tac evaluate_IMP_LENGTH \\ Cases_on `a` \\ fs [])
  \\ Cases_on `q` \\ fs []
  \\ Cases_on `?i. h = Var i` \\ fs []
  THEN1
   (rw [] \\ fs [delete_var_def,evaluate_def,do_app_def,
                 do_app_aux_def,EVAL ``small_enough_int 0``]
    \\ every_case_tac \\ fs [] \\ rw []
    \\ res_tac \\ fs [extract_def,env_rel_def] \\ rw []
    \\ fs [v_rel_def,LLOOKUP_EQ_EL]
    \\ imp_res_tac evaluate_IMP_LENGTH \\ fs []
    \\ fs [GSYM ADD1,ADD_CLAUSES,EL_APPEND2])
  \\ `delete_var h = h` by (Cases_on `h` \\ fs [delete_var_def]) \\ fs []
  \\ Cases_on `evaluate (xs,env2,r')` \\ fs [] \\ Cases_on `q` \\ fs []
  \\ res_tac \\ fs [] \\ rw []
  \\ `extract h xs = 0` by (Cases_on `h` \\ fs [extract_def]) \\ fs []
  \\ imp_res_tac evaluate_SING_IMP \\ rw [] \\ fs []
  \\ fs [v_rel_def,env_rel_def,LLOOKUP_def]
QED

Theorem evaluate_SNOC_Rval:
   evaluate (SNOC x y,env,s) = (Rval a,r) ==>
    ?a1 a2 r1.
      a = SNOC a1 a2 /\ LENGTH y = LENGTH a2 /\
      evaluate (y,env,s) = (Rval a2,r1) /\
      evaluate ([x],env,r1) = (Rval [a1],r)
Proof
  fs [evaluate_SNOC]
  \\ every_case_tac \\ fs []
  \\ imp_res_tac evaluate_SING_IMP \\ rw []
  \\ imp_res_tac evaluate_IMP_LENGTH \\ fs []
QED

Theorem compile_CONS:
   compile ax d (x::xs) = compile ax d [x] ++ compile ax d xs
Proof
  Cases_on `xs` \\ fs [compile_def]
QED

Theorem compile_APPEND:
   !xs ys ax d. compile ax d (xs ++ ys) = compile ax d xs ++ compile ax d ys
Proof
  Induct \\ fs [compile_def]
  \\ once_rewrite_tac [compile_CONS] \\ fs []
QED

Theorem IMP_COMM:
   (b1 ==> b2 ==> b3) <=> (b2 ==> b1 ==> b3)
Proof
  metis_tac []
QED

Theorem exp_size_APPEND:
   !xs ys. exp2_size (xs ++ ys) = exp2_size xs + exp2_size ys
Proof
  Induct \\ fs [bviTheory.exp_size_def]
QED

Theorem env_rel_MAP:
   !ax env1 env2 d a.
      env_rel ax d env1 env2 ==>
      env_rel (MAP ($+ (LENGTH a)) ax) (d + LENGTH a) env1 (a ++ env2)
Proof
  Induct \\ fs [env_rel_def]
  THEN1 (once_rewrite_tac [EQ_SYM_EQ] \\ Induct_on `a` \\ fs [ADD1])
  \\ Cases_on `env1` \\ Cases_on `env2` \\ fs [env_rel_def]
  \\ fs [v_rel_def] \\ rw [env_rel_def] \\ Cases_on `a`
  \\ fs [env_rel_def,v_rel_def,MAP_ID,prove(``(+)0n=I``,fs [FUN_EQ_THM])]
  \\ `t'' ++ h'::t' = (t'' ++ [h']) ++ t'` by fs []
  \\ full_simp_tac std_ss []
  \\ reverse conj_tac THEN1
   (`SUC (LENGTH t'') = LENGTH (t'' ++ [h'])` by fs []
    \\ pop_assum (fn th => rewrite_tac [th])
    \\ first_x_assum match_mp_tac \\ fs [])
  \\ fs [LLOOKUP_EQ_EL,ADD_CLAUSES]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ fs [EL_APPEND2]
QED

Theorem evaluate_env_rel:
   !xs env1 (s1:('c,'ffi) bviSem$state) ax env2 res s2 ys d.
      (evaluate (xs,env1,s1) = (res,s2)) /\
      env_rel ax d env1 env2 /\
      res <> Rerr (Rabort Rtype_error) ==>
      (evaluate (compile ax d xs,env2,s1) = (res,s2))
Proof
  strip_tac \\ completeInduct_on `list_size exp_size xs`
  \\ rw [] \\ fs [PULL_FORALL]
  \\ Cases_on `xs` \\ fs[compile_def,evaluate_def]
  \\ reverse (Cases_on `t`) \\ fs [] THEN1
   (fs [compile_def,evaluate_def]
    \\ qpat_x_assum `!x._` mp_tac
    \\ once_rewrite_tac [IMP_COMM] \\ rw [AND_IMP_INTRO]
    \\ gvs [CaseEq"prod"]
    \\ once_rewrite_tac [GSYM compile_HD_SING] \\ fs []
    \\ once_rewrite_tac [evaluate_CONS] \\ fs [compile_HD_SING]
    \\ first_assum $ drule_then drule
    \\ impl_tac >- (CCONTR_TAC \\ gvs [])
    \\ rpt strip_tac \\ gvs []
    \\ gvs [CaseEq"result"]
    \\ imp_res_tac evaluate_SING_IMP \\ gvs []
    \\ gvs [CaseEq"prod"]
    \\ pop_assum kall_tac
    \\ pop_assum $ drule_then drule
    \\ impl_tac >- (CCONTR_TAC \\ gvs [])
    \\ gvs [])
  \\ fs [bviTheory.exp_size_def]
  \\ qpat_x_assum `!x._` mp_tac
  \\ once_rewrite_tac [IMP_COMM]
  \\ fs [GSYM CONJ_ASSOC]
  \\ Cases_on `?v. h = Var v` \\ rw [] \\ fs []
  THEN1
   (fs [evaluate_def] \\ every_case_tac \\ fs [] \\ rveq \\ fs []
    \\ fs [compile_def,evaluate_def]
    \\ Cases_on `LLOOKUP ax v` \\ fs []
    \\ imp_res_tac env_rel_length
    THEN1 (fs [evaluate_def] \\ metis_tac [env_rel_LLOOKUP_NONE,ADD_COMM])
    \\ drule env_rel_LOOKUP_SOME \\ fs [] \\ fs [v_rel_def]
    \\ disch_then drule \\ fs [] \\ rw []
    \\ fs [evaluate_def] \\ fs [LLOOKUP_EQ_EL]
    \\ fs [EL_DROP] \\ rfs [EL_DROP])
  \\ Cases_on `?x1. h = Raise x1 \/ h = Tick x1`
  THEN1
   (rw [] \\ fs [evaluate_def] \\ every_case_tac \\ fs [] \\ rveq \\ fs []
    \\ fs [compile_def,evaluate_def,compile_HD_SING]
    \\ first_x_assum drule \\ fs [] \\ disch_then drule
    \\ rpt (impl_tac THEN1 fs [bviTheory.exp_size_def] \\ strip_tac \\ fs [])
    \\ fs [compile_def,evaluate_def,compile_HD_SING])
  \\ Cases_on `?x1 x2 x3. h = If x1 x2 x3` \\ rw [] \\ fs []
  THEN1
   (fs [evaluate_def] \\ every_case_tac \\ fs []
    \\ imp_res_tac evaluate_SING_IMP \\ fs [] \\ rveq \\ fs []
    \\ first_assum drule \\ qpat_x_assum `_ = _` mp_tac
    \\ TRY (first_x_assum drule \\ fs [] \\ rw [])
    \\ TRY (qpat_x_assum `!x._` drule)
    \\ TRY (qpat_x_assum `!x._` drule)
    \\ rpt (impl_tac THEN1 fs [bviTheory.exp_size_def] \\ strip_tac \\ fs [])
    \\ fs [compile_def,evaluate_def,compile_HD_SING]
    \\ rw [] \\ pop_assum drule
    \\ rpt (impl_tac THEN1 fs [bviTheory.exp_size_def] \\ strip_tac \\ fs []))
  \\ Cases_on `?ts dest args handler. h = Call ts dest args handler`
  \\ fs [] \\ rveq THEN1
   (Cases_on `handler` \\ fs []
    \\ qpat_x_assum `!_ _ _ _ _. bb` mp_tac
    \\ once_rewrite_tac [IMP_COMM] \\ strip_tac THEN1
     (gvs [compile_def]
      \\ first_x_assum $ qspec_then ‘args’ mp_tac \\ gvs []
      \\ gvs [evaluate_def,CaseEq"prod"]
      \\ disch_then $ drule_then drule
      \\ impl_tac >- (CCONTR_TAC \\ gvs []) \\ gvs [])
    \\ gvs [compile_def]
    \\ first_assum $ qspec_then ‘args’ mp_tac \\ gvs []
    \\ fs [evaluate_def,CaseEq"prod",CaseEq"bool"]
    \\ disch_then $ drule_then drule
    \\ impl_tac >- (CCONTR_TAC \\ gvs []) \\ gvs []
    \\ gvs [CaseEq"result",CaseEq"option",CaseEq"prod",CaseEq"bool"]
    \\ gvs [CaseEq"error_result"] \\ rw [compile_HD_SING]
    \\ first_x_assum $ irule \\ gvs []
    \\ first_x_assum $ irule_at Any
    \\ fs [env_rel_def] \\ fs [v_rel_def,LLOOKUP_def])
  \\ Cases_on `?xs op. h = Op op xs` \\ fs [] THEN1
   (rw [] \\ qpat_x_assum `!_ _ _ _ _. bb` mp_tac
    \\ once_rewrite_tac [IMP_COMM] \\ strip_tac
    \\ gvs [compile_def,evaluate_def]
    \\ gvs [evaluate_def,CaseEq"prod"]
    \\ pop_assum $ drule_at $ Pos $ el 2 \\ gvs []
    \\ disch_then drule
    \\ impl_tac >- (CCONTR_TAC \\ gvs []) \\ gvs [])
  \\ reverse (Cases_on `?ys y. h = Let ys y` \\ fs [])
  THEN1 (Cases_on `h` \\ fs [])
  \\ fs [] \\ rpt (qpat_x_assum `T` kall_tac) \\ rveq \\ fs [evaluate_def]
  \\ pop_assum mp_tac \\ once_rewrite_tac [IMP_COMM] \\ strip_tac
  \\ gvs [CaseEq"prod"]
  \\ gvs [compile_def]
  \\ IF_CASES_TAC \\ gvs [evaluate_def]
  >- (pop_assum $ drule_at $ Pos $ el 2 \\ gvs [])
  \\ IF_CASES_TAC \\ gvs [evaluate_def]
  THEN1
   (imp_res_tac (METIS_PROVE [SNOC_CASES] ``m <> [] ==> ?x y. m = SNOC x y``)
    \\ rveq \\ full_simp_tac std_ss [FRONT_SNOC,LAST_SNOC,LENGTH_SNOC,ADD1]
    \\ fs [evaluate_SNOC,evaluate_def,bviTheory.exp_size_def]
    \\ fs [SNOC_APPEND,exp_size_APPEND,bviTheory.exp_size_def]
    \\ Cases_on `evaluate (y,env1,s1)` \\ fs []
    \\ first_assum $ drule_at $ Pos $ el 2 \\ gvs []
    \\ disch_then drule
    \\ impl_tac >- (CCONTR_TAC \\ gvs []) \\ gvs [compile_HD_SING]
    \\ Cases_on ‘q’ \\ gvs []
    \\ rpt strip_tac
    \\ gvs [CaseEq"prod"]
    \\ first_x_assum $ irule \\ gvs []
    \\ Cases_on ‘v3’ \\ gvs [CaseEq"bool"]
    \\ qexists_tac ‘env1’ \\ gvs []
    \\ imp_res_tac evaluate_IMP_LENGTH \\ fs []
    \\ imp_res_tac evaluate_SING_IMP \\ fs [] \\ rveq
    \\ full_simp_tac std_ss [APPEND,GSYM APPEND_ASSOC,EL_APPEND2,EL,HD]
    \\ fs [env_rel_def] \\ match_mp_tac env_rel_MAP \\ fs [])
  \\ fs [evaluate_def,compile_HD_SING]
  \\ first_assum $ qspec_then ‘ys’ mp_tac
  \\ gvs [] \\ disch_then $ drule_then drule
  \\ impl_tac >- (CCONTR_TAC \\ gvs []) \\ gvs []
  \\ Cases_on `evaluate (ys,env1,s1)` \\ fs []
  \\ reverse (Cases_on `q`) \\ fs [] \\ rveq \\ gvs []
  \\ rpt (disch_then drule) \\ strip_tac
  THEN1 (drule evaluate_delete_var_Rerr \\ fs [])
  \\ fs [] \\ drule evaluate_delete_var_Rval
  \\ rpt (disch_then drule) \\ strip_tac \\ fs [] \\ fs [AND_IMP_INTRO]
  \\ first_x_assum match_mp_tac \\ fs [bviTheory.exp_size_def]
  \\ asm_exists_tac \\ fs []
QED

Theorem compile_thm =
  evaluate_env_rel
  |> Q.SPECL [`xs`,`env`,`s1`,`[]`,`env`,`res`,`s2`,`ys`,`0`] |> GEN_ALL
  |> SIMP_RULE (srw_ss()) [env_rel_def]

Theorem evaluate_compile_exp:
   evaluate ([d],env,s) = (r,t) /\
    r <> Rerr (Rabort Rtype_error) ==>
    evaluate ([bvi_let$compile_exp d],env,s) = (r,t)
Proof
  fs [compile_exp_def]
  \\ `LENGTH (compile [] 0 [d]) = LENGTH [d]` by fs [compile_length]
  \\ Cases_on `compile [] 0 [d]` \\ fs [LENGTH_NIL] \\ rw []
  \\ imp_res_tac compile_thm \\ rfs []
QED

Theorem dest_var_code_labels[simp]:
   ∀x. get_code_labels (delete_var x) = get_code_labels x
Proof
  recInduct bvi_letTheory.delete_var_ind
  \\ rw[bvi_letTheory.delete_var_def]
  \\ EVAL_TAC
QED

Theorem compile_code_labels:
   ∀x y z. BIGUNION (set (MAP get_code_labels (bvi_let$compile x y z))) =
           BIGUNION (set (MAP get_code_labels z))
Proof
  recInduct bvi_letTheory.compile_ind
  \\ rw[bvi_letTheory.compile_def]
  \\ TRY PURE_CASE_TAC \\ fs[]
  \\ TRY PURE_CASE_TAC \\ fs[]
  \\ fs[Once(GSYM bvi_letTheory.compile_HD_SING)]
  \\ fsrw_tac[ETA_ss][MAP_MAP_o, o_DEF]
  \\ drule APPEND_FRONT_LAST
  \\ disch_then(fn th => CONV_TAC(RAND_CONV(ONCE_REWRITE_CONV[GSYM th])))
  \\ simp[]
QED

Theorem compile_exp_code_labels[simp]:
   ∀x. get_code_labels (bvi_let$compile_exp x) = get_code_labels x
Proof
  rw[bvi_letTheory.compile_exp_def]
  \\ simp[Once(GSYM bvi_letTheory.compile_HD_SING)]
  \\ specl_args_of_then``bvi_let$compile``compile_code_labels mp_tac
  \\ simp[]
  \\ simp[Once(GSYM bvi_letTheory.compile_HD_SING)]
QED

val _ = export_theory();
