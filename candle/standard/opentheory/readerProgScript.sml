open preamble basis
     ml_monadBaseTheory ml_monad_translatorLib cfMonadTheory cfMonadLib
     holKernelTheory holKernelProofTheory ml_hol_kernelProgTheory readerTheory
     readerProofTheory

val _ = new_theory "readerProg"
val _ = m_translation_extends "ml_hol_kernelProg"

(* TODO: move *)
val fastForwardFD_A_DELKEY_same = Q.store_thm("fastForwardFD_A_DELKEY_same[simp]",
  `forwardFD fs fd n with infds updated_by A_DELKEY fd =
   fs with infds updated_by A_DELKEY fd`,
  fs [forwardFD_def, IO_fs_component_equality]);

val exc_case_eq = prove_case_eq_thm{case_def=exc_case_def,nchotomy=exc_nchotomy};
val term_case_eq = prove_case_eq_thm{case_def=holSyntaxTheory.term_case_def,nchotomy=holSyntaxTheory.term_nchotomy};
val option_case_eq = prove_case_eq_thm{case_def=optionTheory.option_case_def,nchotomy=optionTheory.option_nchotomy};
val object_case_eq = prove_case_eq_thm{case_def=readerTheory.object_case_def,nchotomy=readerTheory.object_nchotomy};
val exn_case_eq = prove_case_eq_thm{case_def=holKernelTheory.hol_exn_case_def,nchotomy=holKernelTheory.hol_exn_nchotomy};
val list_case_eq = prove_case_eq_thm{case_def=listTheory.list_case_def,nchotomy=listTheory.list_nchotomy};
val case_eq_thms =
  LIST_CONJ
    [exc_case_eq, term_case_eq, option_case_eq,
     object_case_eq, list_case_eq, pair_case_eq,
     exn_case_eq]

(* TODO: Move these to holKernelProofTheory *)

val dest_type_not_clash = Q.store_thm("dest_type_not_clash[simp]",
  `dest_type x y ≠ (Failure (Clash tm),refs)`,
  Cases_on`x` \\ EVAL_TAC);

val mk_fun_ty_not_clash = Q.store_thm("mk_fun_ty_not_clash[simp]",
  `mk_fun_ty t a r ≠ (Failure(Clash tm),refs)`,
  Cases_on`t` \\ EVAL_TAC
  \\ rw[pair_case_eq,exc_case_eq,raise_Fail_def,st_ex_return_def]
  \\ CCONTR_TAC \\ fs[bool_case_eq,COND_RATOR] \\ rw[]);

val type_of_not_clash = Q.store_thm("type_of_not_clash[simp]",
  `∀x y. type_of x y ≠ (Failure (Clash tm),refs)`,
  recInduct type_of_ind
  \\ rw[]
  \\ rw[Once type_of_def,st_ex_bind_def,raise_Fail_def,pair_case_eq,exc_case_eq]
  \\ CASE_TAC \\ fs[st_ex_return_def,pair_case_eq,exc_case_eq]
  \\ CCONTR_TAC \\ fs[pair_case_eq] \\ rw[] \\ fs[] \\ rfs[]
  \\ every_case_tac \\ fs[] \\ rfs[]);

val mk_abs_not_clash = Q.store_thm("mk_abs_not_clash[simp]",
  `mk_abs x y ≠ (Failure (Clash tm),refs)`,
  Cases_on`x` \\ EVAL_TAC \\ CASE_TAC \\ fs[]);

val mk_comb_not_clash = Q.store_thm("mk_comb_not_clash[simp]",
  `mk_comb x y ≠ (Failure (Clash tm),refs)`,
  Cases_on`x` \\ rw[mk_comb_def,st_ex_bind_def,pair_case_eq,exc_case_eq]
  \\ CCONTR_TAC \\ fs[] \\ rw[] \\ fs[]
  \\ every_case_tac \\ fs[raise_Fail_def,st_ex_return_def]);

val mk_eq_not_clash = Q.store_thm("mk_eq_not_clash[simp]",
  `mk_eq x y ≠ (Failure(Clash tm),refs)`,
  Cases_on`x` \\ rw[mk_eq_def,st_ex_bind_def,try_def,otherwise_def,pair_case_eq,exc_case_eq]
  \\ CCONTR_TAC \\ fs[st_ex_return_def,raise_Fail_def] \\ rw[]);

val ABS_not_clash = Q.store_thm("ABS_not_clash[simp]",
  `ABS x y z ≠ (Failure (Clash tm),refs)`,
  Cases_on`y` \\ EVAL_TAC
  \\ every_case_tac \\ fs[st_ex_bind_def,pair_case_eq,exc_case_eq]
  \\ rw[raise_Fail_def]
  \\ CCONTR_TAC
  \\ fs[st_ex_return_def] \\ rveq \\ fs[]);

val MK_COMB_not_clash = Q.store_thm("MK_COMB_not_clash[simp]",
  `MK_COMB (a,b) c <> (Failure (Clash tm), refs)`,
  Cases_on `a` \\ Cases_on `b` \\ EVAL_TAC
  \\ every_case_tac \\ fs [raise_Fail_def, st_ex_bind_def]
  \\ every_case_tac \\ fs [st_ex_return_def]
  \\ metis_tac [mk_eq_not_clash, mk_comb_not_clash]);

val mk_type_not_clash = Q.store_thm("mk_type_not_clash[simp]",
  `!a b. mk_type a b <> (Failure (Clash tm), refs)`,
  Cases \\ once_rewrite_tac [mk_type_def]
  \\ fs [st_ex_bind_def, st_ex_return_def, raise_Fail_def]
  \\ fs [try_def, otherwise_def, get_type_arity_def]
  \\ fs [st_ex_bind_def, raise_Fail_def] \\ rw []
  \\ every_case_tac \\ fs []);

val ASSUME_not_clash = Q.store_thm("ASSUME_not_clash[simp]",
  `!a b. ASSUME a b <> (Failure (Clash tm), refs)`,
  Cases \\ rw [ASSUME_def]
  \\ fs [st_ex_bind_def, st_ex_return_def, raise_Fail_def]
  \\ every_case_tac \\ fs []
  \\ metis_tac [type_of_not_clash, mk_type_not_clash, type_of_not_clash]);

val BETA_not_clash = Q.store_thm("BETA_not_clash[simp]",
  `BETA a b <> (Failure (Clash tm),refs)`,
  strip_tac \\ Cases_on `a`
  \\ fs [BETA_def, raise_Fail_def, st_ex_bind_def, st_ex_return_def]
  \\ every_case_tac \\ fs [] \\ rw []
  \\ rename1 `mk_eq (x, y)` \\ fs []);

val find_axiom_not_clash = Q.store_thm("find_axiom_not_clash[simp]",
  `find_axiom (a,b) c <> (Failure (Clash tm),refs)`,
  Cases_on `a` \\ fs [find_axiom_def, st_ex_bind_def, raise_Fail_def, st_ex_return_def]
  \\ every_case_tac  \\ fs [get_the_axioms_def]);

val mk_const_not_clash = Q.store_thm("mk_const_not_clash[simp]",
  `mk_const (a,b) c <> (Failure (Clash tm),refs)`,
  Cases_on`a` \\ once_rewrite_tac [mk_const_def]
  \\ fs [st_ex_bind_def, st_ex_return_def, raise_Fail_def, try_def, otherwise_def]
  \\ every_case_tac \\ fs []);

val assoc_not_clash = Q.store_thm("assoc_not_clash[simp]",
  `!a b c. assoc a b c <> (Failure (Clash tm),refs)`,
  recInduct assoc_ind \\ rw []
  \\ once_rewrite_tac [assoc_def]
  \\ every_case_tac \\ fs [raise_Fail_def,st_ex_return_def]);

val get_const_type_not_clash = Q.store_thm("get_const_type_not_clash[simp]",
  `get_const_type a b <> (Failure (Clash tm),refs)`,
  Cases_on`a` \\ EVAL_TAC
  \\ fs [raise_Fail_def, st_ex_bind_def, st_ex_return_def]
  \\ every_case_tac \\ fs []);

val DEDUCT_ANTISYM_RULE_not_clash = Q.store_thm("DEDUCT_ANTISYM_RULE_not_clash[simp]",
  `DEDUCT_ANTISYM_RULE a b c <> (Failure (Clash tm),refs)`,
  Cases_on `a` \\ Cases_on `b` \\ once_rewrite_tac [DEDUCT_ANTISYM_RULE_def]
  \\ rw [st_ex_bind_def, st_ex_return_def, raise_Fail_def]
  \\ every_case_tac \\ fs []
  \\ Cases_on `t` \\ fs [mk_eq_def]
  \\ fs [try_def, otherwise_def, st_ex_bind_def, st_ex_return_def, raise_Fail_def]
  \\ every_case_tac \\ fs [] \\ rw []);

val SYM_not_clash = Q.store_thm("SYM_not_clash[simp]",
  `SYM a b <> (Failure (Clash tm),refs)`,
  Cases_on `a` \\ EVAL_TAC \\ fs [raise_Fail_def, st_ex_return_def]
  \\ every_case_tac \\ fs []);

val dest_comb_not_clash = Q.store_thm("dest_comb_not_clash[simp]",
  `dest_comb a b <> (Failure (Clash tm),refs)`,
  Cases_on`a` \\ EVAL_TAC);

val dest_eq_not_clash = Q.store_thm("dest_eq_not_clash[simp]",
  `dest_eq a b <> (Failure (Clash tm),refs)`,
  Cases_on`a` \\ EVAL_TAC \\ fs [raise_Fail_def, st_ex_return_def]
  \\ every_case_tac \\ fs []);

val EQ_MP_not_clash = Q.store_thm("EQ_MP_not_clash[simp]",
  `EQ_MP a b c <> (Failure (Clash tm),refs)`,
  Cases_on`a` \\ Cases_on`b` \\ EVAL_TAC
  \\ fs [raise_Fail_def, st_ex_return_def]
  \\ every_case_tac \\ fs []);

val PROVE_HYP_not_clash = Q.store_thm("PROVE_HYP_not_clash[simp]",
  `PROVE_HYP a b c <> (Failure (Clash tm),refs)`,
  Cases_on `a` \\ Cases_on `b` \\ EVAL_TAC);

val REFL_not_clash = Q.store_thm("REFL_not_clash[simp]",
  `REFL a b <> (Failure (Clash tm),refs)`,
  fs [REFL_def, st_ex_bind_def, st_ex_return_def]
  \\ fs [pair_case_eq, exc_case_eq]);

val TRANS_not_clash = Q.store_thm("TRANS_not_clash[simp]",
  `TRANS a b c <> (Failure (Clash tm),refs)`,
  Cases_on`a` \\ Cases_on `b`
  \\ fs [TRANS_def, st_ex_bind_def, st_ex_return_def, raise_Fail_def]
  \\ rpt (fs [exc_case_eq, pair_case_eq] \\ PURE_TOP_CASE_TAC \\ fs []));

val map_not_clash_thm = Q.store_thm("map_not_clash_thm",
  `!f xs s.
   (!x s. f x s <> (Failure (Clash tm),refs)) ==>
   map f xs s <> (Failure (Clash tm),refs)`,
   strip_tac \\ Induct \\ rw [] \\ once_rewrite_tac [map_def]
   \\ fs [st_ex_bind_def, st_ex_return_def, raise_Fail_def]
   \\ every_case_tac \\ fs [] \\ metis_tac []);

val ALPHA_THM_not_clash = Q.store_thm("ALPHA_THM_not_clash[simp]",
  `!a b c d. ALPHA_THM a (b, c) d <> (Failure (Clash tm),refs)`,
  recInduct ALPHA_THM_ind
  \\ rw [ALPHA_THM_def, raise_Fail_def, st_ex_return_def, st_ex_bind_def]
  \\ every_case_tac \\ fs []
  \\ metis_tac [mk_type_not_clash, map_not_clash_thm, type_of_not_clash]);

val add_constants_not_clash = Q.store_thm("add_constants_not_clash[simp]",
  `add_constants a b <> (Failure (Clash tm),refs)`,
  Cases_on `a` \\ EVAL_TAC \\ every_case_tac \\ fs []);

val add_def_not_clash = Q.store_thm("add_def_not_clash[simp]",
  `add_def a b <> (Failure (Clash tm),refs)`,
  Cases_on `a` \\ EVAL_TAC);

val dest_var_not_clash = Q.store_thm("dest_var_not_clash[simp]",
  `dest_var a b <> (Failure (Clash tm),refs)`,
  Cases_on `a` \\ EVAL_TAC \\ every_case_tac \\ fs [raise_Fail_def, st_ex_return_def]);

val new_specification_not_clash = Q.store_thm("new_specification_not_clash[simp]",
  `new_specification a b <> (Failure (Clash tm),refs)`,
  Cases_on `a`
  \\ fs [new_specification_def, st_ex_bind_def, raise_Fail_def, st_ex_return_def]
  \\ fs [st_ex_return_def, pair_case_eq, exc_case_eq, UNCURRY, st_ex_bind_def]
  \\ fs [bool_case_eq, pair_case_eq, COND_RATOR, exc_case_eq] \\ rw []
  \\ fs [st_ex_return_def, st_ex_bind_def]
  \\ ho_match_mp_tac map_not_clash_thm \\ rw []
  \\ every_case_tac \\ fs []
  \\ CCONTR_TAC \\ fs [] \\ rw [] \\ fs []);

val new_basic_definition_not_clash = Q.store_thm("new_basic_definition_not_clash[simp]",
  `new_basic_definition a b <> (Failure (Clash tm),refs)`,
  fs [new_basic_definition_def, st_ex_bind_def]
  \\ every_case_tac \\ fs []
  \\ CCONTR_TAC \\ fs []);

val add_type_not_clash = Q.store_thm("add_type_not_clash[simp]",
  `add_type (a,b) c <> (Failure (Clash tm),refs)`,
  EVAL_TAC \\ rw [] \\ EVAL_TAC
  \\ every_case_tac \\ fs [raise_Fail_def, st_ex_bind_def, st_ex_return_def]
  \\ every_case_tac \\ fs [] \\ rw []
  \\ fs [set_the_type_constants_def, get_the_type_constants_def]);

val new_basic_type_definition_not_clash = Q.store_thm("new_basic_type_definition_not_clash[simp]",
  `new_basic_type_definition a b c d e <> (Failure (Clash tm),refs)`,
  Cases_on `d` \\ fs [new_basic_type_definition_def]
  \\ fs [st_ex_bind_def, st_ex_return_def, raise_Fail_def, can_def,
         get_type_arity_def, get_the_type_constants_def, otherwise_def]
  \\ every_case_tac \\ fs [] \\ rw []
  \\ rpt (pairarg_tac \\ fs []) \\ rw []
  \\ every_case_tac \\ fs [] \\ rw []
  \\ CCONTR_TAC \\ fs [] \\ rw [] \\ fs [try_def, otherwise_def]
  \\ every_case_tac \\ fs [raise_Fail_def]);

val forall_clash_thm = Q.store_thm("forall_clash_thm",
  `!f l s.
    (!x s. f x s <> (Failure (Clash tm),refs)) ==>
    forall f l s <> (Failure (Clash tm),refs)`,
  recInduct forall_ind \\ once_rewrite_tac [forall_def]
  \\ rw [st_ex_bind_def, st_ex_return_def]
  \\ Cases_on `l` \\ fs []
  \\ every_case_tac \\ fs []
  \\ once_rewrite_tac [forall_def] \\ fs [st_ex_return_def, st_ex_bind_def]
  \\ CCONTR_TAC \\ fs [] \\ rw [] \\ metis_tac []);

val vsubst_not_clash = Q.store_thm("vsubst_not_clash[simp]",
  `vsubst x y s <> (Failure (Clash tm),refs)`,
  fs [vsubst_def, st_ex_bind_def, st_ex_return_def, raise_Fail_def]
  \\ rpt (PURE_TOP_CASE_TAC \\ fs [])
  \\ CCONTR_TAC \\ fs [] \\ rw []
  \\ pop_assum mp_tac \\ fs []
  \\ ho_match_mp_tac forall_clash_thm \\ rw []
  \\ pairarg_tac \\ fs [] \\ rveq
  \\ fs [exc_case_eq, pair_case_eq]);

val image_clash_thm = Q.store_thm("image_clash_thm",
  `!f l s.
    (!x s. f x s <> (Failure (Clash tm),refs)) ==>
    image f l s <> (Failure (Clash tm),refs)`,
  recInduct image_ind \\ once_rewrite_tac [image_def]
  \\ rw [st_ex_bind_def, st_ex_return_def, raise_Fail_def]
  \\ rpt (PURE_TOP_CASE_TAC \\ fs [])
  \\ CCONTR_TAC \\ fs [] \\ rw []
  \\ pop_assum mp_tac \\ fs []
  \\ every_case_tac \\ fs []
  \\ once_rewrite_tac [image_def] \\ fs [st_ex_return_def, st_ex_bind_def]);

val INST_not_clash = Q.store_thm("INST_not_clash[simp]",
  `INST theta x s <> (Failure (Clash tm),refs)`,
  Cases_on `x` \\ fs [INST_def, st_ex_bind_def, st_ex_return_def, exc_case_eq, pair_case_eq]
  \\ ho_match_mp_tac image_clash_thm \\ rw []);


(* and something about the environment? *)
val inst_aux_clash_is_var = Q.store_thm("inst_aux_clash_is_var",
  `!env tyin tm s f t.
     inst_aux env tyin tm s = (Failure (Clash f),t)
     ==>
     ?a b. f = Var a b`,
  recInduct inst_aux_ind \\ rw []
  \\ pop_assum mp_tac
  \\ Cases_on `tm` \\ fs []
  \\ once_rewrite_tac [inst_aux_def] \\ fs []
  \\ simp [st_ex_return_def, st_ex_bind_def, raise_Fail_def]
  \\ simp [handle_Clash_def, raise_Clash_def, UNCURRY]
  \\ every_case_tac \\ fs [] \\ rw []
  \\ res_tac \\ fs []);

val variant_same_ty = Q.store_thm("variant_same_ty",
  `!x z c d.
     variant x z = Var c d
     ==>
     ?a b. z = Var a b /\ b = d`,
  recInduct holSyntaxExtraTheory.variant_ind \\ rw []
  \\ pop_assum mp_tac
  \\ simp [Once holSyntaxExtraTheory.variant_def]
  \\ every_case_tac \\ fs []);

val vsubst_same_Var = Q.store_thm("vsubst_same_Var[simp]",
  `vsubst_aux [(Var a b, Var c d)] (Var c d) = Var a b`,
  once_rewrite_tac [vsubst_aux_def] \\ fs []
  \\ once_rewrite_tac [rev_assocd_def] \\ fs []);

val inst_aux_thm = Q.store_thm("inst_aux_thm",
  `!env tyin tm s f t.
     env = []
     ==>
     inst_aux env tyin tm s <> (Failure (Clash f),t)`,

  recInduct inst_aux_ind \\ rw []
  \\ Cases_on `tm` \\ fs []
  \\ once_rewrite_tac [inst_aux_def] \\ fs []
  \\ fs [st_ex_bind_def, st_ex_return_def, raise_Fail_def, raise_Clash_def]
  >- fs [Once rev_assocd_def]
  >- fs [bool_case_eq, case_eq_thms, COND_RATOR]
  >- fs [case_eq_thms]
  \\ fs [UNCURRY, handle_Clash_def] \\ every_case_tac \\ fs []
  \\ CCONTR_TAC \\ fs [] \\ rw [] \\ rfs []
  \\ fs [dest_var_def, st_ex_return_def, raise_Fail_def]
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
  \\ imp_res_tac inst_aux_clash_is_var \\ rveq
  \\ rpt (qpat_x_assum `_ = (Failure _, _)` mp_tac)
  \\ simp [Once inst_aux_def]
  \\ simp [st_ex_return_def, st_ex_bind_def, raise_Fail_def]
  \\ simp [handle_Clash_def, raise_Clash_def]
  \\ `b = t` by (drule variant_same_ty \\ rw []) \\ fs [] \\ rveq
  \\ Cases_on `t0` \\ fs []
  >-
   (simp [Once vsubst_aux_def, Ntimes rev_assocd_def 2]
    \\ rpt (IF_CASES_TAC \\ fs []) \\ rveq
    \\ fs [Once vsubst_aux_def, Ntimes rev_assocd_def 2]
    \\ strip_tac \\ rveq
    \\ rfs [bool_case_eq] \\ fs [Ntimes rev_assocd_def 2] \\ rveq
    \\ fs [Once inst_aux_def, Ntimes rev_assocd_def 2, st_ex_return_def] \\ rveq \\ fs []
    \\ fs [bool_case_eq, raise_Clash_def] \\ rfs []
    \\ fs [bool_case_eq, COND_RATOR]
    \\ CCONTR_TAC \\ fs [] \\ rw [] \\ fs []
    \\ fs [Once vsubst_aux_def, Ntimes rev_assocd_def 2, bool_case_eq]
    \\ fs [Ntimes holSyntaxExtraTheory.frees_def 3]
    \\ fs [Ntimes holSyntaxExtraTheory.variant_def 3, holSyntaxExtraTheory.vfree_in_def, strcat_def, concat_def]
    \\ rename1 `str1 = strlit _` \\ Cases_on `str1` \\ fs [])
  >-
   (simp [Once vsubst_aux_def, Ntimes rev_assocd_def 2]
    \\ rw [Once inst_aux_def, st_ex_return_def])
  >- cheat (* TODO *)
  (* TODO I'm certain this mix of variant (...) things will ensure there is
     no clash. How ? *)
  \\ cheat
  );

val inst_not_clash = Q.store_thm("inst_not_clash[simp]",
  `inst x y z <> (Failure (Clash tm),refs)`,
  fs [inst_def, st_ex_return_def, bool_case_eq, case_eq_thms, COND_RATOR]
  \\ fs [inst_aux_thm]);

val INST_TYPE_not_clash = Q.store_thm("INST_TYPE_not_clash[simp]",
  `INST_TYPE x y z <> (Failure (Clash tm),refs)`,
  Cases_on `y` \\ fs [INST_TYPE_def, Once image_def]
  \\ fs [st_ex_bind_def, st_ex_return_def]
  \\ every_case_tac \\ fs []
  \\ CCONTR_TAC \\ fs [] \\ rw [] \\ fs [image_clash_thm]);

(* TODO move to readerProofTheory *)

val readLine_not_clash = Q.store_thm("readLine_not_clash[simp]",
  `readLine x y z ≠ (Failure (Clash tm),refs)`,
  strip_tac \\
  fs[readLine_def,st_ex_bind_def,pair_case_eq,exc_case_eq,st_ex_return_def,
     option_case_eq, bool_case_eq,UNCURRY,COND_RATOR]
  \\ rveq \\ fs[] \\ rw[]
  \\ every_case_tac \\ fs [raise_Fail_def]
  \\ pop_assum mp_tac \\ fs []
  \\ ho_match_mp_tac map_not_clash_thm \\ rw []);

val readLines_not_clash = Q.store_thm("readLines_not_clash[simp]",
  `∀ls x y tm refs. readLines ls x y ≠ (Failure (Clash tm),refs)`,
  recInduct readLines_ind
  \\ rw[]
  \\ rw[Once readLines_def]
  \\ CASE_TAC \\ fs[st_ex_return_def]
  \\ simp[st_ex_bind_def]
  \\ CASE_TAC \\ fs[]
  \\ CASE_TAC \\ fs[]
  \\ CCONTR_TAC \\ fs[]);

(* --- Translate readerTheory ---------------------------------------------- *)

val _ = translate init_state_def
val _ = translate mk_BN_def
val _ = translate mk_BS_def
val _ = translate insert_def
val _ = translate delete_def
val _ = translate lookup_def
val _ = translate push_def
val _ = translate insert_dict_def
val _ = translate delete_dict_def
val _ = translate first_def
val _ = translate stringTheory.isDigit_def

val _ = (use_mem_intro := true)
val tymatch_ind = save_thm("tymatch_ind",REWRITE_RULE[GSYM rev_assocd_thm]holSyntaxExtraTheory.tymatch_ind)
val _ = add_preferred_thy"-";
val r = translate (REWRITE_RULE[GSYM rev_assocd_thm]holSyntaxExtraTheory.tymatch_def)
val _ = (use_mem_intro := false)
val r = translate OPTION_MAP_DEF
val r = translate holSyntaxExtraTheory.match_type_def

val _ = m_translate find_axiom_def
val _ = m_translate getNum_def
val _ = m_translate getName_def
val _ = m_translate getList_def
val _ = m_translate getTypeOp_def
val _ = m_translate getType_def
val _ = m_translate getConst_def
val _ = m_translate getVar_def
val _ = m_translate getTerm_def
val _ = m_translate getThm_def
val _ = m_translate pop_def
val _ = m_translate peek_def
val _ = m_translate getPair_def
val _ = m_translate getNvs_def
val _ = m_translate getCns_def
val _ = m_translate getTys_def
val _ = m_translate getTms_def
val r = m_translate readLine_def

val readline_side = Q.store_thm("readline_side",
  `!st1 l s. readline_side st1 l s <=> T`,
  rw [fetch "-" "readline_side_def"] \\ intLib.COOPER_TAC)
  |> update_precondition;

val readline_spec = save_thm (
  "readline_spec",
  mk_app_of_ArrowP ``p: 'ffi ffi_proj`` (theorem "readline_v_thm"));

(* --- CakeML wrapper ------------------------------------------------------ *)

val msg_usage_def = Define `msg_usage = strlit"Usage: reader <article>\n"`

val msg_bad_name_def = Define `
  msg_bad_name s = concat
    [strlit"Bad filename: "; s; strlit".\n"]
  `;

val msg_failure_def = Define `
  msg_failure loc = concat
    [strlit"Reader threw exception: "; loc; strlit".\n"]
  `;

val _ = translate msg_usage_def
val _ = translate msg_bad_name_def
val _ = translate msg_failure_def

val str_prefix_def = Define `
  str_prefix str = extract str 0 (SOME (strlen str - 1))`;

val invalid_line_def = Define`
  invalid_line str ⇔ (strlen str) ≤ 1n ∨ strsub str 0 = #"#"`;

val process_line_def = Define`
  process_line st refs ln =
    if invalid_line ln then (INL st, refs) else
    case readLine (str_prefix ln) st refs
    of (Success st, refs) => (INL st, refs)
     | (Failure (Fail s), refs) => (INR s, refs)`;

val r = translate str_prefix_def;

val r = translate invalid_line_def;
val r = Q.prove(
  `∀x. invalid_line_side x ⇔ T`,
  EVAL_TAC \\ rw[]) |> update_precondition;

val _ = (append_prog o process_topdecs) `
  fun process_line st0 ln =
    if invalid_line ln
    then Inl st0
    else Inl (readline (str_prefix ln) st0)
         handle Fail e => Inr e`;

val process_line_spec = Q.store_thm("process_line_spec",
  `STATE_TYPE st stv ∧ STRING_TYPE ln lnv
   ==>
   app (p: 'ffi ffi_proj) ^(fetch_v "process_line" (get_ml_prog_state()))
   [stv; lnv]
   (HOL_STORE refs)
   (POSTv stv.
      HOL_STORE (SND(process_line st refs ln)) *
      &SUM_TYPE STATE_TYPE STRING_TYPE
        (FST(process_line st refs ln)) stv)`,
  xcf "process_line" (get_ml_prog_state())
  \\ xlet_auto >- xsimpl
  \\ simp[process_line_def]
  \\ xif \\ fs []
  >- ( xcon \\ xsimpl \\ fs[SUM_TYPE_def] )
  \\ CASE_TAC
  \\ reverse CASE_TAC \\ fs[]
  >- (
    CASE_TAC \\ fs[]
    \\ qmatch_asmsub_rename_tac`(Failure (Fail err),refs')`
    \\ xhandle`POSTe ev. &HOL_EXN_TYPE (Fail err) ev * HOL_STORE refs'`
    >- (
      xlet_auto >- xsimpl
      \\ xlet_auto \\ xsimpl )
    \\ xcases
    \\ fs[HOL_EXN_TYPE_def]
    \\ reverse conj_tac >- (EVAL_TAC \\ rw[])
    \\ xcon \\ xsimpl
    \\ fs[SUM_TYPE_def] )
  \\ qmatch_goalsub_abbrev_tac `$POSTv Qval`
  \\ xhandle`$POSTv Qval` \\ xsimpl
  \\ qunabbrev_tac`Qval`
  \\ xlet_auto >- xsimpl
  \\ xlet_auto \\ xsimpl
  \\ xcon \\ xsimpl
  \\ fs[SUM_TYPE_def] );

val process_lines_def = Define`
  (process_lines fd st refs fs [] = STDIO (add_stdout (fastForwardFD fs fd) "OK!\n") * HOL_STORE refs) ∧
  (process_lines fd st refs fs (ln::ls) =
   case process_line st refs ln of
   | (INL st,refs) => process_lines fd st refs (lineForwardFD fs fd) ls
   | (INR e,refs)  => STDIO (add_stderr (lineForwardFD fs fd) (explode (msg_failure e))) * HOL_STORE refs)`;

val _ = (append_prog o process_topdecs) `
  fun process_lines ins st0 =
    case TextIO.inputLine ins of
      NONE => TextIO.print "OK!\n"
    | SOME ln =>
      (case process_line st0 ln of
         Inl st1 => process_lines ins st1
       | Inr e => TextIO.output TextIO.stdErr (msg_failure e))`;

val process_lines_spec = Q.store_thm("process_lines_spec",
  `!n st stv refs.
     STATE_TYPE st stv /\
     WORD8 (n2w fd) fdv /\ fd <= 255 /\ fd <> 1 /\ fd <> 2 /\
     STD_streams fs /\
     get_file_content fs fd = SOME (content, n)
     ==>
     app (p:'ffi ffi_proj) ^(fetch_v"process_lines"(get_ml_prog_state())) [fdv;stv]
       (STDIO fs * HOL_STORE refs)
       (POSTv u.
         &UNIT_TYPE () u *
         process_lines fd st refs fs (MAP implode (linesFD fs fd)))`,
  Induct_on`linesFD fs fd`
  >- (
    rpt strip_tac
    \\ qpat_x_assum`[] = _`(assume_tac o SYM)
    \\ xcf"process_lines"(get_ml_prog_state())
    \\ `IS_SOME (get_file_content fs fd)` by fs []
    \\ `lineFD fs fd = NONE` by fs [linesFD_nil_lineFD_NONE]
    \\ simp[process_lines_def]
    \\ xlet_auto >- xsimpl
    \\ xmatch
    \\ fs[OPTION_TYPE_def]
    \\ reverse conj_tac >- (EVAL_TAC \\ rw[])
    \\ xapp
    \\ xsimpl
    \\ simp[lineFD_NONE_lineForwardFD_fastForwardFD]
    \\ qexists_tac`HOL_STORE refs` \\ xsimpl
    \\ qexists_tac`fastForwardFD fs fd`
    \\ xsimpl)
  \\ rpt strip_tac
  \\ xcf"process_lines"(get_ml_prog_state())
  \\ qpat_x_assum`_::_ = _`(assume_tac o SYM)
  \\ imp_res_tac linesFD_cons_imp
  \\ rveq \\ fs[] \\ rveq
  \\ qmatch_assum_rename_tac`lineFD fs fd = SOME ln`
  \\ xlet_auto >- xsimpl
  \\ xmatch
  \\ fs[OPTION_TYPE_def]
  \\ reverse conj_tac >- (EVAL_TAC \\ rw[])
  \\ reverse conj_tac >- (EVAL_TAC \\ rw[])
  \\ xlet_auto >- (
    xsimpl
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac`refs` \\ xsimpl )
  \\ xmatch
  \\ Cases_on`process_line st refs (implode ln)` \\ fs[]
  \\ qmatch_assum_rename_tac`SUM_TYPE _ _ sm _`
  \\ Cases_on`sm` \\ fs[SUM_TYPE_def]
  \\ (reverse conj_tac >- (EVAL_TAC \\ rw[]))
  >- (
    xapp
    \\ simp[process_lines_def]
    \\ xsimpl
    \\ `STD_streams (lineForwardFD fs fd)` by simp[STD_streams_lineForwardFD]
    \\ asm_exists_tac
    \\ simp[]
    \\ qexists_tac`emp` \\ xsimpl
    \\ qmatch_asmsub_rename_tac`(INL st',refs')`
    \\ qexists_tac`st'` \\ qexists_tac`refs'`
    \\ qexists_tac`fd` \\ xsimpl
    \\ imp_res_tac get_file_content_lineForwardFD_forwardFD
    \\ simp[get_file_content_forwardFD] )
  \\ (reverse conj_tac >- (EVAL_TAC \\ rw[]))
  \\ xlet_auto >- xsimpl
  \\ xapp_spec output_STDIO_spec
  \\ simp[process_lines_def]
  \\ xsimpl
  \\ qmatch_goalsub_abbrev_tac`STDIO fs'`
  \\ qmatch_asmsub_rename_tac`(INR msg,refs')`
  \\ qexists_tac`HOL_STORE refs'` \\ xsimpl
  \\ `STD_streams fs'` by simp[STD_streams_lineForwardFD,Abbr`fs'`]
  \\ drule STD_streams_stderr \\ strip_tac
  \\ fs[stdo_def]
  \\ simp[get_file_content_def,UNCURRY,PULL_EXISTS]
  \\ `2 <= 255n` by simp[] \\ asm_exists_tac
  \\ instantiate \\ xsimpl
  \\ conj_tac >- metis_tac[stderr_v_thm,stdErr_def]
  \\ simp[insert_atI_end]
  \\ simp[add_stdo_def]
  \\ SELECT_ELIM_TAC
  \\ (conj_tac >- metis_tac[STD_streams_stderr])
  \\ rw[stdo_def,up_stdo_def,LENGTH_explode]
  \\ xsimpl);

val _ = (append_prog o process_topdecs) `
  fun read_file file =
    let
      val ins = TextIO.openIn file
    in
      process_lines ins init_state;
      TextIO.close ins
    end
    (* Presuming that openIn will raise only this *)
    handle TextIO.BadFileName =>
      TextIO.output TextIO.stdErr (msg_bad_name file)`;

val readLines_process_lines = Q.store_thm("readLines_process_lines",
  `∀ls st refs res r fs.
   readLines (MAP str_prefix (FILTER ($~ o invalid_line) ls)) st refs = (res,r) ⇒
   ∃n.
     process_lines fd st refs fs ls =
     case res of
     | (Success _) => STDIO (add_stdout (fastForwardFD fs fd) "OK!\n") * HOL_STORE r
     | (Failure (Fail e)) => STDIO (add_stderr (forwardFD fs fd n) (explode (msg_failure e))) * HOL_STORE r`,
  Induct
  \\ rw[process_lines_def]
  >- ( fs[Once readLines_def,st_ex_return_def] \\ rw[] )
  >- (
    rw[process_line_def]
    \\ pop_assum mp_tac
    \\ simp[Once readLines_def]
    \\ rw[st_ex_bind_def]
    \\ CASE_TAC \\ fs[]
    \\ CASE_TAC \\ fs[]
    >- (
      first_x_assum drule
      \\ disch_then(qspec_then`lineForwardFD fs fd`strip_assume_tac)
      \\ simp[]
      \\ CASE_TAC
      \\ CASE_TAC \\ fs[]
      \\ qspecl_then[`fs`,`fd`]strip_assume_tac lineForwardFD_forwardFD
      \\ simp[forwardFD_o]
      \\ metis_tac[] )
    \\ rveq \\ fs[]
    \\ CASE_TAC \\ fs[]
    \\ qspecl_then[`fs`,`fd`]strip_assume_tac lineForwardFD_forwardFD
    \\ simp[]
    \\ metis_tac[] )
  \\ rw[process_line_def]
  \\ first_x_assum drule
  \\ disch_then(qspec_then`lineForwardFD fs fd`strip_assume_tac)
  \\ simp[]
  \\ CASE_TAC
  \\ CASE_TAC \\ fs[]
  \\ qspecl_then[`fs`,`fd`]strip_assume_tac lineForwardFD_forwardFD
  \\ simp[forwardFD_o]
  \\ metis_tac[] );

val read_file_def = Define`
  read_file fs refs fnm =
    (if inFS_fname fs (File fnm) then
       (case readLines (MAP str_prefix (FILTER ($~ o invalid_line) (all_lines fs (File fnm))))
               init_state refs of
        | (Success _, refs) => (add_stdout fs "OK!\n", refs)
        | (Failure (Fail e), refs) => (add_stderr fs (explode (msg_failure e)), refs))
     else (add_stderr fs (explode (msg_bad_name fnm)), refs))`;

val read_file_spec = Q.store_thm("read_file_spec",
  `FILENAME fnm fnv /\ hasFreeFD fs
   ==>
   app (p: 'ffi ffi_proj) ^(fetch_v "read_file" (get_ml_prog_state())) [fnv]
     (STDIO fs * HOL_STORE refs)
     (POSTv u.
       &UNIT_TYPE () u *
       STDIO (FST(read_file fs refs fnm)) *
       HOL_STORE (SND(read_file fs refs fnm)))`,
  xcf "read_file" (get_ml_prog_state())
  \\ reverse (Cases_on `STD_streams fs`)
  >- (fs [TextIOProofTheory.STDIO_def] \\ xpull)
  \\ simp[read_file_def]
  \\ reverse IF_CASES_TAC \\ fs[]
  >- (
    xhandle`POSTe ev.
      &BadFileName_exn ev *
      &(~inFS_fname fs (File fnm)) *
      STDIO fs * HOL_STORE refs`
    >- ( xlet_auto_spec (SOME openIn_STDIO_spec) \\ xsimpl )
    \\ fs[BadFileName_exn_def]
    \\ xcases
    \\ xlet_auto >- xsimpl
    \\ xapp_spec output_STDIO_spec
    \\ xsimpl
    \\ drule STD_streams_stderr \\ strip_tac
    \\ fs[stdo_def]
    \\ simp[get_file_content_def,UNCURRY,PULL_EXISTS]
    \\ `2 <= 255n` by simp[] \\ asm_exists_tac
    \\ instantiate \\ xsimpl
    \\ conj_tac >- metis_tac[stderr_v_thm,stdErr_def]
    \\ simp[insert_atI_end]
    \\ simp[add_stdo_def]
    \\ SELECT_ELIM_TAC
    \\ (conj_tac >- metis_tac[STD_streams_stderr])
    \\ rw[stdo_def,up_stdo_def,LENGTH_explode]
    \\ xsimpl)
  \\ CASE_TAC \\ fs[]
  \\ qmatch_goalsub_abbrev_tac`$POSTv Qval`
  \\ xhandle`$POSTv Qval` \\ xsimpl
  \\ qunabbrev_tac`Qval`
  \\ xlet_auto_spec (SOME openIn_STDIO_spec)
  \\ xsimpl
  \\ imp_res_tac nextFD_leX
  \\ imp_res_tac ALOOKUP_inFS_fname_openFileFS_nextFD
  \\ pop_assum(qspec_then`0`mp_tac) \\ rw[]
  \\ qmatch_asmsub_abbrev_tac`ALOOKUP fs'.infds fd`
  \\ imp_res_tac inFS_fname_ALOOKUP_EXISTS
  \\ `get_file_content fs' fd = SOME (content,0)` by simp[get_file_content_def,Abbr`fs'`]
  \\ imp_res_tac STD_streams_nextFD
  \\ imp_res_tac STD_streams_openFileFS
  \\ pop_assum(qspecl_then[`fnm`,`0`]assume_tac)
  \\ `fd ≠ 1 ∧ fd ≠ 2` by rfs[]
  \\ assume_tac (fetch"-""init_state_v_thm")
  \\ xlet_auto_spec (SOME (Q.SPEC`fs'`(Q.GEN`fs`process_lines_spec)))
  \\ xsimpl
  \\ xapp_spec close_STDIO_spec
  \\ instantiate
  \\ rfs[]
  \\ drule (GEN_ALL readLines_process_lines)
  \\ disch_then(qspecl_then[`fd`,`fs'`]strip_assume_tac)
  \\ simp[Abbr`fs'`,linesFD_openFileFS_nextFD,Abbr`fd`,MAP_MAP_o,o_DEF]
  \\ CASE_TAC
  >- (
    xsimpl
    \\ qexists_tac`HOL_STORE r` \\ xsimpl
    \\ qmatch_goalsub_abbrev_tac`STDIO fs'`
    \\ qexists_tac`fs'` \\ xsimpl
    \\ simp[Abbr`fs'`]
    \\ simp[add_stdout_fastForwardFD] \\ rw [] \\ fs []
    \\ drule (GEN_ALL openFileFS_A_DELKEY_nextFD)
    \\ disch_then (qspecl_then [`0`,`fnm`] mp_tac) \\ rw []
    \\ `1 <> nextFD fs` by fs []
    \\ qmatch_goalsub_abbrev_tac `add_stdout _ str1`
    \\ imp_res_tac add_stdo_A_DELKEY
    \\ first_x_assum (qspecl_then [`str1`,`"stdout"`, `openFileFS fnm fs 0`] mp_tac)
    \\ xsimpl
    )
  \\ CASE_TAC \\ fs[]
  \\ xsimpl
  \\ qexists_tac`HOL_STORE r` \\ xsimpl
  \\ qmatch_goalsub_abbrev_tac`STDIO fs'`
  \\ qexists_tac`fs'` \\ xsimpl
  \\ simp[Abbr`fs'`]
  \\ simp[add_stdo_forwardFD] \\ rw []
  \\ `2 <> nextFD fs` by fs [] \\ fs []
  \\ drule (GEN_ALL openFileFS_A_DELKEY_nextFD)
  \\ disch_then (qspecl_then [`0`,`fnm`] mp_tac) \\ rw []
  \\ imp_res_tac add_stdo_A_DELKEY
  \\ qmatch_goalsub_abbrev_tac `add_stderr _ str1`
  \\ first_x_assum (qspecl_then [`str1`,`"stderr"`,`openFileFS fnm fs 0`] mp_tac)
  \\ xsimpl);

val _ = (append_prog o process_topdecs) `
  fun reader_main u =
    case CommandLine.arguments () of
      [file] => read_file file
    | _      => TextIO.output TextIO.stdErr msg_usage`;

val reader_main_def = Define `
   reader_main fs refs cl =
       case cl of
         [fnm] => FST (read_file fs refs fnm)
       | _ => add_stderr fs (explode msg_usage)`;

val reader_main_spec = Q.store_thm("reader_main_spec",
  `hasFreeFD fs
   ==>
   app (p:'ffi ffi_proj) ^(fetch_v "reader_main" (get_ml_prog_state()))
     [Conv NONE []]
     (STDIO fs * COMMANDLINE cl * HOL_STORE refs)
     (POSTv u.
       &UNIT_TYPE () u *
       STDIO (reader_main fs refs (TL (MAP implode cl))) *
       COMMANDLINE cl)`,
  xcf "reader_main" (get_ml_prog_state())
  \\ fs [reader_main_def]
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ fs [UNIT_TYPE_def]
  \\ reverse (Cases_on `wfcl cl`) >- (simp[COMMANDLINE_def] \\ xpull)
  \\ fs [wfcl_def]
  \\ xlet_auto_spec (SOME CommandLineProofTheory.CommandLine_arguments_spec)
  >-
   (qexists_tac `STDIO fs * HOL_STORE refs`
    \\ xsimpl)
  \\ reverse (Cases_on `STD_streams fs`) >- (fs[STDIO_def] \\ xpull)
  \\ Cases_on `TL (MAP implode cl)` \\ fs [LIST_TYPE_def]
  >-
   (xmatch
    \\ xapp_spec output_stderr_spec
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac `msg_usage`
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac `fs` \\ xsimpl
    \\ fs [theorem"msg_usage_v_thm", UNIT_TYPE_def])
  \\ reverse (Cases_on `t`) \\ fs [LIST_TYPE_def]
  >-
   (xmatch
    \\ xapp_spec output_stderr_spec
    \\ xsimpl
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac `msg_usage`
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac `fs`
    \\ xsimpl
    \\ fs [theorem"msg_usage_v_thm", UNIT_TYPE_def])
  \\ xmatch
  \\ xapp
  \\ instantiate \\ xsimpl
  \\ CONV_TAC SWAP_EXISTS_CONV
  \\ qexists_tac `refs` \\ xsimpl
  \\ Cases_on `cl` \\ fs [] \\ rveq
  \\ fs [implode_def, FILENAME_def, validArg_def]
  \\ asm_exists_tac
  \\ rw [UNIT_TYPE_def]
  \\ xsimpl);

val STD_streams_reader_main = Q.store_thm("STD_streams_reader_main",
  `STD_streams fs ⇒ STD_streams (reader_main fs refs cl)`,
  rw[reader_main_def]
  \\ every_case_tac
  \\ rw[STD_streams_add_stderr]
  \\ rw[read_file_def,STD_streams_add_stderr]
  \\ CASE_TAC \\ rw[STD_streams_add_stderr]
  \\ CASE_TAC \\ rw[STD_streams_add_stderr,STD_streams_add_stdout]
  \\ CASE_TAC \\ rw[STD_streams_add_stderr,STD_streams_add_stdout]
  \\ fs[]);

val init_refs_def = Define`
  init_refs =
   <|the_type_constants := init_type_constants;
     the_term_constants := init_term_constants;
     the_axioms := init_axioms;
     the_context := init_context|>`;

val name = "reader_main"
val spec =
  reader_main_spec
  |> UNDISCH
  |> SIMP_RULE std_ss [STDIO_def]
  |> add_basis_proj
  |> Q.GEN`refs` |> Q.SPEC`init_refs`;
val st = get_ml_prog_state();

(* TODO: where should this go? *)
val HOL_STORE_init_precond = Q.store_thm("HOL_STORE_init_precond",
  `HOL_STORE init_refs
   {Mem (1+(LENGTH(stdin_refs++stdout_refs++stderr_refs++init_type_constants_refs)))
        (Refv init_type_constants_v);
    Mem (2+(LENGTH(stdin_refs++stdout_refs++stderr_refs++init_type_constants_refs++init_term_constants_refs)))
        (Refv init_term_constants_v);
    Mem (3+(LENGTH(stdin_refs++stdout_refs++stderr_refs++init_type_constants_refs++init_term_constants_refs++init_axioms_refs)))
        (Refv init_axioms_v);
    Mem (4+(LENGTH(stdin_refs++stdout_refs++stderr_refs++init_type_constants_refs++init_term_constants_refs++init_axioms_refs++init_context_refs)))
        (Refv init_context_v)}`,
  qmatch_goalsub_abbrev_tac`1 + l1`
  \\ qmatch_goalsub_abbrev_tac`2 + l2`
  \\ qmatch_goalsub_abbrev_tac`3 + l3`
  \\ qmatch_goalsub_abbrev_tac`4 + l4`
  \\ rw[HOL_STORE_def,ml_monad_translatorBaseTheory.REF_REL_def,init_refs_def]
  \\ rw[STAR_def,SEP_EXISTS_THM]
  \\ qmatch_goalsub_abbrev_tac`Mem (l1+1) v1`
  \\ qmatch_goalsub_abbrev_tac`Mem (l2+2) v2`
  \\ qmatch_goalsub_abbrev_tac`Mem (l3+3) v3`
  \\ qmatch_goalsub_abbrev_tac`Mem (l4+4) v4`
  \\ qexists_tac`{Mem(l1+1)v1;Mem(l2+2)v2;Mem(l3+3)v3}`
  \\ qexists_tac`{Mem(l4+4)v4}`
  \\ `l1+1 < l2+2` by simp[Abbr`l1`,Abbr`l2`]
  \\ `l2+2 < l3+3` by simp[Abbr`l2`,Abbr`l3`]
  \\ `l3+3 < l4+4` by simp[Abbr`l3`,Abbr`l4`]
  \\ conj_tac >- SPLIT_TAC
  \\ reverse conj_tac
  >- (
    rw[REF_def,SEP_EXISTS_THM,EVAL``the_context``,cond_STAR,
       ml_monad_translatorBaseTheory.CELL_HPROP_SAT_EQ,ADD1]
    \\ rw[cond_def]
    \\ qexists_tac`init_context_v`
    \\ simp[init_context_v_thm]
    \\ fs[Abbr`l4`]
    \\ SPLIT_TAC )
  \\ qexists_tac`{Mem(l1+1)v1;Mem(l2+2)v2}`
  \\ qexists_tac`{Mem(l3+3)v3}`
  \\ conj_tac >- SPLIT_TAC
  \\ reverse conj_tac
  >- (
    rw[REF_def,SEP_EXISTS_THM,EVAL``the_axioms``,cond_STAR,
       ml_monad_translatorBaseTheory.CELL_HPROP_SAT_EQ,ADD1]
    \\ rw[cond_def]
    \\ qexists_tac`init_axioms_v`
    \\ simp[init_axioms_v_thm]
    \\ fs[Abbr`l3`]
    \\ SPLIT_TAC )
  \\ qexists_tac`{Mem(l1+1)v1}`
  \\ qexists_tac`{Mem(l2+2)v2}`
  \\ conj_tac >- SPLIT_TAC
  \\ reverse conj_tac
  >- (
    rw[REF_def,SEP_EXISTS_THM,EVAL``the_term_constants``,cond_STAR,
       ml_monad_translatorBaseTheory.CELL_HPROP_SAT_EQ,ADD1]
    \\ rw[cond_def]
    \\ qexists_tac`init_term_constants_v`
    \\ simp[init_term_constants_v_thm]
    \\ fs[Abbr`l2`]
    \\ SPLIT_TAC ) \\
  rw[REF_def,SEP_EXISTS_THM,EVAL``the_type_constants``,cond_STAR,
     ml_monad_translatorBaseTheory.CELL_HPROP_SAT_EQ,ADD1]
  \\ rw[cond_def]
  \\ qexists_tac`init_type_constants_v`
  \\ simp[init_type_constants_v_thm]
  \\ fs[Abbr`l1`]
  \\ SPLIT_TAC );
(* -- *)

val () = hprop_heap_thms := HOL_STORE_init_precond :: (!hprop_heap_thms)

val (sem_thm,prog_tm) = call_thm st name spec

val reader_prog_def = Define `reader_prog = ^prog_tm`

val semantics_reader_prog =
  sem_thm
  |> REWRITE_RULE[GSYM reader_prog_def]
  |> DISCH_ALL
  |> CONV_RULE(LAND_CONV EVAL)
  |> SIMP_RULE (srw_ss())[AND_IMP_INTRO,STD_streams_reader_main,GSYM CONJ_ASSOC]
  |> curry save_thm "semantics_reader_prog";

val _ = export_theory ();
