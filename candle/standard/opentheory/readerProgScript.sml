open preamble basis
     ml_monadBaseTheory ml_monad_translatorLib cfMonadTheory cfMonadLib
     holKernelTheory holKernelProofTheory ml_hol_kernelProgTheory readerTheory
     readerProofTheory

val _ = new_theory "readerProg"
val _ = m_translation_extends "ml_hol_kernelProg"

val exc_case_eq = prove_case_eq_thm{case_def=exc_case_def,nchotomy=exc_nchotomy};
val term_case_eq = prove_case_eq_thm{case_def=holSyntaxTheory.term_case_def,nchotomy=holSyntaxTheory.term_nchotomy};
val option_case_eq = prove_case_eq_thm{case_def=optionTheory.option_case_def,nchotomy=optionTheory.option_nchotomy};
val object_case_eq = prove_case_eq_thm{case_def=readerTheory.object_case_def,nchotomy=readerTheory.object_nchotomy};

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

(* TODO move to readerProofTheory *)

val readLine_not_clash = Q.store_thm("readLine_not_clash[simp]",
  `readLine x y z ≠ (Failure (Clash tm),refs)`,
  strip_tac \\
  fs[readLine_def,st_ex_bind_def,pair_case_eq,exc_case_eq,st_ex_return_def,
     option_case_eq, bool_case_eq,UNCURRY,COND_RATOR]
  \\ rveq \\ fs[] \\ rw[]
  \\ every_case_tac \\ fs [raise_Fail_def]
  \\ TRY
   (rename1 `map _ _ _ = (Failure (Clash tm),refs)`
    \\ metis_tac [map_not_clash_thm, getTerm_not_clash, getCns_not_clash,
                  getNvs_not_clash, getType_not_clash, getTms_not_clash,
                  getTys_not_clash])
  \\ cheat);

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
    \\ simp[add_stdout_fastForwardFD]
    \\ cheat
    (* openFileFS_A_DELKEY_nextFD *) )
  \\ CASE_TAC \\ fs[]
  \\ xsimpl
  \\ qexists_tac`HOL_STORE r` \\ xsimpl
  \\ qmatch_goalsub_abbrev_tac`STDIO fs'`
  \\ qexists_tac`fs'` \\ xsimpl
  \\ simp[Abbr`fs'`]
  \\ simp[add_stdo_forwardFD]
  \\ cheat
  (* forwardFD version of fastForwardFD_A_DELKEY_same? *)
  );

val _ = (append_prog o process_topdecs) `
  fun reader_main u =
    case CommandLine.arguments () of
      [file] => read_file file
    | _      => TextIO.output TextIO.stdErr msg_usage`;

val main_spec = Q.store_thm("main_spec",
  `TODO`,
  cheat
  );

val st = get_ml_prog_state ();
val name = "reader_main"
val spec = main_spec |> SIMP_RULE std_ss [STDIO_def] |> add_basis_proj;
val (semantics_thm, prog_tm) = call_thm st name spec

val reader_prog_def = Define `reader_prog = ^prog_tm`

val _ = export_theory ();
