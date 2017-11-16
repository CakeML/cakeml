open preamble ml_translatorTheory ml_progLib ml_translatorLib cfLib
     CommandlineProgTheory clFFITheory Word8ArrayProofTheory

val _ = new_theory"CommandlineProof";

val _ = translation_extends"CommandlineProg";

val wfcl_def = Define`
  wfcl cl ⇔ EVERY validArg cl ∧ ¬NULL cl ∧ SUM (MAP LENGTH cl) + LENGTH cl <= 256`;

val COMMANDLINE_def = Define `
  COMMANDLINE cl =
    IOx cl_ffi_part cl * &wfcl cl`

val set_thm =
  COMMANDLINE_def
  |> SIMP_RULE(srw_ss())[
       cfHeapsBaseTheory.IOx_def,cl_ffi_part_def,
       cfHeapsBaseTheory.IO_def, set_sepTheory.one_def ]
  |> SIMP_RULE(srw_ss())[Once FUN_EQ_THM,set_sepTheory.SEP_EXISTS_THM,set_sepTheory.cond_STAR,PULL_EXISTS]
  |> Q.SPEC`cl`
val set_tm = set_thm |> concl |> find_term(pred_setSyntax.is_insert)

val COMMANDLINE_precond = Q.prove(
  `wfcl cl ⇒ (COMMANDLINE cl) ^set_tm`,
  rw[set_thm]) |> UNDISCH
  |> curry save_thm "COMMANDLINE_precond";

val COMMANDLINE_FFI_part_hprop = Q.store_thm("COMMANDLINE_FFI_part_hprop",
  `FFI_part_hprop (COMMANDLINE x)`,
  rw [COMMANDLINE_def,cfHeapsBaseTheory.IO_def,cfMainTheory.FFI_part_hprop_def,
      cfHeapsBaseTheory.IOx_def, cl_ffi_part_def,
      set_sepTheory.SEP_CLAUSES,set_sepTheory.SEP_EXISTS_THM,
      set_sepTheory.cond_STAR ]
  \\ fs[set_sepTheory.one_def]);

val eq_v_thm = fetch "mlbasicsProg" "eq_v_thm"
val eq_num_v_thm = MATCH_MP (DISCH_ALL eq_v_thm) (EqualityType_NUM_BOOL |> CONJUNCT1)

val st = get_ml_prog_state();

val Commandline_cline_spec = Q.store_thm("Commandline_cline_spec",
  `UNIT_TYPE u uv ==>
    app (p:'ffi ffi_proj) ^(fetch_v "Commandline.cline" st) [uv]
    (COMMANDLINE cl)
    (POSTv clinev. & LIST_TYPE STRING_TYPE (MAP implode  cl) clinev * COMMANDLINE cl)`,
  xcf "Commandline.cline" st
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ rename1`W8ARRAY cs`
  \\ qabbrev_tac`l = MAP ((n2w:num -> word8) o ORD) (FLAT (MAP (\s. s ++ [CHR 0]) cl))`
  \\ fs [COMMANDLINE_def]
  \\ xpull
  \\ `LENGTH l = LENGTH cl + SUM (MAP LENGTH cl)`
  by (
    simp[Abbr`l`,LENGTH_FLAT,MAP_MAP_o,o_DEF,SUM_MAP_PLUS,
         MAP_K_REPLICATE |> SIMP_RULE std_ss [K_DEF],
         SUM_REPLICATE])
  \\ `LENGTH l ≤ 256` by fs[wfcl_def]
  \\ xlet `POSTv u. W8ARRAY cs (l ++ DROP (LENGTH l) (REPLICATE 256 (n2w 0))) * COMMANDLINE cl`
  >- (
    xffi
    \\ fs[COMMANDLINE_def,cfHeapsBaseTheory.IOx_def,cl_ffi_part_def]
    \\ xsimpl
    \\ qmatch_goalsub_abbrev_tac`IO s u ns`
    \\ map_every qexists_tac [`emp`, `s`, `s`, `u`, `ns`]
    \\ xsimpl
    \\ fs[Abbr`u`,Abbr`ns`,cfHeapsBaseTheory.mk_ffi_next_def,ffi_getArgs_def,GSYM cfHeapsBaseTheory.encode_list_def,Abbr`s`]
    \\ simp[EVERY_MAP, LENGTH_REPLICATE, Abbr`l`]
    \\ rw[encode_def] \\ fs[EVERY_REPLICATE])
  \\ xfun_spec`foo``∀c cv. CHAR c cv ⇒ app p foo [cv] emp (POSTv v. &(BOOL (CHR 0 = c) v))`
  >- (
    rw[]
    \\ xapp
    \\ xlet_auto >- xsimpl
    \\ xapp_spec eq_num_v_thm
    \\ instantiate
    \\ xsimpl
    \\ simp[CHAR_EQ_THM,BOOL_def] )
  \\ xlet_auto >- xsimpl
  \\ xapp
  \\ fs[COMMANDLINE_def]
  \\ instantiate
  \\ xsimpl
  \\ qexists_tac`(=) (CHR 0)`
  \\ conj_tac
  >- (
    Q.ISPEC_THEN`p`match_mp_tac (Q.GEN`p` app_basic_IMP_Arrow)
    \\ fs[app_def] )
  \\ fs[wfcl_def]
  \\ simp[TAKE_APPEND,TAKE_LENGTH_TOO_LONG,Abbr`l`,mlstringTheory.TOKENS_eq_tokens_sym,
          MAP_TAKE,MAP_MAP_o,CHR_w2n_n2w_ORD,MAP_DROP,map_replicate,DROP_REPLICATE]
  \\ fsrw_tac[ETA_ss][GSYM SNOC_APPEND]
  \\ Q.ISPEC_THEN`cl`FULL_STRUCT_CASES_TAC SNOC_CASES >- fs[]
  \\ simp[MAP_SNOC,FLAT_SNOC]
  \\ qmatch_goalsub_abbrev_tac`l1 ++ SNOC nl x ++ REPLICATE _ _`
  \\ qmatch_goalsub_abbrev_tac`l1 ++ SNOC nl x ++ l3`
  \\ `l1 ++ SNOC nl x ++ l3 = (l1 ++ x) ++ nl::l3` by simp[SNOC_APPEND]
  \\ pop_assum SUBST_ALL_TAC
  \\ simp[TOKENS_APPEND,Abbr`nl`]
  \\ simp[Abbr`l3`,(TOKENS_NIL|>SPEC_ALL|>EQ_IMP_RULE |> #2),EVERY_REPLICATE]
  \\ qmatch_goalsub_abbrev_tac`((=) nl)`
  \\ `l1 ++ x = FRONT (FLAT (MAP (SNOC nl) (SNOC x l)))`
  by ( simp[Abbr`l1`,FRONT_APPEND] )
  \\ simp[]
  \\ DEP_REWRITE_TAC[TOKENS_FRONT]
  \\ simp[FLAT_EQ_NIL,NULL_EQ,EXISTS_MAP,LAST_FLAT]
  \\ DEP_REWRITE_TAC[FILTER_EQ_ID |> SPEC_ALL |> EQ_IMP_RULE |> #2]
  \\ simp[EVERY_MAP,NULL_EQ]
  \\ DEP_REWRITE_TAC[TOKENS_FLAT_MAP_SNOC]
  \\ fs[EVERY_SNOC,validArg_def,EVERY_MEM,NULL_EQ,MAP_SNOC]);

val hd_v_thm = fetch "ListProg" "hd_v_thm";
val mlstring_hd_v_thm = hd_v_thm |> INST_TYPE [alpha |-> mlstringSyntax.mlstring_ty]

val Commandline_name_spec = Q.store_thm("Commandline_name_spec",
  `UNIT_TYPE u uv ==>
    app (p:'ffi ffi_proj) ^(fetch_v "Commandline.name" st) [uv]
    (COMMANDLINE cl)
    (POSTv namev. & STRING_TYPE (implode (HD cl)) namev * COMMANDLINE cl)`,
    xcf "Commandline.name" st
    \\ xlet `POSTv vz. & UNIT_TYPE () vz * COMMANDLINE cl`
    >-(xcon \\ xsimpl)
    \\ xlet `POSTv cs. & LIST_TYPE STRING_TYPE (MAP implode cl) cs * COMMANDLINE cl`
    >-(xapp \\ rw[])
    \\ Cases_on`cl=[]` >- ( fs[COMMANDLINE_def] \\ xpull \\ fs[wfcl_def] )
    \\ xapp_spec mlstring_hd_v_thm
    \\ xsimpl \\ instantiate \\ Cases_on `cl` \\ rw[]
);

val tl_v_thm = fetch "ListProg" "tl_v_thm";
val mlstring_tl_v_thm = tl_v_thm |> INST_TYPE [alpha |-> mlstringSyntax.mlstring_ty]

val Commandline_arguments_spec = Q.store_thm("Commandline_arguments_spec",
  `UNIT_TYPE u uv ==>
    app (p:'ffi ffi_proj) ^(fetch_v "Commandline.arguments" st) [uv]
    (COMMANDLINE cl)
    (POSTv argv. & LIST_TYPE STRING_TYPE (TL (MAP implode cl)) argv * COMMANDLINE cl)`,
    xcf "Commandline.arguments" st
    \\ xlet `POSTv vz. & UNIT_TYPE () vz * COMMANDLINE cl`
    >-(xcon \\ xsimpl)
    \\ xlet `POSTv cs. & LIST_TYPE STRING_TYPE (MAP implode cl) cs * COMMANDLINE cl`
    >-(xapp \\ rw[])
    \\ Cases_on`cl=[]` >- ( fs[COMMANDLINE_def] \\ xpull \\ fs[wfcl_def] )
    \\ xapp_spec mlstring_tl_v_thm \\ xsimpl \\ instantiate \\ Cases_on `cl` \\ rw[mllistTheory.tl_def]
);

fun prove_hprop_inj_tac thm =
    rw[HPROP_INJ_def, GSYM STAR_ASSOC, SEP_CLAUSES, SEP_EXISTS_THM, HCOND_EXTRACT] >>
      EQ_TAC >-(DISCH_TAC >> IMP_RES_TAC thm >> rw[]) >> rw[];

val UNIQUE_COMMANDLINE = Q.store_thm("UNIQUE_COMMANDLINE",
`!s cl1 cl2 H1 H2. VALID_HEAP s ==>
(COMMANDLINE cl1 * H1) s /\ (COMMANDLINE cl2 * H2) s ==> cl2 = cl1`,
rw[COMMANDLINE_def, cfHeapsBaseTheory.IOx_def, cl_ffi_part_def, encode_def, cfHeapsBaseTheory.encode_list_def, GSYM STAR_ASSOC] >>
IMP_RES_TAC FRAME_UNIQUE_IO >>
fs[] >> rw[] >>
sg `!l1 l2. (MAP Str l1 = MAP Str l2) ==> l2 = l1`
>-(
    Induct_on `l2` >-(rw[])>>
    rw[] >> fs[] >>
    Cases_on `l1` >-(fs[])>>  fs[]
) >>
fs[]);

val COMMANDLINE_HPROP_INJ = Q.store_thm("COMMANDLINE_HPROP_INJ[hprop_inj]",
`!cl1 cl2. HPROP_INJ (COMMANDLINE cl1) (COMMANDLINE cl2) (cl2 = cl1)`,
prove_hprop_inj_tac UNIQUE_COMMANDLINE);

val _ = export_theory();
