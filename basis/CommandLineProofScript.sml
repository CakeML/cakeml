open preamble ml_translatorTheory ml_progLib ml_translatorLib cfLib
     CommandLineProgTheory clFFITheory Word8ArrayProofTheory cfMonadTheory

val _ = new_theory"CommandLineProof";

val _ = translation_extends"CommandLineProg";

val wfcl_def = Define`
  wfcl cl <=> EVERY validArg cl ∧ LENGTH cl < 256 * 256 /\ cl <> []`;

val COMMANDLINE_def = Define `
  COMMANDLINE cl =
    IOx cl_ffi_part cl * &wfcl cl`

val set_thm =
  COMMANDLINE_def
  |> SIMP_RULE(srw_ss())[
       cfHeapsBaseTheory.IOx_def,cl_ffi_part_def,
       cfHeapsBaseTheory.IO_def, set_sepTheory.one_def ]
  |> SIMP_RULE(srw_ss())[Once FUN_EQ_THM,
        set_sepTheory.SEP_EXISTS_THM,set_sepTheory.cond_STAR,PULL_EXISTS]
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

val CommandLine_read16bit_spec = Q.store_thm("CommandLine_read16bit",
  `2 <= LENGTH a ==>
   app (p:'ffi ffi_proj) ^(fetch_v "CommandLine.read16bit" st) [av]
     (W8ARRAY av a)
     (POSTv v. W8ARRAY av a * & NUM (w2n (EL 0 a) + 256 * w2n (EL 1 a)) v)`,
  xcf "CommandLine.read16bit" st
  \\ xlet_auto THEN1 xsimpl
  \\ xlet_auto THEN1 (fs [] \\ xsimpl)
  \\ xlet_auto THEN1 (fs [] \\ xsimpl)
  \\ xlet_auto THEN1 (fs [] \\ xsimpl)
  \\ xlet_auto THEN1 (fs [] \\ xsimpl)
  \\ xapp \\ xsimpl
  \\ Cases_on `a` \\ fs [] \\ Cases_on `t` \\ fs [NUM_def]
  \\ rpt (asm_exists_tac \\ fs [])
  \\ Cases_on `h` \\ Cases_on `h'` \\ fs []
  \\ fs [INT_def] \\ intLib.COOPER_TAC);

val CommandLine_write16bit_spec = Q.store_thm("CommandLine_write16bit",
  `NUM n nv /\ 2 <= LENGTH a ==>
   app (p:'ffi ffi_proj) ^(fetch_v "CommandLine.write16bit" st) [av;nv]
     (W8ARRAY av a)
     (POSTv v. W8ARRAY av (n2w n::n2w (n DIV 256)::TL (TL a)))`,
  xcf "CommandLine.write16bit" st
  \\ xlet_auto THEN1 xsimpl
  \\ xlet_auto THEN1 (fs [] \\ xsimpl)
  \\ xlet_auto THEN1 (fs [] \\ xsimpl)
  \\ xlet_auto THEN1 (fs [] \\ xsimpl)
  \\ xapp \\ xsimpl
  \\ Cases_on `a` \\ fs [] \\ Cases_on `t` \\ fs [NUM_def]
  \\ rpt (asm_exists_tac \\ fs [])
  \\ EVAL_TAC);

val SUC_SUC_LENGTH = prove(
  ``SUC (SUC (LENGTH (TL (TL (REPLICATE (MAX 2 n) x))))) = (MAX 2 n)``,
  Cases_on `n` \\ fs [] THEN1 EVAL_TAC
  \\ Cases_on `n'` \\ fs [] THEN1 EVAL_TAC
  \\ fs [ADD1] \\ rw [MAX_DEF]
  \\ fs [EVAL ``REPLICATE 2 x``]
  \\ once_rewrite_tac [ADD_COMM]
  \\ rewrite_tac [GSYM REPLICATE_APPEND]
  \\ fs [EVAL ``REPLICATE 2 x``]);

val two_byte_sum = prove(
  ``k < 65536 ==> k MOD 256 + 256 * (k DIV 256) MOD 256 = k``,
  rw []
  \\ `(k DIV 256) MOD 256 = k DIV 256` by
        (match_mp_tac LESS_MOD \\ fs [DIV_LT_X,wfcl_def]) \\ fs []
  \\ `(k DIV 256) * 256 + k MOD 256 = k` by metis_tac [DIVISION,EVAL ``0 < 256n``]
  \\ fs []);

val LESS_LENGTH_EXISTS = prove(
  ``!xs n. n < LENGTH xs ==> ?ys y ts. xs = ys ++ y::ts /\ LENGTH ys = n``,
  Induct \\ fs [] \\ Cases_on `n` \\ fs []
  \\ rw [] \\ res_tac \\ fs [] \\ rveq \\ fs []
  \\ qexists_tac `h::ys` \\ fs []);

val DROP_SUC_LENGTH_MAP = prove(
  ``(DROP (SUC (LENGTH ys)) (MAP f ys ⧺ y::ts)) = ts``,
  qsuff_tac `MAP f ys ⧺ y::ts = (MAP f ys ⧺ [y]) ++ ts /\
             SUC (LENGTH ys) = LENGTH (MAP f ys ⧺ [y])`
  THEN1 simp_tac std_ss [DROP_LENGTH_APPEND] \\ fs []);

val CommandLine_cloop_spec = Q.store_thm("CommandLine_cloop_spec",
  `!n nv av cv a.
     LIST_TYPE STRING_TYPE (DROP n cl) cv /\
     NUM n nv /\ n <= LENGTH cl /\ LENGTH a = 2 ==>
     app (p:'ffi ffi_proj) ^(fetch_v "CommandLine.cloop" st) [av; nv; cv]
      (COMMANDLINE cl * W8ARRAY av a)
      (POSTv v. & LIST_TYPE STRING_TYPE cl v * COMMANDLINE cl)`,
  Induct \\ rw []
  THEN1
   (xcf "CommandLine.cloop" st
    \\ xlet_auto THEN1 xsimpl
    \\ xif \\ asm_exists_tac \\ fs []
    \\ xvar \\ xsimpl)
  \\ xcf "CommandLine.cloop" st
  \\ xlet_auto THEN1 xsimpl
  \\ xif \\ asm_exists_tac \\ fs []
  \\ rpt (xlet_auto THEN1 xsimpl)
  \\ fs [ADD1,intLib.COOPER_PROVE ``& (n+1) - 1 = (& n):int``,GSYM NUM_def]
  \\ qabbrev_tac `x = EL n cl`
  \\ fs [COMMANDLINE_def] \\ xpull
  \\ `(n DIV 256) * 256 + n MOD 256 = n` by metis_tac [DIVISION,EVAL ``0 < 256n``]
  \\ `(n DIV 256) MOD 256 = n DIV 256` by
        (match_mp_tac LESS_MOD \\ fs [DIV_LT_X,wfcl_def])
  \\ xlet `POSTv v.
       W8ARRAY av (n2w (strlen x)::n2w (strlen x DIV 256)::[]) * COMMANDLINE cl`
  THEN1
   (xffi
    \\ fs[cfHeapsBaseTheory.IOx_def,cl_ffi_part_def,COMMANDLINE_def]
    \\ xsimpl
    \\ qmatch_goalsub_abbrev_tac`IO s u ns`
    \\ map_every qexists_tac [`emp`, `s`, `s`, `u`, `ns`]
    \\ xsimpl
    \\ unabbrev_all_tac \\ fs []
    \\ fs[cfHeapsBaseTheory.mk_ffi_next_def,ffi_get_arg_length_def,
           GSYM cfHeapsBaseTheory.encode_list_def,LENGTH_EQ_NUM_compute]
    \\ fs [wfcl_def])
  \\ rpt (xlet_auto THEN1 xsimpl)
  \\ qmatch_goalsub_abbrev_tac`W8ARRAY av1 bytes`
  \\ `strlen x < 65536` by
       (fs [wfcl_def,SUC_SUC_LENGTH,Abbr`x`] \\ `n < LENGTH cl` by fs []
        \\ fs [EVERY_EL] \\ first_x_assum drule \\ fs [validArg_def])
  \\ xlet `POSTv v. W8ARRAY av1 (MAP (n2w o ORD) (explode x) ++ DROP (strlen x) bytes) *
       W8ARRAY av [n2w (strlen x); n2w (strlen x DIV 256)] * COMMANDLINE cl`
  THEN1 (xffi
    \\ fs[cfHeapsBaseTheory.IOx_def,cl_ffi_part_def,COMMANDLINE_def]
    \\ qabbrev_tac `extra = W8ARRAY av [n2w (strlen x); n2w (strlen x DIV 256)]`
    \\ xsimpl
    \\ qmatch_goalsub_abbrev_tac`IO s u ns`
    \\ map_every qexists_tac [`extra`, `s`, `s`, `u`, `ns`]
    \\ xsimpl
    \\ unabbrev_all_tac \\ fs []
    \\ fs[cfHeapsBaseTheory.mk_ffi_next_def,ffi_get_arg_def,
           GSYM cfHeapsBaseTheory.encode_list_def,LENGTH_EQ_NUM_compute]
    \\ fs [wfcl_def,SUC_SUC_LENGTH,two_byte_sum])
  \\ xlet_auto
  THEN1 (xsimpl \\ fs [SUC_SUC_LENGTH,two_byte_sum,mlstringTheory.LENGTH_explode])
  \\ xlet_auto THEN1 (xcon \\ xsimpl)
  \\ xapp
  \\ fs [COMMANDLINE_def] \\ xsimpl
  \\ fs [LENGTH_EQ_NUM_compute]
  \\ rveq \\ fs []
  \\ fs [GSYM LESS_EQ,GSYM ADD1]
  \\ drule LESS_LENGTH_EXISTS
  \\ strip_tac \\ rw [] \\ fs []
  \\ asm_rewrite_tac [DROP_LENGTH_APPEND]
  \\ fs [LIST_TYPE_def,DROP_SUC_LENGTH_MAP]
  \\ fs [two_byte_sum]
  \\ rfs [two_byte_sum]
  \\ qpat_x_assum `_ sv` mp_tac
  \\ `strlen x = LENGTH (MAP ((n2w:num->word8) ∘ ORD) (explode x))` by fs [mlstringTheory.LENGTH_explode]
  \\ asm_rewrite_tac [TAKE_LENGTH_APPEND]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND,EL_LENGTH_APPEND,NULL,HD]
  \\ fs [MAP_MAP_o, CHR_w2n_n2w_ORD, GSYM mlstringTheory.implode_def]
  \\ fs[DROP_APPEND,DROP_LENGTH_TOO_LONG]);

val CommandLine_cline_spec = Q.store_thm("CommandLine_cline_spec",
  `UNIT_TYPE u uv ==>
   app (p:'ffi ffi_proj) ^(fetch_v "CommandLine.cline" st) [uv]
    (COMMANDLINE cl)
    (POSTv v. & LIST_TYPE STRING_TYPE cl v * COMMANDLINE cl)`,
  xcf "CommandLine.cline" st
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ qmatch_goalsub_rename_tac `W8ARRAY av`
  \\ fs [EVAL ``REPLICATE 2 x``]
  \\ fs [COMMANDLINE_def]
  \\ xpull
  \\ xlet `POSTv v.
       (W8ARRAY av [n2w (LENGTH cl); n2w (LENGTH cl DIV 256)] * IOx cl_ffi_part cl)`
  THEN1
   (xffi
    \\ fs[cfHeapsBaseTheory.IOx_def,cl_ffi_part_def]
    \\ xsimpl
    \\ qmatch_goalsub_abbrev_tac`IO s u ns`
    \\ map_every qexists_tac [`emp`, `s`, `s`, `u`, `ns`]
    \\ xsimpl
    \\ unabbrev_all_tac \\ fs []
    \\ fs[cfHeapsBaseTheory.mk_ffi_next_def,ffi_get_arg_count_def,
           GSYM cfHeapsBaseTheory.encode_list_def]
    \\ fs [wfcl_def])
  \\ xlet_auto >- xsimpl
  \\ xlet_auto THEN1 (xcon \\ xsimpl)
  \\ xapp
  \\ fs [COMMANDLINE_def]
  \\ xsimpl
  \\ `LENGTH cl <= LENGTH cl` by fs []
  \\ asm_exists_tac \\ fs [] \\ xsimpl
  \\ `DROP (LENGTH cl) cl = []` by fs [DROP_NIL]
  \\ fs [LIST_TYPE_def]
  \\ fs [wfcl_def] \\ rfs [two_byte_sum]);

val hd_v_thm = fetch "ListProg" "hd_v_thm";
val mlstring_hd_v_thm = hd_v_thm |> INST_TYPE [alpha |-> mlstringSyntax.mlstring_ty]

val CommandLine_name_spec = Q.store_thm("CommandLine_name_spec",
  `UNIT_TYPE u uv ==>
    app (p:'ffi ffi_proj) ^(fetch_v "CommandLine.name" st) [uv]
    (COMMANDLINE cl)
    (POSTv namev. & STRING_TYPE (HD cl) namev * COMMANDLINE cl)`,
  xcf "CommandLine.name" st
  \\ xlet `POSTv vz. & UNIT_TYPE () vz * COMMANDLINE cl`
  >-(xcon \\ xsimpl)
  \\ xlet `POSTv cs. & LIST_TYPE STRING_TYPE cl cs * COMMANDLINE cl`
  >-(xapp \\ rw[])
  \\ Cases_on`cl=[]` >- ( fs[COMMANDLINE_def] \\ xpull \\ fs[wfcl_def] )
  \\ xapp_spec mlstring_hd_v_thm
  \\ xsimpl \\ instantiate \\ Cases_on `cl` \\ rw[]);

val tl_v_thm = fetch "ListProg" "tl_v_thm";
val mlstring_tl_v_thm = tl_v_thm |> INST_TYPE [alpha |-> mlstringSyntax.mlstring_ty]

val name_def = Define `
  name () = (\cl. (Success (HD cl), cl))`;

val EvalM_name = Q.store_thm("EvalM_name",
  `Eval env exp (UNIT_TYPE u) /\
    (nsLookup env.v (Long "CommandLine" (Short "name")) =
      SOME CommandLine_name_v) ==>
    EvalM F env st (App Opapp [Var (Long "CommandLine" (Short "name")); exp])
      (MONAD STRING_TYPE exc_ty (name u))
      (COMMANDLINE,p:'ffi ffi_proj)`,
  ho_match_mp_tac EvalM_from_app \\ rw [name_def]
  \\ metis_tac [CommandLine_name_spec]);

val CommandLine_arguments_spec = Q.store_thm("CommandLine_arguments_spec",
  `UNIT_TYPE u uv ==>
    app (p:'ffi ffi_proj) ^(fetch_v "CommandLine.arguments" st) [uv]
    (COMMANDLINE cl)
    (POSTv argv. & LIST_TYPE STRING_TYPE
       (TL cl) argv * COMMANDLINE cl)`,
  xcf "CommandLine.arguments" st
  \\ xlet `POSTv vz. & UNIT_TYPE () vz * COMMANDLINE cl`
  >-(xcon \\ xsimpl)
  \\ xlet `POSTv cs. & LIST_TYPE STRING_TYPE cl cs * COMMANDLINE cl`
  >-(xapp \\ rw[])
  \\ Cases_on`cl=[]` >- ( fs[COMMANDLINE_def] \\ xpull \\ fs[wfcl_def] )
  \\ xapp_spec mlstring_tl_v_thm \\ xsimpl \\ instantiate
  \\ Cases_on `cl` \\ rw[mllistTheory.tl_def]);

val arguments_def = Define `
  arguments () = (\cl. (Success (TL cl), cl))`

val EvalM_arguments = Q.store_thm("EvalM_arguments",
  `Eval env exp (UNIT_TYPE u) /\
    (nsLookup env.v (Long "CommandLine" (Short "arguments")) =
       SOME CommandLine_arguments_v) ==>
    EvalM F env st (App Opapp [Var (Long "CommandLine" (Short "arguments")); exp])
      (MONAD (LIST_TYPE STRING_TYPE) exc_ty (arguments u))
      (COMMANDLINE,p:'ffi ffi_proj)`,
  ho_match_mp_tac EvalM_from_app \\ rw [arguments_def]
  \\ metis_tac [CommandLine_arguments_spec]);

fun prove_hprop_inj_tac thm =
    rw[HPROP_INJ_def, GSYM STAR_ASSOC, SEP_CLAUSES, SEP_EXISTS_THM, HCOND_EXTRACT] >>
      EQ_TAC >-(DISCH_TAC >> IMP_RES_TAC thm >> rw[]) >> rw[];

val UNIQUE_COMMANDLINE = Q.store_thm("UNIQUE_COMMANDLINE",
  `!s cl1 cl2 H1 H2. VALID_HEAP s ==>
     (COMMANDLINE cl1 * H1) s /\ (COMMANDLINE cl2 * H2) s ==> cl2 = cl1`,
  rw[COMMANDLINE_def,cfHeapsBaseTheory.IOx_def,cl_ffi_part_def,
     GSYM STAR_ASSOC]
  \\ IMP_RES_TAC FRAME_UNIQUE_IO
  \\ fs[] \\ rw[]
  \\ metis_tac[decode_encode,SOME_11]);

val COMMANDLINE_HPROP_INJ = Q.store_thm("COMMANDLINE_HPROP_INJ[hprop_inj]",
  `!cl1 cl2. HPROP_INJ (COMMANDLINE cl1) (COMMANDLINE cl2) (cl2 = cl1)`,
  prove_hprop_inj_tac UNIQUE_COMMANDLINE);

val _ = export_theory();
