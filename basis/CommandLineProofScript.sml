(*
  Proof about the command-line module of the CakeML standard basis library.
*)
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

Theorem COMMANDLINE_FFI_part_hprop:
   FFI_part_hprop (COMMANDLINE x)
Proof
  rw [COMMANDLINE_def,cfHeapsBaseTheory.IO_def,cfMainTheory.FFI_part_hprop_def,
      cfHeapsBaseTheory.IOx_def, cl_ffi_part_def,
      set_sepTheory.SEP_CLAUSES,set_sepTheory.SEP_EXISTS_THM,
      set_sepTheory.cond_STAR ]
  \\ fs[set_sepTheory.one_def]
QED

val eq_v_thm = fetch "mlbasicsProg" "eq_v_thm"
val eq_num_v_thm = MATCH_MP (DISCH_ALL eq_v_thm) (EqualityType_NUM_BOOL |> CONJUNCT1)

Theorem CommandLine_read16bit:
   2 <= LENGTH a ==>
   app (p:'ffi ffi_proj) CommandLine_read16bit_v [av]
     (W8ARRAY av a)
     (POSTv v. W8ARRAY av a * & NUM (w2n (EL 0 a) + 256 * w2n (EL 1 a)) v)
Proof
  xcf_with_def "CommandLine.read16bit" CommandLine_read16bit_v_def
  \\ xlet_auto THEN1 xsimpl
  \\ xlet_auto THEN1 (fs [] \\ xsimpl)
  \\ xlet_auto THEN1 (fs [] \\ xsimpl)
  \\ xlet_auto THEN1 (fs [] \\ xsimpl)
  \\ xlet_auto THEN1 (fs [] \\ xsimpl)
  \\ xapp \\ xsimpl
  \\ Cases_on `a` \\ fs [] \\ Cases_on `t` \\ fs [NUM_def]
  \\ rpt (asm_exists_tac \\ fs [])
  \\ Cases_on `h` \\ Cases_on `h'` \\ fs []
  \\ fs [INT_def] \\ intLib.COOPER_TAC
QED

Theorem CommandLine_write16bit:
   NUM n nv /\ 2 <= LENGTH a ==>
   app (p:'ffi ffi_proj) CommandLine_write16bit_v [av;nv]
     (W8ARRAY av a)
     (POSTv v. W8ARRAY av (n2w n::n2w (n DIV 256)::TL (TL a)))
Proof
  xcf_with_def "CommandLine.write16bit" CommandLine_write16bit_v_def
  \\ xlet_auto THEN1 xsimpl
  \\ xlet_auto THEN1 (fs [] \\ xsimpl)
  \\ xlet_auto THEN1 (fs [] \\ xsimpl)
  \\ xlet_auto THEN1 (fs [] \\ xsimpl)
  \\ xapp \\ xsimpl
  \\ Cases_on `a` \\ fs [] \\ Cases_on `t` \\ fs [NUM_def]
  \\ rpt (asm_exists_tac \\ fs [])
  \\ EVAL_TAC
QED

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

Theorem CommandLine_cloop_spec:
   !n nv av cv a.
     LIST_TYPE STRING_TYPE (DROP n cl) cv /\
     NUM n nv /\ n <= LENGTH cl /\ LENGTH a = 2 ==>
     app (p:'ffi ffi_proj) CommandLine_cloop_v [av; nv; cv]
      (COMMANDLINE cl * W8ARRAY av a)
      (POSTv v. & LIST_TYPE STRING_TYPE cl v * COMMANDLINE cl)
Proof
  rw [] \\ qpat_abbrev_tac `Q = $POSTv _`
  \\ simp [COMMANDLINE_def, cl_ffi_part_def, IOx_def, IO_def]
  \\ xpull \\ qunabbrev_tac `Q`
  \\ rpt (pop_assum mp_tac)
  \\ MAP_EVERY qid_spec_tac [`events`, `a`, `cv`, `av`, `nv`, `n`]
  \\ Induct \\ rw []
  THEN1
   (xcf_with_def "CommandLine.cloop" CommandLine_cloop_v_def
    \\ xlet_auto THEN1 xsimpl
    \\ xif \\ asm_exists_tac \\ fs []
    \\ xvar \\ fs [COMMANDLINE_def, cl_ffi_part_def, IOx_def, IO_def]
    \\ xsimpl \\ qexists_tac `events` \\ xsimpl)
  \\ xcf_with_def "CommandLine.cloop" CommandLine_cloop_v_def
  \\ xlet_auto THEN1 xsimpl
  \\ xif \\ asm_exists_tac \\ fs []
  \\ rpt (xlet_auto THEN1 xsimpl)
  \\ fs [ADD1,intLib.COOPER_PROVE ``& (n+1) - 1 = (& n):int``,GSYM NUM_def]
  \\ qabbrev_tac `x = EL n cl`
  \\ `(n DIV 256) * 256 + n MOD 256 = n` by metis_tac [DIVISION,EVAL ``0 < 256n``]
  \\ `(n DIV 256) MOD 256 = n DIV 256` by
        (match_mp_tac LESS_MOD \\ fs [DIV_LT_X,wfcl_def])
  \\ xlet `POSTv v.
       W8ARRAY av (n2w (strlen x)::n2w (strlen x DIV 256)::[]) * COMMANDLINE cl`
  THEN1
   (xffi
    \\ fs[cfHeapsBaseTheory.IOx_def,cl_ffi_part_def,COMMANDLINE_def,IO_def]
    \\ xsimpl
    \\ qmatch_goalsub_abbrev_tac `FFI_part s u ns`
    \\ map_every qexists_tac [`emp`, `s`, `u`, `ns`, `events`]
    \\ xsimpl
    \\ unabbrev_all_tac \\ fs []
    \\ fs[cfHeapsBaseTheory.mk_ffi_next_def,ffi_get_arg_length_def,
           GSYM cfHeapsBaseTheory.encode_list_def,LENGTH_EQ_NUM_compute]
    \\ fs [wfcl_def] \\ xsimpl
    \\ qpat_abbrev_tac `new_events = events ++ _`
    \\ qexists_tac `new_events` \\ xsimpl)
  \\ rpt (xlet_auto THEN1 xsimpl)
  \\ qmatch_goalsub_abbrev_tac`W8ARRAY av1 bytes`
  \\ `strlen x < 65536` by
       (fs [wfcl_def,SUC_SUC_LENGTH,Abbr`x`] \\ `n < LENGTH cl` by fs []
        \\ fs [EVERY_EL] \\ first_x_assum drule \\ fs [validArg_def])
  \\ xlet `POSTv v. W8ARRAY av1 (MAP (n2w o ORD) (explode x) ++ DROP (strlen x) bytes) *
       W8ARRAY av [n2w (strlen x); n2w (strlen x DIV 256)] * COMMANDLINE cl`
  THEN1
   (qpat_abbrev_tac `Q = $POSTv _`
    \\ simp [COMMANDLINE_def,cl_ffi_part_def,IOx_def,IO_def]
    \\ xpull \\ qunabbrev_tac `Q`
    \\ xffi
    \\ fs[cfHeapsBaseTheory.IOx_def,cl_ffi_part_def,COMMANDLINE_def,IO_def]
    \\ qabbrev_tac `extra = W8ARRAY av [n2w (strlen x); n2w (strlen x DIV 256)]`
    \\ xsimpl
    \\ qmatch_goalsub_abbrev_tac `FFI_part s u ns`
    \\ map_every qexists_tac [`extra`, `s`, `u`, `ns`, `events`]
    \\ xsimpl
    \\ unabbrev_all_tac \\ fs []
    \\ fs[cfHeapsBaseTheory.mk_ffi_next_def,ffi_get_arg_def,
           GSYM cfHeapsBaseTheory.encode_list_def,LENGTH_EQ_NUM_compute]
    \\ fs [wfcl_def,SUC_SUC_LENGTH,two_byte_sum] \\ xsimpl
    \\ qpat_abbrev_tac `new_events = events ++ _`
    \\ qexists_tac `new_events` \\ xsimpl)
  \\ xlet_auto
  THEN1 (xsimpl \\ fs [SUC_SUC_LENGTH,two_byte_sum,mlstringTheory.LENGTH_explode])
  \\ xlet_auto THEN1 (xcon \\ xsimpl)
  \\ qpat_abbrev_tac `Q = $POSTv _`
  \\ simp [COMMANDLINE_def,cl_ffi_part_def,IOx_def,IO_def]
  \\ xpull \\ qunabbrev_tac `Q`
  \\ xapp
  \\ GEN_EXISTS_TAC "events'" `events`
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
  \\ fs[DROP_APPEND,DROP_LENGTH_TOO_LONG]
QED

Theorem CommandLine_cline_spec:
   UNIT_TYPE u uv ==>
   app (p:'ffi ffi_proj) CommandLine_cline_v [uv]
    (COMMANDLINE cl)
    (POSTv v. & LIST_TYPE STRING_TYPE cl v * COMMANDLINE cl)
Proof
  rw [] \\ qpat_abbrev_tac `Q = $POSTv _`
  \\ simp [COMMANDLINE_def,cl_ffi_part_def,IOx_def,IO_def]
  \\ xpull \\ qunabbrev_tac `Q`
  \\ xcf_with_def "CommandLine.cline" CommandLine_cline_v_def
  \\ fs [UNIT_TYPE_def] \\ rveq
  \\ xmatch
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ qmatch_goalsub_rename_tac `W8ARRAY av`
  \\ fs [EVAL ``REPLICATE 2 x``]
  \\ fs [COMMANDLINE_def]
  \\ xlet `POSTv v.
       (W8ARRAY av [n2w (LENGTH cl); n2w (LENGTH cl DIV 256)] * IOx cl_ffi_part cl)`
  THEN1
   (xffi
    \\ fs[cfHeapsBaseTheory.IOx_def,cl_ffi_part_def,IO_def]
    \\ xsimpl
    \\ qmatch_goalsub_abbrev_tac `FFI_part s u ns`
    \\ map_every qexists_tac [`emp`, `s`, `u`, `ns`, `events`]
    \\ xsimpl
    \\ unabbrev_all_tac \\ fs []
    \\ fs[cfHeapsBaseTheory.mk_ffi_next_def,ffi_get_arg_count_def,
           GSYM cfHeapsBaseTheory.encode_list_def]
    \\ fs [wfcl_def] \\ xsimpl
    \\ qpat_abbrev_tac `new_events = events ++ _`
    \\ qexists_tac `new_events` \\ xsimpl)
  \\ xlet_auto >- xsimpl
  \\ xlet_auto THEN1 (xcon \\ xsimpl)
  \\ qpat_abbrev_tac `Q = $POSTv _`
  \\ simp [cl_ffi_part_def,IOx_def,IO_def]
  \\ xpull \\ qunabbrev_tac `Q`
  \\ xapp
  \\ fs [COMMANDLINE_def, cl_ffi_part_def, IOx_def, IO_def]
  \\ xsimpl \\ fs [PULL_EXISTS]
  \\ GEN_EXISTS_TAC "x" `events` \\ xsimpl
  \\ `LENGTH cl <= LENGTH cl` by fs []
  \\ asm_exists_tac \\ fs [] \\ xsimpl
  \\ `DROP (LENGTH cl) cl = []` by fs [DROP_NIL]
  \\ fs [LIST_TYPE_def]
  \\ fs [wfcl_def] \\ rfs [two_byte_sum]
  \\ rw [] \\ qexists_tac `x` \\ xsimpl
QED

val hd_v_thm = fetch "ListProg" "hd_v_thm";
val mlstring_hd_v_thm = hd_v_thm |> INST_TYPE [alpha |-> mlstringSyntax.mlstring_ty]

Theorem CommandLine_name_spec:
   UNIT_TYPE u uv ==>
    app (p:'ffi ffi_proj) CommandLine_name_v [uv]
    (COMMANDLINE cl)
    (POSTv namev. & STRING_TYPE (HD cl) namev * COMMANDLINE cl)
Proof
  xcf_with_def "CommandLine.name" CommandLine_name_v_def
  \\ xlet `POSTv cs. & LIST_TYPE STRING_TYPE cl cs * COMMANDLINE cl`
  >-(xapp \\ rw[] \\ fs [])
  \\ Cases_on`cl=[]` >- ( fs[COMMANDLINE_def] \\ xpull \\ fs[wfcl_def] )
  \\ xapp_spec mlstring_hd_v_thm
  \\ xsimpl \\ instantiate \\ Cases_on `cl` \\ rw[]
QED

val tl_v_thm = fetch "ListProg" "tl_v_thm";
val mlstring_tl_v_thm = tl_v_thm |> INST_TYPE [alpha |-> mlstringSyntax.mlstring_ty]

val name_def = Define `
  name () = (\cl. (Success (HD cl), cl))`;

Theorem EvalM_name:
   Eval env exp (UNIT_TYPE u) /\
    (nsLookup env.v (Long "CommandLine" (Short "name")) =
      SOME CommandLine_name_v) ==>
    EvalM F env st (App Opapp [Var (Long "CommandLine" (Short "name")); exp])
      (MONAD STRING_TYPE exc_ty (name u))
      (COMMANDLINE,p:'ffi ffi_proj)
Proof
  ho_match_mp_tac EvalM_from_app \\ rw [name_def]
  \\ metis_tac [CommandLine_name_spec]
QED

Theorem CommandLine_arguments_spec:
   UNIT_TYPE u uv ==>
    app (p:'ffi ffi_proj) CommandLine_arguments_v [uv]
    (COMMANDLINE cl)
    (POSTv argv. & LIST_TYPE STRING_TYPE
       (TL cl) argv * COMMANDLINE cl)
Proof
  xcf_with_def "CommandLine.arguments" CommandLine_arguments_v_def
  \\ xlet `POSTv cs. & LIST_TYPE STRING_TYPE cl cs * COMMANDLINE cl`
  >-(xapp \\ rw[] \\ fs [])
  \\ Cases_on`cl=[]` >- ( fs[COMMANDLINE_def] \\ xpull \\ fs[wfcl_def] )
  \\ xapp_spec mlstring_tl_v_thm \\ xsimpl \\ instantiate
  \\ Cases_on `cl` \\ rw[TL_DEF]
QED

val arguments_def = Define `
  arguments () = (\cl. (Success (TL cl), cl))`

Theorem EvalM_arguments:
   Eval env exp (UNIT_TYPE u) /\
    (nsLookup env.v (Long "CommandLine" (Short "arguments")) =
       SOME CommandLine_arguments_v) ==>
    EvalM F env st (App Opapp [Var (Long "CommandLine" (Short "arguments")); exp])
      (MONAD (LIST_TYPE STRING_TYPE) exc_ty (arguments u))
      (COMMANDLINE,p:'ffi ffi_proj)
Proof
  ho_match_mp_tac EvalM_from_app \\ rw [arguments_def]
  \\ metis_tac [CommandLine_arguments_spec]
QED

fun prove_hprop_inj_tac thm =
    rw[HPROP_INJ_def, GSYM STAR_ASSOC, SEP_CLAUSES, SEP_EXISTS_THM, HCOND_EXTRACT] >>
      EQ_TAC >-(DISCH_TAC >> IMP_RES_TAC thm >> rw[]) >> rw[];

Theorem UNIQUE_COMMANDLINE:
   !s cl1 cl2 H1 H2. VALID_HEAP s ==>
     (COMMANDLINE cl1 * H1) s /\ (COMMANDLINE cl2 * H2) s ==> cl2 = cl1
Proof
  rw[COMMANDLINE_def,cfHeapsBaseTheory.IOx_def,cl_ffi_part_def,
     GSYM STAR_ASSOC]
  \\ IMP_RES_TAC FRAME_UNIQUE_IO
  \\ fs[] \\ rw[]
  \\ metis_tac[decode_encode,SOME_11]
QED

Theorem COMMANDLINE_HPROP_INJ[hprop_inj]:
   !cl1 cl2. HPROP_INJ (COMMANDLINE cl1) (COMMANDLINE cl2) (cl2 = cl1)
Proof
  prove_hprop_inj_tac UNIQUE_COMMANDLINE
QED

val _ = export_theory();
