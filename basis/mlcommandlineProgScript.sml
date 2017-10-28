open preamble
     ml_translatorLib ml_progLib ml_translatorTheory
     cfTheory cfHeapsTheory cfTacticsLib cfTacticsBaseLib basisFunctionsLib
     cfLetAutoTheory mlarrayProgTheory commandLineFFITheory

val _ = new_theory "mlcommandlineProg";

val _ = translation_extends "mlarrayProg";

val _ = option_monadsyntax.temp_add_option_monadsyntax();

(* TODO: where should these be defined? They are not necessary if we have
concrete syntax for FFI calls (issue #161) *)
val Apps_def = tDefine "Apps" `
  (Apps [x;y] = App Opapp [x;y]) /\
  (Apps [] = ARB) /\
  (Apps xs = App Opapp [Apps (FRONT xs); LAST xs])`
  (WF_REL_TAC `measure LENGTH` \\ fs [LENGTH_FRONT]);

val LetApps_def = Define `
  LetApps n f args = Let (SOME n) (Apps (Var f::args))`;
(* -- *)

val _ = ml_prog_update (open_module "Commandline")
val e = ``(App Aw8alloc [Lit (IntLit 256); Lit (Word8 0w)])``

val _ = ml_prog_update (add_Dlet (derive_eval_thm "commandLine_state" e) "commandLine_state" [])

val w8arrayToStrings = process_topdecs
  `fun w8arrayToStrings arr =
    let
      val arrayList = List.tabulate (Word8Array.length arr) (fn x => Char.chr (Word8.toInt (Word8Array.sub arr x)))
      val arrayString = String.implode arrayList
      fun f x = (Char.ord x = 0)
    in String.tokens f arrayString end`

val res = ml_prog_update (ml_progLib.add_prog w8arrayToStrings pick_name)

val e =
  ``LetApps "cs" (Long "Word8Array" (Short "array")) [Lit (IntLit 256); Lit (Word8 0w)] (
      Let NONE (App (FFI "getArgs") [Lit (StrLit ""); Var (Short "cs")])
        (Apps [Var (Short "w8arrayToStrings"); Var (Short "cs")]))``
  |> EVAL |> concl |> rand

val _ = ml_prog_update(add_Dlet_Fun ``"cline"`` ``"u"`` e "cline_v")

val name = process_topdecs `fun name u = List.hd (cline ())`

val _ = ml_prog_update(ml_progLib.add_prog name pick_name)

val arguments = process_topdecs `fun arguments u = List.tl (cline ())`

val _ = ml_prog_update(ml_progLib.add_prog arguments pick_name)

val _ = ml_prog_update (close_module NONE);

val wfcl_def = Define`
  wfcl cl ⇔ EVERY validArg cl ∧ ¬NULL cl ∧ SUM (MAP LENGTH cl) + LENGTH cl <= 256`;

val COMMANDLINE_def = Define `
  COMMANDLINE cl =
    IOx commandLine_ffi_part cl * &wfcl cl`

val set_thm =
  COMMANDLINE_def
  |> SIMP_RULE(srw_ss())[
       cfHeapsBaseTheory.IOx_def,commandLine_ffi_part_def,
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
      cfHeapsBaseTheory.IOx_def, commandLine_ffi_part_def,
      set_sepTheory.SEP_CLAUSES,set_sepTheory.SEP_EXISTS_THM,
      set_sepTheory.cond_STAR ]
  \\ fs[set_sepTheory.one_def]);

val eq_v_thm = fetch "mlbasicsProg" "eq_v_thm"
val eq_num_v_thm = MATCH_MP (DISCH_ALL eq_v_thm) (EqualityType_NUM_BOOL |> CONJUNCT1)

val st = get_ml_prog_state();

val w8arrayToStrings_spec = Q.store_thm ("w8arrayToStrings_spec",
    `!av a.
        app (p:'ffi ffi_proj) ^(fetch_v "Commandline.w8arrayToStrings" st) [av]
        (W8ARRAY av a)
        (POSTv strlv. &LIST_TYPE STRING_TYPE (tokens (\x. x = (CHR 0)) (implode (MAP (CHR o w2n) a))) strlv * W8ARRAY av a)`,
    xcf "Commandline.w8arrayToStrings" st
    \\ xfun_spec `e`
      `!x xv.
        NUM x xv /\ x < LENGTH a ==>
        app p e [xv]
        (W8ARRAY av a)
        (POSTv wordv. &CHAR (CHR (w2n (EL x a))) wordv * W8ARRAY av a)`
      >-(rpt strip_tac \\ first_x_assum match_mp_tac
        \\ xlet `POSTv subv. & WORD (EL x a) subv * W8ARRAY av a`
          >-(xapp \\ fs[])
        \\ xlet `POSTv intv. & NUM (w2n (EL x a)) intv * W8ARRAY av a`
          >-(xapp \\ xsimpl \\ instantiate)
        \\ xapp \\ xsimpl \\ instantiate \\ rw[w2n_lt_256])
      \\ xlet `POSTv lenv. & NUM (LENGTH a) lenv * W8ARRAY av a`
        >-(xapp)
      \\ xlet `POSTv lv. &LIST_TYPE CHAR (MAP (CHR o w2n) a) lv * W8ARRAY av a`
      >-(
        xapp
        \\ simp[LIST_EQ_REWRITE,EL_MAP]
        \\ qexists_tac`\x. CHR(w2n(EL x a))`
        \\ simp[]
      )
      \\ xlet `POSTv strv. &STRING_TYPE (implode (MAP (CHR o w2n) a)) strv * W8ARRAY av a`
        >-(xapp \\ xsimpl \\ instantiate)
      \\ xfun_spec `g`
          `(CHAR --> BOOL) (\x. x = (CHR 0)) g`
          >- (
            Q.ISPEC_THEN`p`(fn th => CONV_TAC(REWR_CONV th)) (Q.GEN`p`cfAppTheory.Arrow_eq_app_basic)
            \\ fs[cfAppTheory.app_def] \\ rw[]
            \\ first_x_assum match_mp_tac
            \\ xlet `POSTv cordv. &NUM (ORD x) cordv`
            >- ( xapp \\ fs[] )
            \\ xapp_spec eq_num_v_thm \\ xsimpl \\ instantiate
            \\ fs[BOOL_def]
            \\ Cases_on`x` \\ fs[] )
      \\ xapp \\ xsimpl \\ instantiate);


val map_app_last_thm = Q.prove(
  `!ls a. ls <> [] ==> (FLAT(MAP (\x. x ++ [a]) ls) = FLAT(MAP (\x. x ++ [a]) (BUTLAST ls)) ++ (LAST ls) ++ [a])`,
  Induct \\ rw[] \\ first_x_assum(qspecl_then [`a`] mp_tac) \\ Cases_on `ls` \\ rw[]
);

val map_app_last_Str = Q.prove(
  `!ls. ls <> [] ==>
      CONCAT(MAP(\s. STRCAT s "\^@") (ls)) = FRONT(CONCAT(MAP(\s. STRCAT (s) "\^@") (ls))) ++ [CHR 0]`,
  Induct \\ rw[] \\ Cases_on `ls` \\ rw[FRONT_APPEND]
  \\ simp_tac std_ss [GSYM APPEND_ASSOC, GSYM CONS_APPEND, FRONT_APPEND] \\ rw[]
  \\ rw[FRONT_DEF]
);

val TOKENS_MAP_inv = Q.store_thm ("TOKENS_MAP_inv",
`!ls P l1. (P = (\x. x = #"\^@")) /\ EVERY validArg ls /\ l1 = (FLAT (MAP (\s. s ++ "\^@") ls)) ==>
 (TOKENS P l1 = ls)`,
  gen_tac \\ Induct_on `ls`
  \\ rw[TOKENS_def] \\ Cases_on `h` \\ fs[validArg_def]
  \\ rw[TOKENS_def]
  \\ pairarg_tac \\ fs[NULL_EQ]
  \\ rw[]
  >-(imp_res_tac SPLITP_NIL_IMP \\ fs[validArg_def])
  \\ (Cases_on `r`
    >-(imp_res_tac SPLITP_NIL_SND_EVERY \\ fs[])
    \\ fs[SPLITP] \\ rfs[]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ fs[SPLITP_APPEND]
    \\ Cases_on `EXISTS (\x. x = #"\^@") t` >- (full_simp_tac std_ss [EVERY_NOT_EXISTS])
    \\ full_simp_tac std_ss [] \\ fs[SPLITP])
  \\ rw[TOKENS_START]
);

val TOKENS_FRONT_MAP = Q.prove(
  `!ls. ls <> [] ==> TOKENS (\x. x = #"\^@") (FRONT (FLAT (MAP (\x. x ++ "\^@") ls))) = TOKENS (\x. x = #"\^@") (FLAT (MAP (\x. x ++ "\^@") ls))`,
  rw[map_app_last_thm, TOKENS_END, FRONT_APPEND]
);


val TOKENS_FRONT_MAP_inv = Q.store_thm ("TOKENS_MAP_inv",
  `!ls P. (P = (\x. x = #"\^@")) /\ EVERY validArg ls /\ ls <> []==> TOKENS P (FRONT(FLAT (MAP (\s. s ++ "\^@") ls))) = ls`,
  rw[TOKENS_FRONT_MAP, TOKENS_MAP_inv]
);

val Commandline_cline_spec = Q.store_thm("Commandline_cline_spec",
  `UNIT_TYPE u uv ==>
    app (p:'ffi ffi_proj) ^(fetch_v "Commandline.cline" st) [uv]
    (COMMANDLINE cl)
    (POSTv clinev. & LIST_TYPE STRING_TYPE (MAP implode  cl) clinev * COMMANDLINE cl)`,
    xcf "Commandline.cline" st
    \\ xlet `POSTv cs. W8ARRAY cs (REPLICATE 256 (n2w 0)) * COMMANDLINE cl`
      >-(xapp \\ xsimpl)
    \\ fs [COMMANDLINE_def]
    \\ xpull
    \\ qabbrev_tac`l = MAP ((n2w:num -> word8) o ORD) (FLAT (MAP (\s. s ++ [CHR 0]) cl))`
    \\ `LENGTH l < 257`
    by (
      fs[Abbr`l`,wfcl_def,LENGTH_FLAT,MAP_MAP_o,o_DEF] \\
      Q.ISPEC_THEN`STRLEN`mp_tac SUM_MAP_PLUS \\
      disch_then(qspec_then`K 1`mp_tac) \\ simp[MAP_K_REPLICATE,SUM_REPLICATE] )
    \\ xlet `POSTv zv. W8ARRAY cs (l ++ DROP (LENGTH l) (REPLICATE 256 (n2w 0))) * & (UNIT_TYPE () zv) * COMMANDLINE cl`
    >-(xffi \\ fs [COMMANDLINE_def,cfHeapsBaseTheory.IOx_def,commandLine_ffi_part_def]
       \\ qmatch_goalsub_abbrev_tac`IO s u ns`
      \\ map_every qexists_tac [`REPLICATE 256 (n2w 0)`,  `emp`, `l ++ DROP (LENGTH l) (REPLICATE 256 (n2w 0))`,
                                `s`, `s`, `u`, `ns`]
      \\ xsimpl
      \\ fs[Abbr`u`,Abbr`ns`,cfHeapsBaseTheory.mk_ffi_next_def,ffi_getArgs_def,decode_def,GSYM cfHeapsBaseTheory.encode_list_def]
      \\ simp[EVERY_MAP, LENGTH_REPLICATE, Abbr`l`]
      \\ rw[Abbr`s`,encode_def] \\ fs[EVERY_REPLICATE])
    \\ xapp \\ xsimpl \\ gen_tac \\ strip_tac
    \\  reverse (conj_tac)  >-(fs[COMMANDLINE_def] \\ xsimpl)
    \\ pop_assum mp_tac
    \\ simp[MAP_MAP_o, CHR_w2n_n2w_ORD,Abbr`l`]
    \\ simp[GSYM MAP_MAP_o]
    \\ `cl <> []` by fs[wfcl_def,NULL_EQ]
    \\ drule map_app_last_Str
    \\ disch_then SUBST_ALL_TAC
    \\ simp[mlstringTheory.implode_STRCAT, GSYM mlstringTheory.str_def, mlstringTheory.strcat_assoc, mlstringTheory.tokens_append]
    \\ qmatch_abbrev_tac`_ _ l1 _ ==> _ _ l2 _`
    \\ `l1 = l2` suffices_by rw[]
    \\ simp[Abbr`l1`,Abbr`l2`]
    \\ Q.ISPEC_THEN`explode`match_mp_tac INJ_MAP_EQ
    \\ simp[MAP_MAP_o, INJ_DEF, mlstringTheory.explode_11, o_DEF, mlstringTheory.explode_implode, mlstringTheory.TOKENS_eq_tokens_sym]
    \\ qmatch_abbrev_tac`TOKENS P l1 ++ TOKENS P l2 = _`
    \\ `TOKENS P l2 = []`
    by (
      simp[TOKENS_NIL,Abbr`l2`,EVERY_MAP,EVERY_MEM]
      \\ rw[] \\ imp_res_tac MEM_DROP_IMP
      \\ imp_res_tac MEM_REPLICATE_IMP \\ fs[Abbr`P`] )
    \\ simp[Abbr`l1`,Abbr`P`]
    \\ match_mp_tac TOKENS_FRONT_MAP_inv
    \\ simp[]
    \\ fs[wfcl_def]
);


val hd_v_thm = fetch "mllistProg" "hd_v_thm";
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

val tl_v_thm = fetch "mllistProg" "tl_v_thm";
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
rw[COMMANDLINE_def, cfHeapsBaseTheory.IOx_def, commandLine_ffi_part_def, encode_def, cfHeapsBaseTheory.encode_list_def, GSYM STAR_ASSOC] >>
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
