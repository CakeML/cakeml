open preamble
     ml_translatorLib ml_progLib miscTheory
     cfTheory cfHeapsTheory cfTacticsLib cfTacticsBaseLib basisFunctionsLib
     mlcharioProgTheory ml_progLib ml_translatorTheory

val _ = new_theory "mlcommandLineProg";

val _ = translation_extends "mlcharioProg";

val _ = ml_prog_update (open_module "commandLine")
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
  ``LetApps "cs" (Long "Word8Array" "array") [Lit (IntLit 256); Lit (Word8 0w)] (
      Let NONE (App (FFI "getArgs") [Var (Short "cs")])
        (Apps [Var (Short "w8arrayToStrings"); Var (Short "cs")]))``
  |> EVAL |> concl |> rand

val _ = ml_prog_update(add_Dlet_Fun ``"cline"`` ``"u"`` e "cline_v")

val name = process_topdecs `fun name u = List.hd (cline ())`

val _ = ml_prog_update(ml_progLib.add_prog name pick_name)

val arguments = process_topdecs `fun arguments u = List.tl (cline ())`
      
val _ = ml_prog_update(ml_progLib.add_prog arguments pick_name)

(*
val e =
  ``Let NONE (App (FFI "getArgs") [Var (Short "commandLine_state")])
      (LetApps "ss" (Short "w8arrayToStrings") [Var (Short "commandLine_state")]
        (Apps [Var (Long "List" "hd"); Var (Short "ss")]))``
  |> EVAL |> concl |> rand

val _ = ml_prog_update(add_Dlet_Fun ``"name"`` ``"u"`` e "name_v")

val e =
  ``Let NONE (App (FFI "getArgs") [Var (Short "commandLine_state")])
      (LetApps "ss" (Short "w8arrayToStrings") [Var (Short "commandLine_state")]
        (Apps [Var (Long "List" "tl"); Var (Short "ss")]))``
  |> EVAL |> concl |> rand

val _ = ml_prog_update(add_Dlet_Fun ``"arguments"`` ``"u"`` e "arguments_v")
*)
val _ = ml_prog_update (close_module NONE);


(* TODO: define more generally (it's used in cat example too I think) *)
val destStr_def = Define`destStr (Str s) = s`;
val isStr_def = Define`(isStr (Str _) = T) ∧ (isStr _ = F)`;
 val _ = export_rewrites["isStr_def","destStr_def"];

val commandLine_fun_def = Define `
  commandLine_fun = (\i bytes s. case (bytes,s) of
      | (b, List commandLineStrings) =>
        if i = "getArgs" ∧ LENGTH b = 256 ∧ EVERY isStr commandLineStrings then
            let commandLine = FLAT (MAP (\s. destStr s ++ [CHR 0]) commandLineStrings) in
            if (LENGTH commandLine < 257) then 
              SOME (((MAP (n2w o ORD) commandLine) ++ DROP (LENGTH commandLine) b), List commandLineStrings)
            else
              SOME ((MAP (n2w o ORD) (TAKE 256 commandLine)), List commandLineStrings)
        else NONE 
      | _ => NONE)`

(*
val COMMANDLINE_def = Define `
  COMMANDLINE (cl:string list) =
    IO (List (MAP Str cl)) commandLine_fun ["getArgs"] *
    SEP_EXISTS w. W8ARRAY commandLine_state w * &(LENGTH w = 256)` 
*)

val COMMANDLINE_def = Define `
  COMMANDLINE (cl:string list) =
    IO (List (MAP Str cl)) commandLine_fun ["getArgs"]`
 
val st = get_ml_prog_state()
(*
options:
  - ask Magnus + Armael how to prove the spec below
  - write/use a custom (non higher-order) version of tabulate for this module instead
*)

val tabulate_spec = Q.store_thm("tabulate_spec",
  `!f fv A heap_inv n nv.
    NUM n nv /\ ls = GENLIST f n /\
    (!i iv. NUM i iv /\ i < n ==> app p fv [iv] heap_inv (POSTv v. &(A (f i) v) * heap_inv))
    ==>
    app p ^(fetch_v "List.tabulate" st) [nv; fv] heap_inv (POSTv lv. &LIST_TYPE A ls lv * heap_inv)`,
    cheat);

(*
  can't prove this with xcf because tabulate comes from the translator so is
  not in A normal form, but CF tactics require code in A normal form

  ntac 4 gen_tac
  \\ Induct
  >- (
    rw[]
    \\ xcf "List.tabulate" st
    \\ xpull_check_not_needed
    \\ head_unfold cf_if_def
    \\ irule local_elim
    \\ hnf
    \\ CONV_TAC(STRIP_QUANT_CONV(LAND_CONV(reduce_conv)))

    \\ app_
    val (asl,w) = top_goal()
    spec_kind_for (#2 (goal_app_infos w))
    xapp_spec
    rw[app_def]
    DB.find"exp2v_def"
    app_basic_def
    hide_environments false
*)

val eq_v_thm = fetch "mlbasicsProg" "eq_v_thm"
val eq_num_v_thm = save_thm("eq_num_v_thm",
        MATCH_MP (DISCH_ALL eq_v_thm) (EqualityType_NUM_BOOL |> CONJUNCT1))

val w8arrayToStrings_spec = Q.store_thm ("w8arrayToStrings_spec",
    `!av a.
        app (p:'ffi ffi_proj) ^(fetch_v "commandLine.w8arrayToStrings" st) [av]
        (W8ARRAY av a)
        (POSTv strlv. &LIST_TYPE STRING_TYPE (tokens (\x. x = (CHR 0)) (implode (MAP (CHR o w2n) a))) strlv * W8ARRAY av a)`,
    xcf "commandLine.w8arrayToStrings" st
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
           (*
           `MAP (CHR o w2n) a = GENLIST (\x. CHR(w2n(EL x a))) (LENGTH a)` by simp[LIST_EQ_REWRITE,EL_MAP]
           \\ pop_assum SUBST1_TAC
           *)
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
      CONCAT(MAP(\s. STRCAT (destStr s) "\^@") (MAP Str ls)) = FRONT(CONCAT(MAP(\s. STRCAT (destStr s) "\^@") (MAP Str ls))) ++ [CHR 0]`,
  Induct \\ rw[] \\ Cases_on `ls` \\ rw[FRONT_APPEND] 
  \\ simp_tac std_ss [GSYM APPEND_ASSOC, GSYM CONS_APPEND, FRONT_APPEND] \\ rw[]
  \\ rw[FRONT_DEF]
);

val CHR_w2n_n2w_ORD = Q.prove(
  `(CHR o w2n o (n2w:num->word8) o ORD) = I`,
  rw[o_DEF, ORD_BOUND, CHR_ORD, FUN_EQ_THM]
);

val validArg_def = Define`
    validArg l <=>  (l <> []) /\ EVERY (\x. x <> #"\^@") l /\ LENGTH l < 256`;

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

val hd_v_thm = fetch "mllistProg" "hd_v_thm";
val mlstring_hd_v_thm = save_thm("mlstring_hd_v_thm",
  hd_v_thm |> INST_TYPE [alpha |-> mlstringSyntax.mlstring_ty])

(* replace TOKENS_EMPTY in misc with this *)
val TOKENS_NIL = Q.store_thm("TOKENS_NIL",
  `!ls. (TOKENS f ls = []) <=> EVERY f ls`,
  Induct \\ rw[TOKENS_def]  \\ pairarg_tac  \\ fs[NULL_EQ, SPLITP] 
  \\ every_case_tac \\ fs[] \\ rw[]);

val MEM_REPLICATE_IMP = Q.store_thm("MEM_REPLICATE_IMP",
  `MEM x (REPLICATE n y) ==> x = y`,
  Induct_on`n` \\ rw[REPLICATE] \\ fs[]);

val commandLine_cline_spec = Q.store_thm("commandLine_cline_spec",
  `UNIT_TYPE u uv /\ cl <> [] /\ EVERY validArg cl /\ l = MAP ((n2w:num -> word8) o ORD) (FLAT (MAP (\s. (destStr s) ++ [CHR 0]) (MAP Str cl)))
    /\ LENGTH l < 257 ==>
    app (p:'ffi ffi_proj) ^(fetch_v "commandLine.cline" st) [uv]
    (COMMANDLINE cl)
    (POSTv clinev. & LIST_TYPE STRING_TYPE (MAP implode  cl) clinev * COMMANDLINE cl)`,
    xcf "commandLine.cline" st
    \\ xlet `POSTv cs. W8ARRAY cs (REPLICATE 256 (n2w 0)) * COMMANDLINE cl` 
      >-(xapp \\ xsimpl)
    \\ fs [COMMANDLINE_def] 
    \\ xlet `POSTv zv. W8ARRAY cs (l ++ DROP (LENGTH l) (REPLICATE 256 (n2w 0))) * & (UNIT_TYPE () zv) * COMMANDLINE cl`
    >-(xffi \\ fs [COMMANDLINE_def]
      \\ map_every qexists_tac [`REPLICATE 256 (n2w 0)`,  `emp`, `l ++ DROP (LENGTH l) (REPLICATE 256 (n2w 0))`, `List (MAP Str cl)`, `List (MAP Str cl)`, `commandLine_fun`, `["getArgs"]`]
      \\ xsimpl \\ fs[commandLine_fun_def]  \\ simp[EVERY_MAP, LENGTH_REPLICATE] \\ rw[] \\ fs[])
    \\ xapp \\ xsimpl \\ gen_tac \\ strip_tac 
    \\  reverse (conj_tac)  >-(fs[COMMANDLINE_def] \\ xsimpl)
    \\ pop_assum mp_tac  
    \\ simp[MAP_MAP_o, CHR_w2n_n2w_ORD] 
    \\ simp[GSYM MAP_MAP_o]
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
);

val commandLine_name_spec = Q.store_thm("commandLine_name_spec",
  `UNIT_TYPE u uv /\ (cl <> []) /\ (EVERY validArg cl) /\
    LENGTH (MAP ((n2w:num -> word8) o ORD) (FLAT (MAP (\s. (destStr s) ++ [CHR 0]) (MAP Str cl)))) < 257 ==>
    app (p:'ffi ffi_proj) ^(fetch_v "commandLine.name" st) [uv]
    (COMMANDLINE cl)
    (POSTv namev. & STRING_TYPE (implode (HD cl)) namev * COMMANDLINE cl)`,
    xcf "commandLine.name" st
    \\ xlet `POSTv vz. & UNIT_TYPE () vz * COMMANDLINE cl`
    >-(xcon \\ xsimpl)
    \\ xlet `POSTv cs. & LIST_TYPE STRING_TYPE (MAP implode cl) cs * COMMANDLINE cl` 
    >-(xapp \\ rw[])
    \\ xapp \\ xsimpl \\ instantiate \\ Cases_on `cl` \\ rw[]
);

val tl_v_thm = fetch "mllistProg" "tl_v_thm";
val mlstring_tl_v_thm = save_thm("mlstring_tl_v_thm",
  tl_v_thm |> INST_TYPE [alpha |-> mlstringSyntax.mlstring_ty])


val commandLine_arguments_spec = Q.store_thm("commandLine_arguments_spec",
  `UNIT_TYPE u uv /\ (cl <> []) /\ (EVERY validArg cl) /\
    LENGTH (MAP ((n2w:num -> word8) o ORD) (FLAT (MAP (\s. (destStr s) ++ [CHR 0]) (MAP Str cl)))) < 257 ==>
    app (p:'ffi ffi_proj) ^(fetch_v "commandLine.arguments" st) [uv]
    (COMMANDLINE cl)
    (POSTv namev. & LIST_TYPE STRING_TYPE (TL (MAP implode cl)) namev * COMMANDLINE cl)`,
    xcf "commandLine.arguments" st
    \\ xlet `POSTv vz. & UNIT_TYPE () vz * COMMANDLINE cl`
    >-(xcon \\ xsimpl)
    \\ xlet `POSTv cs. & LIST_TYPE STRING_TYPE (MAP implode cl) cs * COMMANDLINE cl` 
    >-(xapp \\ rw[])
    \\ xapp \\ xsimpl \\ instantiate \\ Cases_on `cl` \\ rw[mllistTheory.tl_def]
);


(*
val commandLine_name_spec = Q.store_thm("commandLine_name_spec",
  `UNIT_TYPE u uv /\ (cl <> []) /\ (EVERY validArg cl)  ==>
    app (p:'ffi ffi_proj) ^(fetch_v "commandLine.name" st) [uv]
    (COMMANDLINE cl)
    (POSTv namev. & STRING_TYPE (implode (HD cl)) namev * COMMANDLINE cl)`,
    xcf "commandLine.name" st
    \\ fs [COMMANDLINE_def] \\ xpull
    \\ Cases_on `LENGTH (MAP ((n2w:num -> word8) o ORD) (FLAT (MAP (\s. (destStr s) ++ [CHR 0]) (MAP Str cl)))) < 257` 
    >-(
      qmatch_assum_abbrev_tac `LENGTH args < 257` 
      \\ xlet `POSTv zv. IO (List (MAP Str cl)) commandLine_fun ["getArgs"] * 
      W8ARRAY commandLine_state (args ++ DROP (LENGTH args) w) * & (UNIT_TYPE () zv)`
      >-(xffi \\ fs [EVAL ``commandLine_state``, COMMANDLINE_def]
        \\ map_every qexists_tac [`w`,  `emp`, `args ++ DROP (LENGTH args) w`, `List (MAP Str cl)`, `List (MAP Str cl)`, `commandLine_fun`, `["getArgs"]`]
        \\ xsimpl \\ fs[commandLine_fun_def, Abbr `args`] \\ simp[EVERY_MAP])
      \\ xlet `POSTv strlv. SEP_EXISTS ss. &LIST_TYPE STRING_TYPE ss strlv * & (TAKE (LENGTH cl) ss = MAP implode cl) * IO (List (MAP Str cl)) commandLine_fun ["getArgs"] * 
          W8ARRAY commandLine_state (args ++ DROP (LENGTH args) w) `  
      >-(
        xapp \\ xsimpl 
        \\ qexists_tac `IO (List (MAP Str cl)) commandLine_fun ["getArgs"]` 
        \\ qexists_tac `args ++ DROP (LENGTH args) w`
        \\ fs[EVAL ``commandLine_state``] \\ xsimpl
        \\ rpt strip_tac \\ instantiate 
        \\ fs[Abbr `args`]
        \\ qmatch_abbrev_tac`TAKE (LENGTH cl) ls = _`
        \\ `IS_PREFIX ls (MAP implode cl)` suffices_by
        ( rw[IS_PREFIX_APPEND,TAKE_APPEND1]
        \\ rw[TAKE_APPEND1,TAKE_LENGTH_ID_rwt] )
        \\ simp[Abbr`ls`]
        \\ simp[IS_PREFIX_APPEND]
        \\ simp[MAP_MAP_o, CHR_w2n_n2w_ORD] 
        \\ simp[GSYM MAP_MAP_o]
        \\ drule map_app_last_Str
        \\ disch_then SUBST_ALL_TAC
        \\ rw[mlstringTheory.implode_STRCAT, GSYM mlstringTheory.str_def, mlstringTheory.strcat_assoc, mlstringTheory.tokens_append]
        \\ qexists_tac `tokens (\x. x = #"\^@") (implode (MAP CHR (MAP w2n (DROP (STRLEN (FRONT (FLAT (MAP (\s. STRCAT (destStr s) "\^@") (MAP Str cl)))) + 1) w))))`
        \\ rw[] 
        (*now tokens is isolated*)
        \\ Q.ISPEC_THEN`explode`match_mp_tac INJ_MAP_EQ 
        \\ simp[MAP_MAP_o, INJ_DEF, mlstringTheory.explode_11, o_DEF, mlstringTheory.explode_implode, mlstringTheory.TOKENS_eq_tokens_sym]
        \\ rw[TOKENS_FRONT_MAP_inv])
      \\ xapp \\ xsimpl \\ fs [Abbr `args`] 
      \\ instantiate
      \\ `MAP implode cl <> []` by fs[MAP_EQ_NIL]
      \\ `TAKE (LENGTH cl) ss <> []` by metis_tac[]
      \\ fs[TAKE_EQ_NIL]
      \\ Cases_on `cl` \\ fs[]
      \\ Cases_on `ss` \\ fs[]
    )
    (*the commandline is too long here*)
    \\ qmatch_assum_abbrev_tac `¬(LENGTH args < 257)`
    \\ xlet `POSTv zv. IO (List (MAP Str cl)) commandLine_fun ["getArgs"] * 
      W8ARRAY commandLine_state (TAKE 256 args) * & (UNIT_TYPE () zv)`
    >-(xffi \\ fs [EVAL ``commandLine_state``, COMMANDLINE_def]
      \\ map_every qexists_tac [`w`,  `emp`, `TAKE 256 args`, `List (MAP Str cl)`, `List (MAP Str cl)`, `commandLine_fun`, `["getArgs"]`]
      \\ xsimpl \\ fs[commandLine_fun_def, Abbr `args`] \\ simp[EVERY_MAP, MAP_TAKE] \\ xsimpl)
    \\ xlet `POSTv strlv. & LIST_TYPE STRING_TYPE (tokens (\x. x = #"\^@") (implode (TAKE 256 (FLAT (MAP (\l. l ++ "\^@") cl))))) strlv
        * IO (List (MAP Str cl)) commandLine_fun ["getArgs"] * W8ARRAY commandLine_state (TAKE 256 args)`
    >-(xapp \\ xsimpl
      \\ qexists_tac `IO (List (MAP Str cl)) commandLine_fun ["getArgs"]` 
      \\ qexists_tac `TAKE 256 args`
      \\ fs[EVAL ``commandLine_state``] \\ xsimpl
      \\ rpt strip_tac \\ fs[Abbr `args`]
      \\ fs[MAP_MAP_o, CHR_w2n_n2w_ORD, MAP_TAKE]
      \\ fs[GSYM MAP_MAP_o]
      \\ fs[destStr_str] )
    \\ xapp \\ xsimpl \\ instantiate
    \\ fs[LENGTH_NIL, LENGTH_TAKE_EQ, validArg_def, EVERY_MEM]
    \\ rw[mlstringTheory.TOKENS_eq_tokens_sym, mlstringTheory.explode_implode]
    >-(
      CCONTR_TAC \\ fs[]
      \\ imp_res_tac TOKENS_EMPTY
      \\ `MAP (\x. STRCAT x "\^@") cl <> []` by fs[MAP_EQ_NIL]
      \\ `CONCAT (MAP (\x. STRCAT x "\^@") cl) <> []` by fs[FLAT_EQ_NIL] >-(Cases_on `cl` \\ rw[])
      \\ fs[LENGTH_NIL, LENGTH_TAKE_EQ]
      \\ Cases_on `cl` \\ fs[]
      \\ Cases_on `h` >-(last_x_assum (qspecl_then [`""`] mp_tac) \\ rw[])
      \\ first_x_assum (qspecl_then [`h'`] mp_tac) \\ rw[]
      \\ metis_tac[MEM])
    \\ Cases_on `cl` \\ fs[Once TAKE_APPEND]
    \\ first_x_assum (qspecl_then [`h`] mp_tac) \\ rw[]
    \\ fs[TAKE_LENGTH_TOO_LONG]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC, GSYM CONS_APPEND, TOKENS_APPEND]
    \\ fs[MAP_APPEND]
    \\ `validArg h` by fs [validArg_def, EVERY_MEM]
    \\ fs[validArg_TOKENS]
);    

val validArg_TOKENS = Q.prove(
  `!l. validArg l ==> TOKENS (\x. x = #"\^@") l = [l]`,
    Induct \\ rw[validArg_def, TOKENS_def]
    \\ pairarg_tac \\ fs[NULL_EQ] \\ rw[]
    >-(Cases_on `r` \\ imp_res_tac SPLITP_JOIN \\ fs[]
      \\ imp_res_tac SPLITP_NIL_IMP \\ fs[])
    >-(Cases_on `r` >-(imp_res_tac SPLITP_NIL_SND_EVERY \\ fs[])
      \\ imp_res_tac SPLITP_CONS_IMP \\ fs[] \\ full_simp_tac std_ss [EVERY_NOT_EXISTS])
    \\ Cases_on `r` >-(rw[TOKENS_def]) 
      \\ imp_res_tac SPLITP_CONS_IMP \\ fs[] \\ full_simp_tac std_ss [EVERY_NOT_EXISTS]
);
 


*)

(*
AIM: to be able to define echo using the arguments function so that
  `!cl. (*some specification about length of cl being less than 256*) ==>
  app (p:'ffi ffi_proj) echo_v [uv] (COMMANDLINE cl * STDOUT out)
  (POSTv u. COMMANDLINE cl * STDOUT (out ++ (CONCAT (MAP implode (arguments cl)))))`

  is true *)
*)
val _ = export_theory();

