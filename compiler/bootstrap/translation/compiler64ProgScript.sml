open preamble
     to_target64ProgTheory compilerTheory
     exportTheory
     ml_translatorLib ml_translatorTheory

val _ = new_theory"compiler64Prog";

val _ = translation_extends "to_target64Prog";

val () = Globals.max_print_depth := 15;

val () = use_long_names := true;

val spec64 = INST_TYPE[alpha|->``:64``]

val max_heap_limit_64_def = Define`
  max_heap_limit_64 c =
    ^(spec64 data_to_wordTheory.max_heap_limit_def
      |> SPEC_ALL
      |> SIMP_RULE (srw_ss())[wordLangTheory.shift_def]
      |> concl |> rhs)`;

val res = translate max_heap_limit_64_def

val max_heap_limit_64_thm = Q.store_thm("max_heap_limit_64_thm",
  `max_heap_limit (:64) = max_heap_limit_64`,
  rw[FUN_EQ_THM] \\ EVAL_TAC);

val def = spec64 backendTheory.compile_explorer_def

val res = translate def

val backend_compile_explorer_side = Q.prove(`
  ∀x y. backend_compile_explorer_side x y = T`,
  simp[definition"backend_compile_explorer_side_def",PULL_FORALL] \\
  rpt gen_tac \\ ntac 3 strip_tac \\
  qmatch_goalsub_abbrev_tac`compile c.do_mti c.max_app [z]` \\
  `∃a. compile c.do_mti c.max_app [z] = [a]` by
    (Cases_on`c.do_mti`>>fs[clos_mtiTheory.compile_def]>>
    metis_tac[clos_mtiTheory.intro_multi_sing])>>
  specl_args_of_then ``renumber_code_locs_list``
    (clos_numberTheory.renumber_code_locs_length|>CONJUNCT1) assume_tac>>
  rfs[LENGTH_EQ_NUM_compute] \\
  strip_tac \\ fs[]) |> update_precondition;

val def = spec64 backendTheory.compile_def
  |> REWRITE_RULE[max_heap_limit_64_thm]

val res = translate def

val def = spec64 compilerTheory.compile_def

val _ = translate compilerTheory.locs_to_string_def;
val res = translate def

val res = translate basisProgTheory.basis_def

val res = translate inferTheory.init_config_def;

(* Helper functions in exportTheory translated here since they should be common
   for all encoders *)
val res = translate all_bytes_eq
val res = translate byte_to_string_eq

val export_byte_to_string_side_def = prove(
  ``!b. export_byte_to_string_side b``,
  fs [fetch "-" "export_byte_to_string_side_def"]
  \\ Cases \\ fs [] \\ EVAL_TAC \\ fs [])
  |> update_precondition;

val res = translate byte_strlit_def;
val res = translate comm_strlit_def;
val res = translate newl_strlit_def;
val res = translate comma_cat_def;
val res = translate num_to_str_def;

val num_to_str_side_def = prove(
  ``!n. export_num_to_str_side n``,
  ho_match_mp_tac num_to_str_ind \\ rw []
  \\ once_rewrite_tac [fetch "-" "export_num_to_str_side_def"] \\ fs []
  \\ `n MOD 10 < 10` by fs [LESS_MOD] \\ decide_tac)
  |> update_precondition;

val res = translate bytes_row_def;
val res = translate split16_def;

(* Compiler interface in compilerTheory *)
val res = translate error_to_str_def;

val res = translate parse_num_def;

val res = translate find_parse_def;

val res = translate comma_tokens_def;

val res = translate parse_num_list_def;

val res = translate parse_nums_def;

val res = translate find_parse_nums_def;

val spec64 = INST_TYPE[alpha|->``:64``];

val _ = translate (extend_with_args_def |> spec64 |> SIMP_RULE (srw_ss()) [MEMBER_INTRO])

val _ = translate (parse_heap_stack_def |> SIMP_RULE (srw_ss()) [default_heap_sz_def,default_stack_sz_def])

val r = translate (format_compiler_result_def |> Q.GEN`bytes` |> Q.ISPEC`bytes:word8 list`)

val r = translate (compile_to_bytes_def |> spec64)

(* sexp compiler translation -
   TODO: move parts of this to separate translation file(s)
   probably move the _alt definitions into fromSexpTheory itself
*)

(* TODO: this is duplicated in parserProgTheory *)
val monad_unitbind_assert = Q.prove(
  `!b x. monad_unitbind (assert b) x = if b then x else NONE`,
  Cases THEN EVAL_TAC THEN SIMP_TAC std_ss []);
val OPTION_BIND_THM = Q.store_thm("OPTION_BIND_THM",
  `!x y. OPTION_BIND x y = case x of NONE => NONE | SOME i => y i`,
  Cases THEN SRW_TAC [] []);
(* -- *)

val r = translate simpleSexpPEGTheory.pnt_def
val r = translate pegTheory.ignoreR_def
val r = translate pegTheory.ignoreL_def
val r = translate simpleSexpTheory.arb_sexp_def
val r = translate simpleSexpPEGTheory.choicel_def
val r = translate simpleSexpPEGTheory.tokeq_def
val r = translate simpleSexpPEGTheory.pegf_def
val r = translate simpleSexpPEGTheory.grabWS_def
val r = translate simpleSexpPEGTheory.replace_nil_def
val r = translate simpleSexpTheory.destSXNUM_def
val r = translate simpleSexpTheory.destSXCONS_def
val r = translate simpleSexpTheory.destSXSYM_def
val r = translate stringTheory.isPrint_def
val r = translate stringTheory.isGraph_def
val r = translate (simpleSexpTheory.valid_first_symchar_def
                  |> SIMP_RULE std_ss [IN_INSERT,NOT_IN_EMPTY])
val r = translate (simpleSexpTheory.valid_symchar_def
                  |> SIMP_RULE std_ss [IN_INSERT,NOT_IN_EMPTY])
val r = translate simpleSexpPEGTheory.sexpPEG_def
val r = translate pegexecTheory.destResult_def

val r =
  simpleSexpParseTheory.parse_sexp_def
  |> SIMP_RULE std_ss[monad_unitbind_assert,OPTION_BIND_THM,
                  pegexecTheory.pegparse_def,
                  simpleSexpPEGTheory.wfG_sexpPEG,UNCURRY,GSYM NULL_EQ]
  |> translate;

val parse_sexp_side = Q.prove(
  `∀x. simplesexpparse_parse_sexp_side x = T`,
  simp[definition"simplesexpparse_parse_sexp_side_def",
     parserProgTheory.peg_exec_side_def,
     parserProgTheory.coreloop_side_def] \\
  qx_gen_tac`i` \\
  (MATCH_MP pegexecTheory.peg_exec_total simpleSexpPEGTheory.wfG_sexpPEG |> strip_assume_tac)
  \\ fs[definition"pegexec_destresult_side_def"] \\
  (MATCH_MP pegexecTheory.coreloop_total simpleSexpPEGTheory.wfG_sexpPEG |> strip_assume_tac)
  \\ fs[pegexecTheory.coreloop_def]
  \\ qmatch_abbrev_tac`IS_SOME (OWHILE a b c)`
  \\ qmatch_assum_abbrev_tac`OWHILE a b' c = _`
  \\ `b = b'`
  by (
    simp[Abbr`b`,Abbr`b'`,FUN_EQ_THM]
    \\ Cases \\ simp[]
    \\ TOP_CASE_TAC \\ simp[FLOOKUP_DEF] \\ rw[]
    \\ TOP_CASE_TAC \\ simp[]
    \\ TOP_CASE_TAC \\ simp[]
    \\ TOP_CASE_TAC \\ simp[]
    \\ TOP_CASE_TAC \\ simp[] ) \\
  fs[]) |> update_precondition;

val r = fromSexpTheory.sexplist_def
        |> SIMP_RULE std_ss [OPTION_BIND_THM]
        |> translate;

val r = translate simpleSexpTheory.strip_sxcons_def
val r = translate simpleSexpTheory.dstrip_sexp_def


(* TODO: move (used?) *)
val isHexDigit_cases = Q.store_thm("isHexDigit_cases",
  `isHexDigit c ⇔
   isDigit c ∨
   c ∈ {#"a";#"b";#"c";#"d";#"e";#"f"} ∨
   c ∈ {#"A";#"B";#"C";#"D";#"E";#"F"}`,
  rw[isHexDigit_def,isDigit_def]
  \\ EQ_TAC \\ strip_tac \\ simp[]
  >- (
    `ORD c = 97 ∨
     ORD c = 98 ∨
     ORD c = 99 ∨
     ORD c = 100 ∨
     ORD c = 101 ∨
     ORD c = 102` by decide_tac \\
    pop_assum(assume_tac o Q.AP_TERM`CHR`) \\ fs[CHR_ORD] )
  >- (
    `ORD c = 65 ∨
     ORD c = 66 ∨
     ORD c = 67 ∨
     ORD c = 68 ∨
     ORD c = 69 ∨
     ORD c = 70` by decide_tac \\
    pop_assum(assume_tac o Q.AP_TERM`CHR`) \\ fs[CHR_ORD] ));

val isHexDigit_UNHEX_LESS = Q.store_thm("isHexDigit_UNHEX_LESS",
  `isHexDigit c ⇒ UNHEX c < 16`,
  rw[isHexDigit_cases] \\ EVAL_TAC \\
  rw[GSYM simpleSexpParseTheory.isDigit_UNHEX_alt] \\
  fs[isDigit_def]);

val num_from_hex_string_alt_length_2 = Q.store_thm("num_from_hex_string_alt_length_2",
  `num_from_hex_string_alt [d1;d2] < 256`,
  rw[lexer_implTheory.num_from_hex_string_alt_def,
     ASCIInumbersTheory.s2n_def,
     numposrepTheory.l2n_def]
  \\ qspecl_then[`unhex_alt d1`,`16`]mp_tac MOD_LESS
  \\ impl_tac >- rw[]
  \\ qspecl_then[`unhex_alt d2`,`16`]mp_tac MOD_LESS
  \\ impl_tac >- rw[]
  \\ decide_tac);
(* -- *)

val num_from_hex_string_alt_intro = Q.store_thm("num_from_hex_string_alt_intro",
  `EVERY isHexDigit ls ⇒
   num_from_hex_string ls =
   num_from_hex_string_alt ls`,
  rw[ASCIInumbersTheory.num_from_hex_string_def,
     lexer_implTheory.num_from_hex_string_alt_def,
     ASCIInumbersTheory.s2n_def,
     numposrepTheory.l2n_def] \\
  AP_TERM_TAC \\
  simp[MAP_EQ_f] \\
  fs[EVERY_MEM,lexer_implTheory.unhex_alt_def]);

val lemma = Q.prove(`
  isHexDigit x ∧ isHexDigit y ∧ A ∧ B ∧ ¬isPrint (CHR (num_from_hex_string[x;y])) ⇔
  isHexDigit x ∧ isHexDigit y ∧ A ∧ B ∧ ¬isPrint (CHR (num_from_hex_string_alt[x;y]))`,
  rw[EQ_IMP_THM,num_from_hex_string_alt_intro]
  \\ rfs[num_from_hex_string_alt_intro]);

val lemma2 = Q.prove(`
  isHexDigit x ∧ isHexDigit y ⇒
  num_from_hex_string [x;y] = num_from_hex_string_alt [x;y]`,
  rw[num_from_hex_string_alt_intro]);

val r = fromSexpTheory.decode_control_def
        |> SIMP_RULE std_ss [monad_unitbind_assert,lemma,lemma2]
        |> translate;

val fromsexp_decode_control_side = Q.prove(
  `∀x. fromsexp_decode_control_side x = T`,
  ho_match_mp_tac fromSexpTheory.decode_control_ind \\
  rw[Once(theorem"fromsexp_decode_control_side_def")] \\
  rw[Once(theorem"fromsexp_decode_control_side_def")] \\ rfs[] \\
  rw[num_from_hex_string_alt_length_2] \\
  Cases_on`x1` \\ fs[] \\
  rw[Once(theorem"fromsexp_decode_control_side_def")] \\
  rw[Once(theorem"fromsexp_decode_control_side_def")])
  |> update_precondition;

val r = translate fromSexpTheory.odestSEXSTR_def;
val r = translate fromSexpTheory.odestSXSYM_def;
val r = translate fromSexpTheory.odestSXNUM_def;

val r = fromSexpTheory.sexpid_def
        |> SIMP_RULE std_ss [OPTION_BIND_THM,monad_unitbind_assert]
        |> translate;

val fromsexp_sexpid_side = Q.prove(
  `∀x y. fromsexp_sexpid_side x y = T`,
  ho_match_mp_tac fromSexpTheory.sexpid_ind \\ rw[] \\
  rw[Once(theorem"fromsexp_sexpid_side_def")])
|> update_precondition;

val r = fromSexpTheory.sexptctor_def
        |> SIMP_RULE std_ss [OPTION_BIND_THM,monad_unitbind_assert]
        |> translate;

val sexptype_alt_def = tDefine"sexptype_alt"`
 (sexptype_alt s =
    case dstrip_sexp s of
    | NONE => NONE
    | SOME (nm,args) =>
      if nm = "Tvar" ∧ LENGTH args = 1 then
        OPTION_MAP Tvar (odestSEXSTR (EL 0 args))
      else if nm = "Tvar_db" ∧ LENGTH args = 1 then
        OPTION_MAP Tvar_db (odestSXNUM (EL 0 args))
      else if nm = "Tapp" ∧ LENGTH args = 2 then
        OPTION_MAP2 Tapp (sexptype_list (EL 0 args)) (sexptctor (EL 1 args))
      else NONE) ∧
 (sexptype_list s =
    case s of
    | SX_SYM nm => if nm = "nil" then SOME [] else NONE
    | SX_CONS a d =>
      (case sexptype_alt a of
       | NONE => NONE
       | SOME h =>
       case sexptype_list d of
       | NONE => NONE
       | SOME t => SOME (h::t))
    | _ => NONE)`
  (wf_rel_tac`inv_image (measure sexp_size) (λx. case x of INL y => y | INR y => y)` \\ rw[] \\
   imp_res_tac fromSexpTheory.dstrip_sexp_size \\
   fs[LENGTH_EQ_NUM_compute]);

val sexptype_alt_ind = theorem"sexptype_alt_ind";
val sexptype_def = fromSexpTheory.sexptype_def;

val sexptype_alt_intro = Q.store_thm("sexptype_alt_intro",
  `(∀s. sexptype s = sexptype_alt s) ∧ (∀s. sexptype_list s = sexplist sexptype s)`,
  ho_match_mp_tac sexptype_alt_ind \\ rw[]
  >- (
    rw[Once sexptype_alt_def,Once sexptype_def] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[] \\
    simp[monad_unitbind_assert] \\
    srw_tac[ETA_ss][] )
  >- (
    rw[Once fromSexpTheory.sexplist_def,Once (CONJUNCT2 sexptype_alt_def)] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[] ));

val r = translate sexptype_alt_def;

val sexptype_alt_side = Q.prove(
  `(∀x. compiler64prog_sexptype_alt_side x = T) ∧
   (∀x. compiler64prog_sexptype_list_side x = T)`,
  ho_match_mp_tac sexptype_alt_ind \\ rw[] \\
  rw[Once(theorem"compiler64prog_sexptype_alt_side_def")])
  |> update_precondition;

val sexptype_alt_intro1 = Q.prove(
  `sexptype = sexptype_alt ∧ sexplist sexptype = sexptype_list`,
  rw[FUN_EQ_THM,sexptype_alt_intro]);

val r = translate fromSexpTheory.sexppair_def;

val r = fromSexpTheory.sexptype_def_def
        |> SIMP_RULE std_ss [sexptype_alt_intro1]
        |> translate;

val r = translate optionTheory.OPTION_APPLY_def;

val r = fromSexpTheory.sexpspec_def
        |> SIMP_RULE std_ss [OPTION_BIND_THM,monad_unitbind_assert,sexptype_alt_intro1]
        |> translate;

val fromsexp_sexpspec_side = Q.prove(
  `∀x. fromsexp_sexpspec_side x = T`,
  EVAL_TAC \\ rw[] \\ strip_tac \\ fs[])
  |> update_precondition;

val r = fromSexpTheory.sexpopt_def
        |> SIMP_RULE std_ss [OPTION_BIND_THM,monad_unitbind_assert]
        |> translate;

val r = fromSexpTheory.sexplocn_def
        |> SIMP_RULE std_ss [OPTION_BIND_THM,monad_unitbind_assert]
        |> translate;

val r = fromSexpTheory.sexplit_def
        |> SIMP_RULE std_ss [OPTION_BIND_THM,monad_unitbind_assert]
        |> translate;

val fromsexp_sexplit_side = Q.prove(
  `∀x. fromsexp_sexplit_side x = T`,
  EVAL_TAC \\ rw[] \\ strip_tac \\ fs[])
  |> update_precondition;

val sexppat_alt_def = tDefine"sexppat_alt"`
 (sexppat_alt s =
    OPTION_MAP Pvar (odestSEXSTR s) ++
    case dstrip_sexp s of
    | NONE => NONE
    | SOME (nm,args) =>
      if nm = "Pany" ∧ LENGTH args = 0 then
        SOME Pany
      else if nm = "Plit" ∧ LENGTH args = 1 then
        OPTION_MAP Plit (sexplit (EL 0 args))
      else if nm = "Pcon" ∧ LENGTH args = 2 then
        OPTION_MAP2 Pcon (sexpopt (sexpid odestSEXSTR) (EL 0 args))
          (sexppat_list (EL 1 args))
      else if nm = "Pref" ∧ LENGTH args = 1 then
        OPTION_MAP Pref (sexppat_alt (EL 0 args))
      else if nm = "Ptannot" ∧ LENGTH args = 2 then
        OPTION_MAP2 Ptannot (sexppat_alt (EL 0 args)) (sexptype_alt (EL 1 args))
      else NONE) ∧
 (sexppat_list s =
    case s of
    | SX_SYM nm => if nm = "nil" then SOME [] else NONE
    | SX_CONS a d =>
      (case sexppat_alt a of
       | NONE => NONE
       | SOME h =>
       case sexppat_list d of
       | NONE => NONE
       | SOME t => SOME (h::t))
    | _ => NONE)`
  (wf_rel_tac`inv_image (measure sexp_size) (λx. case x of INL y => y | INR y => y)` \\ rw[] \\
   imp_res_tac fromSexpTheory.dstrip_sexp_size \\
   fs[LENGTH_EQ_NUM_compute]);

val sexppat_alt_ind = theorem"sexppat_alt_ind";
val sexppat_def = fromSexpTheory.sexppat_def;

val sexppat_alt_intro = Q.store_thm("sexppat_alt_intro",
  `(∀s. sexppat s = sexppat_alt s) ∧ (∀s. sexppat_list s = sexplist sexppat s)`,
  ho_match_mp_tac sexppat_alt_ind \\ rw[]
  >- (
    rw[Once sexppat_alt_def,Once sexppat_def] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[] \\
    simp[monad_unitbind_assert] \\
    srw_tac[ETA_ss][sexptype_alt_intro1] )
  >- (
    rw[Once fromSexpTheory.sexplist_def,Once (CONJUNCT2 sexppat_alt_def)] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[] ));

val r = translate sexppat_alt_def;

val sexppat_alt_side = Q.prove(
  `(∀x. compiler64prog_sexppat_alt_side x = T) ∧
   (∀x. compiler64prog_sexppat_list_side x = T)`,
  ho_match_mp_tac sexppat_alt_ind \\ rw[] \\
  rw[Once(theorem"compiler64prog_sexppat_alt_side_def")])
  |> update_precondition;

val sexppat_alt_intro1 = Q.prove(
  `sexppat = sexppat_alt ∧ sexplist sexppat = sexppat_list`,
  rw[FUN_EQ_THM,sexppat_alt_intro]);

val sexpexp_alt_def = tDefine"sexpexp_alt"`
  (sexpexp_alt s =
     case dstrip_sexp s of
     | NONE => NONE
     | SOME (nm,args) =>
          if nm = "Raise" ∧ LENGTH args = 1 then
             lift Raise (sexpexp_alt (EL 0 args)) else
          if nm = "Handle" ∧ LENGTH args = 2 then
             OPTION_MAP2 Handle (sexpexp_alt (EL 0 args))
               (sexppes (EL 1 args)) else
          if nm = "Lit" ∧ LENGTH args = 1 then
             lift Lit (sexplit (EL 0 args))
           else
          if nm = "Con" ∧ LENGTH args = 2 then
             OPTION_MAP2 Con (sexpopt (sexpid odestSEXSTR) (EL 0 args))
               (sexpexp_list (EL 1 args))
           else
          if nm = "Var" ∧ LENGTH args = 1 then
             lift Var (sexpid odestSEXSTR (EL 0 args))
           else
          if nm = "Fun" ∧ LENGTH args = 2 then
             OPTION_MAP2 Fun (odestSEXSTR (EL 0 args))
               (sexpexp_alt (EL 1 args))
           else
          if nm = "App" ∧ LENGTH args = 2 then
             OPTION_MAP2 App (sexpop (EL 0 args))
               (sexpexp_list  (EL 1 args))
           else
          if nm = "Log" ∧ LENGTH args = 3 then
             lift Log (sexplop (EL 0 args)) <*> sexpexp_alt (EL 1 args) <*>
             sexpexp_alt (EL 2 args)
           else
          if nm = "If" ∧ LENGTH args = 3 then
             lift If (sexpexp_alt (EL 0 args)) <*> sexpexp_alt (EL 1 args) <*>
             sexpexp_alt (EL 2 args)
           else
          if nm = "Mat" ∧ LENGTH args = 2 then
             OPTION_MAP2 Mat (sexpexp_alt (EL 0 args))
               (sexppes (EL 1 args))
           else
          if nm = "Let" ∧ LENGTH args = 3 then
             lift Let (sexpopt odestSEXSTR (EL 0 args)) <*>
             sexpexp_alt (EL 1 args) <*> sexpexp_alt (EL 2 args)
           else
          if nm = "Letrec" ∧ LENGTH args = 2 then
             OPTION_MAP2 Letrec
               (sexpfuns (EL 0 args))
               (sexpexp_alt (EL 1 args))
           else
          if nm = "Tannot" ∧ LENGTH args = 2 then
             OPTION_MAP2 Tannot (sexpexp_alt (EL 0 args))
               (sexptype_alt (EL 1 args))
           else
          if nm = "Lannot" ∧ LENGTH args = 2 then
            OPTION_MAP2 Lannot (sexpexp_alt (EL 0 args))
              (sexplocn (EL 1 args))
          else NONE) ∧
   (sexpexp_list s =
      case s of
      | SX_SYM nm => if nm = "nil" then SOME [] else NONE
      | SX_CONS a d =>
        (case sexpexp_alt a of
         | NONE => NONE
         | SOME h =>
         case sexpexp_list d of
         | NONE => NONE
         | SOME t => SOME (h::t))
      | _ => NONE) ∧
  (sexppes s =
   case s of
   | SX_SYM nm => if nm = "nil" then SOME [] else NONE
   | SX_CONS a d =>
     (case sexppatexp a of
      | NONE => NONE
      | SOME h =>
      case sexppes d of
      | NONE => NONE
      | SOME t => SOME (h::t))
   | _ => NONE) ∧
  (sexpfuns s =
   case s of
   | SX_SYM nm => if nm = "nil" then SOME [] else NONE
   | SX_CONS a d =>
     (case sexpfun a of
      | NONE => NONE
      | SOME h =>
      case sexpfuns d of
      | NONE => NONE
      | SOME t => SOME (h::t))
   | _ => NONE) ∧
   (sexppatexp s =
    case s of
    | SX_CONS a d =>
      (case (sexppat_alt a, sexpexp_alt d) of
      | (SOME p, SOME e) => SOME (p,e)
      | _ => NONE)
    | _ => NONE) ∧
   (sexpfun s =
     case s of
     | SX_CONS a d =>
       (case d of
       | SX_CONS b d =>
       (case (odestSEXSTR a, odestSEXSTR b, sexpexp_alt d) of
        | (SOME x, SOME y, SOME z) => SOME (x,y,z)
        | _ => NONE)
      | _ => NONE)
    | _ => NONE)`
  (wf_rel_tac`inv_image (measure sexp_size)
    (λx. case x of
         | INL y => y
         | INR (INL y) => y
         | INR (INR (INL y)) => y
         | INR (INR (INR (INL y))) => y
         | INR (INR (INR (INR (INL y)))) => y
         | INR (INR (INR (INR (INR y)))) => y)` \\ rw[] \\
   imp_res_tac fromSexpTheory.dstrip_sexp_size \\
   fs[LENGTH_EQ_NUM_compute]);

val sexpexp_alt_ind = theorem"sexpexp_alt_ind";
val sexpexp_def = fromSexpTheory.sexpexp_def;

val sexpexp_alt_intro = Q.store_thm("sexpexp_alt_intro",
  `(∀s. sexpexp s = sexpexp_alt s) ∧
  (∀s. sexplist sexpexp s = sexpexp_list s) ∧
  (∀s. sexplist (sexppair sexppat sexpexp) s = sexppes s) ∧
  (∀s. sexplist (sexppair odestSEXSTR (sexppair odestSEXSTR sexpexp)) s = sexpfuns s) ∧
  (∀s. sexppair sexppat sexpexp s = sexppatexp s) ∧
  (∀s. sexppair odestSEXSTR (sexppair odestSEXSTR sexpexp) s = sexpfun s)`,
  ho_match_mp_tac sexpexp_alt_ind \\ rw[]
  >- (
    rw[Once sexpexp_alt_def,Once sexpexp_def] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[] \\
    simp[monad_unitbind_assert] \\
    rpt (
    IF_CASES_TAC >- (
      pop_assum strip_assume_tac \\ rveq \\
      full_simp_tac std_ss []
      \\ fsrw_tac[ETA_ss][sexptype_alt_intro1] ) \\
    simp[] ) )
  >- (
    rw[Once fromSexpTheory.sexplist_def,Once (CONJUNCT2 sexpexp_alt_def)] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[] )
  >- (
    rw[Once fromSexpTheory.sexplist_def,Once (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 sexpexp_alt_def)))] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[] )
  >- (
    rw[Once fromSexpTheory.sexplist_def,Once (CONJUNCT1 (funpow 3 CONJUNCT2 sexpexp_alt_def))] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[] )
  >- (
    rw[Once fromSexpTheory.sexplist_def,
       fromSexpTheory.sexppair_def,
       Once (CONJUNCT1 (funpow 4 CONJUNCT2 sexpexp_alt_def))] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[sexppat_alt_intro1] \\
    TOP_CASE_TAC \\ fs[] )
  >- (
    rw[Once fromSexpTheory.sexplist_def,
       fromSexpTheory.sexppair_def,
       Once (funpow 5 CONJUNCT2 sexpexp_alt_def)] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[sexppat_alt_intro1] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[] \\
    TOP_CASE_TAC \\ fs[]));

val r = translate fromSexpTheory.sexpop_def;
val r = translate fromSexpTheory.sexplop_def;

val r = translate sexpexp_alt_def;

val sexpexp_alt_side = Q.prove(
  `(∀x. compiler64prog_sexpexp_alt_side x = T) ∧
   (∀x. compiler64prog_sexpexp_list_side x = T) ∧
   (∀x. compiler64prog_sexppes_side x = T) ∧
   (∀x. compiler64prog_sexpfuns_side x = T) ∧
   (∀x. compiler64prog_sexppatexp_side x = T) ∧
   (∀x. compiler64prog_sexpfun_side x = T)`,
  ho_match_mp_tac sexpexp_alt_ind \\ rw[] \\
  rw[Once(theorem"compiler64prog_sexpexp_alt_side_def")])
  |> update_precondition;

val sexpexp_alt_intro1 = Q.prove(
  `sexpexp = sexpexp_alt ∧
   sexplist (sexppair odestSEXSTR (sexppair odestSEXSTR sexpexp)) = sexpfuns`,
  rw[FUN_EQ_THM,sexpexp_alt_intro]);

val r = fromSexpTheory.sexpdec_def
        |> SIMP_RULE std_ss [OPTION_BIND_THM,monad_unitbind_assert,
                             sexptype_alt_intro1,sexppat_alt_intro1,sexpexp_alt_intro1]
        |> translate;

val fromsexp_sexpdec_side = Q.prove(
  `∀x. fromsexp_sexpdec_side x = T`,
  EVAL_TAC \\ rw[] \\ strip_tac \\ fs[])
  |> update_precondition;

val r = fromSexpTheory.sexptop_def
        |> SIMP_RULE std_ss [OPTION_BIND_THM,monad_unitbind_assert]
        |> translate;

val fromsexp_sexptop_side = Q.prove(
  `∀x. fromsexp_sexptop_side x = T`,
  EVAL_TAC \\ rw[] \\ strip_tac \\ fs[])
  |> update_precondition;

val r = translate (sexp_compile_to_bytes_def |> spec64);

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = export_theory();
