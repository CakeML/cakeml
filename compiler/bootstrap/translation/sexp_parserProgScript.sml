(*
  Translate the alternative s-expression parser.
*)
open preamble decodeProgTheory
     ml_translatorLib ml_translatorTheory
     pegTheory simpleSexpTheory simpleSexpPEGTheory simpleSexpParseTheory fromSexpTheory

val _ = temp_delsimps ["NORMEQ_CONV"]

val _ = new_theory"sexp_parserProg";
val _ = translation_extends "decodeProg";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "sexp_parserProg");
val _ = ml_translatorLib.use_string_type true;

val monad_unitbind_assert = parserProgTheory.monad_unitbind_assert;

Theorem OPTION_BIND_THM:
   !x y. OPTION_BIND x y = case x of NONE => NONE | SOME i => y i
Proof
  Cases THEN SRW_TAC [] []
QED
(* -- *)

val r = translate simpleSexpPEGTheory.pnt_def
val r = translate pegTheory.ignoreR_def
val r = translate pegTheory.ignoreL_def
val r = translate simpleSexpTheory.arb_sexp_def
val r = translate simpleSexpPEGTheory.sumID_def
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
val r = translate pairTheory.PAIR_MAP_THM; (* TODO: isn't this done earlier? *)
val r = translate simpleSexpPEGTheory.sexpPEG_def
val () = next_ml_names := ["destResult"];
val r = translate pegexecTheory.destResult_def

val r =
  simpleSexpParseTheory.parse_sexp_def
  |> SIMP_RULE std_ss[monad_unitbind_assert,OPTION_BIND_THM,
                  pegexecTheory.pegparse_def,
                  simpleSexpPEGTheory.wfG_sexpPEG,UNCURRY,GSYM NULL_EQ]
  |> translate;

val parse_sexp_side = Q.prove(
  `∀x. parse_sexp_side x = T`,
  simp[definition"parse_sexp_side_def",
     parserProgTheory.peg_exec_side_def,
     parserProgTheory.coreloop_side_def] \\
  qx_gen_tac`i` \\
  (MATCH_MP pegexecTheory.peg_exec_total simpleSexpPEGTheory.wfG_sexpPEG |> strip_assume_tac)
  \\ fs[definition"destresult_1_side_def"] \\
  (MATCH_MP pegexecTheory.coreloop_total simpleSexpPEGTheory.wfG_sexpPEG |> strip_assume_tac)
  \\ fs[pegexecTheory.coreloop_def]
  \\ qmatch_abbrev_tac`IS_SOME (OWHILE a b c)`
  \\ qmatch_assum_abbrev_tac`OWHILE a b' c = _`
  \\ qsuff_tac `b = b'` THEN1 fs []
  \\ simp[Abbr`b`,Abbr`b'`,FUN_EQ_THM]
  \\ rpt gen_tac
  \\ TOP_CASE_TAC \\ simp[FLOOKUP_DEF] \\ rw[]
  \\ TOP_CASE_TAC \\ simp[FLOOKUP_DEF] \\ rw[]
  \\ Cases_on ‘k’ \\ TRY (fs [] \\ NO_TAC)
  \\ TOP_CASE_TAC \\ simp[FLOOKUP_DEF] \\ rw[]
  \\ TOP_CASE_TAC \\ simp[FLOOKUP_DEF] \\ rw[]
  \\ TOP_CASE_TAC \\ simp[FLOOKUP_DEF] \\ rw[]
  \\ TOP_CASE_TAC \\ simp[FLOOKUP_DEF] \\ rw[]) |> update_precondition;

val r = fromSexpTheory.sexplist_def
        |> SIMP_RULE std_ss [OPTION_BIND_THM]
        |> translate;

val r = translate simpleSexpTheory.strip_sxcons_def
val r = translate simpleSexpTheory.dstrip_sexp_def


(* TODO: move (used?) *)
Theorem isHexDigit_cases:
   isHexDigit c ⇔
   isDigit c ∨
   c ∈ {#"a";#"b";#"c";#"d";#"e";#"f"} ∨
   c ∈ {#"A";#"B";#"C";#"D";#"E";#"F"}
Proof
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
    pop_assum(assume_tac o Q.AP_TERM`CHR`) \\ fs[CHR_ORD] )
QED

Theorem isHexDigit_UNHEX_LESS:
   isHexDigit c ⇒ UNHEX c < 16
Proof
  rw[isHexDigit_cases] \\ EVAL_TAC \\
  rw[GSYM simpleSexpParseTheory.isDigit_UNHEX_alt] \\
  fs[isDigit_def]
QED

Theorem num_from_hex_string_alt_length_2:
   num_from_hex_string_alt [d1;d2] < 256
Proof
  rw[lexer_implTheory.num_from_hex_string_alt_def,
     ASCIInumbersTheory.s2n_def,
     numposrepTheory.l2n_def]
  \\ qspecl_then[`unhex_alt d1`,`16`]mp_tac MOD_LESS
  \\ impl_tac >- rw[]
  \\ qspecl_then[`unhex_alt d2`,`16`]mp_tac MOD_LESS
  \\ impl_tac >- rw[]
  \\ decide_tac
QED
(* -- *)

Theorem num_from_hex_string_alt_intro:
   EVERY isHexDigit ls ⇒
   num_from_hex_string ls =
   num_from_hex_string_alt ls
Proof
  rw[ASCIInumbersTheory.num_from_hex_string_def,
     lexer_implTheory.num_from_hex_string_alt_def,
     ASCIInumbersTheory.s2n_def,
     numposrepTheory.l2n_def] \\
  AP_TERM_TAC \\
  simp[MAP_EQ_f] \\
  fs[EVERY_MEM,lexer_implTheory.unhex_alt_def]
QED

val lemma = Q.prove(`
  isHexDigit x ∧ isHexDigit y ∧ A ∧ B ∧ ¬isPrint (CHR (num_from_hex_string[x;y])) ⇔
  isHexDigit x ∧ isHexDigit y ∧ A ∧ B ∧ ¬isPrint (CHR (num_from_hex_string_alt[x;y]))`,
  rw[EQ_IMP_THM,num_from_hex_string_alt_intro]
  \\ rfs[num_from_hex_string_alt_intro]);

val lemma2 = Q.prove(`
  isHexDigit x ∧ isHexDigit y ⇒
  num_from_hex_string [x;y] = num_from_hex_string_alt [x;y]`,
  rw[num_from_hex_string_alt_intro]);

val _ = ml_translatorLib.use_string_type false;
val r = fromSexpTheory.decode_control_def
        |> SIMP_RULE std_ss [monad_unitbind_assert,lemma,lemma2]
        |> translate;

val decode_control_side = Q.prove(
  `∀x. decode_control_side x = T`,
  ho_match_mp_tac fromSexpTheory.decode_control_ind \\
  rw[Once(theorem"decode_control_side_def")] \\
  rw[Once(theorem"decode_control_side_def")] \\ rfs[] \\
  rw[num_from_hex_string_alt_length_2] \\
  Cases_on`x1` \\ fs[] \\
  rw[Once(theorem"decode_control_side_def")] \\
  rw[Once(theorem"decode_control_side_def")])
  |> update_precondition;

val decode_control_wrapper_def = Define `
  decode_control_wrapper s =
    case decode_control (explode s) of
      NONE => NONE
    | SOME x => SOME (implode x)`

val r = translate decode_control_wrapper_def

val _ = ml_translatorLib.use_string_type true;

Theorem decode_control_eq:
  decode_control s =
  OPTION_MAP (\x. explode x) (decode_control_wrapper (implode s))
Proof
  fs [decode_control_wrapper_def]
  \\ Cases_on `decode_control s` \\ fs []
QED

val r = translate (fromSexpTheory.odestSEXSTR_def
                   |> REWRITE_RULE [decode_control_eq]);
val r = translate fromSexpTheory.odestSXSYM_def;
val r = translate fromSexpTheory.odestSXNUM_def;

val r = fromSexpTheory.sexpid_def
        |> SIMP_RULE std_ss [OPTION_BIND_THM,monad_unitbind_assert]
        |> translate;

val sexpid_side = Q.prove(
  `∀x y. sexpid_side x y = T`,
  ho_match_mp_tac fromSexpTheory.sexpid_ind \\ rw[] \\
  rw[Once(theorem"sexpid_side_def")])
|> update_precondition;

val r = translate sexptype_alt_def;

val sexptype_alt_side = Q.prove(
  `(∀x. sexptype_alt_side x = T) ∧
   (∀x. sexptype_list_side x = T)`,
  ho_match_mp_tac sexptype_alt_ind \\ rw[] \\
  rw[Once(theorem"sexptype_alt_side_def")])
  |> update_precondition;

val r = translate fromSexpTheory.sexppair_def;

val r = fromSexpTheory.sexptype_def_def
        |> SIMP_RULE std_ss [sexptype_alt_intro1]
        |> translate;

val r = translate optionTheory.OPTION_APPLY_def;

(*
val r = fromSexpTheory.sexpspec_def
        |> SIMP_RULE std_ss [OPTION_BIND_THM,monad_unitbind_assert,sexptype_alt_intro1]
        |> translate;

val sexpspec_side = Q.prove(
  `∀x. sexpspec_side x = T`,
  EVAL_TAC \\ rw[] \\ strip_tac \\ fs[])
  |> update_precondition;
*)

val r = fromSexpTheory.sexpopt_def
        |> SIMP_RULE std_ss [OPTION_BIND_THM,monad_unitbind_assert]
        |> translate;

val r = fromSexpTheory.sexplocpt_def
        |> SIMP_RULE std_ss [OPTION_BIND_THM,monad_unitbind_assert]
        |> translate;

val r = fromSexpTheory.sexplocn_def
        |> SIMP_RULE std_ss [OPTION_BIND_THM,monad_unitbind_assert]
        |> translate;

val r = fromSexpTheory.sexplit_def
        |> SIMP_RULE std_ss [OPTION_BIND_THM,monad_unitbind_assert]
        |> translate;

val sexplit_side = Q.prove(
  `∀x. sexplit_side x = T`,
  EVAL_TAC \\ rw[] \\ strip_tac \\ fs[])
  |> update_precondition;

val r = translate sexppat_alt_def;

val sexppat_alt_side = Q.prove(
  `(∀x. sexppat_alt_side x = T) ∧
   (∀x. sexppat_list_side x = T)`,
  ho_match_mp_tac sexppat_alt_ind \\ rw[] \\
  rw[Once(theorem"sexppat_alt_side_def")])
  |> update_precondition;

val r = translate (fromSexpTheory.sexpop_def
                   |> REWRITE_RULE [decode_control_eq]);

val r = translate fromSexpTheory.sexplop_def;

val r = translate fromSexpTheory.sexpsc_def;

val r = translate sexpexp_alt_def;

val sexpexp_alt_side = Q.prove(
  `(∀x. sexpexp_alt_side x = T) ∧
   (∀x. sexpexp_list_side x = T) ∧
   (∀x. sexppes_side x = T) ∧
   (∀x. sexpfuns_side x = T) ∧
   (∀x. sexppatexp_side x = T) ∧
   (∀x. sexpfun_side x = T)`,
  ho_match_mp_tac sexpexp_alt_ind \\ rw[] \\
  rw[Once(theorem"sexpexp_alt_side_def")])
  |> update_precondition;

val r = translate fromSexpTheory.sexpdec_alt_def

val sexpdec_alt_side = Q.prove(
  `(∀x. sexpdec_alt_side x = T) ∧
   (∀x. sexpdec_list_side x = T)`,
  ho_match_mp_tac sexpdec_alt_ind
  \\ rw[]
  \\ rw[Once(fetch"-""sexpdec_alt_side_def")]
  \\ fs[LENGTH_EQ_NUM_compute])
  |> update_precondition;

Theorem strip_dot_alt =
  simpleSexpParseTheory.strip_dot_def |> PURE_ONCE_REWRITE_RULE [CONS_APPEND];
val _ = translate strip_dot_alt

val _ = translate simpleSexpParseTheory.print_space_separated_def;

val _ = use_string_type false;
val _ = translate simpleSexpParseTheory.escape_string_def;
val _ = use_string_type true;

Theorem num_to_dec_string_v_thm:
  (NUM --> HOL_STRING_TYPE) toString ^(IntProgTheory.tostring_v_thm |> concl |> rand)
Proof
  assume_tac IntProgTheory.tostring_v_thm >>
  fs[NUM_def,Arrow_def,HOL_STRING_TYPE_def,INT_def,AppReturns_def,
     GSYM mlintTheory.num_to_str_thm,mlintTheory.num_to_str_def]
QED

val _ = add_user_proved_v_thm num_to_dec_string_v_thm;

(* TODO: translator failed for some reason if I just prove these as equations on print_sexp *)
val print_sexp_alt_def = tDefine"print_sexp_alt"`
  (print_sexp_alt (SX_SYM s) = s) ∧
  (print_sexp_alt (SX_NUM n) = toString n) ∧
  (print_sexp_alt (SX_STR s) = "\"" ++ IMPLODE(escape_string s) ++ "\"") ∧
  (print_sexp_alt s =
   let (ls,n) = strip_dot s in
   case n of
   | NONE =>
     if LENGTH ls = 2 ∧ HD ls = SX_SYM "quote"
     then "'" ++ print_sexp_alt (EL 1 ls)
     else "(" ++ print_space_separated (MAP print_sexp_alt ls) ++ ")"
   | SOME lst =>
       "(" ++ print_space_separated (MAP print_sexp_alt ls) ++ " . " ++ print_sexp_alt lst ++ ")")`
 (WF_REL_TAC`measure sexp_size` >> rw[] >> simp[simpleSexpTheory.sexp_size_def] >>
   fs[Once simpleSexpParseTheory.strip_dot_def] >>
   pairarg_tac \\ fs[] \\ rw[simpleSexpTheory.sexp_size_def] \\ fs[]
   \\ imp_res_tac simpleSexpParseTheory.strip_dot_MEM_sizelt
   \\ imp_res_tac simpleSexpParseTheory.strip_dot_last_sizeleq
   \\ fsrw_tac[boolSimps.DNF_ss][] \\ simp[]
   \\ fs[LENGTH_EQ_NUM_compute] \\ rw[] \\ fs[]
   \\ res_tac \\ simp[]);

Theorem strip_dot_EQ_NILSOME:
  strip_dot s = ([], SOME x) ⇒ s = x
Proof
  Cases_on ‘s’ >> simp[AllCaseEqs()] >> pairarg_tac >> simp[]
QED

Theorem print_sexp_alt_thm:
  print_sexp s = print_sexp_alt s
Proof
  `?n. n = sexp_size s` by rw[] >>
  pop_assum mp_tac >>
  qid_spec_tac `s` >> qid_spec_tac `n` >>
  ho_match_mp_tac COMPLETE_INDUCTION >>
  rpt strip_tac >> Cases_on `s` >>
  fs[simpleSexpParseTheory.print_sexp_def,print_sexp_alt_def,IMPLODE_EXPLODE_I,
     sexp_size_def, PULL_FORALL] >>
  pairarg_tac >> fs[] >> every_case_tac >>
  gvs[STRCAT_11, LENGTH_EQ_NUM_compute, PULL_EXISTS] >>
  pairarg_tac >> gvs[]
  >- (first_x_assum irule >> dxrule strip_dot_MEM_sizelt >> simp[])
  >- (drule strip_dot_last_sizelt >> dxrule strip_dot_MEM_sizelt >> simp[])
  >- (dxrule strip_dot_MEM_sizelt >>
      disch_then (C (resolve_then Any assume_tac)
                  (DECIDE “x < y ⇒ x < a + (y + 1n)”)) >>
      pop_assum (first_assum o resolve_then Any assume_tac) >>
      simp[Cong MAP_CONG] >> simp[SF ETA_ss])
  >- (drule strip_dot_last_sizelt >> drule strip_dot_MEM_sizelt >> simp[] >>
      rename [‘strip_dot s0 = (els, SOME _)’] >>
      Cases_on ‘NULL els’ >> gs[] >>
      disch_then (C (resolve_then Any assume_tac)
                  (DECIDE “x < y ⇒ x < a + (y + 1n)”)) >>
      pop_assum (first_assum o resolve_then Any assume_tac) >>
      simp[Cong MAP_CONG] >> simp[SF ETA_ss] >>
      Cases_on ‘els’ >> gs[] >>
      dxrule strip_dot_EQ_NILSOME >> simp[])
QED

val _ = translate print_sexp_alt_def;

val print_sexp_alt_side = Q.prove(
  `!x. print_sexp_alt_side x = T`,
  ho_match_mp_tac print_sexp_ind >> rw[] >>
  rw[Once(fetch "-" "print_sexp_alt_side_def")] >>
  fs[LENGTH_EQ_NUM_compute]) |> update_precondition;

val _ = translate print_sexp_alt_thm;

val listsexp_alt = Q.prove(`listsexp = FOLDR (λs1 s2. SX_CONS s1 s2) nil`,
  rpt(CHANGED_TAC(CONV_TAC (DEPTH_CONV ETA_CONV))) >> simp[listsexp_def]);

val _ = translate listsexp_alt

val _ = translate (locnsexp_def |> SIMP_RULE list_ss []);

val _ = ml_translatorLib.use_string_type false;

val _ = translate HEX_def

val l2n_side_thm = Q.prove(`!n l. l2n_side n l <=> (l <> [] ==> n <> 0)`,
  strip_tac >>
  Induct >>
  rpt strip_tac >>
  PURE_ONCE_REWRITE_TAC[lexerProgTheory.l2n_side_def] >>
  rw[] >>
  Cases_on `l = []` >> fs[])

val s2n_side_thm = Q.prove(`!n f l. s2n_side n f l <=> (l <> [] ==> n <> 0)`,
  rw[l2n_side_thm,lexerProgTheory.s2n_side_def]);

val hex_alt_def = Define `hex_alt x = if x < 16 then HEX x else #"0"`

val num_to_hex_string_alt =
    Define `num_to_hex_string_alt = n2s 16 hex_alt`

Theorem num_to_hex_string_alt_intro:
  !n. num_to_hex_string n = num_to_hex_string_alt n
Proof
  simp[num_to_hex_string_def,num_to_hex_string_alt,n2s_def] >>
  ho_match_mp_tac COMPLETE_INDUCTION >>
  rw[] >>
  PURE_ONCE_REWRITE_TAC[numposrepTheory.n2l_def] >>
  rw[hex_alt_def]
QED

val _ = translate hex_alt_def

val _ = Q.prove(`!n. hex_alt_side n <=> T`,
 PURE_REWRITE_TAC[fetch "-" "hex_alt_side_def",fetch "-" "hex_side_def"] >>
 intLib.COOPER_TAC) |> update_precondition;

val _ = translate numposrepTheory.n2l_def;

val n2l_side_thm = Q.prove(`!n m. n2l_side n m <=> n <> 0`,
  strip_tac >>
  ho_match_mp_tac COMPLETE_INDUCTION >>
  rpt strip_tac >>
  PURE_ONCE_REWRITE_TAC[fetch "-" "n2l_side_def"] >>
  rw[]) |> update_precondition

val  _ = translate n2s_def;

val n2s_side_thm = Q.prove(`!n f m. n2s_side n f m <=> n <> 0`,
  rpt strip_tac >>
  PURE_ONCE_REWRITE_TAC[fetch "-" "n2s_side_def"] >>
  rw[n2l_side_thm]) |> update_precondition

val _ = translate num_to_hex_string_alt;

val _ = translate num_to_hex_string_alt_intro;

val r = translate fromSexpTheory.encode_control_def

val _ = use_string_type true;

val _ = translate SEXSTR_def;

val _ = translate litsexp_def;

val litsexp_side_thm = Q.prove(`!v. litsexp_side v <=> T`,
  PURE_ONCE_REWRITE_TAC[fetch "-" "litsexp_side_def"] >> rw[] >>
  intLib.COOPER_TAC) |> update_precondition

val _ = translate optsexp_def;
val _ = translate idsexp_def;
val _ = translate typesexp_def;
val _ = translate patsexp_def;
val _ = translate opsexp_def;
val _ = translate lopsexp_def;
val _ = translate scsexp_def;
val _ = translate locssexp_def;
val _ = translate expsexp_def;
val _ = translate type_defsexp_def;
val _ = translate decsexp_def;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);

val _ = export_theory();
