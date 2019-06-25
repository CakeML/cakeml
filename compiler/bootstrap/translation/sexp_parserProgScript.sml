(*
  Translate the alternative s-expression parser.
*)
open preamble explorerProgTheory
     ml_translatorLib ml_translatorTheory
     pegTheory simpleSexpTheory simpleSexpPEGTheory simpleSexpParseTheory fromSexpTheory

val _ = new_theory"sexp_parserProg";
val _ = translation_extends "explorerProg";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "sexp_parserProg");

(* TODO: this is duplicated in parserProgTheory *)
val monad_unitbind_assert = Q.prove(
  `!b x. monad_unitbind (assert b) x = if b then x else NONE`,
  Cases THEN EVAL_TAC THEN SIMP_TAC std_ss []);
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

val r = translate fromSexpTheory.odestSEXSTR_def;
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

(*
val r = fromSexpTheory.sexptctor_def
        |> SIMP_RULE std_ss [OPTION_BIND_THM,monad_unitbind_assert]
        |> translate;
*)

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

val r = translate fromSexpTheory.sexpop_def;
val r = translate fromSexpTheory.sexplop_def;

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

val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);

val _ = export_theory();
