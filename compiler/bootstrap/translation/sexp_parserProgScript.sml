(*
  Translate the s-expression parser and fromSexp functions.
*)
Theory sexp_parserProg
Ancestors
  decodeProg ml_translator fromSexp
Libs
  preamble ml_translatorLib

open preamble decodeProgTheory
     ml_translatorLib ml_translatorTheory
     fromSexpTheory;

val _ = temp_delsimps ["NORMEQ_CONV"]

val _ = translation_extends "decodeProg";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "sexp_parserProg");
val _ = ml_translatorLib.use_sub_check true;

val monad_unitbind_assert = parserProgTheory.monad_unitbind_assert;

Theorem OPTION_BIND_THM:
   !x y. OPTION_BIND x y = case x of NONE => NONE | SOME i => y i
Proof
  Cases THEN SRW_TAC [] []
QED
(* -- *)

val r = fromSexpTheory.sexplist_def
        |> SIMP_RULE std_ss [OPTION_BIND_THM]
        |> translate;

val r = translate fromSexpTheory.dstrip_sexp_def


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
  fs[isDigit_def, ASCIInumbersTheory.UNHEX_def]
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
  \\ intLib.COOPER_TAC
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

Theorem lemma[local]:
  isHexDigit x ∧ isHexDigit y ∧ A ∧ B ∧ ¬isPrint (CHR (num_from_hex_string[x;y])) ⇔
  isHexDigit x ∧ isHexDigit y ∧ A ∧ B ∧ ¬isPrint (CHR (num_from_hex_string_alt[x;y]))
Proof
  rw[EQ_IMP_THM,num_from_hex_string_alt_intro]
  \\ rfs[num_from_hex_string_alt_intro]
QED

Theorem lemma2[local]:
  isHexDigit x ∧ isHexDigit y ⇒
  num_from_hex_string [x;y] = num_from_hex_string_alt [x;y]
Proof
  rw[num_from_hex_string_alt_intro]
QED

val _ = add_preferred_thy "-";

val r = fromSexpTheory.decode_control_def
        |> SIMP_RULE std_ss [monad_unitbind_assert,lemma,lemma2]
        |> translate_no_ind;

Theorem decode_control_ind[local]:
  decode_control_ind
Proof
  once_rewrite_tac [fetch "-" "decode_control_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ gvs [FORALL_PROD]
  \\ rfs [num_from_hex_string_alt_intro]
QED

val _ = decode_control_ind |> update_precondition;

val decode_control_side = Q.prove(
  `∀x. decode_control_side x = T`,
  ho_match_mp_tac fromSexpTheory.decode_control_ind \\
  rw[Once(theorem"decode_control_side_def")] \\
  rw[Once(theorem"decode_control_side_def")] \\ rfs[] \\
  rw[num_from_hex_string_alt_length_2] \\
  rfs [num_from_hex_string_alt_intro] \\
  rename1 `decode_control_side x1` \\
  Cases_on`x1` \\ fs[] \\
  rw[Once(theorem"decode_control_side_def")] \\
  rw[Once(theorem"decode_control_side_def")])
  |> update_precondition

Definition decode_control_wrapper_def:
  decode_control_wrapper s =
    case decode_control (explode s) of
      NONE => NONE
    | SOME x => SOME (implode x)
End

val r = translate decode_control_wrapper_def

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

val r = translate sexptype_alt_def;

val r = translate fromSexpTheory.sexppair_def;

val r = fromSexpTheory.sexptype_def_def
        |> SIMP_RULE std_ss [sexptype_alt_intro1]
        |> translate;

val r = translate optionTheory.OPTION_APPLY_def;

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

val r = translate encode_thunk_mode_def;
val r = translate decode_thunk_mode_def;

val _ = fromSexpTheory.decode_test_def |> translate;
val _ = fromSexpTheory.decode_prim_type_def |> translate;
val _ = fromSexpTheory.sexparith_def |> translate;

val r = translate (fromSexpTheory.sexpop_def
                   |> REWRITE_RULE [decode_control_eq]);

val r = translate fromSexpTheory.sexplog_def;

val r = translate sexpexp_alt_def;

val r = translate fromSexpTheory.sexpdec_alt_def

val sexpdec_alt_side = Q.prove(
  `(∀x. sexpdec_alt_side x = T) ∧
   (∀x. sexpdec_list_side x = T)`,
  ho_match_mp_tac sexpdec_alt_ind
  \\ rw[]
  \\ rw[Once(fetch"-""sexpdec_alt_side_def")]
  \\ fs[LENGTH_EQ_NUM_compute])
  |> update_precondition;

val _ = translate fromSexpTheory.listsexp_def;

val _ = translate (locnsexp_def |> SIMP_RULE list_ss []);

val _ = translate HEX_def

Theorem l2n_side_thm[local]:
  !n l. l2n_side n l <=> (l <> [] ==> n <> 0)
Proof
  strip_tac >>
  Induct >>
  rpt strip_tac >>
  PURE_ONCE_REWRITE_TAC[lexerProgTheory.l2n_side_def] >>
  rw[] >>
  Cases_on `l = []` >> fs[]
QED

Theorem s2n_side_thm[local]:
  !n f l. s2n_side n f l <=> (l <> [] ==> n <> 0)
Proof
  rw[l2n_side_thm,lexerProgTheory.s2n_side_def]
QED

Definition hex_alt_def:
  hex_alt x = if x < 16 then HEX x else #"0"
End

Definition num_to_hex_string_alt:
  num_to_hex_string_alt = n2s 16 hex_alt
End

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

val _ = translate SEXSTR_def;

val _ = translate litsexp_def;

val litsexp_side_thm = Q.prove(`!v. litsexp_side v <=> T`,
  PURE_ONCE_REWRITE_TAC[fetch "-" "litsexp_side_def"] >> rw[] >>
  intLib.COOPER_TAC) |> update_precondition

val _ = translate optsexp_def;
val _ = translate idsexp_def;
val _ = translate typesexp_def;
val _ = translate patsexp_def;
val _ = translate prim_typesexp_def;
val _ = translate testsexp_def;
val _ = translate arithsexp_def;
val _ = translate opsexp_def;
val _ = translate logsexp_def;
val _ = translate locssexp_def;
val _ = translate expsexp_def;
val _ = translate type_defsexp_def;
val _ = translate decsexp_def;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);
