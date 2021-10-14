(*
  Translate the alternative s-expression parser.

  This file is a copy of the one at $(CAKEMLDIR)compiler/bootstrap/translation,
  except I have removed the translation of the s-expression parsing functions.
*)

open preamble caml_ptreeProgTheory ml_translatorLib ml_translatorTheory
     pegTheory simpleSexpTheory simpleSexpPEGTheory simpleSexpParseTheory
     fromSexpTheory

val _ = temp_delsimps ["NORMEQ_CONV"]

val _ = new_theory"sexp_parserProg";
val _ = translation_extends "caml_ptreeProg";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "sexp_parserProg");
val _ = ml_translatorLib.use_string_type true;

val r = translate stringTheory.isPrint_def
val _ = translate simpleSexpParseTheory.print_space_separated_def;

Theorem strip_dot_alt =
  simpleSexpParseTheory.strip_dot_def |> PURE_ONCE_REWRITE_RULE [CONS_APPEND];
val _ = translate strip_dot_alt


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
   \\ fs[quantHeuristicsTheory.LIST_LENGTH_2] \\ rw[] \\ fs[]
   \\ res_tac \\ simp[]);

Theorem print_sexp_alt_thm:
  print_sexp s = print_sexp_alt s
Proof
  `?n. n = sexp_size s` by rw[] >>
  pop_assum mp_tac >>
  qid_spec_tac `s` >> qid_spec_tac `n` >>
  ho_match_mp_tac COMPLETE_INDUCTION >>
  rpt strip_tac >> Cases_on `s` >>
  fs[simpleSexpParseTheory.print_sexp_def,print_sexp_alt_def,IMPLODE_EXPLODE_I,sexp_size_def] >>
  pairarg_tac >> fs[] >> every_case_tac >> fs[STRCAT_11] >>
  TRY(first_x_assum (match_mp_tac o MP_CANON) >>
      rw[] >>
      imp_res_tac simpleSexpParseTheory.strip_dot_MEM_sizelt >>
      rfs[MEM_EL,ELIM_UNCURRY,PULL_EXISTS] >>
      fs[sexp_size_def]) >>
  TRY(rename1 `print_sexp x` >>
      `print_sexp x = print_sexp_alt x`
        by(first_x_assum (match_mp_tac o MP_CANON) >>
           rw[] >>
           imp_res_tac simpleSexpParseTheory.strip_dot_last_sizelt >>
           fs[sexp_size_def] >> fs[quantHeuristicsTheory.LIST_LENGTH_2] >>
           fs[Once strip_dot_def,ELIM_UNCURRY] >> rveq >> fs[])) >>
  fs[STRCAT_11] >>
  qmatch_goalsub_abbrev_tac `_ a1 = _ a2` >>
  `a1 = a2` suffices_by simp[] >>
  unabbrev_all_tac >>
  match_mp_tac LIST_EQ >>
  rw[EL_MAP] >>
  first_x_assum (match_mp_tac o MP_CANON) >>
  rw[] >>
  imp_res_tac simpleSexpParseTheory.strip_dot_MEM_sizelt >>
  rfs[MEM_EL,ELIM_UNCURRY,PULL_EXISTS] >>
  fs[sexp_size_def]
QED

val _ = translate EL;

val _ = translate print_sexp_alt_def;

val print_sexp_alt_side = Q.prove(
  `!x. print_sexp_alt_side x = T`,
  ho_match_mp_tac print_sexp_ind >> rw[] >>
  rw[Once(fetch "-" "print_sexp_alt_side_def")] >>
  fs[quantHeuristicsTheory.LIST_LENGTH_2]
  \\ rw [fetch "-" "el_side_def"]) |> update_precondition;

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
  PURE_ONCE_REWRITE_TAC[caml_lexProgTheory.l2n_side_def] >>
  rw[] >>
  Cases_on `l = []` >> fs[])

val s2n_side_thm = Q.prove(`!n f l. s2n_side n f l <=> (l <> [] ==> n <> 0)`,
  rw[l2n_side_thm,caml_lexProgTheory.s2n_side_def]);

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
val _ = translate locssexp_def;
val _ = translate expsexp_def;
val _ = translate type_defsexp_def;
val _ = translate decsexp_def;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);

val _ = export_theory();

