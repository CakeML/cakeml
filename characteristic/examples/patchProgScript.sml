open preamble ml_translatorLib ml_progLib
     cfTacticsLib basisFunctionsLib
     rofsFFITheory mlfileioProgTheory ioProgTheory
     charsetTheory diffTheory mlstringTheory;

val _ = new_theory "patchProg";

val _ = translation_extends"ioProg";

fun def_of_const tm = let
  val res = dest_thy_const tm handle HOL_ERR _ =>
              failwith ("Unable to translate: " ^ term_to_string tm)
  val name = (#Name res)
  fun def_from_thy thy name =
    DB.fetch thy (name ^ "_def") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_DEF") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_thm") handle HOL_ERR _ =>
    DB.fetch thy name
  val def = def_from_thy (#Thy res) name handle HOL_ERR _ =>
            failwith ("Unable to find definition of " ^ name)
  in def end

val _ = find_def_for_const := def_of_const;

(* Circumvents a problem where the translator generates unprovable side conditions
   for higher-order functions *)
val unhex_all_def = Define `(unhex_all [] = []) /\ (unhex_all (a::b) = UNHEX a::unhex_all b)`

val unhex_map = Q.prove(`!s. unhex_all s = MAP UNHEX s`, Induct >> fs[unhex_all_def])

val s2n_UNHEX_def = Define `s2n_UNHEX b s = l2n b (unhex_all (REVERSE s))`

val num_from_dec_string_thm = Q.store_thm("num_from_dec_string_thm",
  `!s. toNum s = s2n_UNHEX 10 s`,
  rw[ASCIInumbersTheory.num_from_dec_string_def,s2n_UNHEX_def,ASCIInumbersTheory.s2n_def,
     unhex_map]);

val _ = translate num_from_dec_string_thm;

val l2n_side_IMP = Q.prove(`∀n l. n <> 0 ==> l2n_side n l = T`,
  strip_tac >> Induct >> rw[Once(fetch "-" "l2n_side_def")]);

val unhex_side = Q.prove(`!c. unhex_side c <=> isHexDigit c`,
  Cases >> fs[isHexDigit_def] >> PURE_ONCE_REWRITE_TAC[fetch "-" "unhex_side_def"]
        >> PURE_REWRITE_TAC[AC DISJ_ASSOC DISJ_COMM]
        >> PURE_REWRITE_TAC [GSYM DISJ_ASSOC,AND_CLAUSES]
        >> PURE_ONCE_REWRITE_TAC[EQ_IMP_THM]
        >> rpt strip_tac >> rfs[CHR_11]) |> update_precondition

val unhex_all_side = Q.prove(`!s. unhex_all_side s <=> EVERY isHexDigit s`,
  Induct >> PURE_ONCE_REWRITE_TAC[fetch "-" "unhex_all_side_def"]>> fs[unhex_side])
  |> update_precondition;
                        
val s2n_unhex_side_IMP = Q.prove(`∀n s. n <> 0 ==> s2n_unhex_side n s = EVERY isHexDigit s`,
  rpt strip_tac
  >> rw[Once(fetch "-" "s2n_unhex_side_def"),l2n_side_IMP,unhex_all_side,EVERY_REVERSE]);

val num_from_dec_string_side = Q.prove(`
  ∀s. num_from_dec_string_side s = EVERY isHexDigit s`,
  fs[fetch "-" "num_from_dec_string_side_def",s2n_unhex_side_IMP]) |> update_precondition;

val _ = translate parse_patch_header_def;

fetch "-" "fromstring_side_def"

val tokens_less_eq = Q.prove(`!s f. EVERY (\x. strlen x <= strlen s) (tokens f s)`,
  Induct >> Ho_Rewrite.PURE_ONCE_REWRITE_TAC[SWAP_FORALL_THM]
  >> PURE_ONCE_REWRITE_TAC[TOKENS_eq_tokens_sym]
  >> recInduct TOKENS_ind >> rpt strip_tac
  >> fs[TOKENS_def] >> pairarg_tac >> reverse(Cases_on `l`) >> rw[]
  >- (drule SPLITP_JOIN >> fs[implode_def,strlen_def])
  >> fs[SPLITP_NIL_FST,SPLITP] >> every_case_tac >> fs[]
  >- (`!x. (λx. strlen x <= STRLEN r) x ==> (λx. strlen x <= SUC (STRLEN t)) x`
       by(rpt strip_tac >> PURE_ONCE_REWRITE_TAC[SPLITP_LENGTH] >> fs[])
       >> drule EVERY_MONOTONIC >> pop_assum kall_tac >> disch_then match_mp_tac >> rw[])
  >> `!x. (λx. strlen x <= STRLEN t) x ==> (λx. strlen x <= SUC (STRLEN t)) x` by fs[]
  >> drule EVERY_MONOTONIC >> pop_assum kall_tac >> disch_then match_mp_tac >> rw[]);

val tokens_sum_less_eq = Q.prove(`!s f. SUM(MAP strlen (tokens f s)) <= strlen s`,
  Induct >> Ho_Rewrite.PURE_ONCE_REWRITE_TAC[SWAP_FORALL_THM]
  >> PURE_REWRITE_TAC[TOKENS_eq_tokens_sym,explode_thm,MAP_MAP_o]
  >> recInduct TOKENS_ind >> rpt strip_tac
  >> fs[TOKENS_def] >> pairarg_tac >> fs[] >> Cases_on `l` >> rw[] >> rfs[]
  >> fs[SPLITP_NIL_FST] >> fs[SPLITP] >> every_case_tac
  >> PURE_ONCE_REWRITE_TAC[SPLITP_LENGTH] >> fs[strlen_def,implode_def]);

val tokens_not_nil = Q.prove(`!s f. EVERY (\x. x <> strlit "") (tokens f s)`,
  Induct >> Ho_Rewrite.PURE_ONCE_REWRITE_TAC[SWAP_FORALL_THM]
  >> PURE_REWRITE_TAC[TOKENS_eq_tokens_sym,explode_thm]
  >> recInduct TOKENS_ind >> rpt strip_tac
  >> rw[TOKENS_def] >> pairarg_tac >> fs[] >> reverse(Cases_on `l`)
  >> fs[implode_def]);
  
val tokens_two_less = Q.prove(`!s f s1 s2. tokens f s = [s1;s2] ==> strlen s1 < strlen s /\ strlen s2 < strlen s`,
  ntac 2 strip_tac >> qspecl_then [`s`,`f`] assume_tac tokens_sum_less_eq
  >> qspecl_then [`s`,`f`] assume_tac tokens_not_nil
  >> Induct >> Cases >> Induct >> Cases >> rpt strip_tac >> fs[]);

val hexDigit_IMP_digit = Q.store_thm("hexDigit_IMP_digit",`!c. isDigit c ==> isHexDigit c`,
  rw[isHexDigit_def,isDigit_def]);


val parse_patch_header_side = Q.prove(`!s. parse_patch_header_side s = T`,
  rw[fetch "-" "parse_patch_header_side_def",
     fetch "-" "num_from_string_side_def",
     fetch "-" "fromstring_side_def"]
  >> TRY(match_mp_tac(MATCH_MP EVERY_MONOTONIC hexDigit_IMP_digit) >> fs[string_is_num_def])
  >> TRY(match_mp_tac hexDigit_IMP_digit >> fs[string_is_num_def])
  >> metis_tac[tokens_two_less]) |> update_precondition;

val _ = translate patch_alg_def;

val inputLines = process_topdecs`
  fun inputLines fd =
    let
      fun loop() =
        case inputLine fd of
             NONE => []
           | SOME l => l::loop()
    in
      loop()
    end`

val _ = append_prog inputLines;

val _ = export_theory ();
