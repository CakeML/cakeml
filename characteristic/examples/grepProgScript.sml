open preamble ml_translatorLib ml_progLib
     ioProgTheory basisFunctionsLib
     charsetTheory regexpTheory regexp_parserTheory regexp_compilerTheory

val _ = new_theory "grepProg";

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

(* TODO: translate balanced_map module separately? *)
val _ = pick_name :=
  let val default = !pick_name in
    fn c =>
    if same_const c ``balanced_map$member`` then "balanced_map_member" else
    if same_const c ``balanced_map$empty`` then "balanced_map_empty" else
      default c
  end

val spec64 = INST_TYPE[alpha|->``:64``]
val _ = translate(word_bit_test |> spec64);

val _ = translate (charsetTheory.charset_full_def |> CONV_RULE (RHS_CONV EVAL));
val _ = translate charset_mem_def;

(* TODO: can the regexp one be avoided by using the mllist one instead? *)
val zip_eq_zip = Q.store_thm("zip_eq_zip",
  `regexp$zip = mllist$zip`,
  simp[FUN_EQ_THM]
  \\ ho_match_mp_tac mllistTheory.zip_ind
  \\ EVAL_TAC \\ rw[]);

val r = save_thm("regexp_compareW_ind", regexp_compareW_ind |> REWRITE_RULE[zip_eq_zip])
val _ = add_preferred_thy"-";
val r = translate (regexp_compareW_def |> REWRITE_RULE[zip_eq_zip]);

val r = save_thm("mergesortN_ind", mergesortTheory.mergesortN_ind |> REWRITE_RULE[GSYM mllistTheory.drop_def]);
val r = translate (mergesortTheory.mergesortN_def |> REWRITE_RULE[GSYM mllistTheory.drop_def]);

val _ = use_mem_intro := true;
val r = translate build_or_def;
val _ = use_mem_intro := false;

val r = translate (normalize_def);

val r = translate mem_regexp_def;
val r = translate exec_dfa_def;

val r = translate Brz_def;

(* Version of compile_regexp that avoids dom_Brz and Brzozo.
   The latter functions are probably untranslatable. *)
val compile_regexp_with_limit_def =
 Define
   `compile_regexp_with_limit r =
      let r' = normalize r in
      case Brz balanced_map$empty [r']
               (1n, balanced_map$singleton r' 0n, []) MAXNUM_32 of
          NONE => NONE
        | SOME(states,last_state,state_numbering,table) =>
      (let delta_vecs = table_to_vectors table in
      let accepts_vec = accepts_to_vector (get_accepts state_numbering) last_state
      in
         SOME(state_numbering,
          delta_vecs,
          accepts_vec))`;

val Brz_sound_wrt_Brzozo = Q.store_thm("Brz_sound_wrt_Brzozo",
  `Brz seen worklist acc d = SOME result ==> Brzozo seen worklist acc = result`,
  rpt strip_tac
  >> `IS_SOME (Brz seen worklist acc d)`
       by rw[optionTheory.IS_SOME_DEF]
  >> `IS_SOME (Brz seen worklist acc (rdepth seen worklist acc))`
       by (rw[optionTheory.IS_SOME_DEF] >> metis_tac [rdepth_thm])
  >> `Brz seen worklist acc d = Brz seen worklist acc (rdepth seen worklist acc)`
       by metis_tac [Brz_determ]
  >> fs[Brzozo_def]);

val Brz_sound_wrt_Brzozowski = Q.store_thm("Brz_sound_wrt_Brzozowski",
  `Brz seen worklist acc d = SOME result ==> Brzozowski seen worklist acc = result`,
  rpt strip_tac
  >> `IS_SOME (Brz seen worklist acc d)`
       by rw[optionTheory.IS_SOME_DEF]
  >> rw[Brzozowski_def,dom_Brz_def]
  >> metis_tac[Brz_sound_wrt_Brzozo]);

val compile_regexp_with_limit_sound = Q.store_thm("compile_regexp_with_limit_sound",
  `compile_regexp_with_limit r = SOME result ==> compile_regexp r = result`,
  fs[compile_regexp_with_limit_def,compile_regexp_def]
  >> every_case_tac
  >> IMP_RES_TAC Brz_sound_wrt_Brzozowski
  >> rw[pairTheory.ELIM_UNCURRY]);

val r = translate compile_regexp_with_limit_def;

val regexp_matcher_with_limit_def =
 Define
  `regexp_matcher_with_limit r s =
    case compile_regexp_with_limit r of
           NONE => NONE
         | SOME (state_numbering,deltaL,accepts) =>
   (let start_state = THE (balanced_map$lookup regexp_compare
                               (normalize r) state_numbering) in
    let acceptsV = fromList accepts in
    let deltaV = fromList (MAP fromList deltaL)
    in
      SOME(exec_dfa acceptsV deltaV start_state s))`;

val regexp_matcher_with_limit_sound = Q.store_thm("regexp_matcher_with_limit_sound",
  `regexp_matcher_with_limit r s = SOME result ==> regexp_matcher r s = result`,
  fs[regexp_matcher_with_limit_def,regexp_matcher_def]
  >> every_case_tac
  >> IMP_RES_TAC compile_regexp_with_limit_sound
  >> rw[pairTheory.ELIM_UNCURRY]);

val _ = translate (regexp_matcher_with_limit_def);

val mem_tolist = Q.prove(`MEM (toList l) (MAP toList ll) = MEM l ll`,
  Induct_on `ll` >> fs[]);

val EL_map_toList = Q.prove(`!n. n < LENGTH l ==> EL n' (EL n (MAP toList l)) = sub (EL n l) n'`,
  Induct_on `l`
  >> fs[]
  >> rpt strip_tac
  >> Cases_on `n`
  >> fs[mlvectorTheory.EL_toList]);

val length_tolist_cancel = Q.prove(
  `!n. n < LENGTH l ==> LENGTH (EL n (MAP mlvector$toList l)) = length (EL n l)`,
  Induct_on `l`
  >> fs[]
  >> rpt strip_tac
  >> Cases_on `n`
  >> fs[mlvectorTheory.length_toList]);

val exec_dfa_side_imp = Q.prove(
  `!finals table n s.
   good_vec (MAP toList (toList table)) (toList finals)
    /\ EVERY (λc. MEM (ORD c) ALPHABET) (EXPLODE s)
    /\ n < length finals
   ==> exec_dfa_side finals table n s`,
  Induct_on `s`
  >- fs[fetch "-" "exec_dfa_side_def"]
  >> PURE_ONCE_REWRITE_TAC [fetch "-" "exec_dfa_side_def"]
  >> fs[good_vec_def,mlvectorTheory.length_toList]
  >> rpt GEN_TAC
  >> Induct_on `table`
   >> rpt strip_tac
   >> fs[sub_def,length_def,mlvectorTheory.toList_thm]
   >> `MEM (toList (EL n l)) (MAP toList l)`
        by fs[EL_MEM,mem_tolist,mlvectorTheory.toList_thm]
   >- metis_tac[mlvectorTheory.length_toList]
   >> first_x_assum(MATCH_MP_TAC o Q.SPECL [`finals`,`Vector l`, `x1`])
    >> rpt strip_tac
    >> fs[mlvectorTheory.toList_thm, length_def, mem_tolist]
    >- metis_tac[]
    >> first_x_assum(ASSUME_TAC o Q.SPECL [`toList (EL n l)`,`ORD h`])
    >> first_x_assum(MATCH_MP_TAC o Q.SPECL [`n`,`ORD h`,`x1`])
    >> rfs[mlvectorTheory.length_toList,mem_tolist,EL_map_toList,length_tolist_cancel]);

val compile_regexp_with_limit_dom_brz = Q.prove(
  `!r result.
    compile_regexp_with_limit r = SOME result
    ==> dom_Brz empty [normalize r] (1,singleton (normalize r) 0, [])`,
  rw[compile_regexp_with_limit_def, dom_Brz_def, MAXNUM_32_def]
  >> every_case_tac
  >> metis_tac [IS_SOME_EXISTS]);

val compile_regexp_with_limit_lookup = Q.prove(
  `!r state_numbering delta accepts.
   compile_regexp_with_limit r = SOME(state_numbering,delta,accepts)
   ==> IS_SOME(lookup regexp_compare (normalize r) state_numbering)`,
  rpt strip_tac
  >> `normalize r ∈ fdom regexp_compare state_numbering`
       by(metis_tac[compile_regexp_with_limit_dom_brz,
                    compile_regexp_good_vec,
                    compile_regexp_with_limit_sound])
  >> fs[eq_cmp_bmapTheory.fdom_def]);

val tolist_fromlist_map_cancel = Q.store_thm("tolist_fromlist_map_cancel",
  `MAP mlvector$toList (MAP fromList ll) = ll`,
  Induct_on `ll` >> fs[]);

val regexp_matcher_with_limit_side_def = Q.prove(
  `!r s. regexp_matcher_with_limit_side r s ⇔ T`,
  rw[fetch "-" "regexp_matcher_with_limit_side_def"]
  >> rpt strip_tac
  >- (match_mp_tac exec_dfa_side_imp
      >> rpt strip_tac
      >- (rw[tolist_fromlist_map_cancel]
       >> metis_tac[compile_regexp_with_limit_dom_brz,
                    compile_regexp_good_vec,
                    compile_regexp_with_limit_sound])
      >- simp_tac list_ss [mem_alphabet_iff,ORD_BOUND,alphabet_size_def]
      >- (first_assum(ASSUME_TAC o MATCH_MP compile_regexp_with_limit_lookup)
          >> fs[IS_SOME_EXISTS,length_def,fromList_def]
          >> first_assum(fn thm =>
                         ASSUME_TAC(CONJ (MATCH_MP compile_regexp_with_limit_dom_brz thm)
                                         (MATCH_MP compile_regexp_with_limit_sound thm)))
          >> first_assum (ASSUME_TAC o MATCH_MP compile_regexp_good_vec)
          >> fs[good_vec_def] >> metis_tac []))
  >- metis_tac [compile_regexp_with_limit_lookup]) |> update_precondition;

(* TODO: translate PEG machinery as separate module?
         n.b. INTRO_FLOOKUP is copied from parserProgScript.sml
*)

val INTRO_FLOOKUP = Q.store_thm("INTRO_FLOOKUP",
  `(if n IN FDOM G.rules
     then EV (G.rules ' n) i r y fk
     else Result xx) =
    (case FLOOKUP G.rules n of
       NONE => Result xx
     | SOME x => EV x i r y fk)`,
  SRW_TAC [] [finite_mapTheory.FLOOKUP_DEF]);

val coreloop_def' =
( pegexecTheory.coreloop_def
    |> REWRITE_RULE [INTRO_FLOOKUP]
    |> SPEC_ALL |> ONCE_REWRITE_RULE [FUN_EQ_THM]);

val r = translate coreloop_def';

val r = translate (pegexecTheory.peg_exec_def);

(* -- *)

(* TODO: translate shifts as part of a separate module? word module? *)

val r = translate (shift_left_def |> spec64 |> CONV_RULE (wordsLib.WORD_CONV));

(* -- *)

val r = translate (charset_sing_def |> SIMP_RULE(srw_ss())[shift_left_rwt]);

val _ = use_mem_intro := true;
val r = translate EscapableChar_def;
val _ = use_mem_intro := false;

val r = translate uncharset_char_def
val uncharset_char_side = Q.prove(
  `!x. uncharset_char_side x = T`,
    rw[definition"uncharset_char_side_def"]
    \\ once_rewrite_tac[WORD_AND_COMM]
    \\ `255n = 2 ** 8 - 1` by simp[] \\ pop_assum SUBST1_TAC
    \\ rename1`w  && _` \\ Cases_on`w`
    \\ simp[WORD_AND_EXP_SUB1]
    \\ `n MOD 256 < 256` by simp[]
    \\ simp[]) |> update_precondition;

val r = translate rePEG_def;

val r = translate parse_regexp_def;

val termination_lemma =
  MATCH_MP pegexecTheory.coreloop_total wfG_rePEG
  |> SIMP_RULE(srw_ss())[coreloop_def']

val parse_regexp_side = Q.prove(
  `∀x. parse_regexp_side x = T`,
  rw[definition"parse_regexp_side_def"] \\
  rw[definition"peg_exec_side_def"] \\
  rw[definition"coreloop_side_def"] \\
  qspec_then`MAP add_loc x`strip_assume_tac (Q.GEN`i`termination_lemma) \\
  qmatch_abbrev_tac`IS_SOME (OWHILE f g h)` \\
  qmatch_assum_abbrev_tac`OWHILE f g' h = SOME _` \\
  `g' = g` by (
    unabbrev_all_tac
    \\ simp[FUN_EQ_THM]
    \\ Cases \\ simp[]
    \\ TOP_CASE_TAC \\ simp[] ) \\ fs[]) |> update_precondition;

val _ = export_theory ();
