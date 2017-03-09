open preamble ml_translatorLib ml_progLib
     ioProgTheory cfTacticsLib basisFunctionsLib
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
val _ = ml_translatorLib.pick_name :=
  let val default = !ml_translatorLib.pick_name in
    fn c =>
    if same_const c ``balanced_map$member`` then "balanced_map_member" else
    if same_const c ``balanced_map$empty`` then "balanced_map_empty" else
      default c
  end

val spec64 = INST_TYPE[alpha|->``:64``]
val _ = translate(word_bit_test |> spec64);

val _ = translate (charsetTheory.charset_full_def |> CONV_RULE (RHS_CONV EVAL));
val _ = translate charset_mem_def;

val _ = register_type``:regexp``;

(* TODO: this is largely copied from the bootstrap translation
         can it be properly abstracted out? *)
local
  val ths = ml_translatorLib.eq_lemmas();
in
  fun find_equality_type_thm tm =
    first (can (C match_term tm) o rand o snd o strip_imp o concl) ths
end

val EqualityType_WORD = find_equality_type_thm``WORD``
val EqualityType_CHARSET_CHARSET_TYPE = find_equality_type_thm``CHARSET_CHARSET_TYPE``
  |> REWRITE_RULE[EqualityType_WORD]

val REGEXP_REGEXP_TYPE_def = theorem"REGEXP_REGEXP_TYPE_def";
val REGEXP_REGEXP_TYPE_ind = theorem"REGEXP_REGEXP_TYPE_ind";
val no_closures_def = ml_translatorTheory.no_closures_def;
val LIST_TYPE_def = ml_translatorTheory.LIST_TYPE_def;
val EqualityType_def = ml_translatorTheory.EqualityType_def;
val types_match_def = ml_translatorTheory.types_match_def;
val ctor_same_type_def = semanticPrimitivesTheory.ctor_same_type_def;

val REGEXP_REGEXP_TYPE_no_closures = Q.prove(
  `∀a b. REGEXP_REGEXP_TYPE a b ⇒ no_closures b`,
  ho_match_mp_tac REGEXP_REGEXP_TYPE_ind
  \\ rw[REGEXP_REGEXP_TYPE_def]
  \\ rw[no_closures_def]
  \\ TRY (
    qmatch_assum_rename_tac`LIST_TYPE _ x1 y1` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    last_x_assum mp_tac >>
    rpt(pop_assum kall_tac) >>
    map_every qid_spec_tac[`y1`,`x1`] >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS,no_closures_def] >>
    qx_gen_tac`p` >>
    simp[PULL_EXISTS,no_closures_def] >>
    rw[] >>
    METIS_TAC[EqualityType_def] ) >>
  metis_tac[EqualityType_CHARSET_CHARSET_TYPE,
            EqualityType_def]);

val REGEXP_REGEXP_TYPE_types_match = Q.prove(
  `∀a b c d. REGEXP_REGEXP_TYPE a b ∧ REGEXP_REGEXP_TYPE c d ⇒ types_match b d`,
  ho_match_mp_tac REGEXP_REGEXP_TYPE_ind \\
  rw[REGEXP_REGEXP_TYPE_def] \\
  Cases_on`c` \\ fs[REGEXP_REGEXP_TYPE_def,types_match_def,ctor_same_type_def] \\ rw[] \\
  TRY (
    qmatch_assum_rename_tac`LIST_TYPE _ x1 y1` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    qmatch_assum_rename_tac`LIST_TYPE _ x2 y2` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    last_x_assum mp_tac >>
    rpt(pop_assum kall_tac) >>
    map_every qid_spec_tac[`y2`,`x2`,`y1`,`x1`] >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS,types_match_def,ctor_same_type_def] >- (
      Cases >> simp[LIST_TYPE_def,PULL_EXISTS,types_match_def,ctor_same_type_def] ) >>
    qx_gen_tac`p` >>
    gen_tac >> Cases >> simp[PULL_EXISTS,LIST_TYPE_def] >>
    rw[types_match_def,ctor_same_type_def] >>
    PROVE_TAC[EqualityType_def] ) >>
  metis_tac[EqualityType_CHARSET_CHARSET_TYPE,
            EqualityType_def]);

val REGEXP_REGEXP_TYPE_11 = Q.prove(
  `∀a b c d. REGEXP_REGEXP_TYPE a b ∧ REGEXP_REGEXP_TYPE c d ⇒ (a = c ⇔ b = d)`,
  ho_match_mp_tac REGEXP_REGEXP_TYPE_ind \\
  rw[REGEXP_REGEXP_TYPE_def] \\
  Cases_on`c` \\ fs[REGEXP_REGEXP_TYPE_def] \\ rw[EQ_IMP_THM] \\
  TRY (
    qmatch_assum_rename_tac`LIST_TYPE _ x y1` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    qmatch_assum_rename_tac`LIST_TYPE _ x y2` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    last_x_assum mp_tac >>
    rpt(pop_assum kall_tac) >>
    map_every qid_spec_tac[`y2`,`y1`,`x`] >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS] >>
    rw[] >>
    metis_tac[]) >>
  TRY (
    qmatch_assum_rename_tac`LIST_TYPE _ x1 y` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    qmatch_assum_rename_tac`LIST_TYPE _ x2 y` >>
    qhdtm_x_assum`LIST_TYPE`mp_tac >>
    last_x_assum mp_tac >>
    rpt(pop_assum kall_tac) >>
    map_every qid_spec_tac[`y`,`x1`,`x2`] >>
    Induct >> simp[LIST_TYPE_def,PULL_EXISTS] >- (
      Cases \\ rw[LIST_TYPE_def] ) \\
    gen_tac \\ Cases \\ rw[LIST_TYPE_def] >>
    metis_tac[]) >>
  metis_tac[EqualityType_CHARSET_CHARSET_TYPE,
            EqualityType_def]);

val EqualityType_REGEXP_REGEXP_TYPE = Q.store_thm("EqualityType_REGEXP_REGEXP_TYPE",
  `EqualityType REGEXP_REGEXP_TYPE`,
  metis_tac[REGEXP_REGEXP_TYPE_no_closures,REGEXP_REGEXP_TYPE_types_match,REGEXP_REGEXP_TYPE_11,
  EqualityType_def]);

val _ = store_eq_thm EqualityType_REGEXP_REGEXP_TYPE;
(* -- *)

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

val r = translate (regexp_matcher_with_limit_def);

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

(* TODO: move to regexp_compilerTheory *)

val regexp_matcher_correct = Q.store_thm("regexp_matcher_correct",
  `dom_Brz_alt empty [normalize r] ⇒
   (regexp_matcher r s ⇔ s ∈ regexp_lang r)`,
  rw[regexp_matcher_def]
  \\ pairarg_tac \\ fs[]
  \\ imp_res_tac compile_regexp_good_vec
  \\ rfs[dom_Brz_alt_equal,eq_cmp_bmapTheory.fdom_def]
  \\ imp_res_tac Brzozowski_partial_eval_256
  \\ simp[IN_DEF]);

val regexp_matcher_with_limit_termination = Q.store_thm("regexp_matcher_with_limit_termination",
  `dom_Brz_alt empty [normalize r] ⇒
   ∃result. regexp_matcher_with_limit r s = SOME result`,
  rw[regexp_matcher_with_limit_def]
  \\ every_case_tac \\ simp[]
  \\ fs[compile_regexp_with_limit_def]
  \\ every_case_tac \\ fs[]
  \\ fs[dom_Brz_alt_equal
  dom_Brz_def

(* -- *)

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

(* TODO: move *)
val TL_DROP_SUC = Q.store_thm("TL_DROP_SUC",
  `∀x ls. x < LENGTH ls ⇒ TL (DROP x ls) = DROP (SUC x) ls`,
  Induct \\ rw[] \\ Cases_on`ls` \\ fs[]);

(* TODO: replace ALIST_FUPDKEY_unchanged? *)
val ALIST_FUPDKEY_I = Q.store_thm("ALIST_FUPDKEY_I",
  `∀k f alist.
   (∀v. ALOOKUP alist k = SOME v ⇒ f v = v)
   ==> ALIST_FUPDKEY k f alist = alist`,
  ho_match_mp_tac ALIST_FUPDKEY_ind
  \\ rw[ALIST_FUPDKEY_def]);

val ALIST_FUPDKEY_eq = Q.store_thm("ALIST_FUPDKEY_eq",
  `∀k f1 l f2.
   (∀v. ALOOKUP l k = SOME v ⇒ f1 v = f2 v) ⇒
   ALIST_FUPDKEY k f1 l = ALIST_FUPDKEY k f2 l`,
  ho_match_mp_tac ALIST_FUPDKEY_ind \\ rw[ALIST_FUPDKEY_def]);

val A_DELKEY_ALIST_FUPDKEY = Q.store_thm("A_DELKEY_ALIST_FUPDKEY[simp]",
  `∀fd f ls. A_DELKEY fd (ALIST_FUPDKEY fd f ls) = A_DELKEY fd ls`,
  ho_match_mp_tac ALIST_FUPDKEY_ind
  \\ rw[ALIST_FUPDKEY_def,A_DELKEY_def]);

val A_DELKEY_I = Q.store_thm("A_DELKEY_I",
  `∀x ls. (A_DELKEY x ls = ls ⇔ ¬MEM x (MAP FST ls))`,
  Induct_on`ls`
  \\ rw[A_DELKEY_def,FILTER_EQ_ID,MEM_MAP,EVERY_MEM]
  >- metis_tac[]
  \\ rw[EQ_IMP_THM]
  >- (
    `LENGTH (h::ls) ≤ LENGTH ls` by metis_tac[LENGTH_FILTER_LEQ]
    \\ fs[] )
  \\ first_x_assum(qspec_then`h`mp_tac)
  \\ simp[]);

val LENGTH_FIELDS = Q.store_thm("LENGTH_FIELDS",
  `∀ls. LENGTH (FIELDS P ls) = LENGTH (FILTER P ls) + 1`,
  gen_tac
  \\ completeInduct_on`LENGTH ls`
  \\ Cases
  \\ rw[FIELDS_def]
  \\ pairarg_tac \\ fs[]
  \\ rw[] \\ fs[] \\ rw[ADD1]
  \\ fs[NULL_EQ]
  \\ imp_res_tac SPLITP_NIL_IMP
  \\ imp_res_tac SPLITP_NIL_SND_EVERY
  \\ imp_res_tac SPLITP_IMP
  \\ fs[NULL_EQ]
  \\ fs[SPLITP] \\ rfs[] \\ rw[]
  >- ( `FILTER P t = []` by simp[FILTER_EQ_NIL] \\ fs[EVERY_MEM] )
  \\ first_x_assum(qspec_then`LENGTH t`mp_tac) \\ simp[]
  \\ disch_then(qspec_then`t`mp_tac)
  \\ Cases_on`t` \\ rw[FIELDS_def]
  \\ fs[SPLITP] \\ rfs[]
  \\ rfs[NULL_EQ]);

val FIELDS_NEQ_NIL = Q.store_thm("FIELDS_NEQ_NIL[simp]",
  `FIELDS P ls ≠ []`,
  disch_then(assume_tac o Q.AP_TERM`LENGTH`)
  \\ fs[LENGTH_FIELDS]);

val CONCAT_FIELDS = Q.store_thm("CONCAT_FIELDS",
  `∀ls. CONCAT (FIELDS P ls) = FILTER ($~ o P) ls`,
  gen_tac
  \\ completeInduct_on`LENGTH ls`
  \\ Cases
  \\ simp[FIELDS_def]
  \\ pairarg_tac \\ fs[]
  \\ strip_tac
  \\ fs[Once SPLITP]
  \\ Cases_on`P h` \\ fs[] \\ rveq \\ simp[]
  \\ Cases_on`SPLITP P t` \\ fs[]
  \\ Cases_on`NULL r` \\ fs[NULL_EQ]
  >- (
    imp_res_tac SPLITP_NIL_SND_EVERY
    \\ fs[FILTER_EQ_ID] )
  \\ imp_res_tac SPLITP_IMP
  \\ rfs[NULL_EQ]
  \\ imp_res_tac SPLITP_JOIN
  \\ simp[FILTER_APPEND]
  \\ fs[GSYM FILTER_EQ_ID]
  \\ Cases_on`r` \\ fs[] );

val FIELDS_next = Q.store_thm("FIELDS_next",
  `∀ls l1 l2.
   FIELDS P ls = l1::l2 ⇒
   LENGTH l1 < LENGTH ls ⇒
   FIELDS P (DROP (SUC (LENGTH l1)) ls) = l2`,
  gen_tac
  \\ completeInduct_on`LENGTH ls`
  \\ ntac 4 strip_tac
  \\ Cases_on`ls`
  \\ rw[FIELDS_def]
  \\ pairarg_tac \\ fs[]
  \\ every_case_tac \\ fs[NULL_EQ] \\ rw[] \\ fs[]
  \\ imp_res_tac SPLITP_NIL_IMP \\ fs[]
  \\ imp_res_tac SPLITP_IMP \\ fs[]
  \\ imp_res_tac SPLITP_NIL_SND_EVERY \\ fs[]
  \\ rfs[PULL_FORALL,NULL_EQ]
  \\ fs[SPLITP]
  \\ every_case_tac \\ fs[]
  \\ rw[]
  \\ fs[SPLITP]
  \\ Cases_on`SPLITP P t` \\ fs[]
  \\ Cases_on`SPLITP P q` \\ fs[]
  \\ rw[]
  \\ `FIELDS P t = q::FIELDS P (TL r)`
  by (
    Cases_on`t` \\ fs[]
    \\ rw[FIELDS_def,NULL_EQ] )
  \\ first_x_assum(qspecl_then[`t`,`q`,`FIELDS P (TL r)`]mp_tac)
  \\ simp[] );

val FIELDS_full = Q.store_thm("FIELDS_full",
  `∀P ls l1 l2.
   FIELDS P ls = l1::l2 ∧ LENGTH ls ≤ LENGTH l1 ⇒
   l1 = ls ∧ l2 = []`,
  ntac 2 gen_tac
  \\ completeInduct_on`LENGTH ls`
  \\ ntac 4 strip_tac
  \\ Cases_on`ls`
  \\ simp_tac(srw_ss()++LET_ss)[FIELDS_def]
  \\ pairarg_tac \\ pop_assum mp_tac \\ simp_tac(srw_ss())[]
  \\ strip_tac
  \\ IF_CASES_TAC
  >- (
    simp_tac(srw_ss())[]
    \\ strip_tac \\ rveq
    \\ fs[] )
  \\ IF_CASES_TAC
  >- (
    simp_tac(srw_ss())[]
    \\ strip_tac \\ rveq
    \\ fs[NULL_EQ]
    \\ imp_res_tac SPLITP_NIL_SND_EVERY )
  \\ simp_tac(srw_ss())[]
  \\ strip_tac \\ rveq
  \\ Q.ISPEC_THEN`h::t`mp_tac SPLITP_LENGTH
  \\ last_x_assum kall_tac
  \\ simp[]
  \\ strip_tac \\ fs[]
  \\ `LENGTH r = 0` by decide_tac
  \\ fs[LENGTH_NIL]);

val the_nil_eq_cons = Q.store_thm("the_nil_eq_cons",
  `(the [] x = y::z) ⇔ x = SOME (y ::z)`,
  Cases_on`x` \\ EVAL_TAC);

(* -- *)

(* TODO: move to FileIO or rofsFFI *)
open rofsFFITheory mlfileioProgTheory

val _ = temp_add_monadsyntax();

val validFD_bumpFD = Q.store_thm("validFD_bumpFD",
  `validFD fd fs ⇒ validFD fd (bumpFD fd fs)`,
  rw[bumpFD_def]
  \\ CASE_TAC \\ fs[]
  \\ fs[validFD_def]);

val bumpFD_files = Q.store_thm("bumpFD_files[simp]",
  `(bumpFD fd fs).files = fs.files`,
  EVAL_TAC \\ CASE_TAC \\ rw[]);

val ALOOKUP_inFS_fname_openFileFS_nextFD = Q.store_thm("ALOOKUP_inFS_fname_openFileFS_nextFD",
  `inFS_fname f fs ∧ nextFD fs < 255
   ⇒
   ALOOKUP (openFileFS f fs).infds (nextFD fs) = SOME (f,0)`,
  rw[openFileFS_def,openFile_def]
  \\ imp_res_tac inFS_fname_ALOOKUP_EXISTS
  \\ rw[]);

val openFileFS_files = Q.store_thm("openFileFS_files[simp]",
  `(openFileFS f fs).files = fs.files`,
  EVAL_TAC \\ rw[] \\ every_case_tac \\ fs[] \\ rw[]);

val A_DELKEY_nextFD_openFileFS = Q.store_thm("A_DELKEY_nextFD_openFileFS[simp]",
  `nextFD fs < 255 ⇒
   A_DELKEY (nextFD fs) (openFileFS f fs).infds = fs.infds`,
  rw[openFileFS_def]
  \\ CASE_TAC
  \\ TRY CASE_TAC
  \\ simp[A_DELKEY_I,nextFD_NOT_MEM,MEM_MAP,EXISTS_PROD]
  \\ fs[openFile_def] \\ rw[]
  \\ rw[A_DELKEY_def,FILTER_EQ_ID,EVERY_MEM,FORALL_PROD,nextFD_NOT_MEM]);

val FDline_def = Define`
  FDline fd fs =
    do
      (fnm,off) <- ALOOKUP fs.infds fd;
      content <- ALOOKUP fs.files fnm;
      assert (off < STRLEN content);
      let (l,r) = SPLITP ((=)#"\n") (DROP off content) in
       SOME (l++"\n")
    od`;

val bumpLineFD_def = Define`
  bumpLineFD fd fs =
    case FDline fd fs of
    | NONE => fs
    | SOME ln => bumpFD fd (fs with infds updated_by
        ALIST_FUPDKEY fd (I ## ((+) (LENGTH ln -1))))`;

val validFD_bumpLineFD = Q.store_thm("validFD_bumpLineFD[simp]",
  `validFD fd (bumpLineFD fd fs) = validFD fd fs`,
  rw[validFD_def,bumpLineFD_def]
  \\ CASE_TAC \\ simp[] \\ rw[bumpFD_def]
  \\ CASE_TAC \\ simp[]);

val FDchar_FDline_NONE = Q.store_thm("FDchar_FDline_NONE",
  `FDchar fd fs = NONE <=> FDline fd fs = NONE`,
  rw[FDline_def,FDchar_def] \\ rw[EQ_IMP_THM] \\ rw[]
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]);

val FDchar_SOME_IMP_FDline = Q.store_thm("FDchar_SOME_IMP_FDline",
  `FDchar fd fs = SOME c ⇒ ∃ls. FDline fd fs = SOME (c::ls)`,
  rw[FDchar_def,FDline_def] \\ rw[]
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ Cases_on`DROP off content` \\ rfs[DROP_NIL]
  \\ rfs[DROP_CONS_EL]
  \\ fs[SPLITP]
  \\ rveq
  \\ pop_assum mp_tac \\ CASE_TAC \\ strip_tac \\ rveq
  \\ simp[]);

val FDline_bumpFD = Q.store_thm("FDline_bumpFD",
  `FDline fd fs = SOME (c::cs) ∧ c ≠ #"\n" ⇒
   (case FDline fd (bumpFD fd fs) of NONE => cs = "\n" | SOME cs' => cs = cs') ∧
   bumpLineFD fd (bumpFD fd fs) = bumpLineFD fd fs`,
  rw[FDline_def] \\ rw[Once bumpFD_def,Once bumpLineFD_def]
  \\ rw[FDchar_def,FDline_def]
  \\ pairarg_tac \\ fs[]
  \\ simp[ALIST_FUPDKEY_ALOOKUP]
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ imp_res_tac TL_DROP_SUC
  \\ Cases_on`DROP off content`
  \\ fs[DROP_NIL]
  \\ fs[SPLITP]
  \\ rveq
  \\ ntac 2 (pop_assum mp_tac)
  \\ (IF_CASES_TAC \\ rveq >- ( EVAL_TAC \\ strip_tac \\ rveq \\ fs[] ))
  \\ simp[]
  \\ strip_tac \\ rveq \\ fs[] \\ rveq \\ fs[]
  \\ strip_tac
  \\ Cases_on`SUC off < STRLEN content` \\ fs[]
  \\ TRY (
    `SUC off = STRLEN content` by decide_tac
    \\ fs[DROP_LENGTH_NIL]
    \\ fs[SPLITP] \\ rw[] )
  \\ fs[bumpFD_def,bumpLineFD_def,FDchar_def,FDline_def]
  \\ simp[SPLITP,ALIST_FUPDKEY_ALOOKUP,ADD1]
  \\ TRY (IF_CASES_TAC \\ fs[])
  \\ simp[RO_fs_component_equality]
  \\ simp[ALIST_FUPDKEY_o]
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ simp[FUN_EQ_THM,FORALL_PROD] );

val eq_char_v_thm =
  mlbasicsProgTheory.eq_v_thm
  |> DISCH_ALL
  |> C MATCH_MP (ml_translatorTheory.EqualityType_NUM_BOOL
                 |> CONJUNCTS |> el 5)

val inputLine = process_topdecs`
  fun inputLine fd =
    let
      fun loop acc =
        case FileIO.fgetc fd of
          NONE => #"\n"::acc
        | SOME c => if c = #"\n" then c::acc else loop (c::acc)
    in
      case FileIO.fgetc fd of NONE => NONE
      | SOME c => if c = #"\n" then SOME (String.str c)
                  else SOME (String.implode (rev (loop [c])))
    end`;
val _ = append_prog inputLine;

val inputLine_spec = Q.store_thm("inputLine_spec",
  `∀fd fdv.
    WORD (fd:word8) fdv ∧ validFD (w2n fd) fs ⇒
    app (p:'ffi ffi_proj) ^(fetch_v "inputLine" (get_ml_prog_state())) [fdv]
      (ROFS fs)
      (POSTv sov. &OPTION_TYPE STRING_TYPE (OPTION_MAP implode (FDline (w2n fd) fs)) sov *
                  ROFS (bumpLineFD (w2n fd) fs))`,
  rw[]
  \\ xcf"inputLine"(get_ml_prog_state())
  \\ xfun_spec `loop`
    `!ls acc accv fs.
       LIST_TYPE CHAR acc accv ∧ validFD (w2n fd) fs ∧
       (ls = case FDline (w2n fd) fs of NONE => "\n" | SOME ls => ls)
       ⇒
       app p loop [accv]
         (ROFS fs)
         (POSTv lv. &LIST_TYPE CHAR (REVERSE ls ++ acc) lv *
            ROFS (bumpLineFD (w2n fd) fs))`
  >- (
    ho_match_mp_tac list_INDUCT
    \\ qpat_x_assum`_ fs`kall_tac
    \\ conj_tac
    >- (
      ntac 2 gen_tac \\ qx_gen_tac`fs`
      \\ CASE_TAC
      \\ strip_tac \\ rveq
      \\ fs[FDline_def]
      \\ pairarg_tac \\ fs[]
      \\ pairarg_tac \\ fs[] )
    \\ gen_tac \\ strip_tac
    \\ qx_gen_tac`h`
    \\ ntac 2 gen_tac \\ qx_gen_tac`fs`
    \\ CASE_TAC \\ strip_tac \\ rveq
    >- (
      first_x_assum match_mp_tac
      \\ xlet`POSTv x. &OPTION_TYPE CHAR (FDchar (w2n fd) fs) x *
                       ROFS (bumpFD (w2n fd) fs)`
      >- (xapp \\ rw[])
      \\ xmatch
      \\ rfs[GSYM FDchar_FDline_NONE]
      \\ fs[ml_translatorTheory.OPTION_TYPE_def]
      \\ reverse conj_tac >- (EVAL_TAC \\ rw[]) (* should CF do this automatically? *)
      \\ xcon
      \\ fs[ml_translatorTheory.LIST_TYPE_def]
      \\ fs[bumpFD_def,bumpLineFD_def]
      \\ fs[FDchar_FDline_NONE]
      \\ xsimpl )
    \\ last_x_assum match_mp_tac
    \\ xlet`POSTv x. &OPTION_TYPE CHAR (FDchar (w2n fd) fs) x *
                     ROFS (bumpFD (w2n fd) fs)`
    >- (xapp \\ rw[])
    \\ xmatch
    \\ Cases_on`FDchar (w2n fd) fs` \\ fs[ml_translatorTheory.OPTION_TYPE_def]
    >- fs[FDchar_FDline_NONE]
    \\ reverse conj_tac >- (EVAL_TAC \\ rw[]) (* should CF do this automatically? *)
    \\ reverse conj_tac >- (EVAL_TAC \\ rw[]) (* should CF do this automatically? *)
    \\ rename1`CHAR c cv`
    \\ xlet`POSTv bv. &BOOL(c = #"\n") bv * ROFS (bumpFD (w2n fd)fs)`
    >- ( xapp_spec eq_char_v_thm \\ instantiate \\ xsimpl )
    \\ imp_res_tac FDchar_SOME_IMP_FDline
    \\ fs[] \\ rveq
    \\ xif
    >- (
      xcon
      \\ fs[bumpFD_def,bumpLineFD_def,FDchar_def,FDline_def]
      \\ fs[] \\ rveq
      \\ pairarg_tac \\ fs[]
      \\ pairarg_tac \\ fs[]
      \\ rveq
      \\ simp[ALIST_FUPDKEY_ALOOKUP]
      \\ Cases_on`l` \\ rveq
      >- (
        qpat_x_assum`_ = #"\n" :: _`mp_tac
        \\ simp[] \\ strip_tac \\ rveq
        \\ full_simp_tac std_ss [] \\ rfs[] \\ rveq
        \\ simp[ml_translatorTheory.LIST_TYPE_def]
        \\ qmatch_goalsub_abbrev_tac`_ o xx`
        \\ `xx = I`
        by (
          rw[Abbr`xx`,FUN_EQ_THM]
          \\ match_mp_tac ALIST_FUPDKEY_I
          \\ simp[FORALL_PROD] )
        \\ xsimpl)
      \\ fs[] \\ rveq
      \\ imp_res_tac SPLITP_IMP
      \\ fs[])
    \\ xlet`POSTv x. &LIST_TYPE CHAR (c::acc) x * ROFS (bumpFD (w2n fd) fs)`
    >- ( xcon \\ simp[ml_translatorTheory.LIST_TYPE_def] \\ xsimpl )
    \\ xapp \\ first_x_assum(qspec_then`ARB`kall_tac)
    \\ imp_res_tac validFD_bumpFD
    \\ instantiate
    \\ imp_res_tac FDline_bumpFD
    \\ CASE_TAC \\ fs[] \\ rveq
    \\ xsimpl
    \\ simp_tac std_ss [GSYM APPEND_ASSOC,APPEND] )
  \\ xlet`POSTv x. &OPTION_TYPE CHAR (FDchar (w2n fd) fs) x *
                   ROFS (bumpFD (w2n fd) fs)`
  >- (xapp \\ rw[])
  \\ xmatch
  \\ Cases_on`FDchar (w2n fd) fs` \\ fs[ml_translatorTheory.OPTION_TYPE_def]
  >- (
    reverse conj_tac >- (EVAL_TAC \\ rw[]) (* should CF do this automatically? *)
    \\ xcon
    \\ fs[FDchar_FDline_NONE,ml_translatorTheory.OPTION_TYPE_def]
    \\ simp[bumpFD_def,bumpLineFD_def]
    \\ fs[GSYM FDchar_FDline_NONE]
    \\ xsimpl )
  \\ reverse conj_tac >- (EVAL_TAC \\ rw[]) (* should CF do this automatically? *)
  \\ reverse conj_tac >- (EVAL_TAC \\ rw[]) (* should CF do this automatically? *)
  \\ rename1`CHAR c cv`
  \\ xlet`POSTv bv. &BOOL(c = #"\n") bv * ROFS (bumpFD (w2n fd)fs)`
  >- ( xapp_spec eq_char_v_thm \\ instantiate \\ xsimpl )
  \\ xif
  >- (
    xlet`POSTv sv. &STRING_TYPE (str c) sv * ROFS (bumpFD (w2n fd) fs)`
    >- ( xapp \\ instantiate \\ xsimpl )
    \\ xcon
    \\ fs[FDchar_def,FDline_def]
    \\ pairarg_tac \\ fs[]
    \\ Cases_on`DROP off content` \\ fs[DROP_NIL]
    \\ simp[SPLITP] \\ rfs[DROP_CONS_EL]
    \\ simp[ml_translatorTheory.OPTION_TYPE_def]
    \\ fs[mlstringTheory.str_def]
    \\ fs[bumpFD_def,bumpLineFD_def,FDchar_def,FDline_def,DROP_CONS_EL,SPLITP]
    \\ simp[ALIST_FUPDKEY_ALOOKUP]
    \\ qmatch_goalsub_abbrev_tac`_ o xx`
    \\ `xx = I`
    by (
      rw[Abbr`xx`,FUN_EQ_THM]
      \\ match_mp_tac ALIST_FUPDKEY_I
      \\ simp[FORALL_PROD] )
    \\ xsimpl)
  \\ xlet`POSTv x. &LIST_TYPE CHAR [] x * ROFS (bumpFD (w2n fd) fs)`
  >- (xcon \\ simp[ml_translatorTheory.LIST_TYPE_def] \\ xsimpl)
  \\ xlet`POSTv accv. &LIST_TYPE CHAR [c] accv * ROFS (bumpFD (w2n fd) fs)`
  >- (xcon \\ fs[ml_translatorTheory.LIST_TYPE_def] \\ xsimpl)
  \\ first_x_assum drule
  \\ imp_res_tac validFD_bumpFD
  \\ disch_then drule
  \\ imp_res_tac FDchar_SOME_IMP_FDline
  \\ imp_res_tac FDline_bumpFD
  \\ qmatch_goalsub_abbrev_tac`REVERSE l`
  \\ `l = ls`
  by ( unabbrev_all_tac \\ CASE_TAC \\ fs[] )
  \\ fs[] \\ ntac 2 (pop_assum kall_tac)
  \\ simp[GSYM SNOC_APPEND]
  \\ once_rewrite_tac[GSYM (CONJUNCT2 REVERSE)]
  \\ strip_tac
  \\ xlet`POSTv v. &LIST_TYPE CHAR (REVERSE (c::ls)) v *
                   ROFS (bumpLineFD (w2n fd) fs)`
  >- (xapp \\ xsimpl)
  \\ xlet`POSTv lv. &LIST_TYPE CHAR (c::ls) lv * ROFS (bumpLineFD (w2n fd) fs)`
  >- ( xapp \\ instantiate \\ xsimpl \\ simp[REVERSE_APPEND] )
  \\ xlet`POSTv sv. &STRING_TYPE (implode (c::ls)) sv * ROFS (bumpLineFD (w2n fd) fs)`
  >- (xapp \\ instantiate \\ xsimpl )
  \\ xcon
  \\ simp[ml_translatorTheory.OPTION_TYPE_def]
  \\ xsimpl);

val bumpAllFD_def = Define`
  bumpAllFD fd fs =
    the fs (do
      (fnm,off) <- ALOOKUP fs.infds fd;
      content <- ALOOKUP fs.files fnm;
      SOME (fs with infds updated_by ALIST_FUPDKEY fd (I ## (MAX (LENGTH content))))
    od)`;

val validFD_bumpAllFD = Q.store_thm("validFD_bumpAllFD[simp]",
  `validFD fd (bumpAllFD fd fs) = validFD fd fs`,
  rw[validFD_def,bumpAllFD_def]
  \\ Cases_on`ALOOKUP fs.infds fd` \\ fs[libTheory.the_def]
  \\ pairarg_tac \\ fs[]
  \\ Cases_on`ALOOKUP fs.files fnm` \\ fs[libTheory.the_def]);

val bumpAllFD_files = Q.store_thm("bumpAllFD_files[simp]",
  `(bumpAllFD fd fs).files = fs.files`,
  EVAL_TAC
  \\ Cases_on`ALOOKUP fs.infds fd` \\ fs[libTheory.the_def]
  \\ pairarg_tac \\ fs[]
  \\ Cases_on`ALOOKUP fs.files fnm` \\ fs[libTheory.the_def]);

val FDline_NONE_bumpAll_bumpLine = Q.store_thm("FDline_NONE_bumpAll_bumpLine",
  `FDline fd fs = NONE ⇒
   bumpLineFD fd fs = bumpAllFD fd fs`,
  rw[bumpLineFD_def,bumpAllFD_def]
  \\ fs[FDline_def,libTheory.the_def]
  \\ pairarg_tac \\ fs[libTheory.the_def]
  \\ TRY pairarg_tac \\ fs[]
  \\ simp[RO_fs_component_equality]
  \\ match_mp_tac EQ_SYM
  \\ match_mp_tac ALIST_FUPDKEY_I
  \\ simp[MAX_DEF]);

val bumpAllFD_bumpLineFD = Q.store_thm("bumpAllFD_bumpLineFD[simp]",
  `bumpAllFD fd (bumpLineFD fd fs) = bumpAllFD fd fs`,
  rw[bumpAllFD_def,bumpLineFD_def]
  \\ TOP_CASE_TAC
  \\ fs[FDline_def]
  \\ rw[bumpFD_def,FDchar_def,ALIST_FUPDKEY_ALOOKUP]
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ rveq \\ fs[]
  \\ TOP_CASE_TAC
  \\ fs[ALIST_FUPDKEY_ALOOKUP,libTheory.the_def,
        RO_fs_component_equality,ALIST_FUPDKEY_o]
  \\ match_mp_tac ALIST_FUPDKEY_eq
  \\ simp[MAX_DEF] \\ rw[] \\ fs[]
  \\ qmatch_assum_abbrev_tac`SPLITP P ls = (l,r)`
  \\ Q.ISPEC_THEN`ls`mp_tac SPLITP_LENGTH
  \\ simp[Abbr`ls`]);

val A_DELKEY_bumpAllFD_elim = Q.store_thm("A_DELKEY_bumpAllFD_elim[simp]",
  `A_DELKEY fd (bumpAllFD fd fs).infds = A_DELKEY fd fs.infds`,
  rw[bumpAllFD_def]
  \\ Cases_on`ALOOKUP fs.infds fd` \\ fs[libTheory.the_def]
  \\ pairarg_tac \\ fs[]
  \\ Cases_on`ALOOKUP fs.files fnm` \\ fs[libTheory.the_def]);

val splitlines_def = Define`
  splitlines ls =
  let lines = FIELDS ((=) #"\n") ls in
  (* discard trailing newline *)
  if NULL (LAST lines) then FRONT lines else lines`;

val splitlines_next = Q.store_thm("splitlines_next",
  `splitlines ls = ln::lns ⇒
   splitlines (DROP (SUC (LENGTH ln)) ls) = lns`,
  simp[splitlines_def]
  \\ Cases_on`FIELDS ($= #"\n") ls` \\ fs[]
  \\ Cases_on`LENGTH h < LENGTH ls`
  >- (
    imp_res_tac FIELDS_next
    \\ strip_tac
    \\ `ln = h`
    by (
      pop_assum mp_tac \\ rw[]
      \\ fs[FRONT_DEF] )
    \\ fs[]
    \\ fs[LAST_DEF,NULL_EQ]
    \\ Cases_on`t = []` \\ fs[]
    \\ fs[FRONT_DEF]
    \\ IF_CASES_TAC \\ fs[] )
  \\ fs[NOT_LESS]
  \\ imp_res_tac FIELDS_full \\ fs[]
  \\ IF_CASES_TAC \\ fs[]
  \\ strip_tac \\ rveq \\ fs[]
  \\ simp[DROP_LENGTH_TOO_LONG,FIELDS_def]);

val splitlines_nil = save_thm("splitlines_nil[simp]",
  EVAL``splitlines ""``);

val splitlines_eq_nil = Q.store_thm("splitlines_eq_nil[simp]",
  `splitlines ls = [] ⇔ (ls = [])`,
  rw[EQ_IMP_THM]
  \\ fs[splitlines_def]
  \\ every_case_tac \\ fs[]
  \\ Cases_on`FIELDS ($= #"\n") ls` \\ fs[]
  \\ fs[LAST_DEF] \\ rfs[NULL_EQ]
  \\ Cases_on`LENGTH "" < LENGTH ls`
  >- ( imp_res_tac FIELDS_next \\ fs[] )
  \\ fs[LENGTH_NIL]);

val linesFD_def = Define`
  linesFD fd fs = the [] (
    do
      (fnm,off) <- ALOOKUP fs.infds fd;
      content <- ALOOKUP fs.files fnm;
      assert (off < LENGTH content);
      SOME (splitlines (DROP off content))
    od )`;

val FDline_NONE_linesFD = Q.store_thm("FDline_NONE_linesFD",
  `FDline fd fs = NONE ⇔ linesFD fd fs = []`,
  rw[FDline_def,linesFD_def,EQ_IMP_THM] \\ rw[libTheory.the_def]
  >- ( pairarg_tac \\ fs[libTheory.the_def] \\ pairarg_tac \\ fs[])
  \\ Cases_on`ALOOKUP fs.infds fd` \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ Cases_on`ALOOKUP fs.files fnm` \\ fs[]
  \\ rveq \\ rename1`off < LENGTH ln`
  \\ Cases_on`off < LENGTH ln` \\ fs[]
  \\ fs[libTheory.the_def,DROP_NIL]);

val linesFD_eq_cons_imp = Q.store_thm("linesFD_eq_cons_imp",
  `linesFD fd fs = ln::ls ⇒
   FDline fd fs = SOME (ln++"\n") ∧
   linesFD fd (bumpLineFD fd fs) = ls`,
  simp[linesFD_def,bumpLineFD_def,the_nil_eq_cons]
  \\ strip_tac \\ pairarg_tac \\ fs[]
  \\ conj_asm1_tac
  >- (
    simp[FDline_def]
    \\ Cases_on`DROP off content` \\ rfs[DROP_NIL]
    \\ fs[splitlines_def,FIELDS_def]
    \\ pairarg_tac \\ fs[]
    \\ every_case_tac \\ fs[] \\ rw[]
    \\ fs[NULL_EQ]
    \\ imp_res_tac SPLITP_NIL_IMP \\ fs[] \\ rw[]
    >- ( Cases_on`FIELDS ($= #"\n") t` \\ fs[] )
    >- ( Cases_on`FIELDS ($= #"\n") (TL r)` \\ fs[] ))
  \\ simp[]
  \\ simp[bumpFD_def,FDchar_def,ALIST_FUPDKEY_ALOOKUP]
  \\ reverse IF_CASES_TAC \\ fs[ALIST_FUPDKEY_ALOOKUP,libTheory.the_def]
  >- (
    fs[NOT_LESS]
    \\ imp_res_tac splitlines_next
    \\ fs[DROP_DROP_T]
    \\ rfs[DROP_LENGTH_TOO_LONG] )
  \\ imp_res_tac splitlines_next
  \\ fs[DROP_DROP_T,ADD1]
  \\ Cases_on`off + (STRLEN ln + 1) < LENGTH content` \\ fs[libTheory.the_def]
  \\ fs[NOT_LESS]
  \\ `off + LENGTH ln + 1 = LENGTH content` by simp[]
  \\ fs[DROP_LENGTH_NIL_rwt]);

(* -- *)

val print_matching_lines = process_topdecs`
  fun print_matching_lines match prefix fd =
    case inputLine fd of NONE => ()
    | SOME ln => (if match ln then (print prefix; print ln) else ();
                  print_matching_lines match prefix fd)`;
val _ = append_prog print_matching_lines;

val print_matching_lines_spec = Q.store_thm("print_matching_lines_spec",
  `∀fs out.
   (STRING_TYPE --> BOOL) m mv ∧ STRING_TYPE pfx pfxv ∧
   WORD (fd:word8) fdv ∧ validFD (w2n fd) fs ⇒
   app (p:'ffi ffi_proj)
     ^(fetch_v "print_matching_lines"(get_ml_prog_state())) [mv; pfxv; fdv]
     (ROFS fs * STDOUT out)
     (POSTv uv.
       &UNIT_TYPE () uv *
       ROFS (bumpAllFD (w2n fd) fs) *
       STDOUT (out ++ CONCAT
         (MAP ((++) (explode pfx))
           (FILTER (m o implode)
             (MAP (combin$C (++) "\n")
               (linesFD (w2n fd) fs))))))`,
  Induct_on`linesFD (w2n fd) fs` \\ rw[]
  >- (
    qpat_x_assum`[] = _`(assume_tac o SYM) \\ fs[]
    \\ xcf"print_matching_lines"(get_ml_prog_state())
    \\ xlet`POSTv x. &OPTION_TYPE STRING_TYPE (OPTION_MAP implode (FDline (w2n fd) fs))  x *
                     ROFS (bumpLineFD (w2n fd) fs) * STDOUT out`
    >- ( xapp \\ instantiate \\ xsimpl )
    \\ rfs[GSYM FDline_NONE_linesFD,ml_translatorTheory.OPTION_TYPE_def]
    \\ xmatch
    \\ xcon
    \\ imp_res_tac FDline_NONE_bumpAll_bumpLine
    \\ xsimpl )
  \\ qpat_x_assum`_::_ = _`(assume_tac o SYM) \\ fs[]
  \\ xcf"print_matching_lines"(get_ml_prog_state())
  \\ xlet`POSTv x. &OPTION_TYPE STRING_TYPE (OPTION_MAP implode (FDline (w2n fd) fs))  x *
                   ROFS (bumpLineFD (w2n fd) fs) * STDOUT out`
  >- ( xapp \\ instantiate \\ xsimpl )
  \\ Cases_on`FDline (w2n fd) fs` \\ fs[FDline_NONE_linesFD]
  \\ fs[ml_translatorTheory.OPTION_TYPE_def]
  \\ xmatch
  \\ rename1`FDline _ _ = SOME ln`
  \\ rveq
  \\ xlet`POSTv bv. &BOOL (m (implode ln)) bv * ROFS (bumpLineFD (w2n fd) fs) * STDOUT out`
  >- ( xapp \\ instantiate \\ xsimpl )
  \\ xlet`POSTv x. ROFS (bumpLineFD (w2n fd) fs) * STDOUT (out ++ (if m (implode ln) then explode pfx ++ ln else ""))`
  >- (
    xif
    >- (
      xlet`POSTv x. ROFS (bumpLineFD (w2n fd) fs) * STDOUT (out ++ explode pfx)`
      >- (xapp \\ instantiate \\ xsimpl
          \\ CONV_TAC(SWAP_EXISTS_CONV) \\ qexists_tac`out`
          \\ xsimpl )
      \\ xapp \\ instantiate \\ xsimpl
      \\ simp[mlstringTheory.explode_implode]
      \\ CONV_TAC(SWAP_EXISTS_CONV) \\ qexists_tac`out ++ explode pfx`
      \\ xsimpl )
    \\ xcon \\ xsimpl )
  \\ imp_res_tac linesFD_eq_cons_imp \\ rveq \\ fs[]
  \\ first_x_assum(qspecl_then[`fd`,`bumpLineFD (w2n fd) fs`]mp_tac)
  \\ simp[] \\ strip_tac
  \\ xapp
  \\ CONV_TAC SWAP_EXISTS_CONV
  \\ qexists_tac`out ++ (if m (implode ln) then explode pfx ++ ln else "")`
  \\ fs[] \\ xsimpl
  \\ Cases_on`m (implode ln)` \\ fs[]
  \\ xsimpl);

(* TODO: fix concat_2 problem in mlstringProg *)

val print_matching_lines_in_file = process_topdecs`
  fun print_matching_lines_in_file m file =
    let val fd = FileIO.openIn file
    in (print_matching_lines m (String.concat_2[file,":"]) fd;
        FileIO.close fd)
    end handle FileIO.BadFileName => ()`;
val _ = append_prog print_matching_lines_in_file;

val print_matching_lines_in_file_spec = Q.store_thm("print_matching_lines_in_file_spec",
  `FILENAME f fv ∧
   CARD (FDOM (alist_to_fmap fs.infds)) < 255 ∧
   (STRING_TYPE --> BOOL) m mv
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v"print_matching_lines_in_file"(get_ml_prog_state()))
     [mv; fv]
     (ROFS fs * STDOUT out)
     (POSTv uv. &UNIT_TYPE () uv * ROFS fs *
                STDOUT (out ++
                  if inFS_fname f fs then
                    CONCAT
                      (MAP ((++)(explode f ++ ":"))
                        (FILTER (m o implode)
                           (MAP (combin$C (++) "\n")
                             (splitlines (THE (ALOOKUP fs.files f))))))
                  else ""))`,
  xcf"print_matching_lines_in_file"(get_ml_prog_state())
  \\ qmatch_goalsub_abbrev_tac`_ * ROFS fs * STDOUT result`
  \\ reverse(xhandle`POST
       (λv. &UNIT_TYPE () v * ROFS fs * STDOUT result)
       (λe. &(BadFileName_exn e ∧ ¬inFS_fname f fs) * ROFS fs * STDOUT out)`)
  >- (
    xcases
    \\ fs[BadFileName_exn_def]
    \\ reverse conj_tac >- (EVAL_TAC \\ rw[])
    \\ xcon \\ xsimpl )
  >- ( xsimpl )
  \\ xlet`POST (λv. &(WORD ((n2w (nextFD fs)):word8) v ∧ validFD (nextFD fs) (openFileFS f fs) ∧
                      inFS_fname f fs) * ROFS (openFileFS f fs) * STDOUT out)
               (λe. &(BadFileName_exn e ∧ ¬inFS_fname f fs) * ROFS fs * STDOUT out)`
  >- ( xapp \\ instantiate \\ xsimpl )
  >- ( xsimpl )
  \\ xlet`POSTv v. &LIST_TYPE STRING_TYPE [] v * ROFS (openFileFS f fs) * STDOUT out`
  >- ( xcon \\ xsimpl \\ fs[ml_translatorTheory.LIST_TYPE_def] )
  \\ xlet`POSTv v. &LIST_TYPE STRING_TYPE [strlit":"] v * ROFS (openFileFS f fs) * STDOUT out`
  >- ( xcon \\ xsimpl \\ fs[ml_translatorTheory.LIST_TYPE_def] )
  \\ xlet`POSTv v. &LIST_TYPE STRING_TYPE [f;strlit":"] v * ROFS (openFileFS f fs) * STDOUT out`
  >- ( xcon \\ xsimpl \\ fs[ml_translatorTheory.LIST_TYPE_def,FILENAME_def] )
  \\ xlet`POSTv v. &STRING_TYPE (concat[f;strlit":"]) v * ROFS (openFileFS f fs) * STDOUT out`
  >- ( xapp \\ instantiate \\ xsimpl )
  \\ xlet`POSTv v. &UNIT_TYPE () v * ROFS (bumpAllFD (nextFD fs) (openFileFS f fs)) * STDOUT result`
  \\ fs[] \\ imp_res_tac nextFD_ltX \\ simp[]
  >- (
    xapp
    \\ instantiate
    \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac`out`
    \\ xsimpl
    \\ fs[mlstringTheory.concat_thm,mlstringTheory.explode_implode]
    \\ imp_res_tac inFS_fname_ALOOKUP_EXISTS \\ fs[]
    \\ imp_res_tac ALOOKUP_inFS_fname_openFileFS_nextFD
    \\ simp[linesFD_def]
    \\ Cases_on`0 < LENGTH content` \\ fs[libTheory.the_def,LENGTH_NIL]
    \\ xsimpl )
  \\ xapp
  \\ CONV_TAC SWAP_EXISTS_CONV
  \\ qexists_tac`bumpAllFD (nextFD fs) (openFileFS f fs)`
  \\ instantiate
  \\ xsimpl
  \\ qmatch_goalsub_abbrev_tac`ROFS fs'`
  \\ `fs' = fs` suffices_by xsimpl
  \\ simp[Abbr`fs'`,RO_fs_component_equality]);

val usage_string_def = Define`
  usage_string = strlit"Usage: grep <regex> <file> <file>...\n"`;

val r = translate usage_string_def;

val usage_string_v_thm = theorem"usage_string_v_thm";

val parse_failure_string_def = Define`
  parse_failure_string r = concat[strlit"Could not parse regexp: ";r;strlit"\n"]`;

val r = translate parse_failure_string_def;

(* TODO: This approach (with matcher argument as a function) does not play nicely with CF
val match_line_def = Define`
  match_line matcher (line:string) =
  case matcher line of | SOME T => T | _ => F`;

val r = translate match_line_def;
*)
val match_line_def = Define`
  match_line r s =
    case regexp_matcher_with_limit r s of | SOME T => T | _ => F`;

val r = translate match_line_def;

val build_matcher_def = Define`
  build_matcher r s =
    if strlen s = 0 then
      match_line r []
    else
      match_line r (FRONT (explode s))`;

val r = translate build_matcher_def;

val build_matcher_side = Q.prove(
  `∀r s. build_matcher_side r s = T`,
  rw[definition"build_matcher_side_def"]
  \\ Cases_on`s` \\ fs[LENGTH_NIL]) |> update_precondition;

val build_matcher_v_thm = theorem"build_matcher_v_thm"

val build_matcher_partial_spec = Q.store_thm("build_matcher_partial_spec",
  `REGEXP_REGEXP_TYPE r rv ⇒
   app (p:'ffi ffi_proj) ^(fetch_v"build_matcher"(get_ml_prog_state())) [rv] emp
    (POSTv v. &(STRING_TYPE --> BOOL) (build_matcher r) v)`,
  strip_tac
  \\ rw[app_def]
  \\ irule Arrow_IMP_app_basic
  \\ instantiate
  \\ simp[build_matcher_v_thm]);

val grep = process_topdecs`
  fun grep u =
    case Commandline.arguments ()
    of [] => print usage_string
     | [_] => print usage_string
     | (regexp::files) =>
       case parse_regexp (String.explode regexp) of
         NONE => print (parse_failure_string regexp)
       | SOME r =>
           (* abandoning this approach for now ...
         let
           (* TODO: this would be nicer as:
           val raw_match = match_line (regexp_matcher_with_limit r)
             but how does partial application work in CF? *)
           val raw_match = (fn s => match_line (fn s => regexp_matcher_with_limit r s) s)
         in
           *)
           (* TODO: similar issue with higher-order function, CF seems to need this eta  *)
           List.app (fn file => print_matching_lines_in_file (build_matcher r) file) files
         (* end *)`;
val _ = append_prog grep;

val grep_sem_file_def = Define`
  grep_sem_file L fs filename =
    case ALOOKUP fs.files filename of
    | NONE => ""
    | SOME contents =>
        CONCAT
          (MAP (λmatching_line. explode filename ++ ":" ++ matching_line ++ "\n")
             (FILTER (λline. line ∈ L) (splitlines contents)))`;

val grep_sem_def = Define`
  (grep_sem (_::regexp::filenames) fs =
   if NULL filenames then explode usage_string else
   case parse_regexp regexp of
   | NONE => explode (parse_failure_string (implode regexp))
   | SOME r => CONCAT (MAP (grep_sem_file (regexp_lang r) fs) (MAP implode filenames))) ∧
  (grep_sem _ _ = explode usage_string)`;

val grep_termination_assum_def = Define`
  (grep_termination_assum (_::regexp::filenames) ⇔
   if NULL filenames then T else
     case parse_regexp regexp of
     | NONE => T
     | SOME r => IS_SOME (Brz empty [normalize r] (1,singleton (normalize r) 0,[]) MAXNUM_32)) ∧
  (grep_termination_assum _ ⇔ T)`;

val grep_spec = Q.store_thm("grep_spec",
  `cl ≠ [] ∧ EVERY validArg cl ∧ LENGTH (FLAT cl) + LENGTH cl ≤ 256 ∧
   CARD (set (MAP FST fs.infds)) < 255 ∧
   grep_termination_assum cl
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v"grep"(get_ml_prog_state()))
    [Conv NONE []]
    (STDOUT out * COMMANDLINE cl * ROFS fs)
    (POSTv v. &UNIT_TYPE () v *
      (STDOUT (out ++ grep_sem cl fs)
       * (COMMANDLINE cl * ROFS fs)))`,
  strip_tac
  \\ xcf"grep"(get_ml_prog_state())
  \\ xlet`POSTv v. &UNIT_TYPE () v * STDOUT out * COMMANDLINE cl * ROFS fs`
  >- (xcon \\ xsimpl)
  \\ xlet`POSTv v. &LIST_TYPE STRING_TYPE (TL (MAP implode cl)) v * STDOUT out * COMMANDLINE cl * ROFS fs`
  >- (xapp \\ instantiate \\ xsimpl
      \\ simp[MAP_TL,NULL_EQ,LENGTH_FLAT,MAP_MAP_o,o_DEF] (* TODO: this is duplicated in catProg and bootstrap *)
      \\ Q.ISPECL_THEN[`STRLEN`]mp_tac SUM_MAP_PLUS
      \\ disch_then(qspecl_then[`K 1`,`cl`]mp_tac)
      \\ simp[MAP_K_REPLICATE,SUM_REPLICATE,GSYM LENGTH_FLAT])
  \\ Cases_on`cl` \\ fs[]
  \\ Cases_on`t` \\ fs[ml_translatorTheory.LIST_TYPE_def]
  >- (
    xmatch
    \\ xapp
    \\ simp[grep_sem_def]
    \\ xsimpl
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac`usage_string`
    \\ simp[usage_string_v_thm]
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac`out`
    \\ xsimpl )
  \\ rveq
  \\ rename1`EVERY validArg t`
  \\ Cases_on`t` \\ fs[ml_translatorTheory.LIST_TYPE_def]
  >- (
    xmatch
    \\ xapp
    \\ simp[grep_sem_def]
    \\ xsimpl
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac`usage_string`
    \\ simp[usage_string_v_thm]
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac`out`
    \\ xsimpl )
  \\ rveq
  \\ xmatch
  \\ rename1`grep_sem (grep::regexp::file1::files)`
  \\ simp[grep_sem_def,MAP_MAP_o,o_DEF]
  \\ qmatch_goalsub_abbrev_tac`COMMANDLINE cl`
  \\ qmatch_assum_abbrev_tac`Abbrev(cl = grep::regexp::fls)`
  \\ xlet`POSTv v. &LIST_TYPE CHAR regexp v * STDOUT out * COMMANDLINE cl * ROFS fs`
  >- (
    xapp
    \\ instantiate
    \\ simp[mlstringTheory.explode_implode]
    \\ xsimpl )
  \\ xlet`POSTv v. &OPTION_TYPE REGEXP_REGEXP_TYPE  (parse_regexp regexp) v * STDOUT out * COMMANDLINE cl * ROFS fs`
  >- ( xapp \\ instantiate \\ xsimpl )
  \\ Cases_on`parse_regexp regexp` \\ fs[ml_translatorTheory.OPTION_TYPE_def]
  >- (
    xmatch
    \\ xlet`POSTv v. &STRING_TYPE (parse_failure_string (implode regexp)) v * STDOUT out * COMMANDLINE cl * ROFS fs`
    >- (xapp \\ instantiate \\ xsimpl )
    \\ xapp
    \\ instantiate
    \\ xsimpl
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac`out`
    \\ xsimpl )
  \\ qmatch_goalsub_abbrev_tac`gs1 ++ (FLAT (MAP ff files))`
  \\ `gs1 ++ (FLAT (MAP ff files)) = out ++ FLAT (MAP ff fls)`
  by ( unabbrev_all_tac \\ simp[] )
  \\ pop_assum SUBST1_TAC
  \\ simp[Abbr`gs1`,Abbr`ff`]
  \\ xmatch
  \\ rename1`parse_regexp regexp = SOME r`
  \\ xfun_spec`appthis`
     `∀f fv outp.
      FILENAME f fv ∧ CARD (FDOM (alist_to_fmap fs.infds)) < 255 ⇒
      app p appthis [fv] (STDOUT outp * COMMANDLINE cl * ROFS fs)
        (POSTv v. &UNIT_TYPE () v * STDOUT (outp ++ grep_sem_file (regexp_lang r) fs f) * COMMANDLINE cl * ROFS fs)`
  >- (
    rw[]
    \\ first_x_assum match_mp_tac
    \\ xlet`POSTv mv. &(STRING_TYPE --> BOOL) (build_matcher r) mv * STDOUT outp * COMMANDLINE cl * ROFS fs`
    >- ( xapp_spec build_matcher_partial_spec \\ instantiate \\ xsimpl )
    \\ xapp
    \\ simp[]
    \\ instantiate
    \\ xsimpl
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac`outp`
    \\ xsimpl
    \\ simp[grep_sem_file_def]
    \\ reverse IF_CASES_TAC
    >- (
      CASE_TAC \\ xsimpl
      \\ imp_res_tac ALOOKUP_SOME_inFS_fname )
    \\ imp_res_tac inFS_fname_ALOOKUP_EXISTS
    \\ simp[]
    \\ qmatch_goalsub_abbrev_tac`STDOUT (outp ++ s1)`
    \\ qmatch_goalsub_abbrev_tac`STDOUT (outp ++ s2) * _`
    \\ `s1 = s2` suffices_by xsimpl
    \\ simp[Abbr`s1`,Abbr`s2`]
    \\ AP_TERM_TAC
    \\ simp[FILTER_MAP,MAP_MAP_o]
    \\ simp[Once o_DEF]
    \\ AP_TERM_TAC
    \\ AP_THM_TAC
    \\ AP_TERM_TAC
    \\ simp[FUN_EQ_THM,build_matcher_def]
    \\ simp[mlstringTheory.explode_implode]
    \\ simp[mlstringTheory.implode_def]
    \\ simp[FRONT_APPEND]
    \\ simp[match_line_def]
    \\ gen_tac
    \\ fs[Abbr`cl`,grep_termination_assum_def,Abbr`fls`]
    \\ `dom_Brz_alt empty [normalize r]`
    by ( metis_tac[dom_Brz_alt_equal,dom_Brz_def] )
    \\ imp_res_tac regexp_matcher_correct
    \\ TOP_CASE_TAC
    >- (
      fs[regexp_matcher_with_limit_def,compile_regexp_with_limit_def]
      \\ rfs[IS_SOME_EXISTS] \\ rfs[]
      \\ every_case_tac \\ fs[] )
    \\ imp_res_tac regexp_matcher_with_limit_sound
    \\ rveq
    \\ fs[])
  \\ xapp_spec (INST_TYPE[alpha|->``:mlstring``]mllistProgTheory.app_spec)
  \\ CONV_TAC (RESORT_EXISTS_CONV List.rev)
  \\ qexists_tac`λn. STDOUT (out ++ (CONCAT (MAP (grep_sem_file (regexp_lang r) fs) (TAKE n (MAP implode fls))))) * COMMANDLINE cl * ROFS fs`
  \\ xsimpl
  \\ qexists_tac`MAP implode fls`
  \\ qexists_tac`STRING_TYPE`
  \\ reverse conj_tac
  >- ( simp[Abbr`fls`,MAP_MAP_o,o_DEF] \\ xsimpl )
  \\ reverse conj_tac
  >- ( simp[Abbr`fls`,ml_translatorTheory.LIST_TYPE_def] )
  \\ rw[] \\ rfs[EL_MAP]
  \\ qmatch_assum_abbrev_tac`STRING_TYPE f xv`
  \\ `validArg (explode f)`
  by (
    fs[Abbr`fls`,Abbr`f`,mlstringTheory.explode_implode,EVERY_MEM,MEM_EL,PULL_EXISTS]
    \\ Cases_on`n` \\ fs[] )
  \\ `FILENAME f xv`
  by (
    fs[FILENAME_def,commandLineFFITheory.validArg_def,Abbr`f`,mlstringTheory.explode_implode,mlstringTheory.implode_def]
    \\ fs[EVERY_MEM] )
  \\ first_x_assum drule
  \\ `TAKE (n+1) fls = (TAKE n fls) ++ [EL n fls]` by ( simp[TAKE_EL_SNOC] )
  \\ simp[GSYM MAP_TAKE]
  \\ simp[MAP_MAP_o]
  \\ simp[set_sepTheory.STAR_ASSOC]);

val st = get_ml_prog_state()
val name = "grep"
val spec = grep_spec |> UNDISCH |> ioProgLib.add_basis_proj
val (sem_thm,prog_tm) = ioProgLib.call_thm st name spec

val grep_prog_def = Define`grep_prog = ^prog_tm`;

val grep_semantics = save_thm("grep_semantics",
  sem_thm
  |> REWRITE_RULE[GSYM grep_prog_def]
  |> DISCH_ALL
  |> REWRITE_RULE[AND_IMP_INTRO]
  |> CONV_RULE(LAND_CONV EVAL)
  |> REWRITE_RULE[APPEND]);

val _ = export_theory ();
