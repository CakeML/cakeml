open preamble ml_translatorLib ml_progLib
     mlvectorProgTheory basisFunctionsLib

val _ = new_theory "grepProg";

val _ = translation_extends"mlvectorProg";

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

val _ = (find_def_for_const := def_of_const);

val spec64 = INST_TYPE[alpha|->``:64``]
val conv64 = GEN_ALL o CONV_RULE (wordsLib.WORD_CONV) o spec64 o SPEC_ALL
val conv64_RHS = GEN_ALL o CONV_RULE (RHS_CONV wordsLib.WORD_CONV) o spec64 o SPEC_ALL

val word_bit_mask = Q.store_thm("word_bit_mask",
  `!w. word_bit n (w:64 word) = (((n2w(2**n):64 word) && w) = 1w)`,
  cheat);

translate word_bit_mask;

open charsetTheory;

val _ = translate (charsetTheory.charset_full_def |> CONV_RULE (RHS_CONV EVAL));
val _ = translate charset_mem_def;

open regexpTheory;

val _ = translate normalize_def;

open regexp_compilerTheory;

val _ = translate mem_regexp_def;
val _ = translate exec_dfa_def;  (* TODO: massage precondition *)

val _ = translate Brz_def;

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

(* TODO: Copypasta from regexp_compilerScript follows --- these should either be
   exported from regexp_compilerScript, or the proofs below should go there. *)

val IS_SOME_Brz = Q.prove
(`!d seen worklist acc.
      IS_SOME (Brz seen worklist acc d)
         ==>
        d <> 0`,
 Cases >> rw[Once Brz_def])

val Brz_SOME = Q.prove
(`!d seen worklist acc res.
   (Brz seen worklist acc d = SOME res)
   ==> d <> 0`,
 METIS_TAC [IS_SOME_Brz,IS_SOME_EXISTS]);

val Brz_dlem = Q.prove
(`!d seen worklist acc.
  IS_SOME (Brz seen worklist acc d)
   ==>
  (Brz seen worklist acc d = Brz seen worklist acc (SUC d))`,
 Ho_Rewrite.REWRITE_TAC [IS_SOME_EXISTS,GSYM LEFT_FORALL_IMP_THM]
 >> Induct
    >- metis_tac [Brz_SOME]
    >- (rw[] >> rw[Once Brz_def,LET_THM]
         >> pop_assum mp_tac
         >> BasicProvers.EVERY_CASE_TAC
            >- rw [Brz_def]
            >- (rw [Once Brz_def] >> metis_tac [])
            >- (DISCH_THEN (mp_tac o SIMP_RULE list_ss [Once Brz_def])
                 >> rw[LET_THM]
                 >> metis_tac[]))
);

val Brz_monotone = Q.prove
(`!d1 d2 seen worklist acc.
      IS_SOME(Brz seen worklist acc d1) /\ d1 <= d2
       ==> (Brz seen worklist acc d1 = Brz seen worklist acc d2)`,
 RW_TAC arith_ss [LESS_EQ_EXISTS] THEN
 Induct_on `p` THEN METIS_TAC [ADD_CLAUSES,Brz_dlem]);

val Brz_norm = Q.prove
(`!d seen worklist acc.
   IS_SOME(Brz seen worklist acc d)
    ==>
   (Brz seen worklist acc d = Brz seen worklist acc (rdepth seen worklist acc))`,
  METIS_TAC [Brz_monotone,rdepth_thm]);

val Brz_determ = Q.prove
(`!d1 d2 seen worklist acc.
    IS_SOME(Brz seen worklist acc d1) /\ IS_SOME(Brz seen worklist acc d2)
       ==> (Brz seen worklist acc d1 = Brz seen worklist acc d2)`,
  METIS_TAC [Brz_norm]);

(* End of copypasta *)

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

val _ = translate compile_regexp_with_limit_def;

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

val _ = translate (regexp_matcher_with_limit_def); (* TODO: massage precondition *)

(* TODO: translate regexp parser *)

val _ = export_theory ();
