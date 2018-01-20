open ml_monad_translatorBaseTheory ml_monad_translatorTheory cfHeapsBaseTheory set_sepTheory pred_setTheory cfStoreTheory Satisfy
open semanticPrimitivesTheory cfTacticsLib

val _ = new_theory"cfMonad"

(* Theorems to convert monadic specifications to cf specifications *)

val _ = Globals.max_print_depth := 40;

val _ = hide "state";

val HCOND_EXTRACT = cfLetAutoTheory.HCOND_EXTRACT;

(*********** Comes from cfLetAutoLib.sml ***********************************************)
(* [dest_pure_fact]
   Deconstruct a pure fact (a heap predicate of the form &P) *)
val set_sep_cond_tm = ``set_sep$cond : bool -> hprop``;
fun dest_pure_fact p =
  case (dest_term p) of
  COMB dp =>
    (if same_const set_sep_cond_tm (#1 dp) then (#2 dp)
    else raise (ERR "dest_pure_fact" "Not a pure fact"))
  | _ => raise (ERR "dest_pure_fact" "Not a pure fact");
(***************************************************************************************)

fun PURE_FACTS_FIRST_CONV H =
  let
      val preds = list_dest dest_star H
      val (pfl, hpl) = List.partition (can dest_pure_fact) preds
      val ordered_preds = pfl @ hpl
  in
      if List.null ordered_preds then REFL H
      else
          let val H' = List.foldl (fn (x, y) => mk_star(y, x)) (List.hd ordered_preds)
                                  (List.tl ordered_preds)
          (* For some strange reason, AC_CONV doesn't work *)
          val H_to_norm = STAR_AC_CONV H
          val norm_to_H' = (SYM(STAR_AC_CONV H') handle UNCHANGED => REFL H')
          in TRANS H_to_norm norm_to_H'
          end
  end;

val EXTRACT_PURE_FACTS_CONV =
  (RATOR_CONV PURE_FACTS_FIRST_CONV)
  THENC (SIMP_CONV pure_ss [GSYM STAR_ASSOC])
  THENC (SIMP_CONV pure_ss [HCOND_EXTRACT])
  THENC (SIMP_CONV pure_ss [STAR_ASSOC]);

(* TODO: use EXTRACT_PURE_FACT_CONV to rewrite EXTRACT_PURE_FACTS_TAC *)
fun EXTRACT_PURE_FACTS_TAC (g as (asl, w)) =
  let
      fun is_hprop a = ((dest_comb a |> fst |> type_of) = ``:hprop`` handle HOL_ERR _ => false)
      val hpreds = List.filter is_hprop asl
      val hpreds' = List.map (fst o dest_comb) hpreds
      val hpreds_eqs = List.map (PURE_FACTS_FIRST_CONV) hpreds'
  in
      ((fs hpreds_eqs) >> fs[GSYM STAR_ASSOC] >> fs[HCOND_EXTRACT] >> fs[STAR_ASSOC]) g
  end;
(***********************************************************************************************)

(* COPY/PASTE from cfAppScript *)
val evaluate_list_SING = Q.prove(
  `bigStep$evaluate_list b env st [exp] (st', Rval [v]) <=>
    bigStep$evaluate b env st exp (st', Rval v)`,
  simp [Once bigStepTheory.evaluate_cases, PULL_EXISTS]
  \\ once_rewrite_tac [CONJ_COMM]
  \\ simp [Once bigStepTheory.evaluate_cases, PULL_EXISTS]);

val evaluate_list_raise_SING = Q.prove(
  `bigStep$evaluate_list b env st [exp] (st', Rerr (Rraise v)) <=>
    bigStep$evaluate b env st exp (st', Rerr (Rraise v))`,
  simp [Once bigStepTheory.evaluate_cases, PULL_EXISTS]
  \\ eq_tac \\ fs [] \\ strip_tac
  \\ pop_assum (assume_tac o
                SIMP_RULE std_ss [Once bigStepTheory.evaluate_cases])
  \\ fs []);
(* END OF COPY/PASTE *)

val REFS_PRED_lemma = Q.prove(
`SPLIT (st2heap (p : 'ffi ffi_proj)  st) (h1, h2) /\ H refs h1 ==> REFS_PRED (H,p) refs st`,
rw[REFS_PRED_def, STAR_def]
\\ qexists_tac `h1`
\\ qexists_tac `h2`
\\ fs[SAT_GC]
);

val HPROP_SPLIT3 = Q.prove(
`(H1 * H2 * H3) h ==> ?h1 h2 h3. SPLIT3 h (h1, h2, h3) /\ H1 h1 /\ H2 h2 /\ H3 h3`,
rw[STAR_def, SPLIT_def, SPLIT3_def]
\\ fs[DISJOINT_UNION]
\\ metis_tac[]);

val HPROP_SPLIT3_clock0 = Q.prove(
`(H1 * H2 * H3) (st2heap p st) ==>
 ?h1 h2 h3. SPLIT3 (st2heap p (st with clock := 0)) (h1, h2, h3) /\ H1 h1 /\ H2 h2 /\ H3 h3`,
rw[STAR_def, SPLIT_def, SPLIT3_def]
\\ fs[DISJOINT_UNION, st2heap_def]
\\ metis_tac[]);

val evaluate_Rval_bigStep_to_evaluate = Q.prove(
`evaluate F env st exp (st', Rval x) ==>
?c. evaluate (st with clock := c) env [exp] = (st' with clock := 0, Rval [x])`,
rw[]
\\ fs[funBigStepEquivTheory.functional_evaluate_list, bigClockTheory.big_clocked_unclocked_equiv]
\\ fs[evaluate_list_SING]
\\ instantiate);

val evaluate_Rerr_bigStep_to_evaluate = Q.prove(
`evaluate F env st exp (st', Rerr (Rraise a)) ==>
?c. evaluate (st with clock := c) env [exp] = (st' with clock := 0, Rerr (Rraise a))`,
rw[]
\\ fs[funBigStepEquivTheory.functional_evaluate_list, bigClockTheory.big_clocked_unclocked_equiv]
\\ fs[evaluate_list_raise_SING]
\\ instantiate);

val REFS_PRED_from_SPLIT = Q.prove(
  `!state (st : 'ffi semanticPrimitives$state) H p h1 h2.
   H state h1 ==>
   SPLIT (st2heap p st) (h1,h2) ==>
   REFS_PRED (H,p) state st`,
   rw[REFS_PRED_def]
   \\ rw[STAR_def]
   \\ metis_tac[SAT_GC]);

val ArrowP_PURE_to_app = Q.store_thm("ArrowP_PURE_to_app",
  `!A B f fv x1 xv1 xv2 xvl H Q ro state p.
     A x1 xv1 ==>
     (!gv. B (f x1) gv ==>
     app (p : 'ffi ffi_proj) gv (xv2::xvl) (H state) (Q state)) ==>
     ArrowP ro (H,p) (PURE A) (PURE B) f fv ==>
     app p fv (xv1::xv2::xvl) (H state) (Q state)`,
  rw [app_def, app_basic_def, ArrowP_def, PURE_def]
  \\ drule REFS_PRED_from_SPLIT
  \\ disch_then drule \\ rw[]
  \\ first_x_assum(qspecl_then [`x1`, `state`, `st`, `state`, `st`, `Rval xv1`] assume_tac)
  \\ fs[state_component_equality]
  \\ fs[GSYM AND_IMP_INTRO]
  \\ first_x_assum drule
  \\ disch_then drule \\ rw[]
  \\ first_x_assum (qspec_then `[]` strip_assume_tac)
  \\ rw[]
  \\ fs[REFS_PRED_FRAME_def, REFS_PRED_def]
  \\ `(H st3 * ($= h_k)) (st2heap p st)` by (rw [STAR_def] \\ SATISFY_TAC)
  \\ first_x_assum drule \\ rw[]
  \\ drule HPROP_SPLIT3_clock0 \\ rw[]
  \\ asm_exists_tac \\ fs []
  \\ last_x_assum drule \\ rw[]
  \\ qexists_tac `Val v` \\ fs []
  \\ fs [SEP_CLAUSES,SEP_EXISTS_THM,PULL_EXISTS]
  \\ simp_tac (std_ss++sep_cond_ss) [cond_STAR]
  \\ asm_exists_tac \\ fs []
  \\ drule evaluate_Rval_bigStep_to_evaluate \\ rw[]
  \\ fs[with_same_refs]
  \\ rw[evaluate_ck_def]
  \\ asm_exists_tac \\ simp[]);

val ArrowP_MONAD_to_app = Q.store_thm("ArrowP_MONAD_to_app",
  `!A B C f fv H x xv ro refs p.
     A x xv ==>
     ArrowP ro (H,p) (PURE A) (MONAD B C) f fv ==>
     app (p : 'ffi ffi_proj) fv [xv] (H refs)
     (POST
        (\rv. SEP_EXISTS refs' r. H refs' *
              &(f x refs = (Success r, refs')) * &(B r rv))
        (\ev. SEP_EXISTS refs' e. H refs' *
              &(f x refs = (Failure e, refs')) * &(C e ev)))`,
  rw [app_def, app_basic_def, ArrowP_def, EqSt_def, PURE_def]
  \\ fs [PULL_EXISTS]
  \\ first_x_assum drule
  \\ disch_then (qspecl_then [`refs`,`st`,`[]`] mp_tac)
  \\ impl_keep_tac >- metis_tac [REFS_PRED_lemma]
  \\ rw []
  \\ first_x_assum (qspec_then `[]` strip_assume_tac) \\ rw []
  \\ fs [REFS_PRED_FRAME_def]
  \\ `junk' = []` by fs [state_component_equality]
  \\ fs [with_same_refs]
  \\ fs [evaluate_ck_def]
  \\ `(H refs * ($= h_k)) (st2heap p st)` by (rw [STAR_def] \\ SATISFY_TAC)
  \\ first_x_assum drule \\ rw []
  \\ drule HPROP_SPLIT3_clock0 \\ rw []
  \\ asm_exists_tac \\ fs[]
  \\ Cases_on `res3` \\ Cases_on `f x refs` \\ Cases_on `q` \\ fs [MONAD_def]
  >> TRY (Cases_on `e` \\ fs [])
  >> TRY (drule evaluate_Rval_bigStep_to_evaluate)
  >> TRY (drule evaluate_Rerr_bigStep_to_evaluate)
  >> rw[]
  >> TRY (rename1 `Rval [a]` \\ qexists_tac `Val a`)
  >> TRY (rename1 `Rerr (Rraise a)` \\ qexists_tac `Exn a`)
  >> rw[]
  >> qexists_tac `c`
  >> fs [SEP_CLAUSES,SEP_EXISTS_THM,PULL_EXISTS]
  >> simp_tac (std_ss++sep_cond_ss) [cond_STAR]
  >> simp[]);

val ArrowP_MONAD_EqSt_to_app = Q.store_thm("ArrowP_MONAD_EqSt_to_app",
  `!A B C f fv H x xv ro refs p.
     A x xv ==>
     ArrowP ro (H,p) (EqSt (PURE A) refs) (MONAD B C) f fv ==>
     app (p : 'ffi ffi_proj) fv [xv] (H refs)
     (POST
          (\rv. SEP_EXISTS refs' r. H refs' *
                &(f x refs = (Success r, refs')) * &(B r rv))
          (\ev. SEP_EXISTS refs' e. H refs' *
                &(f x refs = (Failure e, refs')) * &(C e ev)))`,
  rw [app_def, app_basic_def, ArrowP_def, EqSt_def, PURE_def]
  \\ fs [PULL_EXISTS]
  \\ first_x_assum drule
  \\ disch_then (qspecl_then [`st`,`[]`] mp_tac)
  \\ impl_keep_tac >- metis_tac [REFS_PRED_lemma]
  \\ rw []
  \\ first_x_assum (qspec_then `[]` strip_assume_tac) \\ rw []
  \\ fs [REFS_PRED_FRAME_def]
  \\ `junk' = []` by fs [state_component_equality]
  \\ fs [with_same_refs]
  \\ fs [evaluate_ck_def]
  \\ `(H refs * ($= h_k)) (st2heap p st)` by (rw [STAR_def] \\ SATISFY_TAC)
  \\ first_x_assum drule \\ rw []
  \\ drule HPROP_SPLIT3_clock0 \\ rw []
  \\ asm_exists_tac \\ fs[]
  \\ Cases_on `res3` \\ Cases_on `f x refs` \\ Cases_on `q` \\ fs [MONAD_def]
  >> TRY (Cases_on `e` \\ fs [])
  >> TRY (drule evaluate_Rval_bigStep_to_evaluate)
  >> TRY (drule evaluate_Rerr_bigStep_to_evaluate)
  >> rw[]
  >> TRY (rename1 `Rval [a]` \\ qexists_tac `Val a`)
  >> TRY (rename1 `Rerr (Rraise a)` \\ qexists_tac `Exn a`)
  >> rw[]
  >> qexists_tac `c`
  >> fs [SEP_CLAUSES,SEP_EXISTS_THM,PULL_EXISTS]
  >> simp_tac (std_ss++sep_cond_ss) [cond_STAR]
  >> simp[]);

val parsed_terms = save_thm("parsed_terms",
  packLib.pack_list
   (packLib.pack_pair packLib.pack_string packLib.pack_term)
      [("PURE",``PURE : ('a -> v -> bool) -> ('a, 'ffi, 'b) H``),
       ("p",mk_var("p", ``:'ffi ffi_proj``)),
       ("emp",``emp:hprop``)]);

val _ = export_theory();
