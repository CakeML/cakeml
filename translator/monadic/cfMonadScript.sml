open ml_monad_translatorTheory cfHeapsBaseTheory set_sepTheory pred_setTheory cfStoreTheory Satisfy
open semanticPrimitivesTheory cfTacticsLib 

val _ = new_theory"cfMonad"

(* Theorems to convert monadic specifications to cf specifications *)

val _ = Globals.max_print_depth := 40;

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
`SPLIT (st2heap (p : unit ffi_proj)  st) (h1, h2) /\ H refs h1 ==> REFS_PRED H refs p st`,
rw[REFS_PRED_def, STAR_def]
\\ qexists_tac `h1`
\\ qexists_tac `h2`
\\ fs[SAT_GC]
);

val state_with_refs_eq = Q.prove(
 `st with refs := r = st with refs := r' <=> r = r'`,
fs[state_component_equality]);

val HPROP_SPLIT3 = Q.prove(
`(H1 * H2 * H3) h ==> ?h1 h2 h3. SPLIT3 h (h1, h2, h3) /\ H1 h1 /\ H2 h2 /\ H3 h3`,
rw[STAR_def, SPLIT_def, SPLIT3_def]
\\ fs[DISJOINT_UNION]
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

val st2heap_clock_inv = Q.prove(`st2heap p (st with clock := c) = st2heap p st`,
Cases_on `p` \\ fs[st2heap_def]);

val ArrowP_to_app_basic_thm =  Q.store_thm("ArrowP_to_app_basic_thm",
`ArrowP H (PURE A) (MONAD B C) f fv ==>
!refs x xv. A x xv ==>
app_basic (p : unit ffi_proj) fv xv (H refs)
(POST
     (\rv. SEP_EXISTS refs' r. H refs' * &(f x refs = (Success r, refs')) * &(B r rv))
     (\ev. SEP_EXISTS refs' e. H refs' * &(f x refs = (Failure e, refs')) * &(C e ev)))`,
rw[]
\\ rw[app_basic_def]
\\ fs[ArrowP_def]
\\ fs[PURE_def]
\\ last_x_assum (qspec_then `x` ASSUME_TAC)
\\ POP_ASSUM IMP_RES_TAC
\\ fs[]
\\ IMP_RES_TAC REFS_PRED_lemma
\\ qpat_x_assum `!s1. P` IMP_RES_TAC
\\ fs[state_with_refs_eq]
\\ POP_ASSUM(qspec_then `[]` STRIP_ASSUME_TAC)
\\ fs[]
\\ POP_ASSUM(qspec_then `[]` STRIP_ASSUME_TAC)
\\ fs[MONAD_def]
\\ fs[with_same_refs]
\\ fs[REFS_PRED_FRAME_def]
\\ fs[evaluate_ck_def]
\\ `(H refs * (\s. s = h_k)) (st2heap p st)` by (rw[STAR_def] \\ SATISFY_TAC)
\\ qpat_assum `!F. P` IMP_RES_TAC
\\ IMP_RES_TAC HPROP_SPLIT3
\\ fs[] \\ rw[]
\\ Cases_on `res3` \\ Cases_on `f x refs` \\ fs[] \\ Cases_on `q` \\ fs[]
THENL[qexists_tac `Val a` \\ IMP_RES_TAC evaluate_Rval_bigStep_to_evaluate,
      Cases_on `e` \\ fs[] \\ qexists_tac `Exn a` \\ IMP_RES_TAC evaluate_Rerr_bigStep_to_evaluate]
\\ qexists_tac `h1`
\\ qexists_tac `h3`
\\ qexists_tac `s3 with clock := 0`
\\ qexists_tac `c`
\\ fs[st2heap_clock_inv]
\\ fs[SEP_EXISTS_THM]
\\ fs[GSYM STAR_ASSOC]
\\ CONV_TAC ((STRIP_QUANT_CONV o RATOR_CONV) PURE_FACTS_FIRST_CONV)
\\ fs[GSYM STAR_ASSOC, HCOND_EXTRACT]);

val Arrow_PURE_to_app_basic_thm =  Q.store_thm("ArrowP_PURE_to_app_basic_thm",
`ArrowP H (PURE A) (PURE B) f fv ==>
!refs x xv. A x xv ==>
app_basic (p : unit ffi_proj) fv xv (H refs)
(POSTv rv. SEP_EXISTS r. H refs * &(B (f x) rv))`,
rw[]
\\ rw[app_basic_def]
\\ fs[ArrowP_def]
\\ fs[PURE_def]
\\ last_x_assum (qspec_then `x` ASSUME_TAC)
\\ POP_ASSUM IMP_RES_TAC
\\ fs[]
\\ IMP_RES_TAC REFS_PRED_lemma
\\ qpat_x_assum `!s1. P` IMP_RES_TAC
\\ fs[state_with_refs_eq]
\\ POP_ASSUM(qspec_then `[]` STRIP_ASSUME_TAC)
\\ fs[]
\\ POP_ASSUM(qspec_then `[]` STRIP_ASSUME_TAC)
\\ fs[MONAD_def]
\\ fs[with_same_refs]
\\ fs[REFS_PRED_FRAME_def]
\\ fs[evaluate_ck_def]
\\ `(H refs * (\s. s = h_k)) (st2heap p st)` by (rw[STAR_def] \\ SATISFY_TAC)
\\ qpat_assum `!F. P` IMP_RES_TAC
\\ IMP_RES_TAC HPROP_SPLIT3
\\ fs[] \\ rw[]
\\ IMP_RES_TAC evaluate_Rval_bigStep_to_evaluate
\\ qexists_tac `Val v`
\\ qexists_tac `h1`
\\ qexists_tac `h3`
\\ qexists_tac `st with <|clock := 0; refs := st.refs ++ junk|>`
\\ qexists_tac `c`
\\ fs[st2heap_clock_inv]
\\ fs[SEP_EXISTS_THM]
\\ fs[SEP_CLAUSES]);

val _ = export_theory();
