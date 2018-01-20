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

(*
 * REFS_PRED_Mem_Only: a property we need to be satisfied by the heap to
 * prove the following theorems.
 *)

val REFS_PRED_Mem_Only_IMP = Q.store_thm("REFS_PRED_Mem_Only_IMP",
`!H. REFS_PRED_Mem_Only H ==> ((!p st state h1 h2. SPLIT (st2heap p st) (h1, h2) ==> H state h1 ==> ?h3. SPLIT (store2heap st.refs) (h1, h3)))`,
rw[REFS_PRED_Mem_Only_def]
\\ fs[SPLIT_def]
\\ qexists_tac `store2heap st.refs DIFF h1`
\\ rw[]
>-(
    rw[SET_EQ_SUBSET, SUBSET_DEF]
    \\ `x IN st2heap p st` by metis_tac[IN_UNION]
    \\ fs[st2heap_def]
    \\ last_x_assum IMP_RES_TAC
    \\ fs[Mem_NOT_IN_ffi2heap])
\\ fs[DISJOINT_ALT]);

val REFS_PRED_Mem_Only_STAR_IMP = Q.store_thm("REFS_PRED_Mem_Only_STAR_IMP",
`!H1 H2. REFS_PRED_Mem_Only H1 ==> REFS_PRED_Mem_Only H2 ==> REFS_PRED_Mem_Only (\state. H1 state * H2 state)`,
rw[REFS_PRED_Mem_Only_def]
\\ fs[STAR_def, SPLIT_def]
\\ metis_tac[IN_DEF, IN_UNION]);

val REFS_PRED_Mem_Only_REF_REL = Q.store_thm("REFS_PRED_Mem_Only_REF_REL",
`!A get_val r. REFS_PRED_Mem_Only (\state. REF_REL A r (get_val state))`,
rw[REFS_PRED_Mem_Only_def]
\\ fs[REF_REL_def, SEP_EXISTS_THM, HCOND_EXTRACT, REF_def, cell_def, one_def]
\\ rw[]
\\ fs[IN_SING]);

val REFS_PRED_Mem_Only_RARRAY_REL = Q.store_thm("REFS_PRED_Mem_Only_RARRAY_REL",
`!A get_arr r. REFS_PRED_Mem_Only (\state. RARRAY_REL A r (get_arr state))`,
rw[REFS_PRED_Mem_Only_def]
\\ fs[RARRAY_REL_def, RARRAY_def, ARRAY_def, SEP_CLAUSES, SEP_EXISTS_THM, HCOND_EXTRACT, REF_def, cell_def, one_def, GSYM STAR_ASSOC]
\\ fs[STAR_def, SPLIT_def, cond_def]
\\ rw[]
\\ fs[IN_SING]);

val REFS_PRED_Mem_Only_emp = Q.store_thm("REFS_PRED_Mem_Only_emp",
`REFS_PRED_Mem_Only (\(state : 'a). emp)`,
rw[REFS_PRED_Mem_Only_def]
\\ fs[REF_REL_def, SEP_EXISTS_THM, HCOND_EXTRACT, REF_def, cell_def, one_def, emp_def]
\\ rw[]
\\ fs[]);

(*
 * ffi of any type
 *)

val DISJ_TO_IMP = Q.prove(`(A \/ B) <=> ~A ==> B`,
EQ_TAC >-(rw[] \\ rw[])
\\ Cases_on `A`
\\ rw[]);

val INTER_DISJOINT = Q.store_thm("INTER_DISJOINT",
`x IN h1 ==> x IN h2 ==> DISJOINT h1 h2 = F`,
rw[]
\\ rpt STRIP_TAC
\\ fs[DISJOINT_DEF]
\\ `(h1 INTER h2) x` by rw[INTER_DEF]
\\ `{} x` by metis_tac[]
\\ fs[]);

val apply_REFS_PRED_Mem_Only_IMP =
  first_assum (fn x => let val lemma = (MATCH_MP REFS_PRED_Mem_Only_IMP x)
  in first_assum (fn x => (MATCH_MP lemma x) |> drule) end)

val apply_REFS_PRED_Mem_Only_IMP2 =
  first_assum (fn x => let val lemma = (MATCH_MP REFS_PRED_Mem_Only_IMP x)
  in last_assum (fn x => (MATCH_MP lemma x) |> drule) end)

val ArrowP_PURE_to_app = Q.store_thm("ArrowP_PURE_to_app",
  `!A B f fv x1 xv1 xv2 xvl H Q state p.
     REFS_PRED_Mem_Only H ==>
     A x1 xv1 ==>
     (!gv. B (f x1) gv ==>
     app (p : 'ffi ffi_proj) gv (xv2::xvl) (H state) (Q state)) ==>
     ArrowP (H,p) (PURE A) (PURE B) f fv ==>
     app p fv (xv1::xv2::xvl) (H state) (Q state)`,
  cheat (*
  rw [app_def, app_basic_def, ArrowP_def, PURE_def]
  \\ fs [PULL_EXISTS]
  \\ first_x_assum drule
  \\ disch_then (qspecl_then [`state`,`st`,`[]`] mp_tac) \\ simp []
  \\ impl_keep_tac >- metis_tac [REFS_PRED_lemma]
  \\ rw []
  \\ first_x_assum (qspec_then `[]` strip_assume_tac) \\ rw []
  \\ fs [REFS_PRED_FRAME_def] \\ rw []
  \\ fs [evaluate_ck_def]
  \\ `(H state * ($= h_k)) (st2heap p st)` by (rw [STAR_def] \\ SATISFY_TAC)
  \\ first_x_assum drule \\ rw []
  \\ drule (GEN_ALL HPROP_SPLIT3) \\ rw []
  \\ fs [with_same_refs]
  \\ imp_res_tac evaluate_Rval_bigStep_to_evaluate
  \\ qexists_tac `Val v'`
  \\ CONV_TAC (RESORT_EXISTS_CONV rev)
  \\ qmatch_asmsub_abbrev_tac `evaluate _ _ _ = (st2, _)`
  \\ Q.LIST_EXISTS_TAC [`c`,`st2`] \\ fs [Abbr`st2`]
  \\ Q.LIST_EXISTS_TAC [`st2heap p (st with refs := refs) DIFF h1 DIFF h_k`,`h1`]
  \\ first_x_assum drule \\ strip_tac
  \\ fs [SEP_EXISTS_THM, SEP_CLAUSES]
  \\ reverse conj_tac
  >-
   (fs [HCOND_EXTRACT]
    \\ asm_exists_tac
    \\ fs [])
  \\ `SPLIT (st2heap p (st with refs := refs)) (h1, h_k UNION h3)` by
    fs [SPLIT_def, SPLIT3_def, UNION_ASSOC, DISJOINT_SYM]
  \\ apply_REFS_PRED_Mem_Only_IMP
  \\ apply_REFS_PRED_Mem_Only_IMP2 \\ rw []
  \\ fs [SPLIT_def, SPLIT3_def]
  \\ reverse conj_tac >- fs [DISJOINT_ALT]
  \\ fs [st2heap_clock]
  \\ once_rewrite_tac [UNION_COMM]
  \\ simp [DIFF_UNION]
  \\ qpat_x_assum `_ UNION _ UNION _ = _` (assume_tac o GSYM) \\ fs []
  \\ metis_tac [IN_UNION, SUBSET_DEF, UNION_DIFF] *));

val ArrowP_MONAD_to_app = Q.store_thm("ArrowP_MONAD_to_app",
  `!A B C f fv H x xv refs p.
     REFS_PRED_Mem_Only H ==>
     A x xv ==>
     ArrowP (H,p) (PURE A) (MONAD B C) f fv ==>
     app (p : 'ffi ffi_proj) fv [xv] (H refs)
     (POST
          (\rv. SEP_EXISTS refs' r. H refs' * &(f x refs = (Success r, refs')) * &(B r rv))
          (\ev. SEP_EXISTS refs' e. H refs' * &(f x refs = (Failure e, refs')) * &(C e ev)))`,
  cheat (*
  rw [app_def, app_basic_def, ArrowP_def, EqSt_def, PURE_def]
  \\ fs [PULL_EXISTS]
  \\ first_x_assum drule
  \\ disch_then (qspecl_then [`refs`,`st`,`[]`] mp_tac)
  \\ impl_keep_tac >- metis_tac [REFS_PRED_lemma]
  \\ rw []
  \\ first_x_assum (qspec_then `[]` strip_assume_tac) \\ rw []
  \\ fs [REFS_PRED_FRAME_def] \\ rw []
  \\ fs [evaluate_ck_def]
  \\ `(H refs * ($= h_k)) (st2heap p st)` by (rw [STAR_def] \\ SATISFY_TAC)
  \\ first_x_assum drule \\ rw []
  \\ drule (GEN_ALL HPROP_SPLIT3) \\ rw []
  \\ fs [with_same_refs]
  \\ Cases_on `res3` \\ Cases_on `f x refs` \\ Cases_on `q` \\ fs [MONAD_def]
  \\ TRY (Cases_on `e` \\ fs [])
  \\ imp_res_tac evaluate_Rval_bigStep_to_evaluate
  \\ imp_res_tac evaluate_Rerr_bigStep_to_evaluate
  \\ TRY (rename1 `Rval [a]` \\ qexists_tac `Val a`)
  \\ TRY (rename1 `Rerr (Rraise a)` \\ qexists_tac `Exn a`)
  \\ CONV_TAC (RESORT_EXISTS_CONV rev)
  \\ qmatch_asmsub_abbrev_tac `evaluate _ _ _ = (st2, _)`
  \\ Q.LIST_EXISTS_TAC [`c`,`st2`] \\ fs [Abbr`st2`]
  \\ Q.LIST_EXISTS_TAC [`st2heap p (st with refs := refs') DIFF h1 DIFF h_k`,`h1`]
  \\ fs [SEP_EXISTS_THM, SEP_CLAUSES] \\ rw []
  \\ fs [HCOND_EXTRACT]
  \\ `SPLIT (st2heap p (st with refs := refs')) (h1, h_k UNION h3)` by
    fs [SPLIT_def, SPLIT3_def, UNION_ASSOC, DISJOINT_SYM]
  \\ apply_REFS_PRED_Mem_Only_IMP
  \\ apply_REFS_PRED_Mem_Only_IMP2 \\ rw []
  \\ fs [SPLIT_def, SPLIT3_def]
  \\ reverse conj_tac
  \\ TRY (fs [DISJOINT_ALT] \\ NO_TAC)
  \\ fs [st2heap_clock]
  \\ once_rewrite_tac [UNION_COMM]
  \\ simp [DIFF_UNION]
  \\ qpat_x_assum `_ UNION _ UNION _ = _` (assume_tac o GSYM) \\ fs []
  \\ metis_tac [IN_UNION, SUBSET_DEF, UNION_DIFF] *))

val ArrowP_MONAD_EqSt_to_app = Q.store_thm("ArrowP_MONAD_EqSt_to_app",
  `!A B C f fv H x xv refs p.
     REFS_PRED_Mem_Only H ==>
     A x xv ==>
     ArrowP (H,p) (EqSt (PURE A) refs) (MONAD B C) f fv ==>
     app (p : 'ffi ffi_proj) fv [xv] (H refs)
     (POST
          (\rv. SEP_EXISTS refs' r. H refs' * &(f x refs = (Success r, refs')) * &(B r rv))
          (\ev. SEP_EXISTS refs' e. H refs' * &(f x refs = (Failure e, refs')) * &(C e ev)))`,
  cheat (*
  rw [app_def, app_basic_def, ArrowP_def, EqSt_def, PURE_def]
  \\ fs [PULL_EXISTS]
  \\ first_x_assum drule
  \\ disch_then (qspecl_then [`st`,`[]`] mp_tac)
  \\ impl_keep_tac >- metis_tac [REFS_PRED_lemma]
  \\ rw []
  \\ first_x_assum (qspec_then `[]` strip_assume_tac) \\ rw []
  \\ fs [REFS_PRED_FRAME_def] \\ rw []
  \\ fs [evaluate_ck_def]
  \\ `(H refs * ($= h_k)) (st2heap p st)` by (rw [STAR_def] \\ SATISFY_TAC)
  \\ first_x_assum drule \\ rw []
  \\ drule (GEN_ALL HPROP_SPLIT3) \\ rw []
  \\ fs [with_same_refs]
  \\ Cases_on `res3` \\ Cases_on `f x refs` \\ Cases_on `q` \\ fs [MONAD_def]
  \\ TRY (Cases_on `e` \\ fs [])
  \\ imp_res_tac evaluate_Rval_bigStep_to_evaluate
  \\ imp_res_tac evaluate_Rerr_bigStep_to_evaluate
  \\ TRY (rename1 `Rval [a]` \\ qexists_tac `Val a`)
  \\ TRY (rename1 `Rerr (Rraise a)` \\ qexists_tac `Exn a`)
  \\ CONV_TAC (RESORT_EXISTS_CONV rev)
  \\ qmatch_asmsub_abbrev_tac `evaluate _ _ _ = (st2, _)`
  \\ Q.LIST_EXISTS_TAC [`c`,`st2`] \\ fs [Abbr`st2`]
  \\ Q.LIST_EXISTS_TAC [`st2heap p (st with refs := refs') DIFF h1 DIFF h_k`,`h1`]
  \\ fs [SEP_EXISTS_THM, SEP_CLAUSES] \\ rw []
  \\ fs [HCOND_EXTRACT]
  \\ `SPLIT (st2heap p (st with refs := refs')) (h1, h_k UNION h3)` by
    fs [SPLIT_def, SPLIT3_def, UNION_ASSOC, DISJOINT_SYM]
  \\ apply_REFS_PRED_Mem_Only_IMP
  \\ apply_REFS_PRED_Mem_Only_IMP2 \\ rw []
  \\ fs [SPLIT_def, SPLIT3_def]
  \\ reverse conj_tac
  \\ TRY (fs [DISJOINT_ALT] \\ NO_TAC)
  \\ fs [st2heap_clock]
  \\ once_rewrite_tac [UNION_COMM]
  \\ simp [DIFF_UNION]
  \\ qpat_x_assum `_ UNION _ UNION _ = _` (assume_tac o GSYM) \\ fs []
  \\ metis_tac [IN_UNION, SUBSET_DEF, UNION_DIFF] *))

val parsed_terms = save_thm("parsed_terms",
  packLib.pack_list
   (packLib.pack_pair packLib.pack_string packLib.pack_term)
      [("PURE",``PURE : ('a -> v -> bool) -> ('a, 'ffi, 'b) H``),
       ("p",mk_var("p", ``:'ffi ffi_proj``)),
       ("emp",``emp:hprop``)]);

val _ = export_theory();
