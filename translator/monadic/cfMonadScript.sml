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

(*
 * REFS_PRED_Mem_Only: a property we need to be satisfied by the heap to
 * prove the following theorems.
 *)

val REFS_PRED_Mem_Only_def = Define `REFS_PRED_Mem_Only H = !state h. H state h ==> !x. x IN h ==> ?n v. x = Mem n v`;

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
app (p : 'a ffi_proj) gv (xv2::xvl) (H state) (Q state)) ==>
ArrowP H (PURE A) (PURE B) f fv ==>
app p fv (xv1::xv2::xvl) (H state) (Q state)`,
rw[app_def]
\\ rw[app_basic_def]
\\ fs[ArrowP_def]
\\ fs[PURE_def]
\\ first_x_assum (qspec_then `x1` ASSUME_TAC)
\\ POP_ASSUM IMP_RES_TAC
\\ first_x_assum(qspecl_then[`empty_state with refs := st.refs`, `empty_state with refs := st.refs`, `[]`] ASSUME_TAC)
\\ fs[state_component_equality]
\\ sg `!p. ?h2. SPLIT (st2heap p (empty_state with refs := st.refs)) (h_i, h2)`
>-(
    (* last_x_assum IMP_RES_TAC *)
    apply_REFS_PRED_Mem_Only_IMP \\ rw[]
    \\ rw[st2heap_def]
    \\ qexists_tac `h3 UNION (ffi2heap p' empty_state.ffi)`
    \\ fs[SPLIT_def, UNION_ASSOC]
    \\ PURE_ONCE_REWRITE_TAC[DISJOINT_SYM]
    \\ fs[]
    \\ ASSUME_TAC (ISPECL [``p':unit ffi_proj``, ``empty_state with refs := st.refs``] st2heap_SPLIT_FFI)
    \\ fs[SPLIT_def]
    \\ qpat_x_assum `h_i UNION h3 = h` (fn x => fs[SYM x]))
\\ first_x_assum(qspec_then `ARB` STRIP_ASSUME_TAC)
\\ IMP_RES_TAC REFS_PRED_lemma
\\ qpat_x_assum `!refs. R` (fn x => ALL_TAC)
\\ qpat_x_assum `!refs1 p. R ==> ?env. R2` drule \\ rw[]
\\ POP_ASSUM(qspec_then `[]` STRIP_ASSUME_TAC)
\\ fs[REFS_PRED_FRAME_def]
\\ fs[evaluate_ck_def]
\\ rw[]
\\ `(H st3 * (\s. s = h2)) (st2heap ARB (empty_state with refs := st.refs))` by (rw[STAR_def] \\ SATISFY_TAC)
\\ qpat_assum `!F. P` drule \\ rw[]
\\ first_x_assum drule \\ strip_tac
\\ drule HPROP_SPLIT3 \\ rw[]
\\ fs[with_same_refs] \\ rw[]
\\ drule evaluate_Rval_bigStep_to_evaluate \\ rw[]
\\ qexists_tac `Val v`
\\ qexists_tac `h1`
\\ qexists_tac `(st2heap p (st with refs := st.refs ++ junk)) DIFF h1 DIFF h_k`
\\ qexists_tac `st with <| clock := 0; refs := st.refs ++ junk |>`
\\ qexists_tac `c`
\\ fs[SEP_CLAUSES, SEP_EXISTS_THM]
\\ rw[]
>-(    
    sg `SPLIT (st2heap ARB (empty_state with refs := st.refs ++ junk)) (h1, h2 UNION h3)`
    >-(fs[SPLIT_def, SPLIT3_def, UNION_ASSOC] \\ metis_tac[DISJOINT_SYM])
    \\ apply_REFS_PRED_Mem_Only_IMP
    \\ apply_REFS_PRED_Mem_Only_IMP2 \\ rw[]
    \\ fs[state_component_equality]
    \\ fs[SPLIT_def, SPLIT3_def]
    \\ sg `!x. x IN h_i ==> x IN store2heap st.refs`
    >-(
	rw[]
	\\ `x IN (h_i UNION h3')` by fs[]
	\\ metis_tac[UNION_DEF, IN_DEF])
    \\ sg `h2 INTER (store2heap st.refs) = h_k INTER (store2heap st.refs)`
    >-(
	simp[SET_EQ_SUBSET, SUBSET_DEF]
	\\ fs[st2heap_def]
        \\ rw[]
        >-(
            `x IN h_i UNION h_k` by metis_tac[IN_UNION]
            \\ fs[]
            \\ IMP_RES_TAC INTER_DISJOINT)
        \\ `x IN h_i UNION h2` by metis_tac[IN_UNION]
        \\ fs[]
        \\ IMP_RES_TAC INTER_DISJOINT)
    \\ reverse(rw[])
    >-(
	rw[DISJOINT_DEF]
	\\ PURE_ONCE_REWRITE_TAC[GSYM SUBSET_EMPTY]
	\\ PURE_REWRITE_TAC[SUBSET_DEF]
	\\ rpt STRIP_TAC
	\\ fs[]
	\\ metis_tac[])
    >-(
	rw[DISJOINT_DEF]
	\\ PURE_ONCE_REWRITE_TAC[GSYM SUBSET_EMPTY]
	\\ PURE_REWRITE_TAC[SUBSET_DEF]
	\\ rpt STRIP_TAC
	\\ fs[]
	\\ metis_tac[])
    (* DISJOINT h1 h_k *)
    >-(
	rw[DISJOINT_ALT]
	\\ rw[]
	\\ `x IN store2heap (st.refs ++ junk)` by metis_tac[IN_UNION]
	\\ fs[cfAppTheory.store2heap_append_many]
	>-(
	    strip_tac
            \\ `x IN h2` by metis_tac[IN_INTER]
            \\ fs[DISJOINT_ALT]
	    \\ metis_tac[])
	>-(
	    strip_tac
	    \\ `x IN (st2heap p st)` by metis_tac[IN_UNION]
	    \\ fs[st2heap_def]
	    >-(
		`SPLIT (store2heap (st.refs ++ junk)) (store2heap st.refs, store2heap_aux (LENGTH st.refs) junk)` by fs[store2heap_SPLIT]
		\\ fs[SPLIT_def]
		\\ fs[DISJOINT_ALT])
	    \\ Cases_on `x`
	    \\ fs[Mem_NOT_IN_ffi2heap, FFI_split_NOT_IN_store2heap_aux, FFI_full_NOT_IN_store2heap_aux, FFI_part_NOT_IN_store2heap_aux]))
    (* SETS EQUALITY *)
    \\ simp[Once SET_EQ_SUBSET, SUBSET_DEF]
    \\ fs[st2heap_clock]
    \\ rw[]
    >-(
	sg `x IN store2heap (st.refs ++ junk)`
	>-(
	    fs[st2heap_def, cfAppTheory.store2heap_append_many]
	    \\ `x IN h1 ∪ h3''` by fs[]
	    \\ `x IN store2heap st.refs ∪ store2heap_aux (LENGTH st.refs) junk` by metis_tac[]
	    \\ fs[])
	\\ rw[st2heap_def])
    >-(
	sg `x IN st2heap p st`
	>-(
	    `x IN h_i ∪ h_k` by fs[]
	    \\ metis_tac[])
	\\ rw[st2heap_def]
	\\ fs[st2heap_def, cfAppTheory.store2heap_append_many])
    \\ Cases_on `x IN h1` >> fs[]
    \\ Cases_on `x IN h_k` >> fs[]
    \\ fs[IN_DEF, st2heap_def])
>-(qexists_tac `H st3` \\ fs[HCOND_EXTRACT])
\\ ASSUME_TAC (Thm.INST_TYPE[``:'a`` |-> ``:unit``, ``:'b`` |-> ``:'a``] (CONJUNCT1 evaluatePropsTheory.evaluate_ffi_intro))
\\ first_x_assum IMP_RES_TAC
\\ fs[state_component_equality, ml_translatorTheory.empty_state_def, ffiTheory.initial_ffi_state_def]);

val prove_ArrowP_MONAD_to_app_SPLIT3 =
  ntac 3 (POP_ASSUM (fn x => ALL_TAC))
  \\ sg `SPLIT (st2heap pu (empty_state with refs := refs')) (h1, h2 UNION h3)`
  >-(fs[SPLIT_def, SPLIT3_def, UNION_ASSOC] \\ metis_tac[DISJOINT_SYM])
  \\ apply_REFS_PRED_Mem_Only_IMP
  \\ apply_REFS_PRED_Mem_Only_IMP2 \\ rw[]
  (* cleanup *)
  \\ ntac 2 (last_x_assum (fn x => ALL_TAC))
  \\ fs[state_component_equality, st2heap_clock]
  \\ ntac 3 (last_x_assum ASSUME_TAC)
  \\ ntac 6 (last_x_assum (fn x => ALL_TAC))
  (* end of cleanup *)
  \\ fs[SPLIT_def, SPLIT3_def]
  \\ `!x. x IN h_i ==> x IN store2heap st.refs` by metis_tac[IN_UNION]
  \\ sg `h2 INTER (store2heap refs') = h_k INTER (store2heap refs')`
  >-(
      simp[SET_EQ_SUBSET, SUBSET_DEF]
      \\ fs[st2heap_def]
      \\ rw[]
      >-(
	  sg `x IN store2heap st.refs`
	  >-(
	      `x IN store2heap st.refs UNION ffi2heap pu empty_state.ffi` by metis_tac[IN_UNION]
	      \\ Cases_on `x`
	      >> fs[store2heap_def, Mem_NOT_IN_ffi2heap, FFI_split_NOT_IN_store2heap_aux, FFI_full_NOT_IN_store2heap_aux, FFI_part_NOT_IN_store2heap_aux])
	  \\ `x IN h_i ∪ h_k` by metis_tac[IN_UNION]
	  \\ fs[]
	  \\ IMP_RES_TAC INTER_DISJOINT)
      \\ sg `x IN store2heap st.refs`
	  >-(
	     `x IN store2heap st.refs UNION ffi2heap p st.ffi` by metis_tac[IN_UNION]
	     \\ Cases_on `x`
	     >> fs[store2heap_def, Mem_NOT_IN_ffi2heap, FFI_split_NOT_IN_store2heap_aux, FFI_full_NOT_IN_store2heap_aux, FFI_part_NOT_IN_store2heap_aux])
      \\ `x IN h_i ∪ h2` by metis_tac[IN_UNION]
      \\ fs[]
      \\ IMP_RES_TAC INTER_DISJOINT)
  \\ sg `h2 INTER (store2heap st.refs) = h_k INTER (store2heap st.refs)`
  >-(
      simp[SET_EQ_SUBSET, SUBSET_DEF]
      \\ fs[st2heap_def]
      \\ rw[]
      >-(
	  `x IN h_i UNION h_k` by metis_tac[IN_UNION]
	  \\ fs[]
	  \\ IMP_RES_TAC INTER_DISJOINT)
      \\ `x IN h_i UNION h2` by metis_tac[IN_UNION]
      \\ fs[]
      \\ IMP_RES_TAC INTER_DISJOINT)
  \\ reverse(rw[])
  >-(
      rw[DISJOINT_DEF]
      \\ PURE_ONCE_REWRITE_TAC[GSYM SUBSET_EMPTY]
      \\ PURE_REWRITE_TAC[SUBSET_DEF]
      \\ rpt STRIP_TAC
      \\ fs[]
      \\ metis_tac[])
  >-(
      rw[DISJOINT_DEF]
      \\ PURE_ONCE_REWRITE_TAC[GSYM SUBSET_EMPTY]
      \\ PURE_REWRITE_TAC[SUBSET_DEF]
      \\ rpt STRIP_TAC
      \\ fs[]
      \\ metis_tac[])
  (* DISJOINT h1 h_k *)
  >-(
      rw[DISJOINT_ALT]
      \\ rw[]
      \\ `x IN store2heap refs'` by metis_tac[IN_UNION]
      \\ strip_tac
      \\ `x IN h2` by metis_tac[IN_UNION, IN_INTER]
      \\ IMP_RES_TAC INTER_DISJOINT)
  (* SETS EQUALITY *)
  \\ simp[Once SET_EQ_SUBSET, SUBSET_DEF]
  \\ reverse(rw[])
  >-(metis_tac[])
  >-(
      `x IN st2heap p st` by metis_tac[IN_UNION]
      \\ fs[st2heap_def]
      \\ `x IN store2heap refs' ∪ ffi2heap pu empty_state.ffi` by metis_tac[IN_UNION, UNION_ASSOC, IN_INTER]
      \\ fs[]
      \\ irule FALSITY
      \\ Cases_on `x`
      >> fs[store2heap_def, Mem_NOT_IN_ffi2heap, FFI_split_NOT_IN_store2heap_aux, FFI_full_NOT_IN_store2heap_aux, FFI_part_NOT_IN_store2heap_aux])
  \\ fs[st2heap_def]
  \\ metis_tac[IN_UNION];

val prove_MONAD_to_app =
rw[app_def]
\\ rw[app_basic_def]
\\ fs[ArrowP_def]
\\ fs[EqSt_def, PURE_def]
\\ first_x_assum (qspec_then `x` ASSUME_TAC)
\\ POP_ASSUM IMP_RES_TAC
\\ fs[state_component_equality]
\\ first_x_assum(qspecl_then[`empty_state with refs := st.refs`, `[]`] ASSUME_TAC)
\\ sg `!p. ?h2. SPLIT (st2heap p (empty_state with refs := st.refs)) (h_i, h2)`
>-(
    apply_REFS_PRED_Mem_Only_IMP
    \\ apply_REFS_PRED_Mem_Only_IMP2 \\ rw[]
    \\ rw[st2heap_def]
    \\ qexists_tac `h3 UNION (ffi2heap p' empty_state.ffi)`
    \\ fs[SPLIT_def, UNION_ASSOC]
    \\ PURE_ONCE_REWRITE_TAC[DISJOINT_SYM]
    \\ fs[]
    \\ rw[DISJOINT_ALT]
    \\ sg `x' IN store2heap st.refs`
    >-(
	`x' IN h_i UNION h3` by fs[]
        \\ metis_tac[])
    \\ fs[store2heap_def]
    \\ Cases_on `x'`
    >> fs[Mem_NOT_IN_ffi2heap, FFI_split_NOT_IN_store2heap_aux, FFI_full_NOT_IN_store2heap_aux, FFI_part_NOT_IN_store2heap_aux])
\\ first_x_assum(qspec_then `pu` STRIP_ASSUME_TAC)
\\ IMP_RES_TAC REFS_PRED_lemma
\\ last_x_assum drule \\ rw[]
\\ POP_ASSUM(qspec_then `[]` STRIP_ASSUME_TAC)
\\ fs[REFS_PRED_FRAME_def]
\\ fs[evaluate_ck_def]
\\ rw[]
\\ `(H refs * (\s. s = h2)) (st2heap pu (empty_state with refs := st.refs))` by (rw[STAR_def] \\ SATISFY_TAC)
\\ qpat_assum `!F. P` IMP_RES_TAC
\\ IMP_RES_TAC HPROP_SPLIT3
\\ fs[with_same_refs] \\ rw[]
\\ Cases_on `res3`
>> Cases_on `f x refs`
>> Cases_on `q`
>> fs[MONAD_def]
THENL[ALL_TAC, Cases_on `e`]
>> fs[]
THENL[IMP_RES_TAC evaluate_Rval_bigStep_to_evaluate \\ qexists_tac `Val a`,
      IMP_RES_TAC evaluate_Rerr_bigStep_to_evaluate \\ qexists_tac `Exn a`]
\\ qexists_tac `h1`
\\ qexists_tac `(st2heap p (st with refs := refs')) DIFF h1 DIFF h_k`
\\ qexists_tac `st with <| clock := 0; refs := refs' |>`
\\ qexists_tac `c`
\\ fs[SEP_CLAUSES, SEP_EXISTS_THM]
\\ rw[]
>-(prove_ArrowP_MONAD_to_app_SPLIT3)
>-(fs[HCOND_EXTRACT])
>-(
    ASSUME_TAC (Thm.INST_TYPE[``:'a`` |-> ``:unit``, ``:'b`` |-> ``:'a``] (CONJUNCT1 evaluatePropsTheory.evaluate_ffi_intro))
    \\ first_x_assum IMP_RES_TAC
    \\ fs[state_component_equality, ml_translatorTheory.empty_state_def, ffiTheory.initial_ffi_state_def])
>-(prove_ArrowP_MONAD_to_app_SPLIT3)
>-(fs[HCOND_EXTRACT])
\\ ASSUME_TAC (Thm.INST_TYPE[``:'a`` |-> ``:unit``, ``:'b`` |-> ``:'a``] (CONJUNCT1 evaluatePropsTheory.evaluate_ffi_intro))
\\ first_x_assum IMP_RES_TAC
\\ fs[state_component_equality, ml_translatorTheory.empty_state_def, ffiTheory.initial_ffi_state_def]

val ArrowP_MONAD_to_app = Q.store_thm("ArrowP_MONAD_to_app",
`!A B C f fv H x xv refs p.
REFS_PRED_Mem_Only H ==>
A x xv ==>
ArrowP H (PURE A) (MONAD B C) f fv ==>
app (p : 'a ffi_proj) fv [xv] (H refs)
(POST
     (\rv. SEP_EXISTS refs' r. H refs' * &(f x refs = (Success r, refs')) * &(B r rv))
     (\ev. SEP_EXISTS refs' e. H refs' * &(f x refs = (Failure e, refs')) * &(C e ev)))`,
prove_MONAD_to_app);

val ArrowP_MONAD_EqSt_to_app = Q.store_thm("ArrowP_MONAD_EqSt_to_app",
`!A B C f fv H x xv refs p.
REFS_PRED_Mem_Only H ==>
A x xv ==>
ArrowP H (EqSt (PURE A) refs) (MONAD B C) f fv ==>
app (p : 'a ffi_proj) fv [xv] (H refs)
(POST
     (\rv. SEP_EXISTS refs' r. H refs' * &(f x refs = (Success r, refs')) * &(B r rv))
     (\ev. SEP_EXISTS refs' e. H refs' * &(f x refs = (Failure e, refs')) * &(C e ev)))`,
prove_MONAD_to_app);

val _ = export_theory();
