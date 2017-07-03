open preamble ml_translatorTheory ml_translatorLib ml_pmatchTheory patternMatchesTheory
open astTheory libTheory bigStepTheory semanticPrimitivesTheory
open terminationTheory ml_progLib ml_progTheory
open set_sepTheory cfTheory cfStoreTheory cfTacticsLib Satisfy
open cfHeapsBaseTheory basisFunctionsLib mlarrayProgTheory
open ml_monadBaseTheory

val _ = new_theory "ml_monad_translator";

val _ = translation_extends"mlarrayProg";

val _ = temp_overload_on ("monad_bind", ``st_ex_bind``);
val _ = temp_overload_on ("monad_unitbind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("monad_ignore_bind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("ex_bind", ``st_ex_bind``);
val _ = temp_overload_on ("ex_return", ``st_ex_return``);

val _ = temp_overload_on ("CONTAINER", ``ml_translator$CONTAINER``);

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

val _ = temp_type_abbrev("state",``:'ffi semanticPrimitives$state``);

val lemma1 = Q.prove(
`nsLookup env.v (Long "Array" (Short "sub")) = SOME Array_sub_v ==>
evaluate F env st (Var (Long "Array" (Short "sub"))) (st, Rval Array_sub_v)`,
rw[Once evaluate_cases,evaluate_list_cases,PULL_EXISTS]);

val lemma2 = Q.prove(
`?env e. do_opapp [Array_sub_v; Loc loc] = SOME (env, e)`,
rw[do_opapp_def] \\ rw[Array_sub_v_def]);

val lemma3 = Q.prove(`evaluate F env (empty_state with refs := refs) (Lit (IntLit n))
(empty_state with refs := refs, Rval(Litv (IntLit n)))`,
rw[Once evaluate_cases,evaluate_list_cases,PULL_EXISTS]);

val lemma4 = Q.prove(`nsLookup env.v (Short vname) = SOME (Loc loc) ==>
nsLookup env.v (Long "Array" (Short "sub")) = SOME Array_sub_v ==>
EL loc refs = Varray av ==>
evaluate F env (empty_state with refs := refs)
        (Var (Long "Array" (Short "sub")))
        (empty_state with refs := refs,Rval Array_sub_v)`,
rw[Once evaluate_cases,evaluate_list_cases,PULL_EXISTS]);

fetch_v "Array.sub" (get_ml_prog_state())

val ABS_NUM_EQ = Q.prove(`Num(ABS(&n))=n`,
rw[fetch "integer" "Num", integerTheory.INT_ABS]);

val lemma5 = Q.prove(
`nsLookup env.v (Short vname) = SOME (Loc loc) ==>
loc < LENGTH refs ==>
EL loc refs = Varray av ==>
n < LENGTH av ==>
evaluate F env (empty_state with refs := refs)
(App Asub [Var (Short vname); Lit (IntLit (&n))])
(empty_state with refs := refs, Rval (EL n av))`,
rw[]
\\ rw[Once evaluate_cases,evaluate_list_cases,PULL_EXISTS]
\\ qexists_tac `empty_state with refs := refs`
\\ qexists_tac `refs`
\\ qexists_tac `empty_state.ffi`
\\ qexists_tac `Litv (IntLit (&n))`
\\ qexists_tac `empty_state with refs := refs`
\\ qexists_tac `Loc loc`
\\ fs[state_component_equality]
\\ fs[Once evaluate_cases,evaluate_list_cases,PULL_EXISTS]
\\ fs[Once evaluate_cases,evaluate_list_cases,PULL_EXISTS]
\\ fs[do_app_def]
\\ fs[store_lookup_def]
\\ fs[ABS_NUM_EQ]);
  
val get_ref_def = Define `
get_ref get_var = \state. (Success (get_var state), state)`;

val set_ref_def = Define `
set_ref set_var x = \state. (Success (), set_var x state)`;

val Marray_length_def = Define `
Marray_length get_arr = \state. (Success (LENGTH (get_arr state)), state)`;

val Marray_sub_def = Define `
Marray_sub get_arr exc n = \state.
if n < LENGTH (get_arr state) then (Success (EL n (get_arr state)), state)
else (Failure (exc (prim_exn "Subscript")), state)`;

val Marray_update_def = Define `
Marray_update get_arr set_arr exc n x = \state.
if n < LENGTH (get_arr state) then (Success (), set_arr (LUPDATE x n (get_arr state)) state)
else (Failure (exc (prim_exn "Subscript")), state)`;

val EvalM_Marray_length = Q.store_thm("EvalM_Marray_length",
  `!vname loc TYPE EXC_TYPE H get_arr env exp.
    nsLookup env.v (Short vname) = SOME (Loc loc) ==>
    EvalM env (App Alength [Var (Short vname)])
    ((MONAD INT EXC_TYPE) (λrefs. (Success (&(LENGTH (get_arr refs))), refs)))
    (λrefs. (SEP_EXISTS av. ARRAY (Loc loc) av * &(LIST_REL TYPE (get_arr refs) av)) * H refs)`,
  rw[EvalM_def]
  \\ rw[Once evaluate_cases,evaluate_list_cases,PULL_EXISTS]
  \\ ntac 6 (rw[Once evaluate_cases])
  \\ qexists_tac `s with refs := s.refs ++ junk`
  \\ fs[MONAD_def]
  \\ fs[REFS_PRED_def]
  \\ fs[SEP_CLAUSES, SEP_EXISTS_THM]
  \\ EXTRACT_PURE_FACTS_TAC
  \\ FULL_SIMP_TAC bool_ss [GSYM STAR_ASSOC]
  \\ fs[state_component_equality]
  \\ simp[do_app_def]
  \\ simp[store_lookup_def,EL_APPEND1,EL_APPEND2]
  \\ IMP_RES_TAC st2heap_ARRAY_MEM
  \\ IMP_RES_TAC store2heap_IN_LENGTH
  \\ IMP_RES_TAC store2heap_IN_EL
  \\ fs[EL_APPEND1]
  \\ IMP_RES_TAC LIST_REL_LENGTH
  \\ POP_ASSUM(fn x => fs[x])
  \\ fs[REFS_PRED_FRAME_append]);

(* Note: don't like the condition for the exception *)
val EvalM_Marray_sub = Q.store_thm("EvalM_Marray_sub",
  `!vname loc n TYPE EXC_TYPE H get_arr exc env exp.
   (!ev. EXC_TYPE (exc ev) ev) ==>
   nsLookup env.v (Short vname) = SOME (Loc loc) ==>
   EvalM env (App Asub [Var (Short vname); Lit (IntLit (&n))])
   ((MONAD TYPE EXC_TYPE) (Marray_sub get_arr exc n))
   (λrefs. (SEP_EXISTS av. ARRAY (Loc loc) av * &(LIST_REL TYPE (get_arr refs) av)) * H refs)`,
  rw[EvalM_def]
  \\ rw[Once evaluate_cases,evaluate_list_cases,PULL_EXISTS]
  \\ ntac 6 (rw[Once evaluate_cases])
  \\ qexists_tac `s with refs := s.refs ++ junk`
  \\ Cases_on `n < LENGTH (get_arr refs)`
  \\ fs[MONAD_def, Marray_sub_def]
  \\ fs[REFS_PRED_def]
  \\ fs[SEP_CLAUSES, SEP_EXISTS_THM]
  \\ EXTRACT_PURE_FACTS_TAC
  \\ FULL_SIMP_TAC bool_ss [GSYM STAR_ASSOC]
  \\ fs[state_component_equality]
  \\ simp[do_app_def]
  \\ simp[store_lookup_def,EL_APPEND1,EL_APPEND2]
  \\ IMP_RES_TAC st2heap_ARRAY_MEM
  \\ IMP_RES_TAC store2heap_IN_LENGTH
  \\ IMP_RES_TAC store2heap_IN_EL
  \\ fs[EL_APPEND1]
  \\ IMP_RES_TAC LIST_REL_LENGTH
  \\ fs[ABS_NUM_EQ]
  THENL[qexists_tac `Rval (EL n av)`,
        qexists_tac `Rerr (Rraise (prim_exn "Subscript"))`]
  \\ fs[LIST_REL_EL_EQN]
  \\ fs[REFS_PRED_FRAME_append]);
