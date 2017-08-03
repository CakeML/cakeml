structure ml_monadStoreLib :> ml_monadStoreLib = struct 

open preamble ml_translatorTheory ml_translatorLib ml_pmatchTheory patternMatchesTheory
open astTheory libTheory bigStepTheory semanticPrimitivesTheory
open terminationTheory ml_progLib ml_progTheory
open set_sepTheory cfTheory cfStoreTheory cfTacticsLib Satisfy
open cfHeapsBaseTheory basisFunctionsLib
open ml_monadBaseTheory ml_monad_translatorTheory Redblackmap AC_Sort

fun ERR fname msg = mk_HOL_ERR "ml_monadProgLib" fname msg;

val HCOND_EXTRACT = cfLetAutoTheory.HCOND_EXTRACT

(******* COPY/PASTE from ml_monadProgScript.sml *****************************************)
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
(******* End of COPY/PASTE from ml_monadProgScipt.sml *****************************************)

(* Normalize the heap predicate before using the get_heap_constant_thm theorem  *)
val SEP_EXISTS_SEPARATE_lemma = List.hd(SPEC_ALL SEP_CLAUSES |> CONJUNCTS) |> GSYM |> GEN_ALL
val SEP_EXISTS_INWARD_lemma = List.nth(SPEC_ALL SEP_CLAUSES |> CONJUNCTS, 1) |> GSYM |> GEN_ALL

val SEPARATE_SEP_EXISTS_CONV = ((SIMP_CONV pure_ss [GSYM STAR_ASSOC, SEP_EXISTS_INWARD_lemma])
				 THENC (SIMP_CONV pure_ss [STAR_ASSOC, SEP_EXISTS_SEPARATE_lemma]))

val ALLOCATE_EMPTY_RARRAY_lemma = Q.prove(
`!env s. evaluate F env s (App Opref [App AallocEmpty [Con NONE []]])
(s with refs := s.refs ++ [Varray []] ++ [Refv (Loc (LENGTH s.refs))], Rval (Loc (LENGTH s.refs + 1)))`,
rw[]
\\ ntac 10 (rw[Once evaluate_cases])
\\ rw[do_opapp_def, do_con_check_def, build_conv_def, do_app_def, store_alloc_def]
\\ rw[state_component_equality]);

fun get_refs_manip_funs (l : (string * thm * thm * thm) list) =
  List.map (fn (x, _, y, z) => (x, y, z)) l;
fun get_arrays_manip_funs (l : (string * thm * thm * thm * thm * thm * thm * thm) list) =
  List.map (fn (x1, _, x2, x3, x4, x5, x6, x7) => (x1, x2, x3, x4, x5, x6, x7)) l;

fun derive_eval_thm_ALLOCATE_EMPTY_ARRAY v_name value_def = let
    val env = get_env(get_ml_prog_state())
    val s = get_state(get_ml_prog_state())

    val array_v_name = find_const_name (v_name ^ "_v")
    val array_loc_name = find_const_name (v_name ^ "_loc")
    (* val ref_v_name = find_const_name (v_name ^ "_ref_v") *)
    val ref_name = find_const_name (v_name ^ "_ref")

    (* Provisional *)
    val array_v_def = define_abbrev false array_v_name ``[] : v list``
    val ri = get_type_inv (concl value_def |> rhs |> type_of |> dest_type |> snd |> List.hd)
    val array_v_thm = Q.prove(`LIST_REL ^ri [] []`, rw[])
    val array_v_thm = SIMP_RULE pure_ss [GSYM value_def, GSYM array_v_def] array_v_thm
    (***)

    (* Expand the definitions *)
    val th = SPECL [env, s] ALLOCATE_EMPTY_RARRAY_lemma
    val th = SIMP_RULE pure_ss [GSYM array_v_def] th
    val res_pair = rand(concl th)
    val res_pair_eq = EVAL res_pair
    val th = SIMP_RULE pure_ss [res_pair_eq] th

    (* Abbreviate the array location *)
    val array_loc = concl th |> rand |> dest_pair |> fst |> rand |> rator |> rand |> rand |> rand |>
        rator |> rand |> rand
    val array_loc_def = define_abbrev false array_loc_name array_loc
    val th = SIMP_RULE pure_ss [GSYM array_loc_def] th

    (* Abbreviate the reference location *)
    val res = concl th |> rand |> dest_pair |> snd |> rand
    val ref_var = mk_var(ref_name, ``:v``)
    val ref_def = Define `^ref_var = ^res`
    val th = SIMP_RULE pure_ss [GSYM ref_def] th
in (array_v_thm, array_loc_def, ref_def, th) end;

(* Create the store for a static initialization *)
fun create_store refs_init_list arrays_init_list =
  let
      val initial_state = get_state(get_ml_prog_state())
      val initial_store = EVAL ``^initial_state.refs`` |> concl |> rhs

      (* Allocate the references *)
      fun create_ref (name, def) =
	let
	    val value_def = translate def
	    val init_name = concl def |> dest_eq |> fst |> dest_const |> fst
	    val init_name = stringLib.fromMLstring init_name
	    val e = ``(App Opref [Var (Short ^init_name)])``
	    val _ = ml_prog_update (add_Dlet (derive_eval_thm name e) name [])
	    val ref_def = DB.fetch (current_theory()) (name ^ "_def")
	in
	    (value_def, ref_def)
	end
      val ref_name_def_pairs = List.map (fn (n, d, _, _) => (n, d)) refs_init_list
      val refs_trans_results = List.map create_ref ref_name_def_pairs

      (* Allocate the arrays *)
      fun create_array (name, def) =
	let
	    val init_name = concl def |> lhs |> dest_const |> fst

	    val (array_v_def, array_loc_def, ref_def, eval_th) =
		derive_eval_thm_ALLOCATE_EMPTY_ARRAY init_name def
	    val _ = ml_prog_update(add_Dlet eval_th name [])
         in
	     (array_v_def, array_loc_def, ref_def)
	end
      val array_name_def_pairs = List.map (fn (n, d, _, _, _, _, _, _) => (n, d)) arrays_init_list
      val arrays_trans_results = List.map create_array array_name_def_pairs
  in
    (initial_store, refs_trans_results, arrays_trans_results)
  end;

(*
val (initial_store, refs_trans_results, arrays_trans_results) =
create_store refs_init_list arrays_init_list store_hprop_name;
*)

fun find_refs_access_functions refs_init_list = let
    fun find_refs_read (name, get_fun, set_fun) = let
	val (state, pair) = concl get_fun |> dest_eq |> snd |> dest_abs
	val body = dest_pair pair |> fst |> rand
	val refs_read = mk_abs(state, body)
    in refs_read end

    fun find_refs_write (name, get_fun, set_fun) = let
	val (x, body) = concl set_fun |> dest_forall
	val (state, pair) = dest_eq body |> snd |> dest_abs
	val body = dest_pair pair |> snd
	val refs_write = mk_abs(x, mk_abs(state, body))
    in refs_write end

    fun find_read_write (name, get_fun, set_fun) = let
	val refs_read = find_refs_read(name, get_fun, set_fun)
	val refs_write = find_refs_write(name, get_fun, set_fun)
    in (name, get_fun, refs_read, set_fun, refs_write) end
in List.map find_read_write refs_init_list end;

fun find_arrays_access_functions arrays_init_list = let
    fun find_read_write (name, get, set, length, sub, update, alloc) = let
	val state = concl get |> rhs |> dest_abs |> fst
	val get_fun = concl get |> rhs |> dest_abs |> snd |> dest_pair |> fst |> rand
	val get_fun = mk_abs(state, get_fun)
			    
	val x = concl set |> dest_forall |> fst
	val set_fun = concl set |> strip_forall |> snd |> rhs
	val state = dest_abs set_fun |> fst
	val set_fun = dest_abs set_fun |> snd |> dest_pair |> snd
	val set_fun = mk_abs(x, mk_abs(state, set_fun))
    in (get_fun, set_fun) end

    fun find_add_read_write (name, get, set, length, sub, update, alloc) = let
	val (get_fun, set_fun) = find_read_write (name, get, set, length, sub, update, alloc)
    in (name, get, get_fun, set, set_fun, length, sub, update, alloc) end
in List.map find_add_read_write arrays_init_list end;

(*
val refs_init_list = find_refs_access_functions refs_init_list;
val arrays_init_list = find_arrays_access_functions arrays_init_list;
*)
fun create_store_X_hprop refs_manip_list refs_locs arrays_manip_list arrays_refs_locs state_type store_hprop_name =
  let
      val state_var = mk_var("state", state_type)
      (* Create the heap predicate for the store *)
      val create_ref_hprop_params = List.map (fn (x, _, y, _, _) => (x, y)) refs_manip_list
      val create_ref_hprop_params = zip create_ref_hprop_params refs_locs
      (* val (name, get_f) = List.hd create_ref_hprop_params *)
      fun create_ref_hprop ((name, get_f), ref_loc) =
	let
	    val ref_inv = dest_abs get_f |> snd |> type_of |> get_type_inv
	    val get_term = mk_comb (get_f, state_var) |> BETA_CONV |> concl |> dest_eq |> snd

	    val hprop = ``REF_REL ^ref_inv ^ref_loc ^get_term``
	in
	    hprop
	end
      val refs_hprops = List.map create_ref_hprop create_ref_hprop_params

      val create_array_hprop_params =
           List.map (fn (x, _, y, _, _, _, _, _, _) => (x, y)) arrays_manip_list
      val create_array_hprop_params = zip create_array_hprop_params arrays_refs_locs
      (* val ((array_v_def, array_loc_def, ref_def), get_f) = List.hd create_array_hprop_params *)
      fun create_array_hprop ((name, get_f), array_ref_loc) =
	let
	    val ref_inv = dest_abs get_f |> snd |> type_of |> dest_type |> snd |> List.hd
				   |> get_type_inv
	    val get_term = mk_comb (get_f, state_var) |> BETA_CONV |> concl |> dest_eq |> snd

	    val hprop = ``RARRAY_REL ^ref_inv ^array_ref_loc ^get_term``
	in
	    hprop
	end
      val arrays_hprops = List.map create_array_hprop create_array_hprop_params

      val store_hprop = list_mk mk_star (refs_hprops @ arrays_hprops) ``emp : hprop``
      val store_hprop = SIMP_CONV bool_ss [STAR_ASSOC] store_hprop |> concl |> dest_eq |> snd
			handle UNCHANGED => store_hprop
      val store_hprop = mk_abs(state_var, store_hprop)

      (* Create the constant for the store predicate *)
      val loc_vars = List.filter is_var (refs_locs @ arrays_refs_locs)
      val num_vars = List.length loc_vars

      val store_hprop_type = mk_type("fun", [state_type, ``:hprop``])
      fun mk_hprop_type n t = if n = 0 then t else mk_type("fun", [``:v``, mk_hprop_type (n-1) t])
      val store_hprop_type = mk_hprop_type num_vars store_hprop_type
      val store_hprop_var = mk_var(store_hprop_name, store_hprop_type)
      val store_hprop_pred = list_mk_comb (store_hprop_var, loc_vars)
      val store_hprop_def = Define `^store_hprop_pred = ^store_hprop`
  in
      store_hprop_def
  end;

(* val store_X_hprop_def = create_store_X_hprop refs_init_list arrays_init_list refs_trans_results arrays_trans_results state_type store_hprop_name; *)

(* Prove that the current store satisfies the built heap predicate *)
local
    fun instantiate_ref_values refs_trans_results arrays_trans_results (g as (asl, w)) =
      let
	  val (ref_vars, prop) = strip_exists w
	  val props = list_dest dest_conj prop 
	  val props = List.take (props, List.length props -1)
	  val ref_consts_pairs = List.map (fn x => (rand x, (rand o rator) x)) props
	  val ref_consts_map = Redblackmap.insertList
              (Redblackmap.mkDict Term.compare, ref_consts_pairs)
	  val trans_RIs = (List.map fst refs_trans_results) @
			  (List.map (fn (x, _, _) => x) arrays_trans_results)
	  val value_pairs = List.map (fn ref_v => ((rand o rator o concl) ref_v,
              (rand o concl) ref_v)) trans_RIs
	  val value_map = Redblackmap.insertList (Redblackmap.mkDict Term.compare, value_pairs)

	  val init_vars = List.map (fn x => Redblackmap.find (ref_consts_map, x)) ref_vars
	  val instants = List.map (fn x => Redblackmap.find (value_map, x)) init_vars
	  val tac = List.foldl (fn (x, tac) => tac THEN (EXISTS_TAC x)) ALL_TAC instants
      in
	  tac g
      end

    fun instantiate_ref_svalues refs_trans_results arrays_trans_results (g as (asl, w)) =
      let
	  val (ref_vars, prop) = strip_exists w
	  val hprops = rator prop |> list_dest dest_star
	  val ref_consts = mapfilter (fn x => dest_sep_exists x |> snd |> dest_star |> fst |>
              rator |> rand) hprops
	  val ref_svalue_pairs = List.map (fn (ref_v, ref_loc) =>
              ((fst o dest_eq o concl) ref_loc, (rand o rator o concl) ref_v)) refs_trans_results
	  val ref_svalue_map = Redblackmap.insertList
              (Redblackmap.mkDict Term.compare, ref_svalue_pairs)

	  val instants = List.map (fn x => Redblackmap.find (ref_svalue_map, x)) ref_consts
	  val tac = List.foldl (fn (x, tac) => tac THEN (EXISTS_TAC x)) ALL_TAC instants
      in
	  tac g
      end

    val GC_INWARDS = Q.prove(`GC * A = A * GC`, SIMP_TAC std_ss [STAR_COMM])

    val GC_DUPLICATE_0 = Q.prove(`H * GC = H * GC * GC`, rw[GSYM STAR_ASSOC, GC_STAR_GC])

    val GC_DUPLICATE_1 = Q.prove(`A * (B * GC * C) = A * GC * (B * GC * C)`,
				 SIMP_TAC std_ss [GSYM STAR_ASSOC, GC_INWARDS, GC_STAR_GC])

    val GC_DUPLICATE_2 = Q.prove(`A * (B * GC) = A * GC * (B * GC)`,
	ASSUME_TAC (Thm.INST [``C : hprop`` |-> ``emp : hprop``] GC_DUPLICATE_1)
        \\ FULL_SIMP_TAC std_ss [GSYM STAR_ASSOC, SEP_CLAUSES])

    val GC_DUPLICATE_3 = Q.prove(`A * GC * B = GC * (A * GC * B)`,
	SIMP_TAC std_ss [GSYM STAR_ASSOC, GC_INWARDS, GC_STAR_GC])

    val store2heap_aux_decompose_store1 = Q.prove(
      `H (store2heap_aux n (a ++ (b ++ c))) =
      (DISJOINT (store2heap_aux n (a ++ b)) (store2heap_aux (n + LENGTH (a ++b)) c) ==>
      H ((store2heap_aux n (a ++ b)) UNION (store2heap_aux (n + LENGTH (a ++b)) c)))`,
      EQ_TAC
      >-(
	 rw[]
	 \\ FULL_SIMP_TAC pure_ss [GSYM APPEND_ASSOC]
	 \\ FULL_SIMP_TAC pure_ss [store2heap_aux_append_many, ADD_ASSOC]
	 \\ metis_tac[UNION_COMM, UNION_ASSOC]
      )
      \\ rw[]
      \\ qspecl_then [`n`, `a ++ b`, `c`] ASSUME_TAC store2heap_aux_DISJOINT \\ fs[]
      \\ PURE_REWRITE_TAC [Once store2heap_aux_append_many]
      \\ fs[UNION_COMM])

    val store2heap_aux_decompose_store2 = Q.prove(
      `H (store2heap_aux n (a ++ b)) =
      (DISJOINT (store2heap_aux n a) (store2heap_aux (n + LENGTH a) b) ==>
      H ((store2heap_aux (n + LENGTH a) b) UNION (store2heap_aux n a)))`,
      ASSUME_TAC (Thm.INST [``b:v store`` |-> ``[] : v store``] store2heap_aux_decompose_store1
         |> GEN_ALL)
      \\ fs[UNION_COMM])

    val cons_to_append = Q.prove(`a::b::c = [a; b]++c`, fs[])

    val append_empty = Q.prove(`a = a ++ []`, fs[])

    val H_STAR_GC_SAT_IMP = Q.prove(`H s ==> (H * GC) s`,
	rw[STAR_def]
	\\ qexists_tac `s`
        \\ qexists_tac `{}`
        \\ rw[SPLIT_emp2, SAT_GC])

    val store2heap_REF_SAT = Q.prove(`((Loc l) ~~> v) (store2heap_aux l [Refv v])`,
        fs[store2heap_aux_def] >> fs[REF_def, SEP_EXISTS_THM, HCOND_EXTRACT, cell_def, one_def])

    val store2heap_eliminate_ffi_thm = Q.prove(
      `H (store2heap s.refs) ==> (GC * H) (st2heap p s)`,
      rw[] 
      \\ Cases_on `p`
      \\ fs[st2heap_def, STAR_def]
      \\ instantiate
      \\ qexists_tac `ffi2heap (q, r) s.ffi`
      \\ fs[SAT_GC]
      \\ PURE_ONCE_REWRITE_TAC[SPLIT_SYM]
      \\ fs[st2heap_SPLIT_FFI]);

    val rarray_exact_thm = Q.prove(
	`((l = l' + 1) /\ (n = l')) ==>
	 RARRAY (Loc l) av (store2heap_aux n [Varray av; Refv (Loc l')])`,
        rw[]
        \\ rw[RARRAY_def]
	\\ rw[SEP_EXISTS_THM]
	\\ qexists_tac `Loc l'`
        \\ PURE_REWRITE_TAC[Once STAR_COMM]
	\\ `[Varray av; Refv (Loc l')] = [Varray av] ++ [Refv (Loc l')]` by fs[]
        \\ POP_ASSUM(fn x => PURE_REWRITE_TAC[x])
	\\ PURE_REWRITE_TAC[store2heap_aux_decompose_store2]
	\\ DISCH_TAC
	\\ rw[STAR_def, SPLIT_def]
	\\ instantiate
	\\ rw[]
	>-(rw[Once UNION_COMM])
	>-(rw[ARRAY_def, SEP_EXISTS_THM, HCOND_EXTRACT, cell_def, one_def, store2heap_aux_def])
	\\ rw[REF_def, SEP_EXISTS_THM, HCOND_EXTRACT, cell_def, one_def, store2heap_aux_def]);
	
     val eliminate_inherited_references_thm = Q.prove(
       `!a b. H (store2heap_aux (LENGTH a) b) ==> (GC * H) (store2heap_aux 0 (a++b))`,
       rw[]
       \\ fs[STAR_def]
       \\ instantiate
       \\ qexists_tac `store2heap_aux 0 a`
       \\ fs[SPEC_ALL store2heap_aux_SPLIT |> Thm.INST [``n:num`` |-> ``0:num``]
		      |> SIMP_RULE arith_ss [], SAT_GC]);

     val eliminate_substore_thm = Q.prove(
       `(H1 * GC * H2) (store2heap_aux (n + LENGTH a) b) ==>
        (H1 * GC * H2) (store2heap_aux n (a++b))`,
       rw[]
       \\ PURE_ONCE_REWRITE_TAC[GC_DUPLICATE_3]
       \\ rw[Once STAR_def]
       \\ qexists_tac `store2heap_aux n a`
       \\ qexists_tac `store2heap_aux (n + LENGTH a) b`
       \\ simp[SAT_GC, store2heap_aux_SPLIT])

     fun eliminate_inherited_references initial_store =
       if same_const initial_store ``[] : 'a list`` then ALL_TAC
       else let
	   val initial_store = PURE_REWRITE_CONV[GSYM APPEND_ASSOC] initial_store |> concl |> rhs
			       handle UNCHANGED => initial_store
	   fun num_sublists l = let
	       val (l', b) = dest_comb l
	       val (conc, a) = dest_comb l'
	   in if same_const ``list$APPEND : 'a list -> 'a list -> 'a list`` conc then
		  1 + num_sublists b
	      else 1
	   end handle HOL_ERR _ => 1

	   val repeat_num = num_sublists initial_store
	   val tac = PURE_REWRITE_TAC[GSYM APPEND_ASSOC]
		     \\ ntac repeat_num (irule eliminate_substore_thm)		     
                     \\ PURE_REWRITE_TAC [APPEND_ASSOC]
       in tac end

     fun check_ref (g as (asl, w)) = let
	    val hprop = PURE_REWRITE_CONV [GSYM STAR_ASSOC] w
					  |> concl |> rhs |> rator |> rator |> rand
	  in if same_const ``REF`` (strip_comb hprop |> fst) then ALL_TAC g
	     else FAIL_TAC "Not a ref" g end
             handle UNCHANGED => FAIL_TAC "Not a ref" g

     fun check_rarray (g as (asl, w)) = let
	    val hprop = PURE_REWRITE_CONV [GSYM STAR_ASSOC] w
					  |> concl |> rhs |> rator |> rator |> rand
	  in if same_const ``RARRAY`` (strip_comb hprop |> fst) then ALL_TAC g
	     else FAIL_TAC "Not a resizable array" g end
          handle UNCHANGED => FAIL_TAC "Not a resizable array" g

in
    fun prove_valid_store_X_hprop save_th refs_manip_list arrays_manip_list refs_trans_results arrays_trans_results initial_store current_state state_type store_X_hprop_def =
      let
	  val store_hprop_const = concl store_X_hprop_def |> dest_eq |> fst
	  val current_store = ``^current_state.refs``
	  val store_eval_thm = EVAL current_store

	  val refs_get_funs = List.map (fn (_, _, x, _, _) => x) refs_manip_list
          val refs_init_values = List.map (fn (x, _) => concl x |> rator |> rand) refs_trans_results

	  val arrays_get_funs = List.map (fn (_, _, x, _, _, _, _, _, _) => x) arrays_manip_list
	  val arrays_init_values = List.map (fn (x, _, _) => concl x |> rator |> rand)
					    arrays_trans_results

	  val state_var = mk_var("state", state_type)
          fun mk_get_eq (f, v) = let
	      val c = mk_comb(f, state_var)
	      val c = (BETA_CONV c |> concl |> rhs handle HOL_ERR _ => c)
	      val eq = mk_eq(c, v)
	  in eq end
	  val hyps = List.map mk_get_eq ((zip refs_get_funs refs_init_values)
					 @ (zip arrays_get_funs arrays_init_values))
	  val hyps = list_mk_conj hyps handle HOL_ERR _ => ``T``

          val tys = match_type (type_of current_state) ``:unit semanticPrimitives$state``
          val current_state = Term.inst tys current_state
	  val goal = ``!(^state_var) p. ^hyps ==> REFS_PRED ^store_hprop_const state p ^current_state``
          (* set_goal ([], goal) *)

	  val solve_first_ref_subheap_tac =
	    check_ref
            \\ CONV_TAC ((RAND_CONV o RAND_CONV) (PURE_ONCE_REWRITE_CONV[append_empty]))
	    \\ PURE_REWRITE_TAC[GSYM APPEND_ASSOC]
	    \\ PURE_ONCE_REWRITE_TAC [store2heap_aux_decompose_store1]
	    \\ PURE_REWRITE_TAC[GSYM append_empty]
	    \\ DISCH_TAC \\ PURE_ONCE_REWRITE_TAC[STAR_def] \\ BETA_TAC
	    \\ PURE_REWRITE_TAC [SPLIT_def] \\ instantiate
	    \\ POP_ASSUM (fn x => ALL_TAC)
	    \\ CONJ_TAC
	    >-(
	       PURE_ONCE_REWRITE_TAC [store2heap_aux_decompose_store2]
	       \\ DISCH_TAC \\ PURE_ONCE_REWRITE_TAC[STAR_def] \\ BETA_TAC
	       \\ PURE_REWRITE_TAC [SPLIT_def]
	       \\ PURE_ONCE_REWRITE_TAC[DISJOINT_SYM] \\ instantiate
	       \\ SIMP_TAC std_ss [UNION_COMM, SAT_GC]
	       \\ PURE_REWRITE_TAC (List.map snd refs_trans_results)
               (* \\ SIMP_TAC arith_ss [] *)
	       \\ rw[store2heap_REF_SAT])

	  val solve_first_rarray_subheap_tac = 
	      check_rarray
              \\ PURE_ONCE_REWRITE_TAC[cons_to_append]
	      \\ PURE_ONCE_REWRITE_TAC [store2heap_aux_decompose_store2]
              \\ DISCH_TAC \\ PURE_ONCE_REWRITE_TAC[STAR_def] \\ BETA_TAC
              \\ PURE_REWRITE_TAC [SPLIT_def] \\ instantiate
	      \\ POP_ASSUM (fn x => ALL_TAC)
              \\ CONJ_TAC >-(SIMP_TAC std_ss [UNION_COMM])
	      \\ CONJ_TAC
              >-(
		 irule H_STAR_GC_SAT_IMP
		 \\ PURE_REWRITE_TAC (List.concat(List.map (fn (_, x, y) => [x, y])
							   arrays_trans_results))
		 \\ irule rarray_exact_thm
		 \\ SIMP_TAC list_ss [])

	  val solve_tac =
	    ntac 3 STRIP_TAC
            \\ FULL_SIMP_TAC (srw_ss()) [REFS_PRED_def, REF_REL_def, RARRAY_REL_def, store_X_hprop_def]
            \\ PURE_REWRITE_TAC[EMP_STAR_GC, SAT_GC] (* In case the store is empty *)
            \\ SIMP_TAC bool_ss [SEP_CLAUSES, SEP_EXISTS_THM]
	    \\ (CONV_TAC o STRIP_QUANT_CONV) EXTRACT_PURE_FACTS_CONV
	    \\ instantiate_ref_values refs_trans_results arrays_trans_results
	    \\ SIMP_TAC (bool_ss) ((List.map fst refs_trans_results) @
				   (List.map (fn (x, _, _) => x) arrays_trans_results))

	    \\ SIMP_TAC pure_ss [GSYM STAR_ASSOC]
	    \\ PURE_REWRITE_TAC[Once GC_DUPLICATE_0]
	    \\ ntac (List.length refs_trans_results + List.length arrays_trans_results - 1)
	       (ONCE_REWRITE_TAC [GC_DUPLICATE_1])
	    \\ PURE_REWRITE_TAC[Once GC_DUPLICATE_3]
            \\ irule store2heap_eliminate_ffi_thm
	    \\ PURE_REWRITE_TAC [store2heap_def, store_eval_thm]
            \\ eliminate_inherited_references initial_store
            \\ SIMP_TAC list_ss []
	    \\ ntac (List.length refs_trans_results) solve_first_ref_subheap_tac
	    \\ ntac (List.length arrays_trans_results) solve_first_rarray_subheap_tac
	    \\ PURE_REWRITE_TAC[SAT_GC]

	  val store_X_hprop_thm = prove(goal, solve_tac)
	  val store_X_hprop_thm = PURE_REWRITE_RULE[ConseqConvTheory.IMP_CLAUSES_TX] store_X_hprop_thm

	  val thm_name = "INIT_" ^(dest_const store_hprop_const |> fst)
	  val store_X_hprop_thm = if save_th then save_thm(thm_name, store_X_hprop_thm)
				  else store_X_hprop_thm
	  val _ = print ("Saved theorem __ \"" ^thm_name ^"\"\n")
      in
	  store_X_hprop_thm
      end
end;

(* val valid_store_X_hprop_thm = prove_valid_store_X_hprop refs_init_list arrays_init_list initial_store refs_trans_results arrays_trans_results state_type store_X_hprop_def; *)

(* Prove the validity theorem for the characteristic heap predicate *)
fun prove_exists_store_X_hprop save_th state_type store_hprop_name valid_store_X_hprop_thm =
  let
      val store_hprop_const = mk_const(store_hprop_name, mk_type("fun", [state_type, ``:hprop``]))
      val current_state = get_state(get_ml_prog_state())
      val ty_subst = Type.match_type (type_of current_state) ``:unit semanticPrimitives$state``
      val current_state = Term.inst ty_subst current_state

      val ([refs_var, ffi_var], hyps) = concl valid_store_X_hprop_thm |> strip_forall
      val hyps = dest_imp hyps |> fst handle HOL_ERR _ => ``T``
      val interm_goal = ``?(^refs_var) (^ffi_var). ^hyps``
      val interm_solve_tac =  srw_tac[QI_ss][]
      val interm_th = prove(interm_goal, interm_solve_tac)
      (* set_goal([], interm_goal) *)

      val goal = ``VALID_REFS_PRED ^store_hprop_const``

      (* set_goal([], goal) *)
      val solve_tac = 
          PURE_REWRITE_TAC[VALID_REFS_PRED_def]
          \\ STRIP_ASSUME_TAC interm_th
          \\ FIRST[CHANGED_TAC(IMP_RES_TAC valid_store_X_hprop_thm),
		   ASSUME_TAC valid_store_X_hprop_thm] (* if hyps = ``T`` *)
          \\ metis_tac[]

      val thm_name = store_hprop_name ^"_EXISTS"
      val exists_store_X_hprop_thm = if save_th then store_thm(thm_name, goal, solve_tac)
				     else prove(goal, solve_tac)
      val _ = print ("Saved theorem __ \"" ^thm_name ^"\"\n")
  in
      exists_store_X_hprop_thm
  end;

(* val exists_store_X_hprop_thm = prove_exists_store_X_hprop state_type store_hprop_name valid_store_X_hprop_thm; *)

(* Prove the specifications for the get/set functions *)

local

    fun pick_ref_order loc (t1, t2) = let
	val get_loc = (rand o rator) in
	if loc = (get_loc t1) then LESS
	else if loc = (get_loc t2) then GREATER
	else Term.compare(t1, t2) end

    fun PICK_REF_CONV loc = AC_Sort.sort{assoc = STAR_ASSOC, comm = STAR_COMM, dest = dest_star, mk = mk_star, cmp = pick_ref_order loc, combine = ALL_CONV, preprocess = ALL_CONV}

    val H_STAR_empty = Q.prove(`H * emp = H`, rw[SEP_CLAUSES])

in

fun prove_store_access_specs refs_manip_list arrays_manip_list refs_locs_defs arrays_refs_locs_defs store_X_hprop_def state_type exn_ri_def = let
    val exn_ri = CONJUNCTS exn_ri_def |> List.hd |> concl |> strip_forall |> snd
			   |> lhs |> rator |> rator
    val store_pred = concl store_X_hprop_def |> strip_forall |> snd |> dest_eq |> fst
    val exc_type = type_of exn_ri |> dest_type |> snd |> List.hd
    val exc_type_aq = ty_antiq exc_type
    val state_type_aq = ty_antiq state_type

    (* val (name, get_fun_def, read_fun, set_fun_def, write_fun) = List.hd refs_manip_list
       val loc_def = List.hd refs_locs_defs
     *)
    fun prove_ref_specs ((name, get_fun_def, read_fun, set_fun_def, write_fun),
			loc_def) = let
	val name_v = stringLib.fromMLstring name
	val loc = concl loc_def |> lhs
	val TYPE = dest_abs read_fun |> snd |> type_of |> get_type_inv
	val EXN_TYPE = exn_ri
	val get_var = read_fun
	val set_var = write_fun

	val compos_conv = (PURE_REWRITE_CONV[store_X_hprop_def])
			      THENC (ABS_CONV (PICK_REF_CONV loc))
			      THENC (PURE_REWRITE_CONV[GSYM STAR_ASSOC])
			      
	val H_eq = compos_conv store_pred
	val (state_var, H_part) = concl H_eq |> rhs |> dest_abs
	val H_part = if List.length refs_manip_list + List.length arrays_manip_list > 1 then
			 mk_abs(state_var, rand H_part)
		     else mk_abs(state_var, ``emp : hprop``)

	fun rewrite_thm th = let
	    val th = PURE_ONCE_REWRITE_RULE[GSYM loc_def] th
	    val th = PURE_REWRITE_RULE[GSYM get_fun_def, GSYM set_fun_def] th
	    val th = CONV_RULE (DEPTH_CONV BETA_CONV) th
	    val th = PURE_REWRITE_RULE[H_STAR_empty, GSYM H_eq] th
	    val th = PURE_REWRITE_RULE[GSYM loc_def, GSYM get_fun_def, GSYM set_fun_def] th
	    val th = PURE_REWRITE_RULE[GSYM H_eq] th
	    val th = PURE_REWRITE_RULE[GSYM loc_def, GSYM get_fun_def, GSYM set_fun_def] th
	in th end

	(* read *)
	val read_spec = ISPECL[name_v, loc, TYPE, EXN_TYPE, H_part, get_var] EvalM_read_heap
	val read_spec = rewrite_thm read_spec

	val thm_name = "get_" ^name ^"_thm"
	val _ = save_thm(thm_name, read_spec)
	val _ = print ("Saved theorem __ \"" ^thm_name ^"\"\n")

	(* write *)
	val write_spec = ISPECL[name_v, loc, TYPE, EXN_TYPE, H_part, get_var, set_var] EvalM_write_heap
	val write_spec = rewrite_thm write_spec
	val update_conditions = concl write_spec |> strip_forall |> snd |> strip_imp |> fst
	val update_conditions = List.take(update_conditions, 2) |> List.map (SIMP_CONV (srw_ss()) [])
	val write_spec = SIMP_RULE bool_ss update_conditions write_spec

	val thm_name = "set_" ^name ^"_thm"
	val _ = save_thm(thm_name, write_spec)
	val _ = print ("Saved theorem __ \"" ^thm_name ^"\"\n")
    in (read_spec, write_spec) end

    val refs_access_thms = List.map prove_ref_specs (zip refs_manip_list refs_locs_defs)

    (* Arrays *)
    (* val (name, get_def, get_fun, set_fun_def, set_fun, length_def, sub_def, update_def, alloc_def) = List.hd arrays_manip_list;
       val loc_def = List.hd arrays_refs_locs_defs; *)
    fun prove_array_specs ((name, get_def, get_fun, set_fun_def, set_fun, length_def, sub_def, update_def, alloc_def), loc_def) = let
	val name_v = stringLib.fromMLstring name
	val loc = concl loc_def |> lhs
	val TYPE =  get_fun |> dest_abs |> snd |> type_of |> dest_type |> snd |> List.hd |> get_type_inv
	val EXN_TYPE = exn_ri
        val get_arr = get_fun
	val set_arr = set_fun
	val sub_exn = concl sub_def |> rhs |> rand
	val update_exn = concl update_def |> rhs |> rand
	val Eval_sub_rexp = hol2deep sub_exn
	val sub_rexp = concl Eval_sub_rexp |> rator |> rand
	val Eval_update_rexp = hol2deep update_exn
	val update_rexp = concl Eval_update_rexp |> rator |> rand

	val compos_conv = (PURE_REWRITE_CONV[store_X_hprop_def])
			      THENC (ABS_CONV (PICK_REF_CONV loc))
			      THENC (PURE_REWRITE_CONV[GSYM STAR_ASSOC])
			      
	val H_eq = compos_conv store_pred
	val (state_var, H_part) = concl H_eq |> rhs |> dest_abs
	val H_part = if List.length refs_manip_list + List.length arrays_manip_list > 1 then
			 mk_abs(state_var, rand H_part)
		     else mk_abs(state_var, ``emp : hprop``)

	fun rewrite_thm th = let
	    val th = PURE_ONCE_REWRITE_RULE[GSYM loc_def] th
	    val th = PURE_REWRITE_RULE[GSYM length_def, GSYM sub_def, GSYM update_def, GSYM alloc_def] th
	    val th = CONV_RULE (DEPTH_CONV BETA_CONV) th
	    val th = PURE_REWRITE_RULE[GSYM H_eq] th
	in th end

	(* length *)
	val length_thm = ISPECL[name_v, loc, TYPE, EXN_TYPE, H_part, get_arr] EvalM_Marray_length
	val length_thm = rewrite_thm length_thm

	val thm_name = name ^"_length_thm"
	val _ = save_thm(thm_name, length_thm)
	val _ = print ("Saved theorem __ \"" ^thm_name ^"\"\n")

	(* sub *)
	val sub_thm = ISPECL[name_v, loc, TYPE, EXN_TYPE, H_part, get_arr, sub_exn, sub_rexp]
			    EvalM_Marray_sub |> SPEC_ALL
	val sub_thm = rewrite_thm sub_thm |> UNDISCH |> UNDISCH |> UNDISCH

	(* Remove the Eval assumption about the correct evaluation of the xception expression *)
	val sub_assum = concl sub_thm |> dest_imp |> fst
	val env = rator sub_assum |> rator |> rand
	val exn_name_v = rator sub_assum |> rand |> rator |> rand |> rand |> rand
	val types_pairs = CONJUNCTS exn_ri_def
	val types_pairs = List.map (fn x => concl x |> strip_forall |> snd |> rhs |> strip_exists
          |> snd |> dest_conj |> fst |> rhs |> rator |> rand |> rand |> dest_pair) types_pairs
	val deep_type = tryfind (fn (x, y) => if x = exn_name_v then y else failwith "") types_pairs

	val lookup_hyp = ``lookup_cons ^exn_name_v ^env = SOME (1, ^deep_type)``
	val goal = mk_imp(lookup_hyp, sub_assum)

	val solve_tac = rw[Eval_def, lookup_cons_def]
	   \\ PURE_ONCE_REWRITE_TAC[evaluate_cases]
	   \\ simp[exn_ri_def, do_con_check_def]
	   \\ simp[build_conv_def, namespaceTheory.id_to_n_def]
	   \\ EVAL_TAC
	   \\ rw[Once evaluate_cases]
	   \\ rw[Once evaluate_cases]
	   \\ rw[Once evaluate_cases]
	   \\ rw[Once evaluate_cases]
	   \\ simp[exn_ri_def, do_con_check_def]
	   \\ simp[build_conv_def, namespaceTheory.id_to_n_def]
	   \\ simp[state_component_equality, REV_DEF]

	val lookup_th = prove(goal, solve_tac)
	val sub_thm = MP sub_thm (UNDISCH lookup_th)

	val thm_name = name ^"_sub_thm"
	val _ = save_thm(thm_name, sub_thm)
	val _ = print ("Saved theorem __ \"" ^thm_name ^"\"\n")

	(* update *)
	val update_thm = ISPECL[name_v, loc, TYPE, EXN_TYPE, H_part, get_arr, set_arr, update_exn,
				update_rexp] EvalM_Marray_update
			       |> SPEC_ALL
	val update_thm = rewrite_thm update_thm
	val update_conditions = concl update_thm |> strip_imp |> fst
	val update_conditions = List.take(List.drop(update_conditions, 2), 2) 
	val update_conditions = List.map (SIMP_CONV (srw_ss()) []) update_conditions
	val update_thm = SIMP_RULE bool_ss update_conditions update_thm
				   |> UNDISCH |> UNDISCH |> UNDISCH

	val update_assum = concl update_thm |> dest_imp |> fst
	val env = rator update_assum |> rator |> rand
	val exn_name_v = rator update_assum |> rand |> rator |> rand |> rand |> rand
	val types_pairs = CONJUNCTS exn_ri_def
	val types_pairs = List.map (fn x => concl x |> strip_forall |> snd |> rhs |> strip_exists
          |> snd |> dest_conj |> fst |> rhs |> rator |> rand |> rand |> dest_pair) types_pairs
	val deep_type = tryfind (fn (x, y) => if x = exn_name_v then y else failwith "") types_pairs

	val lookup_hyp = ``lookup_cons ^exn_name_v ^env = SOME (1, ^deep_type)``
	val goal = mk_imp(lookup_hyp, update_assum)

	val lookup_th = prove(goal, solve_tac)
	val update_thm = MP update_thm (UNDISCH lookup_th)

	val thm_name = name ^"_update_thm"
	val _ = save_thm(thm_name, update_thm)
	val _ = print ("Saved theorem __ \"" ^thm_name ^"\"\n")

	(* alloc *)
	val alloc_thm = ISPECL[name_v, loc, TYPE, EXN_TYPE, H_part, get_arr, set_arr]
			      EvalM_Marray_alloc |> SPEC_ALL
	val alloc_thm = rewrite_thm alloc_thm
	val alloc_thm = SIMP_RULE bool_ss update_conditions alloc_thm |> DISCH_ALL |> GEN_ALL

	val thm_name = name ^"_alloc_thm"
	val _ = save_thm(thm_name, alloc_thm)
	val _ = print ("Saved theorem __ \"" ^thm_name ^"\"\n")
    in
	(length_thm, sub_thm, update_thm, alloc_thm)
    end

    val arrays_access_thms = List.map prove_array_specs (zip arrays_manip_list arrays_refs_locs_defs)
in
    (refs_access_thms, arrays_access_thms)
end

end

fun create_locs_variables refs_manip_list arrays_manip_list = let
    val refs_names = List.map (fn (n, _, _) => n) refs_manip_list
    val refs_locs_names = List.map (fn x => "init_"^x) refs_names
    val refs_locs_vars = List.map (fn x => mk_var(x, ``:v``)) refs_locs_names

    val arrays_names = List.map (fn (n, _, _, _, _, _, _) => n) arrays_manip_list
    val arrays_locs_names = List.map (fn x => "init_" ^x) arrays_names
    val arrays_locs_vars = List.map (fn x => mk_var(x, ``:v``)) arrays_locs_names
in (refs_locs_vars, arrays_locs_vars) end

type monadic_translation_parameters =
    {store_pred_def : thm,
     refs_specs : (thm * thm) list,
     arrays_specs : (thm * thm * thm * thm) list};

fun translate_dynamic_init_fixed_store refs_manip_list arrays_manip_list store_hprop_name state_type exn_ri_def = let
    (* Create the store predicate *)
    val (refs_locs, arrays_refs_locs) = create_locs_variables refs_manip_list arrays_manip_list
    val refs_manip_list = find_refs_access_functions refs_manip_list
    val arrays_manip_list = find_arrays_access_functions arrays_manip_list    
    val store_X_hprop_def = create_store_X_hprop refs_manip_list refs_locs arrays_manip_list arrays_refs_locs state_type store_hprop_name

    (* Prove the store access specifications *)
    (* Create dummy rewriting rules for the locations *)
    val refs_locs_defs = List.map REFL refs_locs
    val arrays_refs_locs_defs = List.map REFL arrays_refs_locs
    (* Prove the access specifications *)
    val (refs_access_thms, arrays_access_thms) = prove_store_access_specs refs_manip_list arrays_manip_list refs_locs_defs arrays_refs_locs_defs store_X_hprop_def state_type exn_ri_def
in
    {store_pred_def = store_X_hprop_def,
     refs_specs = refs_access_thms,
     arrays_specs = arrays_access_thms} : monadic_translation_parameters
end;

type store_translation_result =
    {refs_init_values : thm list,
     refs_locations  : thm list,
     arrays_init_values : thm list,
     arrays_locations : thm list,
     store_pred_validity : thm,
     store_pred_exists_thm : thm};

fun translate_static_init_fixed_store refs_init_list arrays_init_list store_hprop_name state_type exn_ri_def = let
    (* Create the store *)
    val (initial_store, refs_trans_results, arrays_trans_results) =
	create_store refs_init_list arrays_init_list

    (* Create the store predicate *)
    val refs_manip_list = get_refs_manip_funs refs_init_list |> find_refs_access_functions
    val arrays_manip_list = get_arrays_manip_funs arrays_init_list |> find_arrays_access_functions

    val refs_locs_defs = List.map snd refs_trans_results
    val arrays_refs_locs_defs = List.map (fn (x, y, z) => z) arrays_trans_results
    val refs_locs = List.map (lhs o concl) refs_locs_defs
    val arrays_refs_locs = List.map (lhs o concl) arrays_refs_locs_defs
    val store_X_hprop_def = create_store_X_hprop refs_manip_list refs_locs arrays_manip_list arrays_refs_locs state_type store_hprop_name

    (* Prove the access specifications *)
    val (refs_access_thms, arrays_access_thms) = prove_store_access_specs refs_manip_list arrays_manip_list refs_locs_defs arrays_refs_locs_defs store_X_hprop_def state_type exn_ri_def

    (* Prove the validity and existential theorems *)
    val current_state = get_state(get_ml_prog_state())
    val valid_store_X_hprop_thm = prove_valid_store_X_hprop true refs_manip_list arrays_manip_list refs_trans_results arrays_trans_results initial_store current_state state_type store_X_hprop_def
    val exists_store_X_hprop_thm = prove_exists_store_X_hprop true state_type store_hprop_name
				   valid_store_X_hprop_thm
    (* Return *)
    val (refs_values, refs_locs) = unzip refs_trans_results
    val (arrays_values, arrays_locs) = unzip (List.map (fn (x, _, y) => (x, y)) arrays_trans_results)
in
    ({store_pred_def = store_X_hprop_def,
     refs_specs = refs_access_thms,
     arrays_specs = arrays_access_thms} : monadic_translation_parameters,

    {refs_init_values = refs_values,
     refs_locations = refs_locs,
     arrays_init_values = arrays_values,
     arrays_locations = arrays_locs,
     store_pred_validity = valid_store_X_hprop_thm,
     store_pred_exists_thm = exists_store_X_hprop_thm} : store_translation_result)
end;

end
