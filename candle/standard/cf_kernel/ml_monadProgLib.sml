structure ml_monadProgLib (* TODO: :> ml_monadProgLib *) = struct 

open ml_monadProgTheory Redblackmap

fun ERR fname msg = mk_HOL_ERR "ml_monadProgLib" fname msg;

(* Create the store *)
fun create_store refs_init_list store_hprop_name =
  let
      val _ = if List.null refs_init_list
	      then raise (ERR "create_store" "need a non empty list of reference init values")
	      else ()

      (* Translate the definitions *)
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
      val name_def_pairs = List.map (fn (n, d, _, _) => (n, d)) refs_init_list
      val trans_results = List.map create_ref name_def_pairs
  in
      trans_results
  end;

(*
val trans_results = create_store refs_init_list store_hprop_name;
val refs_type = List.hd refs_init_list |> #3 |> dest_abs |> fst |> type_of;
*)

fun create_store_X_hprop refs_init_list trans_results refs_type store_hprop_name =
  let
      (* Create the heap predicate for the store *)
      val refs_var = mk_var("refs", refs_type)
      val create_ref_hprop_params = zip trans_results (List.map (fn (_, _, x, _) => x) refs_init_list)
      fun create_ref_hprop ((ref_v, ref_loc), get_f) =
	let
	    val (refinement_invariant, deep_const) = concl ref_v |> dest_comb
	    val refinement_invariant = rator refinement_invariant
	    val get_term = mk_comb (get_f, refs_var) |> BETA_CONV |> concl |> dest_eq |> snd
	    val deep_var = mk_var((dest_const deep_const |> fst)^"'", dest_const deep_const |> snd)
	    val ri_hprop = ``&(^refinement_invariant ^get_term ^deep_var) : hprop``
				 
	    val const_loc = concl ref_loc |> dest_eq |> fst
	    val ref_hprop = ``REF ^(concl ref_loc |> dest_eq |> fst) ^deep_var``

	    val hprop = mk_sep_exists(deep_var, mk_star(ref_hprop, ri_hprop))
	in
	    hprop
	end
      val hprops = List.map create_ref_hprop create_ref_hprop_params
      val store_hprop = list_mk mk_star hprops ``emp``
          |> SIMP_CONV bool_ss [STAR_ASSOC] |> concl |> dest_eq |> snd
      val store_hprop = mk_abs(refs_var, store_hprop)
      val store_hprop_var = mk_var(store_hprop_name, mk_type("fun", [refs_type, ``:hprop``]))
      val store_hprop_def = Define `^store_hprop_var = ^store_hprop`
  in
      store_hprop_def
  end;

(* val store_X_hprop_def = create_store_X_hprop trans_results refs_type store_hprop_name; *)

(* Prove that the current store satisfies the built heap predicate *)
local
    fun instantiate_ref_svalues trans_results (g as (asl, w)) =
      let
	  val (ref_vars, prop) = strip_exists w
	  val hprops = rator prop |> list_dest dest_star
	  val ref_consts = mapfilter (fn x => dest_sep_exists x |> snd |> dest_star |> fst |>
              rator |> rand) hprops
	  val ref_svalue_pairs = List.map (fn (ref_v, ref_loc) =>
              ((fst o dest_eq o concl) ref_loc, (rand o rator o concl) ref_v)) trans_results
	  val ref_svalue_map = Redblackmap.insertList
              (Redblackmap.mkDict Term.compare, ref_svalue_pairs)

	  val instants = List.map (fn x => Redblackmap.find (ref_svalue_map, x)) ref_consts
	  val tac = List.foldl (fn (x, tac) => tac THEN (EXISTS_TAC x)) ALL_TAC instants
      in
	  tac g
      end

    fun instantiate_ref_values trans_results (g as (asl, w)) =
      let
	  val (ref_vars, prop) = strip_exists w
	  val props = list_dest dest_conj prop 
	  val props = List.take (props, List.length props -1)
	  val ref_consts_pairs = List.map (fn x => (rand x, (rand o rator) x)) props
	  val ref_consts_map = Redblackmap.insertList
              (Redblackmap.mkDict Term.compare, ref_consts_pairs)
	  val value_pairs = List.map (fn (ref_v, _) => ((rand o rator o concl) ref_v,
              (rand o concl) ref_v)) trans_results
	  val value_map = Redblackmap.insertList (Redblackmap.mkDict Term.compare, value_pairs)

	  val init_vars = List.map (fn x => Redblackmap.find (ref_consts_map, x)) ref_vars
	  val instants = List.map (fn x => Redblackmap.find (value_map, x)) init_vars
	  val tac = List.foldl (fn (x, tac) => tac THEN (EXISTS_TAC x)) ALL_TAC instants
      in
	  tac g
      end

    val GC_INWARDS = Q.prove(`GC * A = A * GC`, SIMP_TAC std_ss [STAR_COMM])

    val GC_DUPLICATE_1 = Q.prove(`A * (B * GC * C) = A * GC * (B * GC * C)`,
				 SIMP_TAC std_ss [GSYM STAR_ASSOC, GC_INWARDS, GC_STAR_GC])

    val GC_DUPLICATE_2 = Q.prove(`A * (B * GC) = A * GC * (B * GC)`,
	ASSUME_TAC (Thm.INST [``C : hprop`` |-> ``emp : hprop``] GC_DUPLICATE_1)
        \\ FULL_SIMP_TAC std_ss [GSYM STAR_ASSOC, SEP_CLAUSES])

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

    val SAT_GC = Q.prove(`!h. GC h`, rw[GC_def, SEP_EXISTS] \\ qexists_tac `\x. T` \\ rw[])

    val store2heap_REF_SAT = Q.prove(`((Loc l) ~~> v) (store2heap_aux l [Refv v])`,
        fs[store2heap_aux_def] >> fs[REF_def, SEP_EXISTS_THM, HCOND_EXTRACT, cell_def, one_def])
in
    fun prove_valid_store_X_hprop trans_results refs_type store_X_hprop_def =
      let
	  val store_hprop_const = concl store_X_hprop_def |> dest_eq |> fst
	  val current_state = get_state(get_ml_prog_state())
	  val current_store = ``^current_state.refs``
	  val store_eval_thm = EVAL current_store

	  val goal = ``?refs. REFS_PRED ^store_hprop_const refs ^current_state``

	  val solve_first_subheap_tac =
	    PURE_REWRITE_TAC[GSYM APPEND_ASSOC]
	    \\ PURE_ONCE_REWRITE_TAC [store2heap_aux_decompose_store1]
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
	       \\ PURE_REWRITE_TAC (List.map snd trans_results)
	       \\ rw[store2heap_REF_SAT]
	    )

	  fun rec_solve_subheaps_tac g =
	    FIRST[solve_first_subheap_tac >> rec_solve_subheaps_tac, ALL_TAC] g

	  val solve_tac =
	    FULL_SIMP_TAC (srw_ss()) [REFS_PRED_def, store_X_hprop_def, store_eval_thm]
	    \\ srw_tac[QI_ss][]
	    \\ instantiate_ref_svalues trans_results
	    \\ SIMP_TAC bool_ss [SEP_CLAUSES, SEP_EXISTS_THM]
	    \\ (CONV_TAC o STRIP_QUANT_CONV) EXTRACT_PURE_FACTS_CONV
	    \\ instantiate_ref_values trans_results
	    \\ SIMP_TAC (bool_ss) (List.map fst trans_results)
	    \\ SIMP_TAC pure_ss [GSYM STAR_ASSOC]
	    \\ PURE_REWRITE_TAC [Once GC_DUPLICATE_2]
	    \\ ntac (List.length trans_results - 2) (ONCE_REWRITE_TAC [GC_DUPLICATE_1])
	    \\ PURE_REWRITE_TAC [store2heap_def]
	    \\ rec_solve_subheaps_tac
	    \\ PURE_REWRITE_TAC [Once store2heap_aux_decompose_store2]
	    \\ DISCH_TAC \\ PURE_REWRITE_TAC[Once STAR_def] \\ BETA_TAC
	    \\ PURE_REWRITE_TAC [SPLIT_def]
	    \\ PURE_REWRITE_TAC[Once DISJOINT_SYM] \\ instantiate
	    \\ SIMP_TAC std_ss [UNION_COMM, SAT_GC]
	    \\ PURE_REWRITE_TAC (List.map snd trans_results)
	    \\ rw[store2heap_REF_SAT]

	  val store_X_hprop_thm = prove(goal, solve_tac)
      in
	  store_X_hprop_thm
      end
end;

(* val valid_store_X_hprop_thm = prove_valid_store_X_hprop trans_results refs_type store_X_hprop_def; *)

(* Prove the validity theorem for the characteristic heap predicate *)
fun prove_exists_store_X_hprop refs_type store_hprop_name valid_store_X_hprop_thm =
  let
      val store_hprop_const = mk_const(store_hprop_name, mk_type("fun", [refs_type, ``:hprop``]))
      val current_state = get_state(get_ml_prog_state())
      val ty_subst = Type.match_type (type_of current_state) ``:unit state``
      val current_state = Term.inst ty_subst current_state
      val goal = ``VALID_REFS_PRED ^store_hprop_const``

      val solve_tac = 
          PURE_REWRITE_TAC[VALID_REFS_PRED_def]
          \\ EXISTS_TAC current_state
          \\ SIMP_TAC std_ss [valid_store_X_hprop_thm]

      val exists_store_X_hprop_thm = prove(goal, solve_tac)
  in
      exists_store_X_hprop_thm
  end;

(* val exists_store_X_hprop_thm = prove_exists_store_X_hprop refs_type store_hprop_name valid_store_X_hprop_thm; *)

(* Prove the specifications for the get/set functions *)

local
    (* Normalize the heap predicate before using the get_heap_constant_thm theorem  *)
    val SEP_EXISTS_SEPARATE_lemma = List.hd(SPEC_ALL SEP_CLAUSES |> CONJUNCTS) |> GSYM |> GEN_ALL
    val SEP_EXISTS_INWARD_lemma = List.nth(SPEC_ALL SEP_CLAUSES |> CONJUNCTS, 1) |> GSYM |> GEN_ALL

    val SEPARATE_SEP_EXISTS_CONV = ((SIMP_CONV pure_ss [GSYM STAR_ASSOC, SEP_EXISTS_INWARD_lemma])
				    THENC (SIMP_CONV pure_ss [STAR_ASSOC, SEP_EXISTS_SEPARATE_lemma]))

    fun pick_sep_exists_order varname (t1, t2) = let
	val get_var_name = fst o dest_const o rand o rator o fst o dest_star
            o snd o dest_sep_exists in
	if is_sep_exists t1 andalso get_var_name t1 = varname then LESS
	else if is_sep_exists t2 andalso get_var_name t2 = varname then GREATER
	else Term.compare(t1, t2) end

    fun PICK_SEP_EXISTS_CONV varname = sort{assoc = STAR_ASSOC, comm = STAR_COMM, dest = dest_star, mk = mk_star, cmp = pick_sep_exists_order varname, combine = ALL_CONV, preprocess = ALL_CONV}

    fun PICK_SEP_EXISTS_TAC varname =
      CONV_TAC(ONCE_DEPTH_CONV(ABS_CONV (SEPARATE_SEP_EXISTS_CONV THENC (PICK_SEP_EXISTS_CONV varname))))

    fun ABSTRACT_HEAP_READ_ACCESS_CONV get_function tm = let
	val ref_var = strip_imp tm |> snd |> rand |> dest_abs |> fst
	val rw_th = (GSYM (EVAL (mk_comb(get_function, ref_var))))
    in PURE_ONCE_REWRITE_CONV [rw_th] tm end
    
    fun ABSTRACT_HEAP_WRITE_ACCESS (g as (asl, w)) = let
	val x = (rand o rand o rand o rator o rand) w
	val (refs, pair_tm) = (dest_abs o rand o rand o rator o rand o rand) w
	val (tml, tmr) = dest_pair pair_tm
	val tmr' = mk_abs(x, mk_abs(refs, tmr))
	val tmr' = mk_comb(mk_comb(tmr', x), refs)
	val rw_thm = ((RATOR_CONV BETA_CONV) THENC BETA_CONV) tmr' |> GSYM
    in CONV_TAC(ONCE_REWRITE_CONV [rw_thm]) g end

    fun ABSTRACT_HEAP_PRED_TAC (g as (asl, w)) = let
	val tm = strip_imp w |> snd |> rand
	val (abs, H) = dest_abs tm
	val (H1, H2) = dest_star H
	val rw_rule = mk_comb (mk_abs(abs, H2), abs) |> BETA_CONV |> GSYM
    in PURE_ONCE_REWRITE_TAC [rw_rule] g end

    fun prove_heap_access_thms get_fun set_fun (g as (asl, w)) =
      let
	  (* Read access *)	    
	  val read_theorem = EVAL ``(!refs x. ^get_fun (^set_fun x refs) = x)``
              |> EQ_IMP_RULE |> snd |> PURE_REWRITE_RULE[IMP_CLAUSES, FORALL_SIMP]

	  (* Write access *)
	  val H = strip_imp w |> snd |> rand |> dest_abs |> snd |>
			    dest_star |> snd |> rator
	  val x = mk_var("x", type_of set_fun |> dest_type |> snd |> List.hd)
	  val refs = mk_var("refs", type_of set_fun |> dest_type |> snd |> List.last |> dest_type |> snd |> List.hd)
	  val eq1 = EVAL ``^H (^set_fun ^x ^refs)``
	  val eq2 = GSYM(EVAL (mk_comb(H, refs)))
	  val write_theorem = TRANS eq1 eq2 |> GENL[refs, x]
      in
	  ((ASSUME_TAC read_theorem) THEN (ASSUME_TAC write_theorem)) g
      end
in

fun prove_store_access_specs refs_init_list trans_results store_X_hprop_def refs_type exc_ri = let
    val store_pred = concl store_X_hprop_def |> dest_eq |> fst
    (* val exc_ri = concl exc_ri_def |> strip_forall |> snd |> list_dest dest_conj |> List.hd
		 |> strip_forall |> snd |> dest_eq |> fst |> rator |> rator *)
    val exc_type = type_of exc_ri |> dest_type |> snd |> List.hd
    val exc_type_aq = ty_antiq exc_type
    val refs_type_aq = ty_antiq refs_type

    fun define_monad_get_fun (name, get_fun) = let
	val return_type_aq = type_of get_fun |> dest_type |> snd |> List.tl |> List.hd |> ty_antiq
	val monad_get_fun = ``(\state. (Success (^get_fun state), state)) :
                              (^refs_type_aq, ^return_type_aq, ^exc_type_aq) M``
	val monad_get_fun = (DEPTH_CONV BETA_CONV) monad_get_fun |> concl |> dest_eq |> snd
			    handle UNCHANGED => monad_get_fun
	val monad_get_fun_name = "get_" ^ name
	val monad_get_fun_var = mk_var(monad_get_fun_name, type_of monad_get_fun)
	val monad_get_fun_def = Define `^monad_get_fun_var = ^monad_get_fun`
    in monad_get_fun_def end

    fun prove_get_spec ((name, init_def, get_fun, set_fun), (value_def, loc_def)) = let
	val name_tm = stringLib.fromMLstring name
	val loc_const = concl loc_def |> dest_eq |> fst
	val ri_pred = concl value_def |> rator |> rator

	val monad_get_fun_def = define_monad_get_fun (name, get_fun)
	val monad_get_fun = concl monad_get_fun_def |> dest_eq |> fst
	val goal = 
          ``nsLookup env.v (Short ^name_tm) = SOME ^loc_const ==>
            EvalM env (App Opderef [Var (Short ^name_tm)])
            (HOL_MONAD ^ri_pred ^exc_ri ^monad_get_fun) ^store_pred``

       val read_tac =
	 PURE_REWRITE_TAC[store_X_hprop_def]
	 \\ PURE_REWRITE_TAC[GSYM STAR_ASSOC]
	 \\ PICK_SEP_EXISTS_TAC (dest_const loc_const |> fst)
	 \\ PURE_REWRITE_TAC[loc_def, monad_get_fun_def]
	 \\ CONV_TAC (ABSTRACT_HEAP_READ_ACCESS_CONV get_fun)
	 \\ ABSTRACT_HEAP_PRED_TAC
	 \\ PURE_REWRITE_TAC[get_heap_constant_thm]

	val thm_name = "get_" ^name ^"_thm"
	val get_spec = store_thm(thm_name, goal, read_tac)
    in get_spec end

    val get_specsl = List.map prove_get_spec (zip refs_init_list trans_results)

    fun define_monad_set_fun (name, set_fun) = let
	val param_type_aq = dest_abs set_fun |> fst |> type_of |> ty_antiq
	val monad_set_fun = ``(\x state. (Success (), ^set_fun x state)) :
                              ^param_type_aq ->  (^refs_type_aq, unit, ^exc_type_aq) M``
	val monad_set_fun = (DEPTH_CONV BETA_CONV) monad_set_fun |> concl |> dest_eq |> snd
			    handle UNCHANGED => monad_set_fun
	val monad_set_fun_name = "set_" ^ name
	val monad_set_fun_var = mk_var(monad_set_fun_name, type_of monad_set_fun)
	val monad_set_fun_def = Define `^monad_set_fun_var = ^monad_set_fun`
    in monad_set_fun_def end

    (* val (name, init_def, get_fun, set_fun) = List.hd refs_init_list
       val (value_def, loc_def) = List.hd trans_results
     *)
    fun prove_set_spec  ((name, init_def, get_fun, set_fun), (value_def, loc_def)) = let
	val name_tm = stringLib.fromMLstring name
	val loc_const = concl loc_def |> dest_eq |> fst
	val ri_pred = concl value_def |> rator |> rator

	val monad_set_fun_def = define_monad_set_fun (name, set_fun)
	val monad_set_fun = concl monad_set_fun_def |> dest_eq |> fst
	val goal = 
          ``nsLookup env.v (Short ^name_tm) = SOME ^loc_const ==>
            Eval env exp (^ri_pred x) ==>
            EvalM env (App Opassign [Var (Short ^name_tm); exp])
            (HOL_MONAD UNIT_TYPE ^exc_ri (^monad_set_fun x)) ^store_pred``

       val write_tac =
	 PURE_REWRITE_TAC[store_X_hprop_def]
	 \\ PURE_REWRITE_TAC[GSYM STAR_ASSOC]
	 \\ PICK_SEP_EXISTS_TAC (dest_const loc_const |> fst)
	 \\ PURE_REWRITE_TAC[loc_def, monad_set_fun_def]
	 \\ CONV_TAC ((RAND_CONV o RAND_CONV o RATOR_CONV o RAND_CONV o RAND_CONV) BETA_CONV)
	 \\ CONV_TAC ((RAND_CONV o RAND_CONV) (ABSTRACT_HEAP_READ_ACCESS_CONV get_fun))
	 \\ ABSTRACT_HEAP_WRITE_ACCESS
	 \\ ABSTRACT_HEAP_PRED_TAC
	 \\ prove_heap_access_thms get_fun set_fun
	 \\ rpt DISCH_TAC
	 \\ IMP_RES_TAC(Thm.INST_TYPE [``:'b`` |-> exc_type] set_heap_constant_thm)
	 \\ POP_ASSUM(fn x => PURE_REWRITE_TAC[x])
	 
       (* set_goal([], goal) *)
	 
       val thm_name = "set_" ^name ^"_thm"
       val set_spec = store_thm(thm_name, goal, write_tac)
    in set_spec end

    val set_specsl = List.map prove_set_spec (zip refs_init_list trans_results)
in
    (get_specsl, set_specsl)
end

end

type store_translation_thms =
    {init_values_thms : thm list,
     locations_thms  : thm list,
     store_pred_def : thm,
     store_pred_validity : thm,
     store_pred_exist_thm : thm,
     get_specs : thm list,
     set_specs : thm list};

fun mk_store_translation_thms values locs pred pred_valid pred_exists gets sets =
   ({init_values_thms = values,
     locations_thms  = locs,
     store_pred_def = pred,
     store_pred_validity = pred_valid,
     store_pred_exist_thm = pred_exists,
     get_specs = gets,
     set_specs = sets} : store_translation_thms);

fun translate_store refs_init_list store_hprop_name exc_ri = let
    val trans_results = create_store refs_init_list store_hprop_name

    val refs_type = List.hd refs_init_list |> #3 |> dest_abs |> fst |> type_of

    val store_X_hprop_def = create_store_X_hprop refs_init_list trans_results refs_type store_hprop_name
    val valid_store_X_hprop_thm = prove_valid_store_X_hprop trans_results refs_type store_X_hprop_def
    val exists_store_X_hprop_thm = prove_exists_store_X_hprop refs_type store_hprop_name
                                   valid_store_X_hprop_thm
    val (get_specs, set_specs) = prove_store_access_specs refs_init_list trans_results
                           store_X_hprop_def refs_type exc_ri

    val (values, locs) = unzip trans_results
in mk_store_translation_thms values locs store_X_hprop_def valid_store_X_hprop_thm exists_store_X_hprop_thm get_specs set_specs end;

end
