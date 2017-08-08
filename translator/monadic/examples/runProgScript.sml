open ml_monadBaseLib ml_monadBaseTheory
open ml_monad_translatorTheory ml_monadStoreLib ml_monad_translatorLib

val _ = new_theory "arrayStateProg"
val _ = ParseExtras.temp_loose_equality();
val _ = patternMatchesLib.ENABLE_PMATCH_CASES();
val _ = monadsyntax.temp_add_monadsyntax()

val _ = temp_overload_on ("monad_bind", ``st_ex_bind``);
val _ = temp_overload_on ("monad_unitbind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("monad_ignore_bind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("return", ``st_ex_return``);

val _ = hide "state";

val _ = (use_full_type_names := false);

(* Register the types used for the translation *)
val _ = register_type ``:'a # 'b``;
val _ = register_type ``:'a list``;
val _ = register_type ``:'a option``;
val _ = register_type ``:('a, 'b) exc``;
val _ = register_type ``:unit``;

(* Create the data type to handle the references *)
val _ = Hol_datatype `
  state_refs = <| the_num : num ;
	          the_num_array : num list ;
                  the_int_array : int list |>`;

(* Data type for the exceptions *)
val _ = Hol_datatype`
  state_exn = Fail of string | ReadError of unit | WriteError of unit`;

val _ = register_exn_type ``:state_exn``;
val STATE_EXN_TYPE_def = theorem"STATE_EXN_TYPE_def";

val _ = register_type ``:state_refs``;
val STATE_REFS_TYPE_def = theorem"STATE_REFS_TYPE_def";

(* Monadic functions to handle the exceptions *)
val exceptions_funs = define_monad_exception_functions ``:state_exn`` ``:state_refs``;
val _ = temp_overload_on ("failwith", ``raise_Fail``);

(* Define the functions used to access the elements of the state_refs data_type *)
val access_funs = define_monad_access_funs (``:state_refs``);
val [(the_num_name, get_the_num_def, set_the_num_def),
     (the_num_array_name, get_the_num_array_def, set_the_num_array_def),
     (the_int_array_name, get_the_int_array_def, set_the_int_array_def)] = access_funs;

val sub_exn = ``ReadError ()``;
val update_exn = ``WriteError ()``;
val array_access_funs = (List.tl access_funs);
val array_manip_funs = define_Marray_manip_funs array_access_funs sub_exn update_exn;

(* Prepare the translation *)
val init_num_def = Define `init_num = (0 : num)`;
val init_num_array_def = Define `init_num_array = [] : num list`;
val init_int_array_def = Define `init_int_array = [] : int list`;
val refs_init_list = [(the_num_name, init_num_def, get_the_num_def, set_the_num_def),
		     (the_num_array_name, init_num_array_def, get_the_num_array_def, set_the_num_array_def),
		     (the_int_array_name, init_int_array_def, get_the_int_array_def, set_the_int_array_def)];
(* val refs_init_list = [(the_num_name, init_num_def, get_the_num_def, set_the_num_def)]; *)

(* val init_num_array_def = Define `init_num_array = [] : num list`;
val init_int_array_def = Define `init_int_array = [] : int list`;
val arrays_init_values = [init_num_array_def, init_int_array_def];
val arrays_init_list = List.map (fn ((x1, x2, x3, x4, x5, x6, x7), x) => (x1, x, x2, x3, x4, x5, x6, x7)) (zip array_manip_funs arrays_init_values); *)

val infer_init_state = ``<|the_num := 0; the_num_array := []; the_int_array := []|>``;

val store_hprop_name = "STATE_STORE";
val state_type = ``:state_refs``;
val EXN_RI = ``STATE_EXN_TYPE``;
val exn_ri_def = STATE_EXN_TYPE_def;

val refs_manip_list = List.map (fn (x, _, y, z) => (x, y, z)) refs_init_list;
(* val arrays_manip_list = List.map (fn (x1, _, x2, x3, x4, x5, x6, x7) => (x1, x2, x3, x4, x5, x6, x7)) arrays_init_list; *)
val arrays_manip_list = [] : (string * thm * thm * thm * thm * thm * thm) list;

val translation_parameters = translate_dynamic_init_fixed_store refs_manip_list arrays_manip_list store_hprop_name state_type exn_ri_def;

(* Initialize the store *)
(* val (translation_parameters, store_trans_result) = translate_static_init_fixed_store refs_init_list arrays_init_list store_hprop_name state_type STATE_EXN_TYPE_def; *)

(* Initialize the translation *)
(* val store_pred_exists = SOME(#store_pred_exists_thm store_trans_result); *)
val store_pred_exists = NONE : thm option;
val _ = init_translation translation_parameters store_pred_exists exn_ri_def [];

(* Prove the theorems necessary to handle the exceptions *)
val (raise_functions, handle_functions) = unzip exceptions_funs;
val exn_thms = add_raise_handle_functions raise_functions handle_functions STATE_EXN_TYPE_def

(* Monadic translations *)
(* val test2_def = Define `test2 n = the_num_array_sub n`;
val def = test2_def |> m_translate;

val test3_def = Define `test3 n x = update_the_num_array n x`;
val def = test2_def |> m_translate;

val test4_def = Define `test4 n x = alloc_the_num_array n x`;
val def = test3_def |> m_translate;

val test5_def = Define `
test5 n z =
    do
	alloc_the_num_array n z;
        return ()
    od`;
val def = test5_def |> m_translate;
val test5_trans_th = m_translate test5_def;

val test6_def = Define `
test6 n z = test5 n z`;
val def = test6_def;
val test6_trans_th = m_translate test6_def;

val test7_def = Define `
(test7 [] = return 0) /\ ((test7 (x::l)) = (do x <- test7 l; return (x+1) od))`;
val def = test7_def;
val test7_v_th = m_translate test7_def;

val test8_def = Define `
test8 l = test7 l`;
val test8_v_th = m_translate test8_def; *)

val test1_def = Define `test1 x = do y <- get_the_num; return (x + y) od`;
val test1_v_th = m_translate test1_def;

val test2_def = Define `test2 (x : num) y = return (x + y)`;
val test2_v_th = m_translate test2_def;

val test3_def = Define `
test3 n m z =
   do
       test2 n z;
       x <- test1 m;
       return x
   od`;
val test3_v_th = m_translate test3_def;

(* New definitions for ml_monadBaseTheory *)
val _ = ParseExtras.temp_tight_equality();

fun evaluate_unique_result_tac (g as (asl, w)) = let
    val asl = List.map ASSUME asl
    val uniques = mapfilter (MATCH_MP evaluate_unique_result) asl
in simp uniques g end;

(* Test *)
val current_state = get_state(get_ml_prog_state());
val current_env = get_env(get_ml_prog_state());

val spec = test3_v_th
val original_spec = spec;

val run_test_def = Define `run_test n m z refs = run (test3 n m z) refs`;
val def = run_test_def;


val Long_tm = ``namespace$Long : tvarN -> (tvarN, tvarN) id -> (tvarN, tvarN) id ``;
fun get_exn_constructs () = let
    val exn_type_def = !EXN_TYPE_def_ref
    val exn_type_conjs = CONJUNCTS exn_type_def
    val deep_cons_list = List.map (fn x => concl x |> strip_forall |> snd |> rhs |> strip_exists
				|> snd |> dest_conj |> fst |> rhs |> rator) exn_type_conjs
    val deep_names = List.map (fn x => rand x |> rand |> dest_pair |> fst) deep_cons_list

    (* Get the module name *)
    val deep_type = List.hd deep_cons_list |> rand |> rand |> dest_pair |> snd |> rand
    val uses_module_name = strip_comb deep_type |> fst |> same_const Long_tm
    val module_name = if uses_module_name then SOME(strip_comb deep_type |> snd |> List.hd)
		      else NONE
in (deep_names, module_name) end;

fun create_local_defs th = let
    (* Retrieve the lookup assumptions for the functions definitions *)
    val LOCAL_ENV = mk_var("LOCAL_ENV", ``:v sem_env``)
    val NAME = mk_var("NAME", ``:tvarN``)
    val EXPR = mk_var("EXPR", ``:v``)
    val pat = ``nsLookup ^LOCAL_ENV.v (Short ^NAME) = SOME ^EXPR``
    val substs =  mapfilter (match_term pat) (hyp th)
    val lookup_info = List.map (fn (tms, _) => (Term.subst tms NAME, Term.subst tms EXPR)) substs
    val lookup_info = List.filter(fn (x, y) => not(is_var y)) lookup_info

    fun get_env_var expr = rator expr |> rator |> rand |> rator |> rand
    fun compute_env_index env = let
	val env_name = dest_var env |> fst
	val env_index_str = String.extract(env_name, String.size local_environment_var_name, NONE)
	val index = string_to_int env_index_str
    in index end

    (* Sort the lookup assumptions *)
    val lookup_info = List.map (fn (name, expr) => let val env = get_env_var expr in
				(compute_env_index env, env, name, expr) end) lookup_info
    fun assum_order (i1 : int, _, _, _) (i2 : int, _, _, _) = i1 > i2
    val lookup_info = Lib.sort assum_order lookup_info
    val lookup_info = List.map (fn (_, x, y, z) => (x, y, z)) lookup_info

    (* Create the function definitions (Let expressions) *)
    val current_env = concl th |> rator |> rator |> rator |> rator |> rand |> rator |> rand
    val all_envs = List.map (fn (x, _, _) => x) lookup_info
    val last_env = List.last all_envs
    val all_envs = current_env::(List.take(all_envs, List.length all_envs - 1))
    val lookup_info = zip all_envs lookup_info

    fun create_fun_let ((env_var2, (env_var1, name, fexp)), th) = let
	(* Build the new environment *)
	val env0 = rator fexp |> rator |> rand |> rand
	val env1 = env_var1
	val vname = name
	val xv = rator fexp |> rand
	val fexp = rand fexp

	val nenv = ``(write ^vname (Closure (merge_env ^env1 ^env0) ^xv ^fexp) ^env1)``

	(* Replace the environment and create the Let expression *)
	val th' = Thm.INST [env_var2 |-> nenv] th
	val th' = MATCH_MP EvalSt_Let_Fun th'

	(* Remove the appropriate nsLookup assumption *)
	val assum = ``nsLookup (merge_env ^nenv ^env0).v (Short ^vname) =
		     SOME (Closure (merge_env (^env_var1) ^env0) ^xv ^fexp)``
	val assum_rw = EVAL assum
	val th' = DISCH assum th' |> SIMP_RULE bool_ss [assum_rw]
    in th' end

    val th = List.foldl create_fun_let th lookup_info

    (* Instantiate the last environment variable *)
    val empty_env = ``<| v := Bind [] []; c := Bind [] [] |> : v sem_env``
    val th = Thm.INST [last_env |-> empty_env] th |> PURE_REWRITE_RULE [merge_env_bind_empty]
in th end;

fun gen_name_tac name (g as (asl, w)) = let
    val renamed_w_th = RENAME_VARS_CONV [name] w
in (PURE_ONCE_REWRITE_TAC[renamed_w_th] \\ strip_tac) g end

val H_STAR_emp = Q.prove(`H * emp = H`, simp[SEP_CLAUSES]);
val emp_tm = ``set_sep$emp``;
fun create_local_references th = let
    val th = PURE_REWRITE_RULE[!H_def] th
			      |> PURE_ONCE_REWRITE_RULE[GSYM H_STAR_emp]
			      |> PURE_REWRITE_RULE[GSYM STAR_ASSOC]
    (* Rename the state variable in the heap invariant *)
    val state_var = concl th |> rator |> rand
    val H_eq = ALPHA_CONV state_var (concl th |> rand)
    val th = PURE_ONCE_REWRITE_RULE[H_eq] th

    val P = concl th |> rator |> rator |> rand
    val STATE_RI = get_type_inv (type_of state_var)

    fun create_local_ref th = let
	(* Instantiate the EvalSt theorem *)
	val exp = concl th |> rator |> rator |> rator |> rand
	val originalH = concl th |> rand
	val H_part = dest_abs originalH |> snd
	val (H_part1, H_part2) = dest_star H_part
	val H_part2 = mk_abs(state_var, H_part2)

	val state_field = rand H_part1
	val get_ref_fun = mk_abs(state_var, state_field)
	val Eval_state_field = hol2deep state_field
	val field_expr = concl Eval_state_field |> rator |> rand
	val TYPE = concl Eval_state_field |> rand |> rator

	val refs_env = concl th |> rator |> rator |> rator |> rator |> rand
	val loc_name = rator refs_env |> rator |> rand
	val loc = rator refs_env |> rand
	val env = rand refs_env

	val gen_th = GEN loc th
	val EvalSt_th = ISPECL[exp, field_expr, get_ref_fun, TYPE, loc_name, env, H_part2, P, state_var] EvalSt_Opref |> BETA_RULE

	(* Retrieve the first assumption *)
	val assum1 = concl EvalSt_th |> dest_imp |> fst
	val assum1_env = assum1 |> rator |> rator |> rand

	(* Prove the assumption about the state field expression *)
	val Eval_state_field_env = concl Eval_state_field |> rator |> rator |> rand
	val Eval_state_field = DISCH_ALL Eval_state_field
					 |> Thm.INST[Eval_state_field_env |-> assum1_env]
	val assum2 = concl Eval_state_field |> dest_imp |> fst
	val lv_env = assum2 |> rator |> rator |> rand
	val lv_vname = assum2 |> rator |> rand |> rand |> rand
	val lv_x = assum2 |> rand |> rand
	val lookup_th = EVAL ``nsLookup ^lv_env.v (Short ^lv_vname)``
	val lv_xv = concl lookup_th |> rhs |> rand
	val Eval_lookup_th = ISPECL [lv_env, lv_vname, lv_xv, lv_x, STATE_RI] Eval_lookup_var
	val Eval_lookup_th = MP Eval_lookup_th lookup_th |> EQ_IMP_RULE |> snd |> UNDISCH
	val Eval_state_field = MP Eval_state_field Eval_lookup_th
	val assum3_th = concl Eval_state_field |> dest_imp |> fst |> EVAL |> EQT_ELIM
	val Eval_state_field = MP Eval_state_field assum3_th

	(* Simplify the first assumption *)
	val EvalSt_th = MP EvalSt_th Eval_state_field

	(* Simplify the second assumption *)
	val EvalSt_th = MP EvalSt_th gen_th
    in EvalSt_th end

    fun create_local_refs_rec th = let
	val originalH = concl th |> rand |> dest_abs |> snd
    in if same_const originalH emp_tm then th
       else create_local_refs_rec (create_local_ref th) end

    val th = create_local_refs_rec th |> PURE_REWRITE_RULE[merge_env_bind_empty]

    (* Transform the EvalSt predicate to an Eval predicate *)
    val th = MATCH_MP EvalSt_to_Eval th
in th end;

fun apply_Eval_Fun (x, th) = let
    val tms = FVL [x] empty_varset
    val [assum] = List.filter (can (fn y => Term.raw_match [] tms ``A ^x xv`` y ([], []))) (hyp th)
    val th = DISCH assum th
    val v = rand assum
    val th = GENL[v, x] th
    val th = MATCH_MP Eval_Fun th
in th end

fun translate_run def = let
    (* Decompose the definition *)
    val (def_lhs, def_rhs) = concl def |> strip_forall |> snd |> dest_eq

    val fname = repeat rator def_lhs |> dest_const |> fst |> get_unique_name
    val _ = print ("Translating monadic " ^ fname ^ "for run\n")
    val fname_str = stringLib.fromMLstring fname

    val Mvar = mk_var("M", ``:('a, 'b, 'c) M``)
    val Svar = mk_var("S", ``:'a``)
    val (tms, tys) = match_term ``run ^Mvar ^Svar`` def_rhs
    val monad_tm = Term.subst tms (Term.inst tys Mvar)
    val state_var = Term.subst tms (Term.inst tys Svar)
    val (monad_f, monad_params) = strip_comb monad_tm

    (* Construct the Eval predicates for the parameters *)
    fun var_create_Eval tm = let
	val (name,ty) = dest_var tm
	val inv = get_type_inv ty
	val str = stringSyntax.fromMLstring name
	val result = ASSUME (mk_comb(``Eval env (Var (Short ^str))``,mk_comb(inv,tm)))
	val result = MATCH_MP (ISPEC_EvalM Eval_IMP_PURE) result
    in check_inv "var" tm result end
    val params_evals = List.map var_create_Eval monad_params

    (* Get the monadic specification *)
    val monad_th = lookup_dynamic_v_thm monad_f
    val monad_th = (MATCH_MP Eval_IMP_PURE monad_th)
		 |> ISPEC (!H)
		 |> PURE_REWRITE_RULE[GSYM ArrowM_def]
    
    (* Insert the parameters *)
    val monad_th = List.foldl (fn (x, th) => MATCH_MP(MATCH_MP EvalM_ArrowM th) x)
			      monad_th params_evals

    (* Add the state parameter assumption *)
    val env = concl monad_th |> rator |> rator |> rator |> rand
    val STATE_RI = get_type_inv (type_of state_var)
    val state_var_name = stringLib.fromMLstring(dest_var state_var |> fst)
    val Eval_state_var_assum = ``Eval ^env (Var (Short ^state_var_name)) (^STATE_RI ^state_var)``
    val monad_th = ADD_ASSUM Eval_state_var_assum monad_th

    (* Symplify the VALID_REFS_PRED assumption *)
    val VALID_REFS_PRED_assum = ``VALID_REFS_PRED ^(!H)``
    val monad_th = PURE_REWRITE_RULE[VALID_REFS_PRED_EvalM_simp] (DISCH VALID_REFS_PRED_assum monad_th)

    (* Translate the run construct *)
    val x = concl monad_th |> rator |> rand |> rand
    val exp = concl monad_th |> rator |> rator |> rand
    val MONAD_TYPE = concl monad_th |> rator |> rand |> rator
    val EXN_TYPE = rand MONAD_TYPE
    val TYPE = rator MONAD_TYPE |> rand
    val vname = stringSyntax.fromMLstring "vname"
    val (exn_cons_names, exn_module_name) = get_exn_constructs ()
    val cons_names = mk_list(exn_cons_names, ``:tvarN``)
    val th = case exn_module_name of
		 SOME module_name =>
		 ISPECL [cons_names, module_name, vname, TYPE, EXN_TYPE, x, exp,
			 !H, state_var, env] EvalM_run_MODULE
	       | NONE =>
		 ISPECL [cons_names, vname, TYPE, EXN_TYPE, x, exp,
			 !H, state_var, env] EvalM_run_SIMPLE
    (* Prove the assumptions *)
    val [EXN_assum, distinct_assum, vname_assum1, vname_assum2] = List.take(
	    concl th |> strip_imp |> fst, 4)
    val EXN_th = prove(EXN_assum, rw[] \\ Cases_on `e` \\ fs[!EXN_TYPE_def_ref])
    val th = MP th EXN_th
		
    val distinct_th = SIMP_CONV list_ss [] distinct_assum |> EQT_ELIM
    val vname_th1 = SIMP_CONV list_ss [] vname_assum1 |> EQT_ELIM
    val vname_th2 = SIMP_CONV list_ss [] vname_assum2 |> EQT_ELIM

    val EXC_TYPE_tm = get_type_inv ``:('a, 'b) exc`` |> rator |> rator
    val EXC_TYPE_def = DB.find "EXC_TYPE_def" |> List.hd |> snd |> fst
		       handle Empty => raise (ERR "m_translate_run" "The `exc` type needs to be registered in the current program")
    val EXC_RI_prove_tac =
	irule EQ_EXT \\ gen_name_tac "A"
        \\ irule EQ_EXT \\ gen_name_tac "B"
        \\ irule EQ_EXT \\ gen_name_tac "x"
        \\ irule EQ_EXT \\ gen_name_tac "v"
        \\ Cases_on `x`
        \\ simp[EXC_TYPE_def, EXC_TYPE_aux_def]
    val EXN_rw = prove(``EXC_TYPE_aux = ^EXC_TYPE_tm``, EXC_RI_prove_tac)

    val th = List.foldl (fn (a, th) => MP th a) th [distinct_th, vname_th1, vname_th2]
    val th = PURE_REWRITE_RULE[EXN_rw] th
    val th = MP th monad_th

    (* Undischarge the lookup assumptions *)
    val every_lookup_assum = concl th |> dest_imp |> fst
    val every_lookup_rw = SIMP_CONV list_ss [] every_lookup_assum
    val th = SIMP_RULE bool_ss [every_lookup_rw, GSYM AND_IMP_INTRO] th |> UNDISCH_ALL

    (* Replace the environment *)
    val nenv = get_current_env()
    val th = Thm.INST [env |-> nenv] th

    (* Create the local function definitions *)
    val th = create_local_defs th

    (*
     * Instantiate the environment 0
     *)
    val global_env = get_env(get_curr_prog_state())
    val params_bindings = List.map(fn x => (concl x |> rator |> rator |> rand |> rand |> rand,
					    concl x |> rator |> rand |> rand)) params_evals
    (* val state_var = concl th |> rator |> rand *)
    val state_var_eval = hol2deep state_var
    val state_var_v = mk_var((dest_var state_var |> fst) ^"_v", ``:v``)
    val state_var_vname = concl state_var_eval |> rator |> rand |> rand |> rand
    val state_var_binding = (state_var_vname, state_var)
    val state_var_binding_v = (state_var_vname, state_var_v)

    val params_bindings = state_var_binding::(List.rev params_bindings)
    
    (* Create variables for the deep embeddings of the parameters *)
    val fvl = HOLset.listItems(FVL ((concl th)::(hyp th)) empty_varset)
    val params_v = List.map (fn (n, var) => variant fvl (mk_var((dest_var var |> fst) ^ "_v", ``:v``))) params_bindings
    val hol_deep_pairs = List.map (fn ((n, x), xv) => (x, xv)) (zip params_bindings params_v)
    val deep_params_map = List.foldr (fn ((x, xv), m) => Redblackmap.insert(m, x, xv)) (Redblackmap.mkDict Term.compare) hol_deep_pairs

    val params_bindings_v = List.map (fn ((n, x), xv) => (n, xv)) (zip params_bindings params_v)
    val params_bindings_v = List.map mk_pair params_bindings_v
    val params_bindings_v = mk_list(params_bindings_v, ``:tvarN # v``)

    (* val params_invs_hyps = List.map (fn ((n, x), xv) => list_mk_comb(get_type_inv (type_of x), [x, xv])) (zip params_bindings deep_params) *)

    (* Create the environment 0 and substitute it *)
    val env0 = ``merge_env <| v := Bind ^params_bindings_v []; c := Bind [] [] |> ^global_env``
    val th = Thm.INST [local_environment_var_0 |-> env0] th
    
    (* Simplify the assumptions *)
    val assums = hyp th
    val lookup_cons_assums = List.filter (can (match_term ``lookup_cons vname env = SOME t``)) assums
    val lookup_cons_rws = mapfilter(fn x => EVAL x |> EQT_ELIM) lookup_cons_assums
    val th = List.foldr (fn (a, th) => MP (DISCH (concl a) th) a) th lookup_cons_rws
    val assums = hyp th
    val nsLookup_assums = List.filter (can (match_term ``nsLookup env id = SOME var``)) assums
    fun Eval_error_msg x = let
	val vname = lhs x |> rand |> rand
	val msg1 = "Error with the binding: "
	val msg2 = stringLib.fromHOLstring vname
	val msg3 = " - check that the proper functions and types are defined in the current CakeML program"
    in msg1 ^msg2 ^msg3 end
    val nsLookup_assums_rws = mapfilter(fn x => EVAL x |> EQT_ELIM handle HOL_ERR _ => raise (ERR "m_translate_run" (Eval_error_msg x))) nsLookup_assums

    val th = List.foldr (fn (a, th) => MP (DISCH (concl a) th) a) th nsLookup_assums_rws
    
    (* Symplify the assumption parameters *)
    val assums = hyp th
    val Eval_var_assums = List.filter (can (match_term ``Eval env exp (P x)``)) assums

    fun rewrite_Eval_var (assum, th) = let
	val env = rator assum |> rator |> rand
	val vname = rator assum |> rand |> rand |> rand
	val x = rand assum |> rand
	val xv = Redblackmap.find (deep_params_map, x)
	val TYPE = rand assum |> rator

	val rw_th = ISPECL[env, vname, xv, x, TYPE] Eval_lookup_var
	val rw_th_assum = concl rw_th |> dest_imp |> fst
	val rw_th = MP rw_th (EVAL rw_th_assum |> EQT_ELIM)
		       
	val inv_to_eval = EQ_IMP_RULE rw_th |> snd |> UNDISCH
	val th = MP (DISCH (concl inv_to_eval) th) inv_to_eval
    in th end

    val th = List.foldl rewrite_Eval_var th Eval_var_assums
			|> PURE_REWRITE_RULE[Bind_list_to_write]

    (* Create the store *)
    val th = create_local_references th

    (* Abstract the parameters *)
    val th = PURE_REWRITE_RULE [GSYM def] th
    val rev_params = List.map snd params_bindings
    val th = List.foldl apply_Eval_Fun th rev_params

    (* Expand the handle_mult expression *)
    val th = PURE_REWRITE_RULE[handle_mult_def, handle_one_def] th

    (* Store the spec *)
    val th = PURE_REWRITE_RULE[Eval_Fun_rw] th
    val fname = repeat rator def_lhs |> dest_const |> fst |> get_unique_name
    val v = th |> concl |> rand |> rator |> rand
    val e = th |> concl |> rand |> rand
    val v_name = find_const_name (fname ^ "_v")
    val _ = ml_prog_update (add_Dlet_Fun fname_str v e v_name)
    val s = get_curr_prog_state ()
    val v_def = hd (get_v_defs s)
    val th = th |> REWRITE_RULE [GSYM v_def]

    (* Store the certificate for later use *)
    val pre = TRUTH
    val _ = add_v_thms (fname,fname,th,pre)
    val th = save_thm(fname ^ "_v_thm",th)
in th end

val _ = export_theory ();
