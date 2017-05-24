open  preamble ml_progLib ioProgLib ml_translatorLib
	       cfTacticsLib basisFunctionsLib ml_translatorTheory;
    
val _ = new_theory "xletAuto";

val _ = translation_extends"ioProg";

(*val queue_decls = process_topdecs
    `fun empty_queue u = ref (Array.arrayEmpty (), 0)

    fun push q x =
    	case !q of (qa,i) =>
	let val l = Array.length qa in
      	if i >= l then
      	   let val qa' = Array.array (2*l+1) x in
	   (Array.copy qa qa' 0;
	   q := (qa', i+1))
	   end
      	else
	   (Array.update qa i x; q := (qa,i+1))
	end

    exception EmptyQueue

    fun pop q =
    	case !q of (qa,i) =>
      	if i = 0 then raise EmptyQueue
      	else let val x = Array.sub qa (i-1) in (q := (qa, i-1); x) end`;

val _ = append_prog queue_decls;

val QUEUE_def  = Define `
  QUEUE A vs qv =
  SEP_EXISTS av xv iv vvs junk. REF qv xv * &(xv= (Conv NONE [av;iv])) * & NUM (LENGTH vs) iv * ARRAY av (vvs ++ junk) * & LIST_REL A vs vvs`;


(* Some automated tactics, function definitions *)

val auto_cf_tac1 = rpt (FIRST [xapp, xlit, xcon, xvar]) >> xsimpl;

val cf_lookup = Redblackmap.fromList String.compare [("cf_app", xapp), ("cf_lit", xlit), ("cf_con", xcon), ("cf_var", xvar)];

fun auto_cf_tac2 (g as (asl, w)) =
  let
    val name = (#1 (dest_const (#1 (strip_comb w))))
    val tac = Redblackmap.find (cf_lookup, name)
  in
  tac end
      g;

val (perso_disj1_tac : tactic) =
  fn (g as (asl: term list, w)) =>
  (let
    val (lg, rg)  = dest_disj w
  in
  ([(asl, lg)], (fn ls => DISJ1 (hd ls) rg))
  end);

val ERR = mk_HOL_ERR "son_ho";

val (build_conv_tm, mk_build_conv, dest_build_conv, is_build_conv) = HolKernel.syntax_fns3 "semanticPrimitives" "build_conv";
val (exp2v_tm, mk_exp2v, dest_exp2v, is_exp2v) = HolKernel.syntax_fns2 "cfNormalise" "exp2v";

(* Code taken from cfSyntax.sml *)
fun make6 tm (a,b,c,d,e,f) =
  list_mk_icomb (tm, [a, b, c, d, e, f]);

fun dest6 c e tm =
  case with_exn strip_comb tm e of
      (t, [t1, t2, t3, t4, t5, t6]) =>
      if same_const t c then (t1, t2, t3, t4, t5, t6) else raise e
    | _ => raise e;

val s6 = HolKernel.syntax_fns {n = 6, make = make6, dest = dest6} "cf";
val (cf_let_tm, mk_cf_let, dest_cf_let, is_cf_let) = s6 "cf_let";

(* Manipulation of expressions *)

fun get_value env e =
  cfTacticsLib.reduce_conv (mk_exp2v (env, e))
  |> concl |> rhs |> optionSyntax.dest_some;

fun con_expr_condition let_expr_args asl w env pre post =
  let
    val nvar0 = mk_var("v",semanticPrimitivesSyntax.v_ty)
    val ctx = free_varsl (w :: asl)
    val nvar = prim_variant ctx nvar0
    val [con_name, con_args] = let_expr_args
    val (con_args_exprs, _) = listSyntax.dest_list con_args
    val con_args_tms = List.map (get_value env) con_args_exprs
    val con_args_list_tm = listSyntax.mk_list (con_args_tms, semanticPrimitivesSyntax.v_ty)
    val con_tm = mk_build_conv (``^env.c``,con_name,con_args_list_tm)
      |> cfTacticsLib.reduce_conv |> concl |> rhs |> optionSyntax.dest_some
    val nvar_eqn = mk_eq(nvar,con_tm)
  in
    `POSTv ^nvar. &^nvar_eqn * ^pre`
  end;

(* Functions to aply to retrieve the pointers from the heap predicates *)
fun get_REF_ptr p = cfHeapsBaseSyntax.dest_REF p |> #1;
fun get_ARRAY_ptr p = cfHeapsBaseSyntax.dest_ARRAY p |> #1;
val QUEUE_tm = ``QUEUE``;
fun get_QUEUE_ptr p =
  let
    val (queue_tm, args) = strip_comb p
  in
    if not (same_const QUEUE_tm queue_tm)
    then raise ERR "get_QUEUE_ptr" "not a queue"
    else List.last args
  end;

val get_ptr_fun_list = [
  get_REF_ptr,
  get_ARRAY_ptr,
  get_QUEUE_ptr
];

(* [get_heap_pred_ptr]
   Retrieves the pointer defined in a primitive heap predicate
   (a predicate of the form: ``REF r v``, ``ARRAY r v``...).
 *)
fun get_heap_pred_ptr p =
  let fun rec_get p fl =
    case fl of
    f::fl' => (let val ret_val = f p in SOME ret_val end handle _ => rec_get p fl')
    | _ => NONE
  in
    rec_get p get_ptr_fun_list
  end;

(* [dest_postv] *)
val postv_tm = ``cfHeapsBase$POSTv``;
fun dest_postv c =
  dest_binder postv_tm (ERR "dest_postv" "Not a POSTv abstraction") c;

(* [is_postv] *)
fun is_postv c =
  let val _ = dest_binder postv_tm (ERR "" "") c in true end handle _ => false;

(* [rename_dest_postv]
   Deconstructs the POSTv of a heap condition and rename the POSTv value
   so that it is a fresh variable. *)
fun rename_dest_postv (varsl, c) =
  let
      val (v, c1) = dest_postv c
      val v' = variant varsl v
      val c2 = Term.subst [v |-> v'] c1
  in
      (v', c2)
  end;

(* [dest_poste] *)
val poste_tm = ``cfHeapsBase$POSTe``;
fun dest_poste c =
  dest_binder poste_tm (ERR "dest_poste" "Not a POSTe abstraction") c;

(* [is_poste] *)
fun is_poste c =
  let val _ = dest_binder poste_tm (ERR "" "") c in true end handle _ => false;

(* [rename_dest_poste]
   Deconstructs the POSTe of a heap condition and rename the POSTe value
   so that it is a fresh variable. *)
fun rename_dest_poste (varsl, c) =
  let
      val (v, c1) = dest_poste c
      val v' = variant varsl v
      val c2 = Term.subst [v |-> v'] c1
  in
      (v', c2)
  end;

(* [dest_post] *)
val post_tm = ``cfHeapsBase$POST``;
fun dest_post c =
  let
      val (c', poste_abs) = dest_comb c
      val (ptm, postv_abs) = dest_comb c'
  in
      if same_const ptm post_tm then
	  let
	      val (postv_v, postv_pred) = dest_abs postv_abs
	      val (poste_v, poste_pred) = dest_abs poste_abs
	  in
	      (postv_v, postv_pred, poste_v, poste_pred)
	  end
      else
	  raise (ERR "" "")
  end
  handle _ => raise (ERR "dest_post" "Not a POST abstraction");

(* [is_post] *)
fun is_post c =
  let
      val (c', poste_abs) = dest_comb c
      val (ptm, postv_abs) = dest_comb c'
  in
      if same_const ptm post_tm then true else false
  end
  handle _ => false;

(* [rename_dest_post] *)
fun rename_dest_post (varsl, c) =
  if is_postv c then
      let
	  val (postv_v, postv_pred) = dest_postv c
	  val postv_v' = variant varsl postv_v
	  val postv_pred' = Term.subst [postv_v |-> postv_v'] postv_pred
      in
	  (SOME postv_v', SOME postv_pred', NONE, NONE) end
  else if is_poste c then
      let
	  val (poste_v, poste_pred) = dest_poste c
	  val poste_v' = variant varsl poste_v
	  val poste_pred' = Term.subst [poste_v |-> poste_v']  poste_pred
      in
	  (NONE, NONE, SOME poste_v', SOME poste_pred') end
  else if is_post c then
      let
	  val (postv_v, postv_pred, poste_v, poste_pred) = dest_post c
	  val postv_v' = variant varsl postv_v
	  val postv_pred' = Term.subst [postv_v |-> postv_v'] postv_pred
	  val poste_v' = variant (postv_v'::varsl) poste_v
	  val poste_pred' = Term.subst [poste_v |-> poste_v']  poste_pred
      in
	  (SOME postv_v', SOME postv_pred', SOME poste_v', SOME poste_pred') end
  else
      raise (ERR "rename_dest_post" "Not a heap post-condition");

(* [rename_dest_exists]
  Deconstructs the existential quantifiers of a heap condition,
  and rename the previsouly bound variables to prevent name conflicts. *)
fun rename_dest_exists (varsl, c) =
  let fun rec_dest varsl lv c =
    if is_sep_exists c then
      let
        val (nv, nc) = dest_sep_exists c
	val nv' = variant varsl nv
	val nc' = Term.subst [nv |-> nv'] nc
	val (nlv, fc) = rec_dest (nv'::varsl) lv nc'
      in
        (nv'::nlv, fc)
      end
    else
      (([]:term list), c)
  in
    rec_dest varsl ([]:term list) c
  end;

(* [dest_pure_fact]
   Deconstructs a pure fact (a heap predicate of the form &P) *)
val set_sep_cond_tm = ``set_sep$cond``;
fun dest_pure_fact p =
  case (dest_term p) of
  COMB dp =>
    (if same_const set_sep_cond_tm (#1 dp) then (#2 dp)
    else raise (ERR "dest_pure_fact" "Not a pure fact"))
  | _ => raise (ERR "dest_pure_fact" "Not a pure fact");

(* [sort_heap_pred]
   Determines whether a heap predicate is a pure fact or not,
   and adds it to the according list. *)
fun sort_heap_pred hp hpl pfl =
  let
    val pure_pred = dest_pure_fact hp
  in
    (hpl, pure_pred::pfl)
  end
  handle HOL_ERR _ => (hp::hpl, pfl);


(* list_dest_star
   Deconstructs a (star) conjunction of heap conditions.
   Splits the conjuncts between heap conditions and pure facts.
 *)
fun list_dest_star c =
  let fun rec_dest hpl pfl c =
    let
      val (nc1, nc2) = dest_star c
      val (hpl1, pfl1) = rec_dest hpl pfl nc1
      val (hpl2, pfl2) = rec_dest hpl1 pfl1 nc2
    in
      (hpl2, pfl2)
    end
    handle HOL_ERR _ => sort_heap_pred c hpl pfl
  in
    rec_dest ([]:term list) ([]:term list) c
  end;

(* list_heap_pointers
   List the heap pointers used in a list of heap predicates.
   The functions retrieving the heap pointers is defined by the
   list get_ptr_fun_list. *)
fun list_heap_ptrs hpl =
  case hpl of
  hp::hpl' =>
    let
      val ptrs = list_heap_ptrs hpl'
    in
      case get_heap_pred_ptr hp of
      SOME v => v::ptrs
      | NONE => ptrs
    end
   | [] => ([]:term list);

(* [dest_heap_condition]
  Deconstructs a heap predicate. Needs to be provided a list of terms
  representing variables to avoid name collision
  Returns:
  - the list of existentially quantified variables
  - the list of heap pointers used in the heap predicates
  - the list of heap predicates
  - the list of pure facts *)
fun dest_heap_condition (varsl, c) =
  let
    val (ex_vl, c') = rename_dest_exists (varsl, c)
    val (hpl, pfl) = list_dest_star c'
    val ptrs = list_heap_ptrs hpl
  in
    (ex_vl, hpl, pfl)
  end;

(* [mk_heap_condition]
   Creates a heap condition of the form:
      (SEP_EXISTS x1...xn. H1 * ... Hk * &P1 * ... * &Pl)
   Parameters:
   - the list of existentially quantified variables
   - the list of heap predicates
   - the list of pure facts
 *)
fun mk_heap_condition (ex_vl, hpl, pfl) =
  let
    val c1 = list_mk_star hpl ``:hprop``
    val hprop_pfl = List.map (fn x => mk_cond x) pfl
    val c2 = list_mk_star (c1::hprop_pfl) ``:hprop``
    val c3 = list_mk (mk_sep_exists) ex_vl c2
  in
    c3
  end;

(* [mk_postv] *)
fun mk_postv (postv_v, c) = mk_binder postv_tm "mk_postv" (postv_v, c);

(* [mk_poste] *)
fun mk_poste (poste_v, c) = mk_binder poste_tm "mk_poste" (poste_v, c);

(* [mk_post] *)
fun mk_post (postv_v, postv_abs, poste_v, poste_abs) =
  let
      val postv_pred = mk_abs (postv_v, postv_abs)
      val poste_pred = mk_abs (poste_v, poste_abs)
      val post_cond_pre = mk_comb (post_tm, postv_pred)
      val post_cond = mk_comb (post_cond_pre, poste_pred)
  in
      post_cond
  end;

(* [mk_heap_post_condition]
   Creates a heap post condition.
   Parameters:
   - the optional postv value
   - the optional postv predicate
   - the optional poste value
   - the optional poste predicate
*)

fun mk_heap_post_condition (postv_v, postv_pred, poste_v, poste_pred) =
  case (postv_v, postv_pred, poste_v, poste_pred) of
      (SOME postv_v, SOME postv_pred, NONE, NONE) => mk_postv (postv_v, postv_pred)
   |  (NONE, NONE, SOME poste_v, SOME poste_pred) => mk_poste (poste_v, poste_pred)
   |  (SOME postv_v, SOME postv_pred, SOME poste_v, SOME poste_pred) =>
            mk_post (postv_v, postv_pred, poste_v, poste_pred)
   | _  => raise (ERR "mk_heap_post_condition" "Not valid parameters");

(******** Get the post-condition given by the app specification ***********)
(* [find_spec]
   Finds a proper specification for the application in the goal.
   The code has been taken from xspec (cfTactics) *)
fun find_spec g =
  let
    val (asl, w) = (xapp_prepare_goal g) |> #1 |> List.hd
    val (ffi_ty, f) = (goal_app_infos w)
  in
  case xspec_in_asl f asl of
      SOME (k, a) =>
      (print
      ("Using a " ^ (spec_kind_toString k) ^
       " specification from the assumptions\n");
      cf_spec ffi_ty k (ASSUME a))
   | NONE =>
       case xspec_in_db f of
          SOME (thy, name, k, thm) =>
	  (print ("Using " ^ (spec_kind_toString k) ^
	  " specification " ^ name ^
	  " from theory " ^ thy ^ "\n");
	  cf_spec ffi_ty k thm)
       | NONE =>
          raise ERR "find_spec" ("Could not find a specification for " ^
                             fst (dest_const f))
  end;

(* [rename_dest_foralls]
   Removes the forall operators from a term. Renames the  bound
   variables so that they are fresh regarding a given list
   of assumptions *)
fun rename_dest_foralls (asl, spec) =
  let
    val fvl = free_varsl asl
    fun rec_remove fvl spec =
      if not (is_forall spec) then (([]:term list), spec)
      else
      let
        val (x, spec') = dest_forall spec
	val x' = variant fvl x
	val subst_spec = Term.subst [x |-> x'] spec'
	val (xl, fspec) = rec_remove (x'::fvl) subst_spec
      in
        (x'::xl, fspec)
      end
  in
    rec_remove fvl spec
  end;

(* [xlet_find_spec]
   Find the app specification to use given a goal to prove *)
fun xlet_find_spec g =
  let
    (* Find the specification *)
    val dummy_spec = `POSTv (v:v). &T`
    val g' = xlet dummy_spec g |> #1 |> List.hd
  in
    find_spec g'
  end;

(* [xlet_dest_app_spec] *)
fun xlet_dest_app_spec asl let_pre specH =
  let
      (* Get the parameters and pre/post-conditions written in the specification *)
      val (_, noquant_spec_tm) = rename_dest_foralls ((let_pre::asl), (concl specH))
      val impsl_spec = list_dest dest_imp noquant_spec_tm
      val app_asl = List.take (impsl_spec, (List.length impsl_spec)-1)
      val app_spec = List.last impsl_spec
  in
      (app_asl, app_spec)
  end;

(* [xlet_subst_parameters] *)
fun xlet_subst_parameters env app_info asl let_pre app_asl app_spec  =
  let
    (* Find the parameters given to the function *)
    val COMB (_, parameters) = dest_term app_info
    val (params_expr_list, _) = listSyntax.dest_list parameters
    val params_tm_list = List.map (get_value env) params_expr_list
    
    (* Get the parameters and pre/post-conditions written in the specification *)
    val (app_spec1, app_post) = dest_comb app_spec
    val (app_spec2, app_pre) = dest_comb app_spec1
    val spec_parameters = dest_comb app_spec2 |> #2
    val (spec_params_tm_list, _) = listSyntax.dest_list spec_parameters

    (* Match the parameters *)
    fun create_subst l1 l2 =
      (case (l1, l2) of
      (e1::l1', e2::l2') => (e1 |-> e2)::(create_subst l1' l2')
      | (([]:term list), ([]:term list)) => ([]:{redex: term, residue: term} list))
    val params_subst = create_subst spec_params_tm_list params_tm_list
    val subst_app_asl = List.map (Term.subst params_subst) app_asl
    val subst_app_pre = Term.subst params_subst app_pre
    val subst_app_post = Term.subst params_subst app_post
  in
    (subst_app_asl, subst_app_pre, subst_app_post)
  end;

(* [list_mk_fun] *)
fun list_mk_fun params_types output_type = List.foldr (fn (t1, t2) => mk_type ("fun", [t1, t2])) output_type params_types;

(* [xlet_match_asl] *)
fun xlet_match_asl (inst_tac:tactic) origin_asl target_asl =
  let
      (* Retrieve the lists/sets of free variables *)
      val kwn_varset = FVL origin_asl empty_varset
      val target_varset = FVL target_asl empty_varset
      val all_varset = HOLset.union (kwn_varset, target_varset)
      val all_varsl = HOLset.listItems all_varset
      val unkwn_varset = HOLset.difference (target_varset, kwn_varset)
      val unkwn_varsl = HOLset.listItems unkwn_varset

      (* Build the big "goal" formula *)
      val unkwn_vars_types = List.map (fn v => type_of v) unkwn_varsl
      val synthPredsTypeL = unkwn_vars_types
      val synthPredType = list_mk_fun synthPredsTypeL ``:bool``
      val synthPredVar = mk_var ("synthP", synthPredType) |> variant all_varsl
      val synthPred = list_mk_comb (synthPredVar, unkwn_varsl)
      val open_goal_formula = list_mk_conj (List.rev (synthPred::target_asl))
      val close_goal_formula = list_mk_exists (unkwn_varsl, open_goal_formula)
      val matching_goal = (origin_asl, close_goal_formula)

      (* Match - note that the synthPred should be in the last subgoal *)
      val (_, matched_w) = (inst_tac matching_goal) |> #1 |> List.last

      (* Extract the instantiated variables - if everything went well,
	     there should only remain the synthesis predicate in the goal *)
      val extracted_terms  =
	  (let
	      val (pred_name, tml) = strip_comb matched_w
	  in
	      if pred_name = synthPredVar then
		  tml
	      else
		  (raise (ERR "" ""))
	  end
	   handle _ =>
		  raise (ERR "xlet_match_pre_conditions" "Unable to perform the matching"))
      val paired_terms = ListPair.zip (unkwn_varsl, extracted_terms)
      val tm_subst = List.map (fn (x, y) => (x |-> y)) paired_terms
  in
      tm_subst
  end;

(* [xlet_match_pre_conditions] *)
fun xlet_match_pre_conditions (inst_tac:tactic) asl let_pre app_asl app_pre app_post =
  let
    (* Determine the known variables (given by the assumptions)
    and the unknown ones (given by the app specification - they need
    to be instantiated *)
    val kwn_varset = FVL (let_pre::asl) empty_varset
    val app_varset = FVL (app_pre::app_post::app_asl) empty_varset
    val unkwn_varset = HOLset.difference (app_varset, kwn_varset)
    val unkwn_varsl = HOLset.listItems unkwn_varset

    (* Decompose the pre/post conditions *)
    val varset1 = HOLset.union (unkwn_varset, kwn_varset)
    val varsl1 = HOLset.listItems varset1
    val (pre_ex_vl, pre_hpl, pre_pfl) =
          dest_heap_condition (varsl1, let_pre)
    val varsl2 = List.concat [varsl1, pre_ex_vl]
    val (app_pre_ex_vl, app_pre_hpl, app_pre_pfl) =
          dest_heap_condition (varsl2, app_pre)

    (*
     * Match the pre-conditions to instantiate the unknown variables
     *)
    (* Transform the heap predicates to predicates *)
    val varsl3 = List.concat [varsl2, app_pre_ex_vl]
    val H_tm = variant varsl3 ``H:heap``
    val transf_pre_hpl = List.map (fn x => mk_comb (x, H_tm)) pre_hpl
    val transf_app_pre_hpl = List.map (fn x => mk_comb (x, H_tm)) app_pre_hpl

    (* Perform the matching *)
    val origin_asl = List.concat [asl, transf_pre_hpl, pre_pfl, [``emp ^H_tm``]]
    val target_asl = List.concat [app_asl, transf_app_pre_hpl, app_pre_pfl]
    val tm_subst = xlet_match_asl inst_tac origin_asl target_asl
    val subst_app_post = Term.subst tm_subst app_post
  in
      (pre_ex_vl, pre_hpl, pre_pfl, subst_app_post)
  end;

(* [xlet_find_ptrs_eq_classes]
   Finds the equivalence classes of the ptrs. Is necessary in order not to duplicate
   the heap predicates. *)
fun xlet_find_ptrs_eq_classes (match_tac : tactic) asl let_pre_hpl let_pre_pfl =
  if List.length let_pre_hpl = 0 then []
  else
  let
    (* Find the free variables *)
    val fvarset = FVL (List.concat [asl, let_pre_hpl, let_pre_pfl]) empty_varset
    val fvarsl = HOLset.listItems fvarset
    val fvars_types = List.map type_of fvarsl

    (* Find a name for the heap and convert the heap predicates accordingly *)
    val H_tm = variant fvarsl ``H:heap``
    val transf_pre_hpl = List.map (fn x => mk_comb (x, H_tm)) let_pre_hpl

    (* Create the synthesis predicate *)
    val synPredTypeL = fvars_types
    val synPredType = list_mk_fun synPredTypeL ``:bool``
    val synPredVar =  mk_var ("synthP", synPredType) |> variant (H_tm::fvarsl)
    val synPred = list_mk_comb (synPredVar, fvarsl)

    (* Create the unifying goal *)
    val unif_goal = (List.concat [asl, transf_pre_hpl, let_pre_pfl], synPred)

    (* Unify *)
    val (_, unified_w) = (match_tac unif_goal) |> #1 |> List.last

    (* Extract the terms *)
    val extracted_terms  =
      (let
	val (pred_name, tml) = strip_comb unified_w
      in
	if pred_name = synPredVar then
	  tml
	else
	  (raise (ERR "" ""))
      end
      handle _ =>
	  raise (ERR "xlet_find_ptrs_eq_classes" "Unable to perform the matching"))
	  
    (* Create the substitution map *)
    val paired_tms = ListPair.zip (fvarsl, extracted_terms)
    val subst_map = List.map (fn (x, y) => (x |-> y)) paired_tms
  in
    subst_map
  end;

(* [filter_heap_predicates]
   Removes the predicates from which pointers are members of a given list.
   Parameters:
   - a map linking every pointer symbol to its class representative (regarding
     the = relation)
   - a list of heap predicates
   - a list of pointer variables *)
val emp_tm = ``emp``;
fun filter_heap_predicates subst_map hpl pl =
  let
    val pl = HOLset.listItems (FVL pl empty_tmset)
    val subst_pl = List.map (fn x => Term.subst subst_map x) pl
    val ps = ref (HOLset.addList (empty_varset, subst_pl))
    fun filter_pred tm =
      case (get_heap_pred_ptr tm) of
      SOME r => let val r' = Term.subst subst_map r in
                  if not (HOLset.member (!ps, r')) then
                    (ps := (HOLset.add (!ps, r')); true)
		  else
		    false
		end
      | NONE => not (same_const emp_tm tm)
  in
    List.filter filter_pred hpl
  end;

(* [xlet_mk_post_conditions] *)
fun xlet_mk_post_condition match_tac asl let_pre_ex_vl let_pre_hpl let_pre_pfl app_post =
  let
    val varset1 = FVL (List.concat [asl, let_pre_hpl]) empty_varset
			
    (* Decompose the app post-condition *)
    val cur_free_varset =
	FVL (List.concat [asl, let_pre_hpl, let_pre_pfl, [app_post]]) empty_varset
    val cur_free_varsl = HOLset.listItems cur_free_varset
    val (post_postv_vo, post_postv_po, post_poste_vo, post_poste_po) =
	rename_dest_post (cur_free_varsl, app_post)

    (* Get the equivalence classes for the ptrs in the let-pre-condition *)
    val subst_map = xlet_find_ptrs_eq_classes match_tac asl let_pre_hpl let_pre_pfl

    (* Filter the heap predicates from the let pre-condition *)
    fun mk_post_cond_aux (subst_map, pred_opt) =
      (case pred_opt of
	  SOME pred =>
	  let
	      val (post_ex_vl, post_hpl, post_pfl) =
		  dest_heap_condition (cur_free_varsl, pred)
	      val post_ptrs = list_heap_ptrs post_hpl
	      val filtered_pre_hpl =
		  filter_heap_predicates subst_map let_pre_hpl post_ptrs
	      val let_heap_condition =
		  mk_heap_condition ((List.concat [let_pre_ex_vl, post_ex_vl]),
				    (List.concat [post_hpl, filtered_pre_hpl]),
				    (List.concat [post_pfl, let_pre_pfl]))
	  in
	      SOME let_heap_condition
	  end
	  | NONE => NONE)
    val post_postv_po' = mk_post_cond_aux (subst_map, post_postv_po)
    val post_poste_po' = mk_post_cond_aux (subst_map, post_poste_po)
				
    (* Construct the post-condition *)
    val let_heap_condition =
	mk_heap_post_condition (post_postv_vo, post_postv_po', post_poste_vo, post_poste_po')
  in
    let_heap_condition
  end;

(* [xlet_is_heap_spec]
   Determines the type of an application specification, given its conclusion.
   A specification must be of one of the following forms:
       !x1...xn. P1 x1 ... xn ==> ... ==> Pm x1 ... xn ==> CONCL
   where CONCL is:
       CONCL = | app p fv [y1...yk] P Q
               | (TYPE1 --> ... --> TYPEk) f fv
*)
fun xlet_is_heap_spec app_concl =
  list_dest dest_comb app_concl |> List.hd  |> (same_const ``cfApp$app``);

(* xlet_post_condition_from_app_spec *)
fun xlet_post_condition_from_app_spec inst_tac match_tac env asl app_info let_pre post app_asl app_concl  =
  let
      (* Apply the parameters given in the let expression *)
      val (app_asl, app_pre, app_post) =
	  xlet_subst_parameters env app_info asl let_pre app_asl app_concl

      (* Match the let pre-condition and the app specification *)
      val (let_pre_ex_vl, let_pre_hpl, let_pre_pfl, app_post) =
	  xlet_match_pre_conditions inst_tac asl let_pre app_asl app_pre app_post
				    
      (* Construct the let condition *)
      val let_post_condition =
	  xlet_mk_post_condition match_tac asl
				 let_pre_ex_vl let_pre_hpl let_pre_pfl app_post
  in
      let_post_condition
  end;

(* [xlet_app_auto] *)
(*val (match_tac, inst_tac, app_info, env, let_pre, let_post) = (xlet_auto_match_tac, xlet_auto_inst_tac, let_expr, env, pre, post);*)
fun xlet_app_auto inst_tac match_tac app_info env let_pre post (g as (asl, w)) =
  let
      (* Find the specification *)
      val specH = xlet_find_spec g

      (* Split the conclusion from the assumptions in the app specification *)
      val (app_asl, app_concl) = xlet_dest_app_spec asl let_pre specH
						   
      (* Apply the parameters given in the let expression *)
      val let_post_condition =
	  xlet_post_condition_from_app_spec
	      inst_tac match_tac env asl app_info let_pre post app_asl app_concl
  in
      (* Return *)
      (specH, let_post_condition)
  end;

(* [xlet_expr_auto] *)
fun xlet_expr_auto let_expr env pre post (g as (asl, w))   =
  let
      val (let_expr_op, let_expr_args) = strip_comb let_expr
  in
    if same_const let_expr_op cf_con_tm then
      let val let_heap_condition =
        con_expr_condition let_expr_args asl w env pre post
      in
         Term let_heap_condition
      end
    else
      raise (ERR "xlet_expr_auto" "not handled yet")
  end;

(* Auxiliary functions to test that a given term is of the given form (the standard is_cf_con,... don't work in the cases I need them) *)
fun is_cf_con_aux let_expr =
  same_const cf_con_tm (let_expr |> strip_comb |> #1)
  handle HOL_ERR _ => false;

fun is_cf_app_aux let_expr =
  same_const cf_app_tm (let_expr |> strip_comb |> #1)
  handle HOL_ERR _ => false;

(* [xlet_find_auto_aux] *)
val xlet_find_auto_aux = fn inst_tac => fn match_tac  =>
  fn (g as (asl, w)) =>
     if is_cf_let w then
	 let
	     val (goal_op, goal_args) = strip_comb w
	     val let_expr = List.nth (goal_args, 1)
	     val env = List.nth (goal_args, 3)
	     val pre = List.nth (goal_args, 4)
	     val post = List.nth (goal_args, 5)
	 in
	     if is_cf_con_aux let_expr then
		 xlet_expr_auto let_expr env pre post g
             else if is_cf_app_aux let_expr then
		 let val (_, c) =
			 xlet_app_auto inst_tac match_tac let_expr env pre post g
		 in c end
	     else
		 raise (ERR "xlet_auto" "Not handled yet")
	 end
      else
	  raise (ERR "xlet_auto" "Not a cf_let expression");

(* [xlet_auto_aux] *)
val xlet_auto_aux = fn (inst_tac:tactic) => fn (match_tac:tactic) =>
  fn (g as (asl, w)) =>
     if is_cf_let w then
	 let
	     val (goal_op, goal_args) = strip_comb w
	     val let_expr = List.nth (goal_args, 1)
	     val env = List.nth (goal_args, 3)
	     val pre = List.nth (goal_args, 4)
	     val post = List.nth (goal_args, 5)
	 in
	     if is_cf_con_aux let_expr then
		 let val c = xlet_expr_auto let_expr env pre post g
		 in xlet `^c` g end
	     else if is_cf_app_aux let_expr then 
		 let val (H, c) =
			 xlet_app_auto inst_tac match_tac let_expr env pre post g
		 in (xlet `^c` THENL [xapp_spec H, all_tac]) g end
	     else
		 raise (ERR "xlet_auto" "Not handled yet")
	 end
      else
	  raise (ERR "xlet_auto" "Not a cf_let expression");

(* The congruence theorem for the star operator -
   TODO: integrate it in the matching algorithm *)
val star_congr = Q.store_thm("star_congr",
`!H:heap. (P * Q) H <=> ?H1 H2. SPLIT H (H1, H2) /\ P H1 /\ Q H2`,
strip_tac >> EQ_TAC >> fs[set_sepTheory.STAR_def] >> instantiate);

val SPLIT_congr = Q.store_thm("SPLIT_congr",
`SPLIT H (H1, H2) /\ (?H3 H4. SPLIT H1 (H3, H4) /\ P H1 H2 H3 H4) <=>
(?H3 H4. SPLIT H (H1, H2) /\  SPLIT H1 (H3, H4) /\ P H1 H2 H3 H4)`,
EQ_TAC >-(rw[])>> rw[] >> rw[] >> instantiate);

(* Some theorems used for simplication and matching *)
val int_num_convert_add = Q.store_thm("int_num_convert_add",
`!(x:num) (y:num).(&x) + &y = &(x+y)`, rw[] >> intLib.ARITH_TAC);
val int_num_convert_times = Q.store_thm("int_num_convert_times",
`!(x:num) (y:num).(&x) * &y = &(x*y)`, rw[] >> intLib.ARITH_TAC);
val int_num_convert_le = Q.store_thm("int_num_convert_le",
`!(x:num) (y:num). (&x <= &y) = (x <= y)`, rw[]);
val int_num_convert_less = Q.store_thm("int_num_convert_less",
`!(x:num) (y:num). (&x < &y) = (x < y)`, rw[]);
val int_num_convert_ge = Q.store_thm("int_num_convert_ge",
`!(x:num) (y:num). (&x >= &y) = (x >= y)`, rw[] >> intLib.ARITH_TAC);
val int_num_convert_great = Q.store_thm("int_num_convert_great",
`!(x:num) (y:num). (&x > &y) = (x > y)`, rw[] >> intLib.ARITH_TAC);
val int_num_convert_eq = Q.store_thm("int_num_convert_eq",
`!(x:num) (y:num). (&x = &y) = (x = y)`, rw[] >> intLib.ARITH_TAC);
val int_num_convert_subs = Q.store_thm("int_num_convert_subs",
`!(x:num) (y:num). (&x - &y = &z) <=> (x - y = z) /\ y <= x`,
rw[] >> intLib.ARITH_TAC);

val empty_list_thm = Q.store_thm("empty_list_thm",
`(!l. LENGTH l = 0 <=> l = []) /\ (!l. 0 = LENGTH l <=> l = [])`,
CONJ_TAC >> rw[LENGTH_NIL] >> `0 = LENGTH l <=> LENGTH l = 0` by rw[] >> rw[LENGTH_NIL]);


(* Unicity results for the value pointed to by a heap pointer *)
val ARRAY_PTR_UNICITY = Q.store_thm("ARRAY_PTR_UNICITY",
`ARRAY a av1 h ==> ARRAY a av2 h = (av1 = av2)`,
rw[cfHeapsBaseTheory.ARRAY_def] >>
fs[cfHeapsBaseTheory.cell_def] >>
fs[set_sepTheory.one_def, set_sepTheory.SEP_EXISTS] >>
fs[set_sepTheory.STAR_def] >>
fs[set_sepTheory.cond_def] >>
fs[set_sepTheory.SPLIT_def] >>
rw[] >> metis_tac[]
);

val REF_UNICITY = Q.store_thm("REF_UNICITY",
`REF r v1 H ==> REF r v2 H = (v1 = v2)`,
rw[cfHeapsBaseTheory.REF_def] >>
fs[cfHeapsBaseTheory.cell_def] >>
fs[set_sepTheory.one_def, set_sepTheory.SEP_EXISTS] >>
fs[set_sepTheory.STAR_def] >>
fs[set_sepTheory.cond_def] >>
fs[set_sepTheory.SPLIT_def] >>
rw[] >> metis_tac[]
);

(* REPLICATE congruence rules *)
val APPEND_LENGTH_INEQ = Q.store_thm("APPEND_LENGTH_INEQ",
`!l1 l2. LENGTH(l1) <= LENGTH(l1++l2) /\ LENGTH(l2) <= LENGTH(l1++l2)`,
Induct >-(strip_tac >> rw[]) >> rw[]);

val REPLICATE_APPEND_RIGHT = Q.prove(
`a++b = REPLICATE n x ==> ?n'. b = REPLICATE n' x`,
strip_tac >>
`b = DROP (LENGTH a) (a++b)` by simp[GSYM DROP_LENGTH_APPEND] >>
`b = DROP (LENGTH a) (REPLICATE n x)` by POP_ASSUM (fn thm => metis_tac[thm]) >>
`b = REPLICATE (n - (LENGTH a)) x` by POP_ASSUM (fn thm => metis_tac[thm, DROP_REPLICATE]) >>
instantiate);

val REPLICATE_APPEND_LEFT = Q.prove(
`a++b = REPLICATE n x ==> ?n'. a = REPLICATE n' x`,
strip_tac >>
`?n'. b = REPLICATE n' x` by metis_tac[REPLICATE_APPEND_RIGHT] >>
`n >= n'` by rw[]
>-(
    `n' = LENGTH(REPLICATE n' x) /\ n = LENGTH (REPLICATE n x)` by metis_tac[LENGTH_REPLICATE] >>
    `LENGTH(REPLICATE n' x) <= LENGTH(REPLICATE n x)` by metis_tac[APPEND_LENGTH_INEQ] >>
  rw[] ) >>
rw[] >> `REPLICATE n x = REPLICATE (n-n') x ++ REPLICATE n' x` by simp[REPLICATE_APPEND] >>
fs[] >> qexists_tac `n-n'` >> rw[]);

val REPLICATE_APPEND_EXISTS_lem = Q.prove(
`!a b x n. a++b = REPLICATE n x <=> ?p q. a = REPLICATE p x /\ b = REPLICATE q x /\ p + q = n`,
rw[] >> EQ_TAC
  >-(strip_tac >>
     qexists_tac `LENGTH a` >>
     qexists_tac `LENGTH b` >>
     rw[] >-(metis_tac[REPLICATE_APPEND_LEFT, LENGTH_REPLICATE])
     >-(metis_tac[REPLICATE_APPEND_RIGHT, LENGTH_REPLICATE]) >>
`LENGTH(a++b) = n` by metis_tac[LENGTH_REPLICATE] >>
rw[]) >>
rpt strip_tac >>
rw[REPLICATE_APPEND]);

val REPLICATE_APPEND_EXISTS = Q.store_thm("REPLICATE_APPEND_EXISTS",
`!a b x n. a++b = REPLICATE n x <=> ?p q. a = REPLICATE p x /\ b = REPLICATE q x /\ p + q = n /\ LENGTH a = p /\ LENGTH b = q`,
rw[] >> EQ_TAC
  >-(rw[REPLICATE_APPEND_EXISTS_lem]
       >-(rw[LENGTH_REPLICATE])
       >-(rw[LENGTH_REPLICATE]) >>
       rw[LENGTH_REPLICATE]) >>
  rw[REPLICATE_APPEND_EXISTS_lem] >>
  instantiate);

val REPLICATE_APPEND_EXISTS_SYM = Q.store_thm("REPLICATE_APPEND_EXISTS",
`!a b x n. REPLICATE n x = a ++ b <=> ?p q. a = REPLICATE p x /\ b = REPLICATE q x /\ p + q = n /\ LENGTH a = p /\ LENGTH b = q`,
rw[] >> EQ_TAC >-(metis_tac[REPLICATE_APPEND_EXISTS]) >> metis_tac[REPLICATE_APPEND_EXISTS]);

val REPLICATE_APPEND_EQ = Q.store_thm("REPLICATE_APPEND_EQ",
`!x n n1 n2. REPLICATE n x = REPLICATE n1 x ++ REPLICATE n2 x <=> n = n1 + n2`,
rw[] >> EQ_TAC
>-(rw[] >> MP_TAC (SPECL [``REPLICATE n1 x``, ``REPLICATE n2 x``, ``x``, ``n:num``] REPLICATE_APPEND_EXISTS_SYM) >> rw[LENGTH_REPLICATE]) >>
rw[GSYM REPLICATE_APPEND]);

val LIST_REL_RIGHT_congr_recip = Q.prove(
`!R. LIST_REL R (a ++ b) x ==> ?a' b'. LIST_REL R a a' /\ LIST_REL R b b' /\ x = a' ++ b'`,
rpt strip_tac >>
qexists_tac `TAKE (LENGTH a) x` >>
qexists_tac `DROP (LENGTH a) x` >>
rw[] >>
(mp_tac ((Thm.INST [``P:'a->'b->bool`` |-> ``R:'a->'b->bool``] LIST_REL_APPEND_IMP) |> SPECL [``a:'a list``, ``TAKE (LENGTH a) x:'b list``, ``b:'a list``, ``DROP (LENGTH a) x:'b list``]) >>
SIMP_TAC list_ss [] >>
`LENGTH a <= LENGTH x` by rw[APPEND_LENGTH_INEQ]
>-(
   `LENGTH a <= LENGTH (a ++ b)` by rw[] >>
   `LENGTH (a ++ b) = LENGTH x` by metis_tac[LIST_REL_LENGTH] >>
   metis_tac[LIST_REL_LENGTH]
) >>
rw[]));

val LIST_REL_RIGHT_congr_imp = Q.prove(`!R. (?a' b'. LIST_REL R a a' /\ LIST_REL R b b' /\ x = a' ++ b') ==> LIST_REL R (a ++ b) x`,
metis_tac[rich_listTheory.EVERY2_APPEND_suff]);

val LIST_REL_RIGHT_congr = Q.store_thm("LIST_REL_RIGHT_congr",
`!R. LIST_REL R (a ++ b) x <=> ?a' b'. LIST_REL R a a' /\ LIST_REL R b b' /\ x = a' ++ b'`,
metis_tac[LIST_REL_RIGHT_congr_recip, LIST_REL_RIGHT_congr_imp]);


val LIST_REL_LEFT_congr_recip = Q.prove(
`!R. LIST_REL R x (a ++ b) ==> ?a' b'. LIST_REL R a' a /\ LIST_REL R b' b /\ x = a' ++ b'`,
rpt strip_tac >>
qexists_tac `TAKE (LENGTH a) x` >>
qexists_tac `DROP (LENGTH a) x` >>
rw[] >>
(mp_tac ((Thm.INST [``P:'a->'b->bool`` |-> ``R:'a->'b->bool``] LIST_REL_APPEND_IMP) |> SPECL [``TAKE (LENGTH a) x:'a list``, ``a:'b list``, ``DROP (LENGTH a) x:'a list``, ``b:'b list``]) >>
SIMP_TAC list_ss [] >>
`LENGTH a <= LENGTH x` by rw[APPEND_LENGTH_INEQ]
>-(
   `LENGTH a <= LENGTH (a ++ b)` by rw[] >>
   `LENGTH (a ++ b) = LENGTH x` by metis_tac[LIST_REL_LENGTH] >>
   metis_tac[LIST_REL_LENGTH]
) >>
rw[]
));

val LIST_REL_LEFT_congr_imp = Q.prove(
`!R. (?a' b'. LIST_REL R a' a /\ LIST_REL R b' b /\ x = a' ++ b') ==> LIST_REL R x (a ++ b)`,
metis_tac[rich_listTheory.EVERY2_APPEND_suff]);

val LIST_REL_LEFT_congr = Q.store_thm("LIST_REL_LEFT_congr",
`!R. LIST_REL R x (a ++ b) <=> ?a' b'. LIST_REL R a' a /\ LIST_REL R b' b /\ x = a' ++ b'`,
metis_tac[LIST_REL_LEFT_congr_recip, LIST_REL_LEFT_congr_imp]);

(* Congruence rules to rewrite the refinement invariants *)
fun eqtype_unicity_thm_tac x =
  let
      val assum = MP (SPEC ``abs:'a -> v -> bool`` EqualityType_def |> EQ_IMP_RULE |> fst) x
  in
      MP_TAC assum
  end;

val EQTYPE_UNICITY_R = Q.store_thm("EQ_UNICITY_R",
`!abs x y1 y2. EqualityType abs ==> abs x y1 ==> (abs x y2 <=> y2 = y1)`,
rpt strip_tac >> FIRST_ASSUM eqtype_unicity_thm_tac >> metis_tac[]);

val EQTYPE_UNICITY_L = Q.store_thm("EQ_UNICITY_R",
`!abs x1 x2 y. EqualityType abs ==> abs x1 y ==> (abs x2 y <=> x2 = x1)`,
rpt strip_tac >> FIRST_ASSUM eqtype_unicity_thm_tac >> metis_tac[]);

fun generate_refin_invariant_thms conj_eq_type_thms =
  let
      fun thm_strip_conj th =
	let
	    val (th1, r_conj) = (CONJUNCT1 th, CONJUNCT2 th)
	    val conjuncts = thm_strip_conj r_conj
	in
	    th1::conjuncts
	end
	handle _ => [th]
      fun get_ref_inv th = concl th |> dest_comb |> snd
      fun get_types ref_inv =
	let
	    val [t1,t'] = type_of ref_inv |> dest_type |> snd
	    val [t2, _] = dest_type t' |> snd
	in
	    (t1, t2)
	end
      fun gen_left_rule eq_type_thm =
	let
	    val ref_inv = get_ref_inv eq_type_thm
	    val (t1, t2) = get_types ref_inv
	    val th1 = Thm.INST_TYPE [``:'a`` |-> t1, ``:'b`` |-> t2] EQTYPE_UNICITY_L
	    val th2 = SPEC ref_inv th1
	    val (x1, x2, y) = (mk_var("x1", t1), mk_var("x2", t1), mk_var("y", t2))
	    val th3 = SPECL [x1, x2, y] th2
	    val th4 = MP th3 eq_type_thm
	    val th5 = GENL [x1, x2, y] th4
	in
	    th4
	end
      fun gen_right_rule eq_type_thm =
	let
	    val ref_inv = get_ref_inv eq_type_thm
	    val (t1, t2) = get_types ref_inv
	    val th1 = Thm.INST_TYPE [``:'a`` |-> t1, ``:'b`` |-> t2] EQTYPE_UNICITY_R
	    val th2 = SPEC ref_inv th1
	    val (x, y1, y2) = (mk_var("x", t1), mk_var("y1", t2), mk_var("y2", t2))
	    val th3 = SPECL [x, y1, y2] th2
	    val th4 = MP th3 eq_type_thm
	    val th5 = GENL [x, y1, y2] th4
	in
	    th5
	end
      val eq_type_thms = List.concat(List.map thm_strip_conj conj_eq_type_thms)
      val left_rules = List.map gen_left_rule eq_type_thms
      val right_rules = List.map gen_right_rule eq_type_thms
  in
      List.concat [left_rules, right_rules]
  end;


val RECONSTRUCT_INT = Q.store_thm("RECONSTRUCT_INT", `v = (Litv (IntLit i)) <=> INT i v`, rw[INT_def]);
val RECONSTRUCT_NUM = Q.store_thm("RECONSTRUCT_NUM", `v = (Litv (IntLit (&n))) <=> NUM n v`, rw[NUM_def, INT_def]);
val RECONSTRUCT_BOOL = Q.store_thm("RECONSTRUCT_BOOL", `v = Boolv b <=> BOOL b v`, rw[BOOL_def]);

val NUM_INT_EQ = Q.store_thm("NUM_INT_EQ",
`(!x y v. INT x v ==> (NUM y v <=> x = &y)) /\
(!x y v. NUM y v ==> (INT x v <=> x = &y)) /\
(!x v w. INT (&x) v ==> (NUM x w <=> w = v)) /\
(!x v w. NUM x v ==> (INT (&x) w <=> w = v))`,
fs[INT_def, NUM_def] >> metis_tac[]);

val refin_invariant_thms = NUM_INT_EQ::(generate_refin_invariant_thms [EqualityType_NUM_BOOL]);

(* Build the inverse defs for the refinement invariants *)
val refin_invariant_defs = [NUM_def, INT_def, BOOL_def, UNIT_TYPE_def];
val refin_invariant_invert_defs = (List.map GSYM refin_invariant_defs)
				  @ [RECONSTRUCT_BOOL, RECONSTRUCT_INT, RECONSTRUCT_NUM];
val refin_inv_rewrite_thms = List.concat [refin_invariant_thms, refin_invariant_invert_defs]

val rewrite_thms = [integerTheory.INT_ADD,
		  int_num_convert_times,
		  int_num_convert_ge,
		  int_num_convert_great,
		  int_num_convert_eq,
		  int_num_convert_less,
		  int_num_convert_le,
		  int_num_convert_subs,
		  LENGTH_NIL,
		  LENGTH_NIL_SYM,
		  REPLICATE_APPEND_EQ
];
val match_thms = List.concat [rewrite_thms, refin_inv_rewrite_thms];
val match_defs = refin_invariant_defs;

(* [auto_cf_tac] *)
val (no_exists_tac : tactic) =
 fn (g as (asl, w)) =>
    if is_exists w then raise (ERR "no_exists_tac" "The goal begins with an existential operator")
    else all_tac g;

val auto_cf_tac = rpt (FIRST [xapp, xlit, xcon, xvar, xmatch, xif, xraise]) >> rw match_defs >> fs match_defs >> xsimpl;

(* This tactic is used in xlet_match_pre_conditions to automatically instantiate
   the variables found in the app specification. If xlet_auto or xlet_find_auto
   raises an exception stating that it was 'Unable to perform the matching', then
   changing this tactic might solve the problem. *)
val xlet_auto_inst_tac =
    (FIRST[
	  rw all_match_thms >>
	  fs all_match_thms >>
	  FIRST [instantiate >> rw[], all_tac] >>
	  no_exists_tac >>
	  rw[]
    ]);

(* This tactic is used in xlet_find_ptrs_eq_classes to find the equivalence classes
   for the variables *)
val xlet_auto_match_tac = (rw all_match_thms >>
			      fs all_match_thms >>
			      rw all_match_thms);

(* [xlet_find_auto] *)
val xlet_find_auto = xlet_find_auto_aux xlet_auto_inst_tac xlet_auto_match_tac;

(* [xlet_auto] *)
val (xlet_auto : tactic) = xlet_auto_aux xlet_auto_inst_tac xlet_auto_match_tac;

(* [xauto_tac] *)
val xauto_tac_aux = MAP_FIRST (fn t => CHANGED_TAC t)
	[auto_cf_tac,
	 fs[BOOL_def, INT_def, NUM_def, UNIT_TYPE_def, LIST_REL_def],
	 fs[LIST_REL_LENGTH, REPLICATE, LENGTH_REPLICATE],
	 fs match_thms,
	 numLib.ARITH_TAC,
	 xlet_auto];

val xauto_tac = rpt xauto_tac_aux;


(*******************************************************************************************)
(**** DEBUG materiel: functions to produce the matching goal of the xlet_auto tactic********)
(*******************************************************************************************)
fun xlet_match_asl_debug (inst_tac:tactic) origin_asl target_asl =
  let
      (* Retrieve the lists/sets of free variables *)
      val kwn_varset = FVL origin_asl empty_varset
      val target_varset = FVL target_asl empty_varset
      val all_varset = HOLset.union (kwn_varset, target_varset)
      val all_varsl = HOLset.listItems all_varset
      val unkwn_varset = HOLset.difference (target_varset, kwn_varset)
      val unkwn_varsl = HOLset.listItems unkwn_varset

      (* Build the big "goal" formula *)
      val unkwn_vars_types = List.map (fn v => type_of v) unkwn_varsl
      val synthPredsTypeL = unkwn_vars_types
      val synthPredType = list_mk_fun synthPredsTypeL ``:bool``
      val synthPredVar = mk_var ("synthP", synthPredType) |> variant all_varsl
      val synthPred = list_mk_comb (synthPredVar, unkwn_varsl)
      val open_goal_formula = list_mk_conj (List.rev (synthPred::target_asl))
      val close_goal_formula = list_mk_exists (unkwn_varsl, open_goal_formula)
      val matching_goal = (origin_asl, close_goal_formula)
  in
      matching_goal
  end;

fun xlet_match_pre_conditions_debug (inst_tac:tactic) asl let_pre app_asl app_pre app_post =
  let
      (* Determine the known variables (given by the assumptions)
    and the unknown ones (given by the app specification - they need
    to be instantiated *)
      val kwn_varset = FVL (let_pre::asl) empty_varset
      val app_varset = FVL (app_pre::app_post::app_asl) empty_varset
      val unkwn_varset = HOLset.difference (app_varset, kwn_varset)
      val unkwn_varsl = HOLset.listItems unkwn_varset

      (* Decompose the pre/post conditions *)
      val varset1 = HOLset.union (unkwn_varset, kwn_varset)
      val varsl1 = HOLset.listItems varset1
      val (pre_ex_vl, pre_hpl, pre_pfl) =
          dest_heap_condition (varsl1, let_pre)
      val varsl2 = List.concat [varsl1, pre_ex_vl]
      val (app_pre_ex_vl, app_pre_hpl, app_pre_pfl) =
          dest_heap_condition (varsl2, app_pre)

      (*
       * Match the pre-conditions to instantiate the unknown variables
       *)
      (* Transform the heap predicates to predicates *)
      val varsl3 = List.concat [varsl2, app_pre_ex_vl]
      val H_tm = variant varsl3 ``H:heap``
      val transf_pre_hpl = List.map (fn x => mk_comb (x, H_tm)) pre_hpl
      val transf_app_pre_hpl = List.map (fn x => mk_comb (x, H_tm)) app_pre_hpl

      (* Perform the matching *)
      val origin_asl = List.concat [asl, transf_pre_hpl, pre_pfl, [``emp ^H_tm``]]
      val target_asl = List.concat [app_asl, transf_app_pre_hpl, app_pre_pfl]
  in
      xlet_match_asl_debug inst_tac origin_asl target_asl
  end;

fun xlet_post_condition_from_app_spec_debug inst_tac match_tac env asl app_info let_pre post app_asl app_concl  =
  let
      (* Apply the parameters given in the let expression *)
      val (app_asl, app_pre, app_post) =
	  xlet_subst_parameters env app_info asl let_pre app_asl app_concl

  in
      (* Match the let pre-condition and the app specification *)
      xlet_match_pre_conditions_debug inst_tac asl let_pre app_asl app_pre app_post
  end;

fun xlet_app_auto_debug inst_tac match_tac app_info env let_pre post (g0 as (asl, w)) =
  let
      (* Find the specification *)
      val specH = xlet_find_spec g0

      (* Split the conclusion from the assumptions in the app specification *)
      val (app_asl, app_concl) = xlet_dest_app_spec asl let_pre specH
						   
      (* Apply the parameters given in the let expression *)
  in
      xlet_post_condition_from_app_spec_debug
	  inst_tac match_tac env asl app_info let_pre post app_asl app_concl
  end;

val xlet_auto_aux = fn inst_tac => fn match_tac => fn (g as (asl, w)) =>
		       let
			   val (goal_op, goal_args) = strip_comb w
			   val let_expr = List.nth (goal_args, 1)
			   val env = List.nth (goal_args, 3)
			   val pre = List.nth (goal_args, 4)
			   val post = List.nth (goal_args, 5)
		       in
			   xlet_app_auto_debug inst_tac match_tac let_expr env pre post g
		       end;

val generate_msg = xlet_auto_aux;
val generate_msg_auto = xlet_auto_aux xlet_auto_inst_tac xlet_auto_match_tac;

(*****************************************************************)
(********************** SPECIFICATIONS ***************************)
(*****************************************************************)

val st = get_ml_prog_state();

val empty_queue_spec = Q.store_thm ("empty_queue_spec",
    `!uv. app (p:'ffi ffi_proj) ^(fetch_v "empty_queue" st) [uv]
          emp (POSTv qv. QUEUE A [] qv)`,
    xcf "empty_queue" st \\
    xlet `POSTv uv. &UNIT_TYPE () uv` >- (xcon >> xsimpl) \\
    xlet `POSTv av. ARRAY av []` THEN1(xapp \\ fs[]) \\
    xlet `POSTv pv. SEP_EXISTS av iv.
      &(pv = Conv NONE [av; iv]) * ARRAY av [] * &NUM 0 iv`
    THEN1(xcon \\ xsimpl) \\
    xapp \\ simp[QUEUE_def] \\ xsimpl
);

val empty_queue_spec = Q.store_thm ("empty_queue_spec",
    `!uv. app (p:'ffi ffi_proj) ^(fetch_v "empty_queue" st) [uv]
          emp (POSTv qv. QUEUE A [] qv)`,
    xcf "empty_queue" st >>
    xlet_auto >- auto_cf_tac >>
    xlet_auto >- auto_cf_tac >>
    xlet_auto >- auto_cf_tac >>
    simp[QUEUE_def] >> auto_cf_tac
);

val (ptrs_tac:tactic) =
    (fs[cfHeapsBaseTheory.ARRAY_def, cfHeapsBaseTheory.REF_def] >>
       fs[cfHeapsBaseTheory.cell_def] >>
       fs[set_sepTheory.one_def, set_sepTheory.SEP_EXISTS] >>
       fs[set_sepTheory.STAR_def] >>
       fs[set_sepTheory.cond_def] >>
       fs[set_sepTheory.SPLIT_def] >>
       rw[] >> fs[]);

(***** Interesting examples for automatic solving *******)
(* Example 1 *)
val extm1 = ``?(mid:'a list). LENGTH mid = LENGTH (junk:'a list) /\ mid = REPLICATE (LENGTH mid) (xv:'a)``;
val exg1 = ([]:term list, extm1);
(* Failure *)
bossLib.DECIDE extm1;
(* Success *)
SIMP_CONV (list_ss ++ QUANT_INST_ss []) [] extm1;

(* Example 2 *)
val extm2 =
``?(mid:'a list) (afr:'a list). LENGTH mid = LENGTH (junk:'a list) /\ LENGTH afr = LENGTH mid + n /\ mid = REPLICATE (LENGTH mid) xv /\ afr = REPLICATE (LENGTH afr) xv``;
(* Success *)
SIMP_CONV (list_ss ++ QUANT_INST_ss []) [] extm2;

(* Example 3 *)
val extm3 =
``?(mid:'a list) (afr:'a list). LENGTH mid = LENGTH (junk:'a list) /\ LENGTH afr + LENGTH mid = n /\ mid = REPLICATE (LENGTH mid) xv /\ afr = REPLICATE (LENGTH afr) xv``;
(* Partial success *)
val extm4 = SIMP_CONV (list_ss ++ QUANT_INST_ss []) [] extm3;
(* Not better *)
val extm5 = SIMP_CONV (list_ss ++ EXPAND_QUANT_INST_ss [num_qp]) [] extm3;
val extm6 = SIMP_CONV (arith_ss ++ EXPAND_QUANT_INST_ss [num_qp]) [lem1] extm3;

(* The push spec without automation *)  
val push_spec = Q.store_thm ("push_spec",
    `!qv xv vs x. app (p:'ffi ffi_proj) ^(fetch_v "push" st) [qv; xv]
          (QUEUE A vs qv * & A x xv)
	  (POSTv uv. QUEUE A (vs ++ [x]) qv)`,
    xcf "push" st >>
    simp[QUEUE_def] >>
    xpull >>
    xlet `POSTv qr. & (qr = (Conv NONE [av; iv]))
	* qv ~~> Conv NONE [av; iv] * ARRAY av (vvs ++ junk)`
    >- (xapp >> xsimpl) >>
    xmatch >>
    xlet `POSTv v. &NUM (LENGTH (vvs ++ junk)) v
	* qv ~~> Conv NONE [av; iv]  * ARRAY av (vvs ++ junk)`
    >- (auto_cf_tac1) >>
    xlet `POSTv cb. &BOOL ((LENGTH vs) >= (LENGTH junk + LENGTH vvs)) cb
	* qv ~~> Conv NONE [av; iv] * ARRAY av (vvs ++ junk)`
    >- (xapp >> fs[NUM_def, INT_def, BOOL_def] >> xsimpl >> intLib.COOPER_TAC) >>
    xif
    >- (
       imp_res_tac LIST_REL_LENGTH >> fs[] >> `LENGTH junk = 0` by decide_tac >>
       xlet `POSTv nlv. & NUM (2* (LENGTH vs)) nlv
		* qv ~~> Conv NONE [av; iv] * ARRAY av (vvs ++ junk)`
       >- (xapp >> fs[NUM_def, INT_def] >> xsimpl) >>
       xlet `POSTv nlv. & NUM (2* (LENGTH vs) + 1) nlv
		* qv ~~> Conv NONE [av; iv] * ARRAY av (vvs ++ junk)`
       >- (xapp >> fs[INT_def, NUM_def] >> xsimpl >> fs[integerTheory.INT_ADD]) >>
       xlet `POSTv nav. ARRAY nav (REPLICATE (2 * LENGTH vvs + 1) xv)
		* qv ~~> Conv NONE [av; iv] * ARRAY av (vvs ++ junk)`
       >-(xapp >> xsimpl >> instantiate) >>
       xlet `POSTv uv. ARRAY nav (vvs ++ (REPLICATE (LENGTH vvs + 1) xv))
		* qv ~~> Conv NONE [av; iv] * ARRAY av (vvs ++ junk)`
       >-(
	  xapp >> xsimpl >> fs[LENGTH_NIL, LENGTH_NIL_SYM] >>
	  `2 * LENGTH vvs = LENGTH vvs + LENGTH vvs` by simp[] >>
	  pop_assum SUBST1_TAC >>
	  fs[GSYM REPLICATE_APPEND, LENGTH_REPLICATE]
	  ) >>
       xlet `POSTv niv. &NUM ((LENGTH vvs)+1) niv
		* ARRAY nav (vvs ++ REPLICATE (LENGTH vvs + 1) xv)
		* qv ~~> Conv NONE [av; iv] * ARRAY av (vvs ++ junk)`
       >-(
	  xapp >> xsimpl >> fs[NUM_def] >> instantiate >>
	  fs[integerTheory.INT_ADD]
	) >>
       xlet `POSTv ftv. ARRAY nav (vvs ++ REPLICATE (LENGTH vvs + 1) xv)
		* &(ftv = (Conv NONE [nav;niv])) *  qv ~~> Conv NONE [av; iv]
		* ARRAY av (vvs ++ junk)`
	>-(xcon >> xsimpl) >>
	xapp >> xsimpl >> fs[NUM_def] >>
	rpt strip_tac >>
	qexists_tac `vvs ++ [xv]` >>
	fs[LIST_REL_def] >>
	qexists_tac `REPLICATE (LENGTH vvs) xv` >>
	`LENGTH vvs + 1 = (SUC (LENGTH vvs))`by intLib.ARITH_TAC >>
	pop_assum SUBST1_TAC >>
	fs[REPLICATE]
	) >> 
    xlet `POSTv uv. SEP_EXISTS junk'. qv ~~> Conv NONE [av; iv]
        * ARRAY av (vvs ++ [xv] ++ junk')`
    >-(
	xapp >> xsimpl >> instantiate >>
	rpt strip_tac >>
        `LENGTH vs = LENGTH vvs` by metis_tac[LIST_REL_LENGTH] >>
        `(LENGTH junk) > 0` by intLib.ARITH_TAC >>
	Cases_on `junk`
        >-(irule FALSITY >> fs[LENGTH]) >>
	qexists_tac `t` >>
	rw[lupdate_append2]
    ) >>
    xlet `POSTv niv. &NUM (LENGTH vs + 1) niv * qv ~~> Conv NONE [av; iv]
	* ARRAY av (vvs ++ [xv] ++ junk')`
    >-(
	xapp >> fs[NUM_def, INT_def, BOOL_def]  >>  xsimpl >>
	fs[integerTheory.INT_ADD]
    ) >>
    xlet `POSTv np. &(np = Conv NONE [av; niv]) * qv ~~> Conv NONE [av; iv]
	* ARRAY av (vvs ++ [xv] ++ junk')`
    >-(xcon >> xsimpl) >>
    xapp >> xsimpl >>
    rpt strip_tac >>
    qexists_tac `vvs ++ [xv]` >>
    qexists_tac `junk'` >>
    fs[APPEND]
);

val push_spec = Q.store_thm ("push_spec",
    `!qv xv vs x. app (p:'ffi ffi_proj) ^(fetch_v "push" st) [qv; xv]
          (QUEUE A vs qv * & A x xv)
	  (POSTv uv. QUEUE A (vs ++ [x]) qv)`,
  xcf "push" st >>
  fs[QUEUE_def] >>
  xpull >>
  xauto_tac
  (* 3 subgoals *)
  >-(
     xlet `POSTv v.
     ARRAY av' (vvs ++ junk ++ REPLICATE (LENGTH junk + LENGTH vvs +1) xv) *
     ARRAY av (vvs ++ junk) *
     qv ~~> Conv NONE [av; Litv (IntLit (&LENGTH vs))]`
     >-(
	  xauto_tac >> qexists_tac `REPLICATE (LENGTH junk + LENGTH vvs) xv` >>
          fs[REPLICATE_APPEND_EXISTS, LENGTH_REPLICATE] >>
	  SIMP_TAC (list_ss ++ QUANT_INST_ss []) [] >> fs[LENGTH_REPLICATE] >>
	  qexists_tac `REPLICATE (LENGTH junk + LENGTH vvs + 1) xv` >>
	  rw[]
      ) >>
     xauto_tac >>
     qexists_tac `vvs ++ [xv]` >>
     qexists_tac `REPLICATE (LENGTH junk + LENGTH vvs) xv` >>
     rw[] >> fs[LIST_REL_LENGTH] >> fs[int_num_convert_ge] >>
     (* fs and rw don't work??? *)
     `LENGTH vvs = LENGTH vs` by metis_tac[LIST_REL_LENGTH] >>
     `LENGTH junk = 0` by  bossLib.DECIDE_TAC >>
     fs[LENGTH_NIL] >>
     `LENGTH vs + 1 = SUC (LENGTH vs)` by rw[] >>
     metis_tac[REPLICATE]
    )
  >-(
     qexists_tac `vvs ++ [xv]` >>
     qexists_tac `DROP 1 junk` >>
     fs[int_num_convert_eq, int_num_convert_add, int_num_convert_ge] >>
     `LENGTH vs = LENGTH vvs` by metis_tac[LIST_REL_LENGTH] >>
     `LENGTH vvs < LENGTH junk + LENGTH vvs` by rw[] >>
     `LENGTH junk > 0` by rw[]  >>
     Cases_on `junk` >-(fs[int_num_convert_ge]) >>
     fs[NUM_def, INT_def] >>
     rw[] >>
     rw[lupdate_append2]
  ) >>
  computeLib.EVAL_TAC
);

(* Preparation of push_spec *)
val EmptyQueue_exn_def = Define`
  EmptyQueue_exn v = (v = Conv (SOME ("EmptyQueue", TypeExn (Short "EmptyQueue"))) [])`;

val eq_num_v_thm =
  mlbasicsProgTheory.eq_v_thm
  |> DISCH_ALL
  |> C MATCH_MP (EqualityType_NUM_BOOL |> CONJUNCT1);

(* Pop spec without automation *)
val pop_spec = Q.store_thm("pop_spec",
  `∀qv.
   app (p:'ffi ffi_proj) ^(fetch_v "pop" st) [qv]
     (QUEUE A vs qv)
     (POST (λv. &(¬NULL vs ∧ A (LAST vs) v) * QUEUE A (FRONT vs) qv)
           (λe. &(NULL vs ∧ EmptyQueue_exn e) * QUEUE A vs qv))`,
  xcf "pop" st \\
  simp[QUEUE_def] >> xpull >>
  qmatch_abbrev_tac`_ _ frame _` \\
  xlet `POSTv qr. & (qr = (Conv NONE [av; iv])) * frame`
  >- ( xapp \\ simp[Abbr`frame`] \\ xsimpl ) \\
  xmatch \\
  xlet `POSTv bv. &(BOOL (LENGTH vs = 0) bv) * frame`
  >- (
    xapp_spec eq_num_v_thm \\
    xsimpl \\
    instantiate ) \\
  xif
  >- (
    xlet `POSTv ev. &EmptyQueue_exn ev * frame`
    >- (
      xcon
      \\ xsimpl
      \\ simp[EmptyQueue_exn_def] ) \\
    xraise \\
    xsimpl \\
    fs[LENGTH_NIL,NULL_EQ,Abbr`frame`] \\
    xsimpl) \\
  xlet `POSTv niv. &(NUM (LENGTH vs - 1) niv) * frame`
  >- (
    xapp
    \\ xsimpl
    \\ fs[NUM_def]
    \\ instantiate
    \\ simp[integerTheory.INT_SUB] )
  \\ xlet `POSTv xv. &(A (LAST vs) xv) * frame`
  >- (
    xapp
    \\ xsimpl
    \\ simp[Abbr`frame`]
    \\ xsimpl
    \\ instantiate
    \\ imp_res_tac LIST_REL_LENGTH
    \\ simp[]
    \\ `vs ≠ [] ∧ vvs ≠ []` by (rpt strip_tac \\ fs[])
    \\ `vvs = FRONT vvs ++ [LAST vvs]` by simp[APPEND_FRONT_LAST]
    \\ pop_assum SUBST1_TAC
    \\ simp[EL_APPEND1,EL_APPEND2]
    \\ imp_res_tac list_rel_lastn
    \\ pop_assum(qspec_then`1`mp_tac)
    \\ simp[LASTN_1] ) \\
  xlet `POSTv niv2. &(NUM (LENGTH vs - 1) niv2) * frame`
  >- (
    xapp
    \\ xsimpl
    \\ fs[NUM_def]
    \\ instantiate
    \\ simp[integerTheory.INT_SUB] ) \\
  xlet `POSTv pv. &(pv = Conv NONE [av; niv2]) * frame`
  >- ( xcon \\ xsimpl ) \\
  xlet `POSTv uv. qv ~~> pv * ARRAY av (vvs ++ junk)`
  >- (
    xapp
    \\ simp[Abbr`frame`]
    \\ xsimpl ) \\
  xvar
  >- (
    xsimpl
    \\ fs[NULL_EQ,LENGTH_NIL,LENGTH_FRONT,PRE_SUB1]
    \\ qexists_tac`FRONT vvs`
    \\ qexists_tac`[LAST vvs] ++ junk`
    \\ `vvs ≠ []` by (rpt strip_tac \\ fs[])
    \\ simp[APPEND_FRONT_LAST]
    \\ fs[LIST_REL_FRONT_LAST] )
  \\ fs[NULL_EQ,LENGTH_NIL]
  \\ xsimpl);

(* Pop spec with xlet_auto *)
val pop_spec = Q.store_thm("pop_spec",
  `∀qv.
   app (p:'ffi ffi_proj) ^(fetch_v "pop" st) [qv]
     (QUEUE A vs qv)
     (POST (λv. &(¬NULL vs ∧ A (LAST vs) v) * QUEUE A (FRONT vs) qv)
           (λe. &(NULL vs ∧ EmptyQueue_exn e) * QUEUE A vs qv))`,
  xcf "pop" st >>
  simp[QUEUE_def] >>
  xpull >>
  xlet_auto
  >-(xsimpl >> fs all_match_thms) >> 
  xmatch >>
  rw[]
  >-(xlet `POSTv bv. &(BOOL (LENGTH vs = 0) bv) *
     qv ~~> Conv NONE [av; Litv (IntLit (&LENGTH vs))] * ARRAY av (vvs ++ junk)`
     >-(xapp_spec eq_num_v_thm >> xsimpl) >>
     xif
     >-(
	xlet_auto
	>-(xcon \\ xsimpl) >>
	xraise >>
	xsimpl >>
	fs[LENGTH_NIL,NULL_EQ, EmptyQueue_exn_def]
      ) >>
      xlet_auto
      >-(
	 xsimpl
	 >> fs[NUM_def]
	 >> instantiate
      )>>
      xlet_auto
      >-(
	  xsimpl
	  >> fs all_match_thms
	  (* Some work done by hand *)
	  >> imp_res_tac LIST_REL_LENGTH
	  >> simp[]
	  >> `vs ≠ [] ∧ vvs ≠ []` by (rpt strip_tac \\ fs[])
	  >> `vvs = FRONT vvs ++ [LAST vvs]` by simp[APPEND_FRONT_LAST]
	  >> pop_assum SUBST1_TAC
	  >> simp[EL_APPEND1,EL_APPEND2]
	  (*------------------------*)
      ) >>
      xlet_auto
      >-(xsimpl >> fs[NUM_def]) >>
      xlet_auto
      >- ( xcon \\ xsimpl ) \\
      xlet_auto
      >-(xsimpl) >>
      xvar
      >-(
	  xsimpl
	  >> fs[NULL_EQ,LENGTH_NIL,LENGTH_FRONT,PRE_SUB1]
	  (* *)
	  >> qexists_tac`FRONT vvs`
	  >> qexists_tac`[LAST vvs] ++ junk`
	  >> `vvs ≠ []` by (rpt strip_tac \\ fs[])
	  >> simp[APPEND_FRONT_LAST]
	  >> `LENGTH vvs <> 0` by metis_tac[LENGTH_NIL]
	  >> imp_res_tac LIST_REL_LENGTH
	  >> `LENGTH vs - 1 < LENGTH vvs` by bossLib.DECIDE_TAC
	  >> fs[EL_APPEND1]
	  >> fs[LIST_REL_FRONT_LAST]
	  >> fs[LAST_EL]
	  >> fs[INT_def]
	  >> fs all_match_thms
	  >> ` PRE(LENGTH vvs) = LENGTH vvs - 1` by rw[]
	  >> POP_ASSUM (fn x => fs[x])
      ) >>
      xsimpl
      >> fs[NULL_EQ,LENGTH_NIL]
      ) >>
  computeLib.EVAL_TAC
);

(* Pop spec with xauto_tac *)
val pop_spec = Q.store_thm("pop_spec",
  `∀qv.
   app (p:'ffi ffi_proj) ^(fetch_v "pop" st) [qv]
     (QUEUE A vs qv)
     (POST (λv. &(¬NULL vs ∧ A (LAST vs) v) * QUEUE A (FRONT vs) qv)
           (λe. &(NULL vs ∧ EmptyQueue_exn e) * QUEUE A vs qv))`,
  xcf "pop" st >>
  simp[QUEUE_def, EmptyQueue_exn_def] >>
  xpull >>
  xauto_tac
  >-(xlet `POSTv bv. &(BOOL (LENGTH vs = 0) bv) *
  qv ~~> Conv NONE [av; Litv (IntLit (&LENGTH vs))] * ARRAY av (vvs ++ junk)`
  >-(xapp_spec eq_num_v_thm >> xsimpl) >>
  xauto_tac
  (* 5 subgoals: here the first 3 can be solved with the same tactics *)
  >> imp_res_tac LIST_REL_LENGTH
  >> simp[]
  >> `vs ≠ [] ∧ vvs ≠ []` by (rpt strip_tac \\ fs[])
  >> `vvs = FRONT vvs ++ [LAST vvs]` by simp[APPEND_FRONT_LAST]
  >> pop_assum SUBST1_TAC
  >> simp[EL_APPEND1,EL_APPEND2]
  (* Remaining 2 subgoals *)
  >-(
      fs[NULL_EQ,LENGTH_NIL,LENGTH_FRONT,PRE_SUB1]
      >> qexists_tac`FRONT vvs`
      >> qexists_tac`[LAST vvs] ++ junk`
      >> `vvs ≠ []` by (rpt strip_tac \\ fs[])
      >> simp[APPEND_FRONT_LAST]
      >> `LENGTH vvs <> 0` by metis_tac[LENGTH_NIL]
      >> imp_res_tac LIST_REL_LENGTH
      >> `LENGTH vs - 1 < LENGTH vvs` by bossLib.DECIDE_TAC
      >> fs[EL_APPEND1]
      >> fs[LIST_REL_FRONT_LAST]
      >> fs[LAST_EL]
      >> fs[INT_def]
      >> fs all_match_thms
      >> ` PRE(LENGTH vvs) = LENGTH vvs - 1` by rw[]
      >> POP_ASSUM (fn x => fs[x])
  ) >>
  xsimpl
  >> fs[NULL_EQ,LENGTH_NIL]
  ) >>
computeLib.EVAL_TAC
);
*)
val _ = export_theory ();
