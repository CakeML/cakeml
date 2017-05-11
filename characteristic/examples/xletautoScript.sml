open  preamble ml_progLib ioProgLib ml_translatorLib
	       cfTacticsLib basisFunctionsLib ml_translatorTheory;

val _ = new_theory "queueProg";

val _ = translation_extends"ioProg";

val queue_decls = process_topdecs
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


(**********************)

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

(*********** CF AUTO TAC ***********************)

val ERR = mk_HOL_ERR "son_ho";

val (build_conv_tm, mk_build_conv, dest_build_conv, is_build_conv) = HolKernel.syntax_fns3 "semanticPrimitives" "build_conv";
val (exp2v_tm, mk_exp2v, dest_exp2v, is_exp2v) = HolKernel.syntax_fns2 "cfNormalise" "exp2v";
val (cf_let_tm, mk_cf_let, dest_cf_let, is_cf_let) = s6 "cf_let";

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
fun dest_postv c = dest_binder postv_tm (ERR "dest_heap_condition" "The condition does not begin with a POSTv abstraction") c;

(* [dest_hc_postv]
  Deconstructs the POSTv of a heap condition (if there is) *)
fun dest_hc_postv varsl c =
  let val (postv, c1) =
    let
      val (postv_, c1_) = dest_postv c
      val postv_2 = variant varsl postv_
      val c2_ = Term.subst [postv_ |-> postv_2] c1_
    in
      (SOME postv_2, c2_)
    end
    handle HOL_ERR _ => (NONE, c)
  in
    (postv, c1)
  end;
  
(* [dest_hc_exists]
  Deconstructs the existential quantifiers of a heap condition *)
fun dest_hc_exists varsl c =
  let fun rec_dest varsl lv c =
    if is_sep_exists c then
      let
        val (nv, nc) = dest_sep_exists c
	val nv' = variant varsl nv
	val nc' = Term.subst [nv |-> nv'] nc
	val (nlv, fc) = rec_dest (nv'::varsl)  lv nc'
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

(* dest_hc_star
   Deconstructs a (star) conjunction of heap conditions.
   Splits the conjuntcs between heap conditions and pure facts.
 *)
fun dest_hc_star c =
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
  Deconstructs a heap pre/post condition. Needs to be provided a list of terms
  representing variables to avoid name collision
  Returns:
  - the POSTv variable
  - the list of existentially quantified variables
  - the list of heap pointers used in the heap predicates
  - the list of heap predicates
  - the list of pure facts *)
fun dest_heap_condition varsl c =
  let
    val (postv_v, c1)  = dest_hc_postv varsl c
    val varsl' = case postv_v of SOME v => v::varsl | NONE => varsl
    val (ex_vl, c2) = dest_hc_exists varsl' c1
    val (hpl, pfl) = dest_hc_star c2
    val ptrs = list_heap_ptrs hpl
  in
    (postv_v, ex_vl, ptrs, hpl, pfl)
  end;

(* [mk_postv] *)
fun mk_postv postv_v c = mk_binder postv_tm "mk_postv" (postv_v, c);
  
(* [mk_heap_condition]
   Creates a heap pre/post condition.
   Parameters:
   - the (eventual) POSTv variable
   - the list of existentially quantified variables
   - the list of heap predicates
   - the list of pure facts
*)

fun mk_heap_condition postv_v ex_vl hpl pfl =
  let
    val c1 = list_mk_star hpl ``:hprop``
    val hprop_pfl = List.map (fn x => mk_cond x) pfl
    val c2 = list_mk_star (c1::hprop_pfl) ``:hprop``
    val c3 = list_mk (mk_sep_exists) ex_vl c2
  in
    case postv_v of
    SOME v => mk_postv v c3
    | NONE => c3
  end;

(******** Get the post-condition given by the app specification ***********)
(* [find_spec]
   The code is taken from xspec *)
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

(* [remove_foralls]
   Removes the forall operators from a term. Renames the  bound
   variables so that they are fresh regarding a given list
   of assumptions *)
fun remove_foralls asl spec =
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
      val (_, noquant_spec_tm) = remove_foralls (let_pre::asl) (concl specH)
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
    val (pre_postv_v, pre_ex_vl, pre_ptrs, pre_hpl, pre_pfl) =
          dest_heap_condition varsl1 let_pre
    val varsl2 = List.concat [varsl1, pre_ex_vl,
          case pre_postv_v of SOME v => [v] | NONE => []]
    val (app_pre_postv_v, app_pre_ex_vl, app_pre_ptrs, app_pre_hpl, app_pre_pfl) =
          dest_heap_condition varsl2 app_pre (* Rmk: app_pre_postv_v should be NONE *)

    (*
     * Match the pre-conditions to instantiate the unknown variables
     *)
    (* Transform the heap predicates to predicates *)
    val varsl3 = List.concat [varsl2, app_pre_ex_vl,
			      case app_pre_postv_v of SOME v => [v] | NONE => []]
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
fun xlet_find_ptrs_eq_classes (match_tac : tactic)  asl let_pre_hpl let_pre_pfl =
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
   Removes the predicates from which pointers are members of a given list *)
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
    (* Analyse the app post-condition *)
    val cur_free_varset = FVL (List.concat [asl, let_pre_hpl, let_pre_pfl, [app_post]]) empty_varset
    val cur_free_varsl = HOLset.listItems cur_free_varset
    val (post_postv_v, post_ex_vl, post_ptrs, post_hpl, post_pfl) =
          dest_heap_condition cur_free_varsl app_post

    (* Filter the heap predicates from the let pre-condition *)
    val subst_map = xlet_find_ptrs_eq_classes match_tac asl let_pre_hpl let_pre_pfl
    val filtered_pre_hpl = filter_heap_predicates subst_map let_pre_hpl post_ptrs

    (* Construct the post-condition *)
    val let_heap_condition = mk_heap_condition post_postv_v
            (List.concat [let_pre_ex_vl, post_ex_vl])
	    (List.concat [post_hpl, filtered_pre_hpl])
	    (List.concat [post_pfl, let_pre_pfl])
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
val (match_tac, inst_tac, app_info, env, let_pre, let_post) = (xlet_auto_match_tac, xlet_auto_inst_tac, let_expr, env, pre, post);
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
val xlet_auto_aux = fn inst_tac => fn match_tac =>
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


val empty_list_thm = Q.store_thm("empty_list_thm",
`(!l. LENGTH l = 0 <=> l = []) /\ (!l. 0 = LENGTH l <=> l = [])`,
CONJ_TAC >> rw[LENGTH_NIL] >> `0 = LENGTH l <=> LENGTH l = 0` by rw[] >> rw[LENGTH_NIL]);


(* Unicity results for the value pointed to by a heap pointer *)
val ARRAY_PTR_UNICITY = Q.store_thm("ARRAY_PTR_UNICITY",
`ARRAY a av1 H /\ ARRAY a av2 H <=> ARRAY a av1 H /\ av1 = av2`,
EQ_TAC
>-(
  rw[cfHeapsBaseTheory.ARRAY_def] >>
  fs[cfHeapsBaseTheory.cell_def] >>
  fs[set_sepTheory.one_def, set_sepTheory.SEP_EXISTS] >>
  fs[set_sepTheory.STAR_def] >>
  fs[set_sepTheory.cond_def] >>
  fs[set_sepTheory.SPLIT_def] >>
  rw[] >> fs[]
) >>
rpt (rw[]));

val REF_UNICITY = Q.store_thm("REF_UNICITY",
`REF r v1 H /\ REF r v2 H <=> REF r v1 H /\ v1 = v2`,
EQ_TAC
>-(
  rw[cfHeapsBaseTheory.REF_def] >>
  fs[cfHeapsBaseTheory.cell_def] >>
  fs[set_sepTheory.one_def, set_sepTheory.SEP_EXISTS] >>
  fs[set_sepTheory.STAR_def] >>
  fs[set_sepTheory.cond_def] >>
  fs[set_sepTheory.SPLIT_def] >>
  rw[] >> fs[]
) >>
rpt (rw[]));

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

val LIST_REL_RIGHT_congr = Q.store_thm("LIST_REL_RIGHT_congr",
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

val LIST_REL_LEFT_congr = Q.store_thm("LIST_REL_LEFT_congr",
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

(* Theorems and definitions used by the instantiation and matching tactics *)
val match_defs = [];
val refin_inv_defs = [NUM_def, INT_def, BOOL_def, UNIT_TYPE_def];
val match_thms = [int_num_convert_add, int_num_convert_times, empty_list_thm];
val all_match_thms = List.concat [match_defs, match_thms, refin_inv_defs];

(* [auto_cf_tac] *)
val (no_exists_tac : tactic) =
 fn (g as (asl, w)) =>
    if is_exists w then raise (ERR "no_exists_tac" "The goal begins with an existential operator")
    else all_tac g;

val auto_cf_tac = rpt (FIRST [xapp, xlit, xcon, xvar, xmatch, xif]) >> rw match_defs >> fs match_defs >> xsimpl;

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

(********************** SPECIFICATIONS ***************************)
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

set_trace "types" 0;

val msg1 = generate_msg_auto (top_goal());
val msg2 = xlet_auto_inst_tac msg1 |> #1 |> List.last;
val msg3 = (rw[ARRAY_PTR_UNICITY, REPLICATE_APPEND_EXISTS]) msg2 |> #1 |> List.last;


val msg5 = ([``((&LENGTH (vs :α list)) :int) ≥
  ((&(LENGTH (junk :v list) + LENGTH (vvs :v list))) :int)``,
     ``(A :α -> v -> bool) (x :α) (xv :v)``,
     ``LIST_REL (A :α -> v -> bool) (vs :α list) (vvs :v list)``,
     ``((qv :v) ~~>
   Conv (NONE :(tvarN # tid_or_exn) option)
     [(av :v); Litv (IntLit ((&LENGTH (vs :α list)) :int))]) (H1 :heap)``,
     ``ARRAY (av :v) (((vvs :v list) ++ (junk :v list)) :v list) (H2 :heap)``,
     ``ARRAY (av' :v)
    (REPLICATE
       ((2 :num) * (LENGTH (junk :v list) + LENGTH (vvs :v list)) + (1 :
        num)) (xv :v)) (H3 :heap)``,
     ``emp (H4 :heap)``],
    ``∃(Q1:heap) (afr :v list) (mid :v list).
    ARRAY (av' :v) ((mid ++ afr) :v list) (Q1 :heap) ∧
    LENGTH (junk :v list) + LENGTH (vvs :v list) = LENGTH mid ∧
    (synthP :v list -> v list -> num -> v list reln) afr ([] :v list)
    (0 :num) mid ((vvs ++ junk) :v list) /\ (Q1 = H1 \/ Q1 = H2 \/ Q1 = H3 \/ Q1 = H4)``);

val (ptrs_tac:tactic) =
    (fs[cfHeapsBaseTheory.ARRAY_def, cfHeapsBaseTheory.REF_def] >>
       fs[cfHeapsBaseTheory.cell_def] >>
       fs[set_sepTheory.one_def, set_sepTheory.SEP_EXISTS] >>
       fs[set_sepTheory.STAR_def] >>
       fs[set_sepTheory.cond_def] >>
       fs[set_sepTheory.SPLIT_def] >>
       rw[] >> fs[]);

val msg6 = ptrs_tac msg5 |> #1 |> List.last;
val msg7 = fs[emp_def] msg6 |> #1 |> List.last;
val msg8 = fs[REPLICATE_APPEND_EXISTS] msg7 |> #1 |> List.last;
val msg9 = (rw[] >> fs[]) msg8 |> #1 |> List.last;
val msg10 = SIMP_TAC (list_ss ++ QUANT_INST_ss []) [lem1] msg9
val msg10 = SIMP_TAC (arith_ss ++ QUANT_INST_ss []) [lem1] msg9

		     REV_FULL_SIMP_TAC arith_ss []  msg9


val msg10 = ([]:term list, ``?mid. LENGTH junk = LENGTH mid /\ mid = REPLICATE (LENGTH mid) xv``);
instantiate  msg10;

val msg11 = ([]:term list, ``?mid. LENGTH mid = LENGTH junk /\ mid = REPLICATE (LENGTH mid) xv``);
bossLib.DECIDE ``?(mid:'a list). LENGTH mid = LENGTH (junk:'a list) /\ mid = REPLICATE (LENGTH mid) (xv:'a)``



(** Tests SIMP_CONV **)
SIMP_CONV (list_ss ++ QUANT_INST_ss []) [] ``?(mid:'a list). LENGTH mid = LENGTH (junk:'a list) /\ mid = REPLICATE (LENGTH mid) (xv:'a) /\ A mid``;

SIMP_CONV (list_ss ++ QUANT_INST_ss [implication_concl_qp]) [] ``?(mid:'a list). LENGTH mid = LENGTH (junk:'a list) /\ mid = REPLICATE (LENGTH mid) (xv:'a) /\ A mid``;

val t1 = SIMP_CONV (list_ss ++ QUANT_INST_ss []) [] ``?(mid:'a list) (afr : 'a list). LENGTH (junk:'a list) = LENGTH mid /\ mid = REPLICATE (LENGTH mid) (xv:'a) /\ afr = REPLICATE (LENGTH afr) xv /\ A mid afr /\ LENGTH junk + LENGTH afr = LENGTH mid + LENGTH bsp`` |> concl |> dest_comb |> #2;
val t2 = fs[lem1] ([]:term list, t1) |> #1 |> List.last;
SIMP_TAC (list_ss ++ QUANT_INST_ss []) [lem1] t2;

val lem1 = Q.prove(`!(x:num) y z. x + y = y + z <=> x = z`, rw[]);
val lem2 = Q.prove(`!(x:num) y z. x > 0 ==> x*y = (x-1)*y + y`,
rw[] >> `?x'. x = x' + 1` by rw[] >-(qexists_tac `x-1` >> rw[]) >> rw[]);

SIMP_CONV arith_ss [lem2] ``x + y = 2*y + 3``
`x + y = 2*y + 3 <=> x = y + 3`,
intLib.ARITH_TAC)

`(x:num) + y = 2*y + 3 <=> x = y + 3`,
numLib.ARITH_TAC)
numLib.ARITH_CONV  ``(x:num) + y = 2*y + 3``


SIMP_TAC list_ss [ARRAY_PTR_UNICITY] g1


SIMP_CONV (arith_ss) [] ``∃afr mid.
LENGTH junk + LENGTH vvs = LENGTH mid ∧
synthP afr [] 0 mid (vvs ++ junk) ∧
(y = y' ∧ mid ++ afr = vvs ++ junk ∨
mid = REPLICATE (LENGTH mid) xv ∧ afr = REPLICATE (LENGTH afr) xv ∧
LENGTH afr + LENGTH junk + LENGTH vvs = 2 * (LENGTH junk + LENGTH vvs) + 1)``


DB.find "APPEND" |> DB.find_in "LENGTH"
	  DB.find "LENGTH" |> DB.find_in "TAKE"
DB.find "LIST_REL" |> DB.find_in "LENGTH"
			      

val (g as (asl, w)) = top_goal ();
xlet_find_auto (top_goal ());
mlbasicsProgTheory.deref_spec;
val msg1 = generate_msg_auto (top_goal ());
xlet_auto_inst_tac msg1;
HINT_EXISTS_TAC msg1;

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

(* The push spec with xlet_auto and a bit of auto_cf_tac *)
val push_spec = Q.store_thm ("push_spec",
    `!qv xv vs x. app (p:'ffi ffi_proj) ^(fetch_v "push" st) [qv; xv]
          (QUEUE A vs qv * & A x xv)
	  (POSTv uv. QUEUE A (vs ++ [x]) qv)`,
  xcf "push" st >>
  fs[QUEUE_def] >>
  xpull >>
  xlet_auto >-(auto_cf_tac >> fs[INT_def, NUM_def]) >>
  xmatch >> xsimpl >>
  rw[]
  >- (rpt strip_tac >>
      xlet_auto
      >- (rw[] >> fs[NUM_def] >> xsimpl) >>
      xlet_auto
      >-(fs[BOOL_def, INT_def, NUM_def] >> rw[] >> xsimpl) >>
      xif
      >-(
	   xlet_auto
	   >-(fs[BOOL_def, INT_def, NUM_def] >> rw[] >> xsimpl)>>
	   xlet_auto
	   >-(fs[BOOL_def, INT_def, NUM_def] >> rw[] >> xsimpl) >>
	   xlet_auto
	   >-(auto_cf_tac >> fs all_match_thms) >>
	   (* xlet_auto *)
	   xlet `POSTv v.
           ARRAY av' (vvs ++ junk ++ REPLICATE (LENGTH junk + LENGTH vvs +1) xv) *
           ARRAY av (vvs ++ junk) *
	   qv ~~> Conv NONE [av; Litv (IntLit (&LENGTH vs))]`
           >- (auto_cf_tac >>
	       fs refin_inv_defs >>
	       fs[REPLICATE_APPEND_EXISTS, LENGTH_REPLICATE] >>
	       SIMP_TAC (list_ss ++ QUANT_INST_ss []) [] >> fs[LENGTH_REPLICATE] >>
	       qexists_tac `REPLICATE (LENGTH junk + LENGTH vvs + 1) xv` >>
	       rw[]
	       >-(rw[LENGTH_REPLICATE])
	       >-(rw[LENGTH_REPLICATE]) >>
	       rw[REPLICATE]
	   ) >>
	   (************)
	   xlet_auto
	   >-(fs[BOOL_def, INT_def, NUM_def] >> rw[] >> xsimpl) >>
	   xlet_auto
	   >-(auto_cf_tac) >>
	   auto_cf_tac >> fs[UNIT_TYPE_def, LENGTH_REPLICATE, LIST_REL_def] >>
	   fs[NUM_def, INT_def, integerTheory.INT_ADD] >>
	   (* instantiation *)
	   qexists_tac `vvs ++ [xv]` >>
	   qexists_tac `REPLICATE (LENGTH junk + LENGTH vvs) xv` >>
	   (* ------------- *)
	   rw[] >> fs[LIST_REL_LENGTH] >> fs[int_num_convert_ge] >>
           (* fs and rw don't work??? *)
           `LENGTH vvs = LENGTH vs` by metis_tac[LIST_REL_LENGTH] >>
           `LENGTH junk = 0` by  bossLib.DECIDE_TAC >>
	   fs[LENGTH_NIL] >>
	   `LENGTH vs + 1 = SUC (LENGTH vs)` by rw[] >>
	   metis_tac[REPLICATE]
	   (* ----------------------- *)
       ) >>
       xlet_auto
       >-(auto_cf_tac >> fs[int_num_convert_ge]) >>
       xlet_auto
       >-(auto_cf_tac) >>
       xlet_auto
       >-(auto_cf_tac) >>
       auto_cf_tac >>
       fs[UNIT_TYPE_def] >>
       (* instantiation and dirty handling *)
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
       (* ------------------------------- *)
     ) >>
  (* validate_pat - what is that? *)
  computeLib.EVAL_TAC
);

val xauto_tac_aux = MAP_FIRST (fn t => CHANGED_TAC t)
	[auto_cf_tac,
	 fs[BOOL_def, INT_def, NUM_def, UNIT_TYPE_def, LIST_REL_def],
	 fs[LIST_REL_LENGTH, REPLICATE, LENGTH_REPLICATE],
	 fs[integerTheory.INT_ADD, int_num_convert_times, int_num_convert_ge, int_num_convert_great, int_num_convert_eq, int_num_convert_less, int_num_convert_le, empty_list_thm],
	 numLib.ARITH_TAC,
	 xlet_auto];

val xauto_tac = rpt xauto_tac_aux;

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
 
val _ = export_theory ()


val _ = process_topdecs `fun test1 i = 3+i` |> append_prog;

val st = get_ml_prog_state ();

(************************************************************************************)
(************************************************************************************)
(************************************************************************************)
(************************************************************************************)
(************************************************************************************)
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
    val (pre_postv_v, pre_ex_vl, pre_ptrs, pre_hpl, pre_pfl) =
          dest_heap_condition varsl1 let_pre
    val varsl2 = List.concat [varsl1, pre_ex_vl,
          case pre_postv_v of SOME v => [v] | NONE => []]
    val (app_pre_postv_v, app_pre_ex_vl, app_pre_ptrs, app_pre_hpl, app_pre_pfl) =
          dest_heap_condition varsl2 app_pre (* Rmk: app_pre_postv_v should be NONE *)

    (*
     * Match the pre-conditions to instantiate the unknown variables
     *)
    (* Transform the heap predicates to predicates *)
    val varsl3 = List.concat [varsl2, app_pre_ex_vl,
			      case app_pre_postv_v of SOME v => [v] | NONE => []]
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
