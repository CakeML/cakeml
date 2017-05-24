structure XLetAuto :> XLetAuto =
struct

open  preamble ml_progLib ioProgLib ml_translatorLib
	       cfTacticsLib basisFunctionsLib ml_translatorTheory
	       AssumSimpLib IntroRewriteLib XLetAuto
	       
(************************ Functions ************************************************)

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


(* RENAME_SPEC_ALL *)
fun RENAME_SPEC_ALL varsl th =
  let
      val (v, th') = SPEC_VAR th
      val v' = variant varsl v
  in
      if v <> v' then
	  RENAME_SPEC_ALL (v'::varsl) (Thm.INST [v |-> v'] th')
      else
	  RENAME_SPEC_ALL (v::varsl) th'
  end
  handle _ => th;

(* [xlet_subst_parameters] *)
fun xlet_subst_parameters env app_info asl let_pre app_spec  =
  let
      (* Retrieve the list of free variables *)
      val fvset = FVL (app_info::let_pre::asl) empty_varset
      val fvl = HOLset.listItems fvset
		      
      (* Find the parameters given to the function *)
      val (app_info', parameters) = dest_comb app_info
      val (params_expr_list, _) = listSyntax.dest_list parameters
      val params_tm_list = List.map (get_value env) params_expr_list

      (* Find the ffi variable *)
      val ffi = dest_comb app_info' |> fst |> dest_comb |> snd
    
      (* Get the parameters written in the specification *)
      val inst_app_spec = RENAME_SPEC_ALL fvl app_spec
      val app_spec1 = concl inst_app_spec |> list_dest dest_imp |> List.last
      val app_spec2 = dest_comb app_spec1 |> fst
      val app_spec3 = dest_comb app_spec2 |> fst
      val spec_parameters = dest_comb app_spec3 |> snd
      val (spec_params_tm_list, _) = listSyntax.dest_list spec_parameters

      (* And the ffi variable *)
      val spec_ffi = dest_comb app_spec3 |> fst |> dest_comb |> fst |> dest_comb |> snd

      (* Match the parameters *)
      fun create_subst l1 l2 =
	(case (l1, l2) of
	     (e1::l1', e2::l2') => (e1 |-> e2)::(create_subst l1' l2')
	   | (([]:term list), ([]:term list)) => ([]:{redex: term, residue: term} list))
      val params_subst = (spec_ffi |-> ffi)::create_subst spec_params_tm_list params_tm_list

      (* Perform the substitution in the app specification *)
      val subst_app_spec = Thm.INST params_subst inst_app_spec
  in
      subst_app_spec
  end;

(*
   Analyses a theorem of the form: 
   (?s. (A * H) s) ==> ((A * H ==>> B * H') <=> (C /\ H ==>> H'))
   Returns: (A, B, C)
*)
val hprop_extract_pattern = ``(?(s:heap). (A * H) s) ==> ((A * H ==>> B * H') <=> (C /\ H ==>> H'))``;
fun convert_extract_thm th =
    let
	val c = strip_forall (concl th) |> snd
	val (tsubst, _) = match_term hprop_extract_pattern c
	val cond = Term.subst tsubst ``A:hprop``
	val eq = Term.subst tsubst ``B:hprop``
	val res = Term.subst tsubst ``C:bool``
    in
	(cond, eq, res)
    end;

(* Some auxiliary definitions for the match_heap_conditions function *)
val sep_imp_tm = ``$==>> : hprop -> hprop -> bool``;
fun mk_sep_imp (t1, t2) = list_mk_comb (sep_imp_tm, [t1, t2]);

(* Convert equations to substitutions *)
fun convert_eqs_to_subs eqs =
  let
      val eql = list_dest dest_conj eqs |> List.map dest_eq
      val tsubst = List.map (fn (x, y) => (x |-> y)) eql
  in
      tsubst
  end;

(* [match_heap_conditions] *)
fun match_heap_conditions extract_thms hcond sub_hcond =
  let
      (* Retrieve the extraction triplets *)
      val extr_triplets = mapfilter convert_extract_thm extract_thms
      val extr_pairs = List.map (fn (c, w, r) => (mk_sep_imp (c, w), r)) extr_triplets

      (* Decompose the heap conditions *)
      val hc_hpl = list_dest dest_star hcond |> List.filter (fn x => not (same_const ``emp:hprop`` x))
      val shc_hpl = list_dest dest_star sub_hcond |>
			      List.filter (fn x => (not (same_const ``emp:hprop`` x)))

      (* Perfom the matching *)
      fun try_match obj pat_pair =
	let
	    val tsubst = match_term (fst pat_pair) obj |> fst
	    val eqs = Term.subst tsubst (snd pat_pair)
	in
	    convert_eqs_to_subs eqs
	end
	    
      fun match_loop_int h1 (h2::hl2) =
	let
	    val result = mapfilter (try_match (mk_sep_imp (h1, h2))) extr_pairs
	in
	    (List.hd result, hl2)
	end
	handle _ => let val (results, hl2') = match_loop_int h1 hl2 in (results, h2::hl2') end
			     
      fun match_loop_ext (h1::hl1) hl2 =
	(let
	    val (res1, hl2') = match_loop_int h1 hl2
	    val (results, hl1', hl2'') = match_loop_ext hl1 hl2'
	in
	    (List.revAppend(res1, results), hl1', hl2'')
	end
	 handle _ =>
		let val (results, hl1', hl2') = match_loop_ext hl1 hl2 in (results, h1::hl1', hl2') end)
	| match_loop_ext [] hl2 = ([], [], hl2)
  in
      match_loop_ext hc_hpl shc_hpl
  end;

(* [xlet_simp_spec] *)
fun xlet_simp_spec asl app_info let_pre app_spec sset match_thms =
  let
      (* Retrieve the theorems necessary for the matching *)
      val (extract_thms, ri_expand_thms, ri_retract_thms, rw_thms, rw_intro_thms) = match_thms
      
      (* Perform rewrites and simplifications on the assumptions *)
      val rw_asl = CONV_ASSUM list_ss rw_thms asl
      val all_rw_thms = List.revAppend (AND_IMP_INTRO::rw_asl, rw_thms)

      (* Add the asl in the assumptions of the app spec *)
      val app_spec' = List.foldr (fn (x, y) => ADD_ASSUM x y) app_spec asl
      
      (* Replace the ==> by /\ in the app specification, remove the quantifiers *)
      val app_spec'' = PURE_REWRITE_RULE [AND_IMP_INTRO] app_spec'
      val norm_app_spec = SPEC_ALL app_spec''

      (* Get rid of the constants *)
      val constElimConv = (SIMP_CONV sset (AND_IMP_INTRO::(ri_expand_thms@rw_thms)))
			      THENC (SIMP_CONV sset (AND_IMP_INTRO::(ri_retract_thms@rw_thms)))
      val norm_app_spec' = CONV_RULE (RATOR_CONV constElimConv) norm_app_spec
			     
      (* Match the pre-conditions *)
      fun match_hconds avoid_tms app_spec =
	let
	    val app_pre = concl (UNDISCH_ALL app_spec) |> list_dest dest_imp |> List.last |>
				dest_comb |> fst |> dest_comb |> snd
	    val rw_app_pre = (SIMP_CONV sset all_rw_thms app_pre |> concl |> dest_eq |> snd
			      handle _ => app_pre )
	    val rw_let_pre = (SIMP_CONV sset all_rw_thms let_pre |> concl |> dest_eq |> snd
			      handle _ => let_pre)
	    val (substsl, _, _) = match_heap_conditions extract_thms let_pre app_pre
	    val filt_subst =
		List.filter (fn {redex = x, residue = y} => not (HOLset.member (avoid_tms, x))) substsl
	    val used_subst = List.map (fn {redex = x, residue = y} => x) filt_subst

	    (* Instantiate the variables *)
	    val (vars_subst, terms_subst) =
		List.partition (fn {redex = x, residue = y} => is_var x) filt_subst
	    val app_spec1 = Thm.INST vars_subst app_spec

	    (* And add the other equalities as new hypotheses *)
	    val terms_eqs = List.map (fn {redex = x, residue = y} => mk_eq(x, y)) terms_subst
	    val app_spec2 = List.foldr (fn (eq, th) => ADD_ASSUM eq th) app_spec1 terms_eqs
	    val app_spec3 = List.foldr (fn (eq, th) => DISCH eq th) app_spec2 terms_eqs
	    val app_spec4 = PURE_REWRITE_RULE [AND_IMP_INTRO] app_spec3
	in
	    (app_spec4, used_subst)
	end
	    
      (* Apply the conversion algorithms on the app spec *)
      fun simplify_spec app_spec =
	let
	    (* Perform the simplification *)
	    val composConv = (INTRO_REWRITE_CONV rw_intro_thms (List.map concl rw_asl))
			       THENC (SIMP_CONV sset (AND_IMP_INTRO::rw_thms))
			       THENC (SIMP_CONV (list_ss ++ SQI_ss) [])
	    val app_spec'' = CONV_RULE (CHANGED_CONV (RATOR_CONV composConv)) app_spec

	    (* Perform substitutions *)
	    val knwn_vars = FVL (let_pre::asl) empty_varset
	    val unkwn_vars = HOLset.difference (FVL [concl app_spec''] empty_varset, knwn_vars)
	    val conjuncts = (concl app_spec'' |> dest_imp |> fst |> list_dest dest_conj
			     handle _ => [])
	    val equalities = mapfilter (fn x => dest_eq x) conjuncts
	    fun can_be_subst x y =
	      is_var x andalso HOLset.member(unkwn_vars, x)
	      andalso not (List.exists (fn z => z = x) (free_vars y))
	    fun subst_f (x, y) =
	      (if can_be_subst x y then (x |-> y)
	       else if can_be_subst y x then (y |-> x)
	       else failwith "")
	    val instList = mapfilter subst_f equalities
	    val app_spec''' = Thm.INST instList app_spec''
	in
	    app_spec'''
	end
	    
      (* Recursive modifications *)
      fun rec_simplify used_subst app_spec =
	let
	    (* Match the pre-conditions *)
	    val (app_spec', new_subst) = match_hconds used_subst app_spec

	    (* Update the used substitutions (prevents loops) *)
	    val used_subst' = HOLset.addList (used_subst, new_subst)

	    (* Perform the simplification *)
	    val app_spec'' = (rec_simplify used_subst' (simplify_spec app_spec') handle _ => app_spec')
	in
	    app_spec''
	end

      val simp_app_spec = rec_simplify empty_tmset norm_app_spec'

       (* Modify the post-condition inside the app_spec *)
      fun simplify_app_post app_spec =
	if (is_imp (concl app_spec)) then
	    let val conv_f = RAND_CONV (RAND_CONV (SIMP_CONV sset all_rw_thms))
	    in CONV_RULE conv_f app_spec end
	else let val conv_f = (RAND_CONV (SIMP_CONV sset all_rw_thms))
	     in CONV_RULE conv_f app_spec end

      val simp_app_spec = simplify_app_post simp_app_spec

      (* Compute the frame *)
      val app_pre = concl (UNDISCH_ALL app_spec) |> list_dest dest_imp |> List.last |>
				dest_comb |> fst |> dest_comb |> snd
      val rw_app_pre = (SIMP_CONV list_ss all_rw_thms app_pre |> concl |> dest_eq |> snd
			handle _ => app_pre)
      val rw_let_pre = (SIMP_CONV list_ss all_rw_thms let_pre |> concl |> dest_eq |> snd
			handle _ => app_pre)
      val (vars_subst, frame_hpl, []) = match_heap_conditions extract_thms let_pre app_pre
  in
      if HOLset.isSubset (FVL [concl simp_app_spec] empty_varset, FVL (app_info::let_pre::asl) empty_varset)
      then (DISCH_ALL (MP_ASSUM rw_asl simp_app_spec), frame_hpl)
      else raise (ERR "xlet_simp_spec" "Unable to find a proper instantiation for the app specification")
  end
  handle _ => raise (ERR "xlet_simp_spec" "");

(* [xlet_mk_post_conditions] *)
fun xlet_mk_post_condition asl frame_hpl app_spec =
  let
      (* Find the currently free variables (to prevent name conflicts) *)
      val fvl = FVL asl empty_varset |> HOLset.listItems

      (* Retrieve the post_condition *)
      val app_post = concl (UNDISCH_ALL app_spec) |> dest_comb |> snd
      
      (* Decompose the app post-condition *)
      val (post_postv_vo, post_postv_po, post_poste_vo, post_poste_po) =
	  rename_dest_post (fvl, app_post)

      (* Filter the heap predicates from the let pre-condition *)
      fun mk_post_cond_aux pred_opt =
	(case pred_opt of
	     SOME pred =>
	     let
		 val (post_ex_vl, post_hpl, post_pfl) =
		     dest_heap_condition (fvl, pred)
		 val let_heap_condition =
		     mk_heap_condition ((List.concat [post_ex_vl]),
					(List.concat [post_hpl, frame_hpl]),
					(List.concat [post_pfl]))
	     in
		 SOME let_heap_condition
	     end
	   | NONE => NONE)
      val post_postv_po' = mk_post_cond_aux post_postv_po
      val post_poste_po' = mk_post_cond_aux post_poste_po
					    
      (* Construct the post-condition *)
      val let_heap_condition =
	  mk_heap_post_condition (post_postv_vo, post_postv_po', post_poste_vo, post_poste_po')
  in
      let_heap_condition
  end;
	
(* [xlet_app_auto] *)
(*val (app_info, env, let_pre, match_thms) = (let_expr, env, pre, xlet_auto_match_thms);*)
fun xlet_app_auto app_info env let_pre (g as (asl, w)) match_thms =
  let
      (* Find the specification *)
      val app_spec = xlet_find_spec g |> DISCH_ALL |> GEN_ALL

      (* Apply the parameters given in the let expression *)
      val subst_app_spec = xlet_subst_parameters env app_info asl let_pre app_spec
						  
      (* Perform the matching *)
      val (final_app_spec, frame_hpl) =
	  xlet_simp_spec asl app_info let_pre subst_app_spec (srw_ss()) match_thms

      (* Compute the let post-condition *)
      val let_post_condition =
	  xlet_mk_post_condition ((concl final_app_spec)::(frame_hpl@asl))
				 frame_hpl final_app_spec
  in
      (* Return *)
      (final_app_spec, let_post_condition)
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
fun xlet_find_auto_aux match_thms (g as (asl, w)) =
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
		      xlet_app_auto let_expr env pre g match_thms
	      in c end
	  else
	      raise (ERR "xlet_auto" "Not handled yet")
      end
  else
      raise (ERR "xlet_auto" "Not a cf_let expression");

(* [xlet_auto_aux] *)
fun xlet_auto_aux match_thms (g as (asl, w)) =
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
		      xlet_app_auto let_expr env pre g match_thms
	      in (xlet `^c` THENL [xapp_spec H, all_tac]) g end
	  else
	      raise (ERR "xlet_auto" "Not handled yet")
      end
  else
      raise (ERR "xlet_auto" "Not a cf_let expression");

(* [xlet_find_auto] *)
val xlet_find_auto = xlet_find_auto_aux xlet_auto_match_thms;

(* [xlet_auto] *)
val (xlet_auto : tactic) = xlet_auto_aux xlet_auto_match_thms;

end
