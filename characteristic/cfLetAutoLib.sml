structure cfLetAutoLib :> cfLetAutoLib =
struct

open preamble ml_progLib cfTacticsLib ml_translatorTheory
     eqSolveRewriteLib Satisfy cfLetAutoTheory

(* TODO: move these to preamble, or Drule? *)
(********************************************************************************************)
(******************** Some conversions used to perform the matching *************************)
(*
   MP_ASSUM:

   (!a in T'. T |= a)      T' |= g
   ===============================
               T |= g
  *)
fun MP_ASSUML thl th =
  let
      val conclList = List.map (fn x => (concl x, x)) thl
      val conclMap = Redblackmap.fromList Term.compare conclList
      val num_hyps = List.length (hyp th)
      val th' = DISCH_ALL th
      fun rec_mp th n =
        if n > 0 then
          let
            val h = concl th |> dest_imp |> fst
            val hyp_th = Redblackmap.find (conclMap, h)
            val th' = MP th hyp_th
          in
            rec_mp th' (n-1)
          end
        else th
  in
      rec_mp th' num_hyps
  end;


(*
   CONV_ASSUM: use a conversion to rewrite an assumption list so that:
   (!a' in T'. T |= a') /\ (!a in T. T' |= a)
   Returns the list of theorems: !a' in T'. T |= a'
*)
fun CONV_ASSUM sset rws asl =
  let
      val tautl = List.map ASSUME asl |> List.map CONJUNCTS |> List.concat
      fun try_conv th = (CONV_RULE (SIMP_CONV sset rws) th handle HOL_ERR _ => th)
  in
      List.map try_conv tautl
  end;

(**** INTRO_REWRITE: use rewrite rules of the form h1 ==> ... ==> hn ==> PAT <=> y = z ********)
(* INTRO_REWRITE_CONV *)
fun INTRO_REWRITE_CONV thl asl =
    let
	val base_thms = (List.map ASSUME asl) @ thl
	val disj_thl = List.concat (List.map CONJUNCTS thl)
	fun match_on_asl th = mapfilter (MATCH_MP th) base_thms
	fun is_rw_th th = SPEC_ALL th |> concl |> is_eq
	fun generate_rewrites thl =
	  let
	      val (rewrite_thl, thl') = List.partition is_rw_th thl
	      val thl'' = List.concat (mapfilter match_on_asl thl')
	  in
	      case thl'' of
		  [] => rewrite_thl
		| _ => List.revAppend (generate_rewrites thl'', rewrite_thl)
	  end
	val rw_thms = generate_rewrites disj_thl
    in
	SIMP_CONV bool_ss rw_thms
    end;

(* INTRO_REWRITE_TAC *)
fun INTRO_REWRITE_TAC rws (g as (asl, w)) = CONV_TAC (INTRO_REWRITE_CONV rws asl) g;

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
  handle HOL_ERR _ => th;

(************************ Functions ************************************************)

val ERR = mk_HOL_ERR "cfLetAutoLib";

(* TODO: move to semanticPrimitivesSyntax *)
val (build_conv_tm, mk_build_conv, dest_build_conv, is_build_conv) = HolKernel.syntax_fns3 "semanticPrimitives" "build_conv";
(* TODO: move to cfcNormaliseSyntax? *)
val (exp2v_tm, mk_exp2v, dest_exp2v, is_exp2v) = HolKernel.syntax_fns2 "cfNormalise" "exp2v";

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

(* TODO: move these postv/poste/post functions to cfHeapsBaseSyntax *)
(* [dest_postv] *)
val postv_tm = ``cfHeapsBase$POSTv``;
fun dest_postv c =
  dest_binder postv_tm (ERR "dest_postv" "Not a POSTv abstraction") c;

(* [is_postv] *)
fun is_postv c =
  let val _ = dest_binder postv_tm (ERR "" "") c in true end handle HOL_ERR _ => false;

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
  let val _ = dest_binder poste_tm (ERR "" "") c in true end handle HOL_ERR _ => false;

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
  handle HOL_ERR _ => raise (ERR "dest_post" "Not a POST abstraction");

(* [is_post] *)
fun is_post c =
  let
      val (c', poste_abs) = dest_comb c
      val (ptm, postv_abs) = dest_comb c'
  in
      if same_const ptm post_tm then true else false
  end
  handle HOL_ERR _ => false;

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
val set_sep_cond_tm = ``set_sep$cond : bool -> hprop``;
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
    val hprop_pfl = List.map (fn x => mk_comb (set_sep_cond_tm, x)) pfl
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


(* [xlet_subst_parameters]
   The app specification is supposed to be quantified over all the "unknwn" variables.
*)
fun xlet_subst_parameters env app_info asl let_pre app_spec  =
  let
      (* Retrieve the list of free variables *)
      val fvset = FVL (app_info::let_pre::asl) empty_varset
      val fvl = HOLset.listItems fvset

      (* Retrieve the type variables *)
      val asl_atoms = all_atomsl (app_info::let_pre::asl) empty_tmset
      val asl_typevars =
	  HOLset.foldr (fn (a, ts) => Redblackset.addList(ts, type_vars (type_of a)))
		       (Redblackset.empty Type.compare) asl_atoms
      val spec_atoms = all_atoms (concl (DISCH_ALL app_spec))
      val spec_typevars =
	  HOLset.foldr (fn (a, ts) => Redblackset.addList(ts, type_vars (type_of a)))
		       (Redblackset.empty Type.compare) spec_atoms
      val redundant_typevars = Redblackset.intersection(asl_typevars, spec_typevars)
						       |> Redblackset.listItems
      val all_typevars = Redblackset.union(asl_typevars, spec_typevars)
					 |> Redblackset.listItems
      val all_typevars_names = Redblackset.addList (Redblackset.empty String.compare,
						   List.map dest_vartype all_typevars)
      val red_typevars_names = List.map dest_vartype redundant_typevars

      (* Substitute the redundant type variables *)
      fun rename_typevar varnames name i =
	let
	    val name' = name ^(Int.toString i)
	in
	    if Redblackset.member(varnames, name') then rename_typevar varnames name (i+1)
	    else name'
	end
      fun rename_typevars varnames (vn::vars) =
	let
	    val (varnames', pairs) = rename_typevars varnames vars
	    val vn' = rename_typevar varnames' vn 0
	    val varnames'' = Redblackset.add(varnames', vn')
	in
	    (varnames'', (vn, vn')::pairs)
	end
	| rename_typevars varnames [] = (varnames, [])
      val (_, new_type_names) = rename_typevars all_typevars_names red_typevars_names
      val type_subst = List.map (fn (x, y) => (mk_vartype x |-> mk_vartype y)) new_type_names
      val app_spec = Thm.INST_TYPE type_subst app_spec

      (* Find the parameters given to the function *)
      val (app_info', parameters) = dest_comb app_info
      val (params_expr_list, _) = listSyntax.dest_list parameters
      val params_tm_list = List.map (get_value env) params_expr_list

      (* NOT SURE if proper way: rewrite the values to prevent conflicts with the
         parameters found by xapp_spec *)
      val asl_thms = List.map ASSUME asl
      val params_tm_list = List.map (fn x => SIMP_CONV bool_ss asl_thms x
				|> concl |> dest_eq |> snd handle HOL_ERR _ => x) params_tm_list
      (*************************************************)

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
	     (e1::l1', e2::l2') =>
	     let
		 val tys1 = match_type (type_of e1) (type_of e2)
		 val (tms2, tys2) = create_subst l1' l2'
	     in
		 ((e1, e2)::tms2, List.concat [tys1, tys2])
	     end
	   | ([], []) => ([], []))
      val (tm_pairs, ty_subst) = create_subst (spec_ffi::spec_params_tm_list) (ffi::params_tm_list)
      val params_subst = List.map (fn (x, y) => (Term.inst ty_subst x |-> y)) tm_pairs

      (* Perform the substitution in the app specification *)
      val typed_app_spec = Thm.INST_TYPE ty_subst inst_app_spec
      val subst_app_spec = Thm.INST params_subst typed_app_spec
  in
      subst_app_spec
  end;

(*
   Analyses a theorem of the form:
   (?s. (A * H) s) ==> ((A * H ==>> B * H') <=> (C /\ H ==>> H'))
   Returns: (A, B, C)
*)
val hprop_extract_pattern = ``VALID_HEAP s ==> (A * H) s /\ (B * H') s ==> EQ``;
fun convert_extract_thm th =
    let
	val c = strip_forall (concl th) |> snd
	val (tsubst, _) = match_term hprop_extract_pattern c
	val cond = Term.subst tsubst ``A:hprop``
	val eq = Term.subst tsubst ``B:hprop``
	val res = Term.subst tsubst ``EQ:bool``
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

(*********************************************************************************
 *
 * Theorems, conversions, solvers used by the xlet_auto tactic
 *
 *********************************************************************************)
(* Theorems used to compute the frame *)
val FRAME_THMS = ref [UNIQUE_REFS,
		      UNIQUE_ARRAYS,
		      UNIQUE_W8ARRAYS
		     ];

fun add_frame_thms ths = FRAME_THMS := (ths @ !FRAME_THMS);
fun get_frame_thms uv = !FRAME_THMS;

(* Refinement invariants: definitions *)
val RI_DEFSL = ref ([] : thm list);
fun add_RI_defs defs = (RI_DEFSL := defs @ !RI_DEFSL);
fun get_RI_desl uv = !RI_DEFSL;

fun generate_expand_retract_thms ri_defs =
  let
      val ri_l = List.map (fn x => SPEC_ALL x |> concl |> dest_eq |> fst) ri_defs
      fun inst_ri ri =
	let
	    val ty = dest_type (type_of ri) |> snd |> List.hd
	    val v = mk_var ("v", ty)
	    val v' = variant (free_vars ri) v
	in
	    mk_comb (ri, v')
	end
	handle HOL_ERR _ => ri
	     | Empty => ri
      val inst_ri_l = List.map inst_ri ri_l
      val expandThms = List.map (GEN_ALL o (SIMP_CONV (srw_ss()) (ri_defs @ !RI_DEFSL))) inst_ri_l
      val retractThms = List.map GSYM expandThms
  in
      (expandThms, retractThms)
  end;

(* Theorems to expand or retract the definitions of refinement invariants*)
val RI_EXPAND_THMSL = ref ([] : thm list);
val RI_RETRACT_THMSL = ref ([] : thm list);
fun add_RI_expand_retract_thms expandThms retractThms =
  (RI_EXPAND_THMSL := expandThms @ !RI_EXPAND_THMSL;
   RI_RETRACT_THMSL := retractThms @ !RI_RETRACT_THMSL);

fun get_RI_expand_thms uv = !RI_EXPAND_THMSL;
fun get_RI_retract_thms uv = !RI_RETRACT_THMSL;

(* List of equality types *)
val EQUALITY_TYPE_THMS = ref ([] : thm list); (* CONJUNCTS EqualityType_NUM_BOOL) *)

fun add_RI_equality_type_thms thms = (EQUALITY_TYPE_THMS := thms @ !EQUALITY_TYPE_THMS);
fun get_RI_equality_type_thms uv = !EQUALITY_TYPE_THMS;

(* Unicity theorems for the refinement invariants *)
val INTRO_RW_THMS = ref ([NUM_INT_EQ, LIST_REL_UNICITY_RIGHT, LIST_REL_UNICITY_LEFT]);

fun generate_RI_unicity_thms eq_type_thms =
  let
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
	    val th5 = GEN_ALL th4
	in
	    th5
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
	    val th5 = GEN_ALL th4
	in
	    th5
	end
      val eq_type_thms = List.concat(List.map CONJUNCTS eq_type_thms)
      val left_rules = List.map gen_left_rule eq_type_thms
      val right_rules = List.map gen_right_rule eq_type_thms
  in
      List.concat [left_rules, right_rules]
  end;

fun add_intro_rw_thms thms = (INTRO_RW_THMS := thms @ !INTRO_RW_THMS);
fun get_intro_rewrite_thms uv = !INTRO_RW_THMS;

(* Basic rewrite theorems *)
val RW_THMS = ref [(* Handle the int_of_num operator *)
                    integerTheory.INT_ADD,
		    INT_OF_NUM_TIMES,
		    INT_OF_NUM_LE,
		    INT_OF_NUM_LESS,
		    INT_OF_NUM_GE,
		    INT_OF_NUM_GREAT,
		    INT_OF_NUM_EQ,
		    INT_OF_NUM_SUBS,
		    INT_OF_NUM_SUBS_2,

		    (* Handle lists *)
		    LENGTH_NIL,
		    LENGTH_NIL_SYM,
		    REPLICATE_APPEND_DECOMPOSE,
		    REPLICATE_APPEND_DECOMPOSE_SYM,
		    LIST_REL_DECOMPOSE_RIGHT,
		    LIST_REL_DECOMPOSE_LEFT,
		    LENGTH_REPLICATE,
		    TAKE_LENGTH_ID,
		    DROP_nil,
		    DROP_LENGTH_TOO_LONG,
		    NULL_EQ,
		    (* REPLICATE *)
		    (* REPLICATE_PLUS_ONE *)

		    (*mlbasicsProgTheory.not_def*)

		    (* Arithmetic equations simplification *)
		    NUM_EQ_SIMP1,
		    NUM_EQ_SIMP2,
		    NUM_EQ_SIMP3,
		    NUM_EQ_SIMP4,
		    NUM_EQ_SIMP5,
		    NUM_EQ_SIMP6,
		    NUM_EQ_SIMP7,
		    NUM_EQ_SIMP8,
		    NUM_EQ_SIMP9,
		    NUM_EQ_SIMP10,
		    NUM_EQ_SIMP11,
		    NUM_EQ_SIMP12,
		    MIN_DEF
		   ];
fun add_rewrite_thms thms = (RW_THMS := thms @ !RW_THMS);
fun get_rewrite_thms uv = !RW_THMS;

(* Default simpset *)
val DEF_SIMPSET = ref pure_ss;
val _ = (DEF_SIMPSET := srw_ss());

fun add_simp_frag sf = (DEF_SIMPSET := ((!DEF_SIMPSET) ++ sf));

fun add_refinement_invariants ri_defs eqTypeThms =
  let
      val eqTypeThms = List.concat (List.map CONJUNCTS eqTypeThms)
      val (expandThms, retractThms) = generate_expand_retract_thms ri_defs
      val unicityThms = generate_RI_unicity_thms eqTypeThms
      val invertDefs = List.map GSYM ri_defs
  in
      add_RI_defs ri_defs;
      add_RI_equality_type_thms (List.concat (List.map CONJUNCTS eqTypeThms));
      add_RI_expand_retract_thms (expandThms @ ri_defs) (invertDefs @ retractThms);
      add_intro_rw_thms unicityThms;
      add_rewrite_thms eqTypeThms
  end;

val _ = add_refinement_invariants [NUM_def, INT_def, BOOL_def, UNIT_TYPE_def, STRING_TYPE_def] [EqualityType_NUM_BOOL]
				  
fun add_match_thms thms =
  let
      (* Partition the theorems between the rewrite theorems and the intro rewrite ones *)
      fun is_intro_rw th =
	let
	    val thc = concl th
	    val eq = strip_imp thc |> snd
	    (* If not an equality (possible) : throw exception *)
	    val (leq, req) = dest_eq eq
	    val lvars = HOLset.addList (empty_varset, free_vars leq)
	    val rvars = HOLset.addList (empty_varset, free_vars req)
	in
	    not (HOLset.isSubset (rvars, lvars))
	end
	(* Catch the exception thrown if the conclusion is not an equality *)
	handle HOL_ERR _ => false

      val (intro_rws, rws) = List.partition is_intro_rw thms
  in
      add_intro_rw_thms intro_rws;
      add_rewrite_thms rws
  end;

(* Heuristics *)
(* fun default_heuristic_solver asl app_spec =
  let
      val knwn_vars = HOLset.listItems(FVL asl empty_varset)
      val app_spec_hyps = concl app_spec |> dest_imp |> fst |> list_dest dest_conj
      val pos_subst = satisfy knwn_vars asl app_spec_hyps
  in
      pos_subst
  end *)


fun default_heuristic_solver asl app_spec =
  let
      (* Retrieve the list of hypothesis to satisfy *)
      val app_spec_hyps = concl app_spec |> dest_imp |> fst |> list_dest dest_conj
      
      (* Retrieve the known variables from the assumptions *)
      val knwn_vars = FVL asl empty_varset

      (* Retrieve the type variables present in the assumptions *)
      val asl_atoms = all_atomsl asl empty_tmset
      val knwn_typevarset =
	  HOLset.foldr (fn (a, ts) => Redblackset.addList(ts, type_vars (type_of a)))
		       (Redblackset.empty Type.compare) asl_atoms
      val knwn_typevars = Redblackset.listItems knwn_typevarset

      (* Match every hypothesis of the app_spec against every assumption *)
      val asl_net = List.foldr (fn (x, net) => Net.insert (x, x) net) Net.empty asl
      fun find_insts hyp =
	let
	    val pos_matches = Net.match hyp asl_net
	    val pos_insts = mapfilter
		(match_terml knwn_typevars knwn_vars hyp) pos_matches
	in
	    pos_insts
	end

      val pos_insts = List.map find_insts app_spec_hyps

      (* Find an instantiation such that all the hypothesis are satisfied
         - not efficient *)

      (* Add a substitution to a map of substitutions *)
      fun add_tms ({redex = x, residue = y}, tm_map) =
	case Redblackmap.peek (tm_map, x) of
	    SOME y' => if y = y' then tm_map else failwith ""
	  | NONE => Redblackmap.insert (tm_map, x, y)

      fun add_tmsl tmsl tm_map =
	List.foldr add_tms (Redblackmap.mkDict Term.compare) tmsl

      fun add_tys ({redex = x, residue = y}, ty_map) =
	case Redblackmap.peek (ty_map, dest_vartype x) of
	    SOME y' => if y = y' then ty_map else failwith ""
	  | NONE => Redblackmap.insert (ty_map, dest_vartype x, y)

      fun add_tysl tysl ty_map =
	List.foldr add_tys (Redblackmap.mkDict String.compare) tysl

      (* Create maps from sybstitutions lists *)
      fun map_from_tms tms =
	add_tmsl tms (Redblackmap.mkDict Term.compare)

      fun map_from_tys tys =
	add_tysl tys (Redblackmap.mkDict String.compare)

      (* Recursive (and exhaustive) search *)
      fun rec_search (tm_map, ty_map) (insts::pos_insts) =
	let
	    fun rec_search_i (inst::insts) pos_insts =
	      (let
		  val tm_map' = add_tmsl (fst inst) tm_map
		  val ty_map' = add_tysl (snd inst) ty_map
	      in
		  rec_search (tm_map', ty_map') pos_insts
	      end
	      handle HOL_ERR _ => rec_search_i insts pos_insts)
	      | rec_search_i [] pos_insts = failwith ""
	in
	    rec_search_i insts pos_insts
	end
	| rec_search (tm_map, ty_map) [] = (tm_map, ty_map)

      val (tm_inst, ty_inst) = rec_search (Redblackmap.mkDict Term.compare,
					Redblackmap.mkDict String.compare)
				       pos_insts

      (* Convert the maps to proper substitutions *)
      val tm_subst = List.map (fn (x, y) => (x |-> y)) (Redblackmap.listItems tm_inst)
      val ty_subst = List.map (fn (x, y) => (mk_vartype x |-> y))
			      (Redblackmap.listItems ty_inst)
  in
      (tm_subst, ty_subst)
  end;
      
val heuristic_solver = ref default_heuristic_solver;
fun set_heuristic_solver solver = heuristic_solver := solver;

val USE_HEURISTICS = ref true;
fun use_heuristics b = USE_HEURISTICS := true;

(************************************************************************************
 *
 * Matching and simplification functions
 *
 ************************************************************************************)
(* [match_heap_conditions] *)
fun match_heap_conditions hcond sub_hcond =
  let
      val extract_thms = !FRAME_THMS

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

      (* Interior loop *)
      fun match_loop_int h1 (h2::hl2) =
	let
	    val result = mapfilter (try_match (mk_sep_imp (h1, h2))) extr_pairs
	in
	    (List.hd result, hl2)
	end
	handle HOL_ERR _ => let val (results, hl2') = match_loop_int h1 hl2 in (results, h2::hl2') end

      (* Exterior loop *)
      fun match_loop_ext (h1::hl1) hl2 =
	(let
	    val (res1, hl2') = match_loop_int h1 hl2
	    val (results, hl1', hl2'') = match_loop_ext hl1 hl2'
	in
	    (List.revAppend(res1, results), hl1', hl2'')
	end
	 handle HOL_ERR _ =>
		let val (results, hl1', hl2') = match_loop_ext hl1 hl2 in (results, h1::hl1', hl2') end)
	| match_loop_ext [] hl2 = ([], [], hl2)
  in
      match_loop_ext hc_hpl shc_hpl
  end;

(* [match_hconds] : match two pre-conditions in order to extract a frame *)
fun match_hconds rewrite_thms avoid_tms let_pre app_spec =
  let
      val sset = !DEF_SIMPSET

      val app_pre = concl (UNDISCH_ALL app_spec) |> list_dest dest_imp |> List.last |>
			  dest_comb |> fst |> dest_comb |> snd
      val rw_app_pre = (SIMP_CONV sset rewrite_thms app_pre |> concl |> dest_eq |> snd
			handle HOL_ERR _ => app_pre )
      val rw_let_pre = (SIMP_CONV sset rewrite_thms let_pre |> concl |> dest_eq |> snd
			handle HOL_ERR _ => let_pre)
      val (substsl, _, _) = match_heap_conditions let_pre app_pre
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
  end;

(* [find_equality_types] : find instantiations for the polymorphic types (ie: the quantified
	 refinement invariants) *)
val equality_type_pattern = ``EqualityType (A:'a -> v -> bool)``
val equality_type_tm = ``EqualityType:('a -> v -> bool)->bool``
fun find_equality_types asl app_spec =
  let
      val eq_type_thms = !EQUALITY_TYPE_THMS

      (* Retrieve information from the assumptions list *)
      fun is_eqtype_clause t =
	let
	    val P = dest_comb (concl t) |> fst
	in
	    same_const equality_type_tm P
	end
	handle HOL_ERR _ => false

      val eq_types_thmsl = List.concat (List.map (fn th =>
			List.filter is_eqtype_clause (CONJUNCTS th))
				eq_type_thms)
      val eq_types_set = HOLset.addList (empty_tmset, List.map
			(fn x => snd(dest_comb (concl x))) eq_types_thmsl)

      (* Find the known and unknown variables *)
      val knwn_vars = FVL asl empty_varset
      val unkwn_vars = HOLset.difference (FVL [concl app_spec] empty_varset, knwn_vars)

      (* Destroy the conjunctions in the hypotheses of the app specification *)
      val clauses = concl app_spec |> dest_imp |> fst |> list_dest dest_conj

      (* Find the polymorphic types *)
      fun extract_eqtype t =
	let
	    val (ts, tys) = match_term equality_type_pattern t
	    val [{redex = _, residue = A}] = ts
	    val ty = type_of A |> dest_type |> snd |> List.hd
	in
	    if not(HOLset.member (knwn_vars, A)) then (A, ty) else failwith ""
	end
      val eq_types = mapfilter extract_eqtype clauses

      (* Find the hyp clauses giving information about those types *)
      fun find_related A ty =
	let
	    val x = mk_var("x", ty)
	    val mterm = mk_comb(mk_comb(A, x), ``v:v``)
	    val matchf = match_terml [] (HOLset.add (empty_varset, A)) mterm
	    val related_clauses = mapfilter (fn t => (matchf t; t)) clauses
	in
	    related_clauses
	end
      val related_clauses = List.map (fn (A, ty) => (A, find_related A ty)) eq_types

      (* Compare with the assumptions list *)
      fun match_with_asl A clause =
	let
	    val varsl =
		List.filter (fn v => HOLset.member(knwn_vars, v)) (free_vars clause)
	    val varset = HOLset.addList(empty_varset, varsl)
	    val masl = mapfilter (Term.match_terml [] varset clause) asl
	in
	    masl
	end
      val substs = List.map (fn (A, clauses) =>
				(A, List.concat(List.map
				  (match_with_asl A) clauses))) related_clauses

      (* Analyse the possible substitutions and instantiate if possible *)
      fun keep_substitution A (tm_subst, ty_subst) =
	let
	    val A' = Term.subst tm_subst (Term.inst ty_subst A)
	in
	    HOLset.member (eq_types_set, A')
	end
      val filt_substs_ll =
	  List.map (fn (A, sl) => List.filter (keep_substitution A) sl) substs
      val filt_substs = List.concat filt_substs_ll

      (* Perform the substitutions *)
      fun perform_subst ((tm_subst, ty_subst), spec) =
	Thm.INST tm_subst (Thm.INST_TYPE ty_subst spec)
      val app_spec' = List.foldr perform_subst app_spec filt_substs

      (* For every A, remove the `EqualityType A` predicate if A is instantiated *)
      val conv_f = SIMP_CONV bool_ss eq_types_thmsl
      val app_spec'' = CONV_RULE (RATOR_CONV (RAND_CONV conv_f)) app_spec'
  in
      app_spec''
  end
  handle HOL_ERR _ => app_spec;

(* [simplify_spec] : simplify an app specification by instantiating the quantified variables
   in a safe manner *)
fun simplify_spec let_pre asl app_spec =
  let
      val sset = !DEF_SIMPSET
      val asl_thms = List.map ASSUME asl

      val knwn_vars = FVL asl empty_varset
      val unkwn_vars = HOLset.difference (FVL [concl app_spec] empty_varset, knwn_vars)

      (* Perform the simplification *)
      val compos_conv = (INTRO_REWRITE_CONV (!INTRO_RW_THMS) asl)
			 THENC (SIMP_CONV sset (AND_IMP_INTRO::asl_thms))
			 THENC (SIMP_CONV (list_ss ++ SQI_ss) [])
			 THENC (ELIM_UNKWN_CONV unkwn_vars)
      val app_spec1 =
	  CONV_RULE (CHANGED_CONV (RATOR_CONV (RAND_CONV compos_conv))) app_spec

      (* Perform substitutions *)
      val conjuncts = (concl app_spec1 |> dest_imp |> fst |> list_dest dest_conj
		       handle HOL_ERR _ => [])
      val equalities = mapfilter (fn x => dest_eq x) conjuncts
      fun can_be_subst x y =
	is_var x andalso HOLset.member(unkwn_vars, x)
	andalso not (List.exists (fn z => z = x) (free_vars y))
      fun subst_f (x, y) =
	(if can_be_subst x y then (x |-> y)
	 else if can_be_subst y x then (y |-> x)
	 else failwith "")
      val instList = mapfilter subst_f equalities
      val app_spec2 = Thm.INST instList app_spec1
  in
      app_spec2
  end;

exception XLET_ERR of thm;

(* [xlet_simp_spec] *)
fun xlet_simp_spec asl app_info let_pre app_spec =
  let
      val rw_thms = !RW_THMS
      val sset = !DEF_SIMPSET

      (* Perform rewrites and simplifications on the assumptions *)
      val rw_asl = CONV_ASSUM list_ss rw_thms asl
      val rw_asl_concl = List.map concl rw_asl
      val all_rw_thms = List.revAppend (AND_IMP_INTRO::rw_asl, rw_thms)

      (* Add the asl in the assumptions of the app spec *)
      val app_spec1 = List.foldr (fn (x, y) => ADD_ASSUM x y) app_spec asl

      (* Replace the ==> by /\ in the app specification, remove the quantifiers *)
      val app_spec2 = PURE_REWRITE_RULE [AND_IMP_INTRO] app_spec1
      val norm_app_spec = SPEC_ALL app_spec2

      (* Get rid of the constants *)
      val constElimConv = (SIMP_CONV sset (AND_IMP_INTRO::((!RI_EXPAND_THMSL)@rw_thms)))
			      THENC (SIMP_CONV sset (AND_IMP_INTRO::((!RI_RETRACT_THMSL)@rw_thms)))
      val norm_app_spec' = CONV_RULE (RATOR_CONV constElimConv) norm_app_spec

      (* Recursive modifications *)
      fun rec_simplify used_subst app_spec =
	let
	    (* Match the pre-conditions *)
	    val (app_spec1, new_subst) = match_hconds all_rw_thms used_subst let_pre app_spec

	    (* Update the used substitutions (prevents loopings) *)
	    val used_subst' = HOLset.addList (used_subst, new_subst)

	    (* Instantiate the polymorphic types and get rid of the constants *)
	    val app_spec2 = find_equality_types (let_pre::rw_asl_concl) app_spec1
						 |> CONV_RULE (RATOR_CONV constElimConv)

	    (* Perform the simplification *)
	    val app_spec3 = (rec_simplify used_subst'
			(simplify_spec let_pre rw_asl_concl app_spec2) handle HOL_ERR _ => app_spec2)
	in
	    app_spec3
	end

      val simp_app_spec = rec_simplify empty_tmset norm_app_spec'
				       (* Get rid of T ==> _ and some other expressions *)
				       |> CONV_RULE (SIMP_CONV bool_ss [])

      (* Use heuristics if necessary *)
      val used_heuristics = ref false
      fun heuristic_inst asl app_spec =
	if (not o HOLset.isSubset) (FVL [concl simp_app_spec] empty_varset,
				    FVL (app_info::let_pre::asl) empty_varset)
	   andalso !USE_HEURISTICS
	then
	    let
		 val solver = !heuristic_solver
		 val (tm_subst, ty_subst) = solver asl app_spec
		 val ty_app_spec = Thm.INST_TYPE ty_subst app_spec
		 val tm_subst' =
		     List.map (fn {redex = x, residue = y} =>
				  (Term.inst ty_subst x |-> y)) tm_subst
		 val subst_app_spec = Thm.INST tm_subst' ty_app_spec
	     in
		 used_heuristics := true;
		 subst_app_spec
	     end
	else app_spec (* instantiation is re-tested below *)
		 
      val hsimp_app_spec = heuristic_inst rw_asl_concl simp_app_spec

       (* Modify the post-condition inside the app_spec *)
      fun simplify_app_post app_spec =
	if (is_imp (concl app_spec)) then
	    let val conv_f = RAND_CONV (RAND_CONV (SIMP_CONV sset all_rw_thms))
	    in CONV_RULE conv_f app_spec end
	else let val conv_f = (RAND_CONV (SIMP_CONV sset all_rw_thms))
	     in CONV_RULE conv_f app_spec end

      val simp_app_spec = simplify_app_post hsimp_app_spec

      (* Compute the frame *)
      val app_pre = concl (UNDISCH_ALL app_spec) |> list_dest dest_imp |> List.last |>
				dest_comb |> fst |> dest_comb |> snd
      val rw_app_pre = (SIMP_CONV list_ss all_rw_thms app_pre |> concl |> dest_eq |> snd
			handle HOL_ERR _ => app_pre)
      val rw_let_pre = (SIMP_CONV list_ss all_rw_thms let_pre |> concl |> dest_eq |> snd
			handle HOL_ERR _ => app_pre)
      val (vars_subst, frame_hpl, []) = match_heap_conditions let_pre app_pre

      (* Change the assumptions in the spec *)
      val final_spec = MP_ASSUML rw_asl simp_app_spec

      (* Used heuristics? *)
      val _ = if !used_heuristics then print "xlet_auto : using heuristics\n" else ()

      (* Have all the variables been instantiated? *)
      val _ = if (not o HOLset.isSubset) (FVL [concl simp_app_spec] empty_varset,
					  FVL (app_info::let_pre::asl) empty_varset)
	      then raise (XLET_ERR (GEN_ALL simp_app_spec))
	      else ()
  in
      (final_spec, frame_hpl)
  end
  handle HOL_ERR{message = msg, origin_function = fname,
		 origin_structure  = sname} => raise (ERR "xlet_simp_spec" msg);

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
fun xlet_app_auto app_info env let_pre opt_app_spec (g as (asl, w)) =
  let
      (* Find the specification  *)
      val app_spec =
	  case opt_app_spec of
	      SOME spec => spec
	    | NONE =>
	      let
		  val app_spec = xlet_find_spec g |> DISCH_ALL |> GEN_ALL
		  (* Apply the parameters given in the let expression *)
		  val subst_app_spec =
		      xlet_subst_parameters env app_info asl let_pre app_spec
	      in
		  subst_app_spec
	      end

      (* Perform the matching *)
      val (final_app_spec, frame_hpl) =
	  xlet_simp_spec asl app_info let_pre app_spec

      (* Compute the let post-condition *)
      val let_post_condition =
	  xlet_mk_post_condition ((concl final_app_spec)::(frame_hpl@asl))
				 frame_hpl final_app_spec
  in
      (* Return *)
      print ("Post condition: " ^(term_to_string let_post_condition) ^ "\n");
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

(* [xlet_find_auto] *)
fun xlet_find_auto (g as (asl, w)) =
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
		      xlet_app_auto let_expr env pre NONE g
	      in c end
	      handle XLET_ERR app_spec =>
		     (print "xlet_find_auto: unable to instantiate the specification, adding it to the assumptions";
		      concl app_spec)
	  else
	      raise (ERR "xlet_find_auto" "Not handled yet")
      end
  else
      raise (ERR "xlet_find_auto" "Not a cf_let expression");

(* [xlet_auto_spec]
   The parameters given to the function in the "let" expression must have been
   substituted in the app specification. The app specification should typically be
   the spec returned by a previous, failed call to xlet_auto.
*)
fun xlet_auto_spec (opt_spec : thm option) (g as (asl, w)) =
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
		      xlet_app_auto let_expr env pre opt_spec g
	      in (xlet `^c` THENL [xapp_spec H, all_tac]) g end
	      handle XLET_ERR app_spec =>
		     (print ("xlet_auto_spec: unable to instantiate the specification"
		            ^"adding it to the assumptions");
		      ASSUME_TAC app_spec g)
	  else
	      raise (ERR "xlet_auto_spec" "Not handled yet")
      end
  else
      raise (ERR "xlet_auto_spec" "Not a cf_let expression");

(* [xlet_auto] *)
fun xlet_auto (g as (asl, w)) =
  xlet_auto_spec NONE g
  handle HOL_ERR {origin_structure = _, origin_function = fname, message = msg}
	 => raise (ERR "xlet_auto" msg);


end

(******** DEBUG ********)

(*val (g as (asl, w)) = top_goal();
val (goal_op, goal_args) = strip_comb w;
val let_expr = List.nth (goal_args, 1);
val env = List.nth (goal_args, 3);
val pre = List.nth (goal_args, 4);
val post = List.nth (goal_args, 5);
val (app_info, env, let_pre) = (let_expr, env, pre);

(* Find the specification *)
val app_spec = xlet_find_spec g |> DISCH_ALL |> GEN_ALL;

(* Apply the parameters given in the let expression *)
val subst_app_spec = xlet_subst_parameters env app_info asl let_pre app_spec;

val app_spec = subst_app_spec;

(* Perform the simplification (xlet_simp) *)
*)
