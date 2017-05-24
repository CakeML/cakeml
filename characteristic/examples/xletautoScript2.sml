open  preamble ml_progLib ioProgLib ml_translatorLib
	       cfTacticsLib basisFunctionsLib ml_translatorTheory;

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

(******************************************* TESTS *****************************************)

val LIST_APPEND_REPLICATE_EQ = Q.store_thm("LIST_APPEND_REPLICATE_EQ",
`a ++ b = REPLICATE n x <=>
a = REPLICATE (LENGTH a) x /\ b = REPLICATE (LENGTH b) x /\ LENGTH a + LENGTH b = n`,
cheat);

val extract_th1 = Q.prove(`(?s. (REF r v * H) s) ==> ((REF r v * H) ==>> (REF r v' * H')
								    <=> (v' = v /\ H ==>> H'))`, cheat);
val extract_th2 =Q.prove(`(?s. (ARRAY a av * H) s) ==> ((ARRAY a av * H) ==>> (ARRAY a av' * H')
									 <=> (av' = av /\ H ==>> H'))`, cheat);

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
		  REPLICATE_APPEND_EQ,
		  LIST_APPEND_REPLICATE_EQ
		  
];
val match_thms = List.concat [rewrite_thms, refin_inv_rewrite_thms];
val extract_thms = [extract_th1, extract_th2];
val ri_expand_thms = refin_invariant_defs;
val ri_retract_thms = refin_inv_rewrite_thms;
val rw_thms = rewrite_thms;
val rw_intro_thms = refin_inv_match_thms;
val xlet_auto_match_thms = (extract_thms, ri_expand_thms, ri_retract_thms, rw_thms, rw_intro_thms);

val st = get_ml_prog_state();

val empty_queue_spec = Q.store_thm ("empty_queue_spec",
    `!uv. app (p:'ffi ffi_proj) ^(fetch_v "empty_queue" st) [uv]
          emp (POSTv qv. QUEUE A [] qv)`,
    xcf "empty_queue" st \\
    xlet_auto >> (xvar >> xsimpl) \\
    xlet_auto >> (xsimpl) \\
    xlet_auto >> (xvar >> xsimpl) \\
    xapp \\ simp[QUEUE_def] \\ xsimpl
				   );

mlarrayProgTheory.array_copy_spec
val (g as (asl, w)) = top_goal();
xlet_find_auto g;
val push_spec = Q.store_thm ("push_spec",
    `!qv xv vs x. app (p:'ffi ffi_proj) ^(fetch_v "push" st) [qv; xv]
          (QUEUE A vs qv * & A x xv)
	  (POSTv uv. QUEUE A (vs ++ [x]) qv)`,
  xcf "push" st >>
  fs[QUEUE_def] >>
  xpull >>
  xlet_auto >-(xsimpl) >>
  xmatch >> xsimpl >>
  rw[]
  >- (xlet_auto >-(xsimpl) >>
      xlet_auto >-(xsimpl) >>
      xif
      >-(
	   xlet_auto >-(xsimpl) >>
	   xlet_auto >-(xsimpl) >>
	   xlet_auto >-(xsimpl) >>
	   xlet_auto >-(xsimpl) >>
	       
	   (* xlet_auto - use rw rules with existential research *)
	   xlet `POSTv v.
           ARRAY av' (vvs ++ junk ++ REPLICATE (LENGTH junk + LENGTH vvs +1) xv) *
           ARRAY av (vvs ++ junk) *
	   qv ~~> Conv NONE [av; Litv (IntLit (&LENGTH vs))]`
           >- (auto_cf_tac >>
	       fs all_match_thms >>
	       qexists_tac `REPLICATE (LENGTH junk + LENGTH vvs) xv` >>
	       fs[LENGTH_REPLICATE]
	       fs refin_invariant_defs >>
	       rw [REPLICATE_APPEND_EQ]
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
