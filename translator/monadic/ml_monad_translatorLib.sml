structure ml_monad_translatorLib :> ml_monad_translatorLib = struct

open preamble
open astTheory libTheory semanticPrimitivesTheory bigStepTheory
     ml_translatorTheory ml_progTheory ml_progLib
     ml_pmatchTheory ml_monadBaseTheory ml_monad_translatorBaseTheory
     ml_monad_translatorTheory
open terminationTheory
open cfTacticsLib
open Net List packLib stringSimps
open ml_monadStoreLib

val get_term = let
  val ys = unpack_list (unpack_pair unpack_string unpack_term) m_translator_terms
  in fn s => snd (first (fn (n,_) => n = s) ys) end

(* val get_packed_type = let
  val ys = unpack_list (unpack_pair unpack_string unpack_type) m_translator_types
  in fn s => snd (first (fn (n,_) => n = s) ys) end *)

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;

fun primCases_on tm = Cases_on [ANTIQUOTE tm]

val _ = (print_asts := true);

val _ = (use_full_type_names := false);

(* Some constants *)
val venvironment = mk_environment v_ty
val v_env = mk_var("env",venvironment)
val exp_ty = ``:ast$exp``
val exp_var = mk_var("exp", exp_ty)
val cl_env_tm = mk_var("cl_env",venvironment)
val string_ty = ``:tvarN``
val a_ty = ``:'a``
val b_ty = ``:'b``
val c_ty = ``:'c``
val d_ty = ``:'d``
val unit_ty = ``:unit``
val poly_M_type = ``:'a -> ('b, 'c) exc # 'a``
val v_bool_ty = ``:v -> bool``
val hprop_ty = ``:hprop``
val string_ty = ``:string``
val bool_ty = ``:bool``
val recclosure_exp_ty = ``:(tvarN, tvarN # ast$exp) alist``
val v_var = mk_var("v",v_ty)

val ArrowM_const = ``ArrowM``
val Eval_const = ``Eval``
val EvalM_const = ``EvalM``
val MONAD_const = ``MONAD : (α->v->bool) -> (β->v->bool) -> ((γ,α,β)M,γ) H``
val PURE_const = ``PURE : (α -> v -> bool) -> (α, β) H``
val SND_const = ``SND``

val Fun_const = ``ast$Fun``
val Short_const = ``namespace$Short``
val Var_const = ``ast$Var``
val Closure_const = ``semanticPrimitives$Closure``

val failure_pat = ``\v. (Failure(C v), state_var)``
val Eval_pat = ``Eval env exp (P (res:'a))``
val Eval_pat2 = ``Eval env exp P``
val derive_case_EvalM_abs = ``\EXN_TYPE res H. EvalM env st exp (MONAD P EXN_TYPE res) H``
val Eval_name_RI_abs = ``\name RI. Eval env (Var (Short name)) RI``
val write_const = ``write``
val RARRAY_REL_const = ``RARRAY_REL``
val run_const = ``ml_monadBase$run``
val EXC_TYPE_aux_const = ``EXC_TYPE_aux``

val return_pat = ``st_ex_return x``
val bind_pat = ``st_ex_bind x y``
val otherwise_pat = ``x otherwise y``
val if_statement_pat = ``if b then (x:('a,'b,'c) M) else (y:('a,'b,'c) M)``
val raise_goal_abs = ``
      \cons_name deep_type refin_inv EXN_RI f.
      !H x a.
      (lookup_cons cons_name env = SOME (1,deep_type)) ==>
      Eval env exp1 (refin_inv x) ==>
      EvalM env st (Raise (Con (SOME (Short cons_name)) [exp1]))
        (MONAD a EXN_RI (f x)) H``
val PreImp_EvalM_abs = ``\a name RI f H. PreImp a (!st. EvalM env st (Var (Short name)) (RI f) H)``

(* ---- *)

fun mk_write name v env = ISPECL[name,v,env] write_def
				|> concl |> rator |> rand

fun my_list_mk_comb (f,xs) = let
    fun mk_type_rec f_ty (x_ty::x_ty'::tys) = let
	val [ty1,ty2] = dest_type f_ty |> snd
	val (ty3,args_ty) = mk_type_rec ty2 (x_ty'::tys)
	val ty4 = mk_type("fun",[ty1,ty3])
	val args_ty = mk_type("fun",[x_ty,args_ty])
    in (ty4,args_ty) end
      | mk_type_rec f_ty [x] = let
	  val [ty1,ty2] = dest_type f_ty |> snd
      in (ty1,x) end
      | mk_type_rec f_ty [] = failwith "mk_type_rec"
    val args_types = List.map type_of xs
    val (src_ty,target_ty) = mk_type_rec (type_of f) args_types
    val tys = Type.match_type src_ty target_ty
    val f = Term.inst tys f
in list_mk_comb(f, xs) end

fun ISPECL_TM xs tm = let
    val tm1 = my_list_mk_comb(tm,xs)
    fun apply_beta (x1::x2::xs) = (RATOR_CONV (apply_beta (x2::xs)))
					     THENC BETA_CONV
      | apply_beta [x] = BETA_CONV
      | apply_beta [] = ALL_CONV
    val tm2 = apply_beta xs tm1 |> concl |> rand
in tm2 end				   

fun dest_monad_type ty =
  let val s = (match_type poly_M_type ty) in
      (type_subst s a_ty, type_subst s b_ty, type_subst s c_ty) end

(* Should be moved somewhere else *)
fun list_dest f tm =
  let val (x,y) = f tm in list_dest f x @ list_dest f y end
  handle HOL_ERR _ => [tm];
val dest_fun_type = dom_rng;
fun domain ty = ty |> dest_fun_type |> fst;

val dest_args = snd o strip_comb;

fun D th = let
  val th = th |> DISCH_ALL |> PURE_REWRITE_RULE [AND_IMP_INTRO]
in if is_imp (concl th) then th else DISCH T th end;

(* Same as D, but leaves the VALID_REFS_PRED in the assumptions *)
fun Dfilter th a0 = let
    val pat = concl VALID_REFS_PRED_def |> strip_forall |> snd |> dest_eq |> fst
    val hyps = hyp th
    val th = List.foldl (fn (a, th) => if can (match_term pat) a then th
				       else if a = a0 then th
				       else DISCH a th) th hyps
    val th = PURE_REWRITE_RULE [AND_IMP_INTRO] th
  in if is_imp (concl th) then th else DISCH T th end

(* The store predicate *)
val H_def = ref UNIT_TYPE_def; (* need a theorem here... *)
val default_H = ref ``\refs. emp``;
val H = ref ``\refs. emp``;
val dynamic_init_H = ref false; (* Has the store predicate free variables? *)
val store_pinv_def = ref (NONE : thm option);

fun move_VALID_REFS_PRED_to_assums th = let
    val pat = concl VALID_REFS_PRED_def |> strip_forall |> snd |> dest_eq |> fst
    val H_var = rand pat
    val (tms, tys) = match_term H_var (!H)
    val pat = Term.inst tys pat |> Term.subst tms
    val a = ASSUME pat
    val th = SIMP_RULE bool_ss [a] th
in th end

(* The type of the references object *)
val refs_type = ref unit_ty;

(* The exception refinement invariant and type *)
val EXN_TYPE_def_ref = ref UNIT_TYPE_def;
val EXN_TYPE = ref ``UNIT_TYPE``;
val exn_type = ref unit_ty;

(* Some functions to generate monadic types *)
(* ``:^(!refs_type) -> (^ty, ^(!exn_type)) exc # ^(!refs_type)`` *)
fun M_type ty = Type.type_subst [a_ty |-> !refs_type,
				 b_ty |-> ty,
				 c_ty |-> !exn_type]
				poly_M_type
val aM = ref (ty_antiq (M_type a_ty));
val bM = ref (ty_antiq (M_type b_ty));

(* The theorem stating that there exists a store stasfying the store predicate *)
val VALID_STORE_THM = ref (NONE : thm option);

(* Additional theories where to look for refinement invariants *)
val type_theories = ref ([current_theory(), "ml_translator"] : string list);

(* Theorems proved to handle exceptions *)
val exn_handles = ref ([] : (term * thm) list);
val exn_raises = ref ([] : (term * thm) list);
val exn_functions_defs = ref ([] : (thm * thm) list);

(* The access patterns to use references and arrays *)
val access_patterns = ref([] : (term * thm) list);
val refs_functions_defs = ref([] : (thm * thm) list);
val arrays_functions_defs = ref([] : (thm * thm * thm * thm * thm * thm) list);

(* The specifications for dynamically initialized stores *)
val dynamic_v_thms = ref (Net.empty : (string * string * term * thm * thm * string option) net);

fun add_dynamic_v_thms (name, ml_name, th, pre_def) = let
    val th = UNDISCH_ALL th
    val thc = concl th
    val hol_fun = thc |> rator |> rand
    val _ = dynamic_v_thms := (Net.insert (hol_fun, (name, ml_name, hol_fun, th, pre_def, NONE))
					 (!dynamic_v_thms))
    val _ = print("Added a dynamic specification for " ^(dest_const hol_fun |> fst) ^"\n")
    val _ = if concl pre_def =T then () else
            (print ("\nWARNING: " ^ml_name^" has a precondition.\n\n"))
in () end;

fun lookup_dynamic_v_thm tm = let
    val matches = Net.match tm (!dynamic_v_thms)
    val (name, ml_name, hol_fun, th, pre_cond, module) = first (fn (_, _, _, x, _, _) => (concl x |> rator |> rand |> same_const tm)) matches
    val th = MATCH_MP Eval_Var_Short th
    val v_name = stringSyntax.fromMLstring ml_name
    val th = SPECL [stringSyntax.fromMLstring ml_name, v_env] th |> UNDISCH_ALL
in th end;

(* The environment extension for dynamically initialized stores *)
(* val dynamic_init_env = ref (NONE : term option); *)
val dynamic_refs_bindings = ref ([] : (term * term) list);

(* Abbreviations of the function values in the case of a dynamically initialized store*)
val local_code_abbrevs = ref([] : thm list);

fun get_all_access_funs_defs () = let
    val refs_access_defs = List.concat (List.map (fn (x,y) => [x,y]) (!refs_functions_defs))
    val arrays_access_defs = List.concat (List.map (fn (x1,x2,x3,x4,x5,x6)
     => [x1,x2,x3,x4,x5,x6]) (!arrays_functions_defs))
in List.concat [refs_access_defs,arrays_access_defs] end

(* Some minor functions *)
fun ISPEC_EvalM th = ISPEC (!H) th;
fun ISPEC_EvalM_EXN_TYPE th = ISPEC (!EXN_TYPE) th;
fun ISPEC_EvalM_MONAD th = ISPECL[!H, !EXN_TYPE] th;
fun ISPEC_EvalM_VALID th = case (!VALID_STORE_THM) of
			   SOME store_th => MP (ISPEC (!H) th) store_th
			    | NONE => UNDISCH (ISPEC (!H) th)
fun inst_monad_type tm =
  let
      val ty_subst = Type.match_type poly_M_type (type_of tm)
      val a = Type.type_subst ty_subst a_ty
      val c = Type.type_subst ty_subst c_ty
      val tm' = Term.inst [a |-> !refs_type, c |-> !exn_type] tm
  in
      tm'
  end;
(* ---- *)

(* Functions to manipulate of the current closure environment *)
fun get_curr_prog_state () = let
  val k = ref init_state
  val _ = ml_prog_update (fn s => (k := s; s))
  in !k end

val local_environment_var_name = "%env";
val num_local_environment_vars = ref 0;
val local_environment_var_0 = mk_var("%env", venvironment);
fun get_curr_env () =
   if !dynamic_init_H then let
       val _ = num_local_environment_vars :=
	       ((!num_local_environment_vars) +1)
       val env_var = mk_var(local_environment_var_name ^(int_to_string (!num_local_environment_vars)),venvironment)
   in env_var end
   else get_env (get_curr_prog_state ());
(* *)

fun mk_PURE x = my_list_mk_comb (Term.inst[b_ty |-> !refs_type]
					      PURE_const,[x])

(* COPY/PASTE from ml_translatorLib *)
fun MY_MATCH_MP th1 th2 = let
  val tm1 = fst (dest_imp (concl th1))
  val tm2 = concl th2
  val (s,i) = match_term tm1 tm2
  in MP (INST s (INST_TYPE i th1)) th2 end;
(* End of COPY/PASTE from ml_translatorLib *)

fun get_m_type_inv ty = let
    val MONAD_tm = Term.inst [c_ty |-> !refs_type] MONAD_const
    val RI = get_type_inv (dest_monad_type ty |> #2)
  in my_list_mk_comb(MONAD_tm,[RI,!EXN_TYPE]) end
  handle HOL_ERR _ => raise (ERR "get_m_type_inv" "unsupported type")

fun get_arrow_type_inv ty =
  if can dest_monad_type ty then get_m_type_inv ty else let
    val (ty1,ty2) = dest_fun_type ty
    val i1 = get_arrow_type_inv ty1 handle HOL_ERR _ =>
             (mk_PURE (get_type_inv ty1))
    val i2 = get_arrow_type_inv ty2
  in my_list_mk_comb (ArrowM_const, [!H,i1,i2]) end;

fun smart_get_type_inv ty =
  if not (can dest_monad_type ty) andalso
     can get_arrow_type_inv ty then let
    val inv = get_arrow_type_inv ty
    in ONCE_REWRITE_CONV [ArrowM_def] inv |> concl |> rand |> rand end
  else get_type_inv ty;

val ArrowP_PURE_pat = get_term "ArrowP PURE";
val ArrowP_EqSt_pat = get_term "ArrowP EqSt";
fun get_EqSt_var tm =
  if can (match_term ArrowP_PURE_pat) tm
  then get_EqSt_var ((rand o rand) tm)
  else if can (match_term ArrowP_EqSt_pat) tm
  then SOME ((rand o rand o rator) tm)
  else NONE

fun get_monad_pre_var th lhs fname = let
    val thc = UNDISCH_ALL th |> PURE_REWRITE_RULE[ArrowM_def]
			  |> concl |> rator |> rand |> rator |> rand
    val state_var = get_EqSt_var thc
in 
    case state_var of
	NONE => get_pre_var lhs fname
      | SOME state_var => let
	  fun list_mk_type [] ret_ty = ret_ty
	    | list_mk_type (x::xs) ret_ty = mk_type("fun",[type_of x,list_mk_type xs ret_ty])
	  val args = state_var::(dest_args lhs)
	  val ty = list_mk_type args bool
	  val v = mk_var(fname ^ "_side",ty)
      in (List.foldl (fn (x,y) => mk_comb(y,x)) v args) end end

(* Retrieves the parameters given to Eval or EvalM *)
fun get_Eval_arg e = if same_const (strip_comb e |> fst) Eval_const then e |> rand |> rand
		     else e |> rator |> rand |> rand;
fun get_Eval_env e = if same_const (strip_comb e |> fst) Eval_const then e |> rator |> rator |> rand
		     else e |> rator |> rator |> rator |> rator |> rand;
fun get_Eval_exp e = if same_const (strip_comb e |> fst) Eval_const then e |> rator |> rand
		     else e |> rator |> rator |> rand;
val get_EvalM_state = rand o rator o rator o rator;
(* ---- *)

(* Prove the specifications for the exception handling *)
(* val (raise_fun_def, cons_name, exn_type, deep_type) = List.hd raise_info *)
fun prove_raise_spec exn_ri_def EXN_RI_tm (raise_fun_def, cons_name, exn_type, deep_type) = let
    val fun_tm = concl raise_fun_def |> strip_forall |> snd |> lhs |> strip_comb |> fst
    val refin_inv = smart_get_type_inv exn_type

    val solve_tac =
      rw[Eval_def,EvalM_def,MONAD_def,raise_fun_def] >>
      rw[Once evaluate_cases] >>
      rw[Once evaluate_cases] >>
      srw_tac[boolSimps.DNF_ss][] >> disj1_tac >>
      rw[Once evaluate_cases,PULL_EXISTS] >>
      rw[Once(CONJUNCT2 evaluate_cases)] >>
      first_x_assum(qspec_then`(s with refs := s.refs ++ junk).refs`strip_assume_tac) >>
      IMP_RES_TAC (evaluate_empty_state_IMP
		   |> INST_TYPE [``:'ffi``|->unit_ty]) >>
      rw[do_con_check_def,build_conv_def] >>
      fs [lookup_cons_def] >>
      fs[exn_ri_def,namespaceTheory.id_to_n_def] >>
      asm_exists_tac \\ fs[] >>
      PURE_REWRITE_TAC[GSYM APPEND_ASSOC] \\ fs[REFS_PRED_FRAME_append]

    val goal = ISPECL_TM [cons_name,deep_type,refin_inv,
			  EXN_RI_tm,fun_tm] raise_goal_abs
    (* set_goal ([], goal) *)

   val thm_name = "EvalM_" ^(dest_const fun_tm |> fst)
   val raise_spec = store_thm(thm_name, goal, solve_tac)
   val _ = print ("Saved theorem __ \"" ^thm_name ^"\"\n")
in raise_spec end;

val namespaceLong_tm = ``namespace$Long``;
(* val (handle_fun_def, ECons, exn_type, deep_type) = List.hd handle_info *)
fun prove_handle_spec exn_ri_def EXN_RI_tm (handle_fun_def, ECons, exn_type, deep_type) = let
    val fun_tm = concl handle_fun_def |> strip_forall |> snd |> lhs |> strip_comb |> fst
    val TYPE = smart_get_type_inv exn_type
    val EXN_TYPE = EXN_RI_tm
    val handle_fun = concl handle_fun_def |> strip_forall |> snd |> lhs |> strip_comb |> fst

    val is_module_exn = rand deep_type |> strip_comb |> fst |> same_const namespaceLong_tm
    val handle_thm = if is_module_exn then let
        val module_name = rand deep_type |> rator |> rand
	val cons_name = rand deep_type |> rand |> rand
    in ISPECL [cons_name, module_name, ECons, TYPE, EXN_TYPE, handle_fun]
			    EvalM_handle_MODULE |> SPEC_ALL end
    else let
	val cons_name = rand deep_type |> rand
    in ISPECL [cons_name, ECons, TYPE, EXN_TYPE, handle_fun]
			    EvalM_handle_SIMPLE |> SPEC_ALL end

    (* Prove the assumptions *)
    val assumptions = concl handle_thm |> strip_imp |> fst
    val assumptions = List.take(assumptions, 4)

    fun case_tac (g as (asl, w)) = let
	val t = lhs w |> strip_comb |> snd |> List.hd
    in Cases_on `^t` g end

    val tactics = [rw[handle_fun_def],
		   rw[handle_fun_def] \\ Cases_on `x1 s` \\ fs[] \\
                   case_tac \\ rw[] \\ case_tac \\ rw[],
		   rw[exn_ri_def],
		   rw[exn_ri_def] \\ Cases_on `e` \\ fs[exn_ri_def]]
    val proofs = List.map(fn(g, t) => prove(g, t)) (zip assumptions tactics)
    (* set_goal([], List.nth(assumptions, 1)) *)

    (* Remove the assumptions from the theorem *)
    val handle_thm = List.foldl (fn (p, th) => MP th p) handle_thm proofs

    (* Generalize the heap invariant *)
    val heap_inv = concl handle_thm |> strip_imp |> snd |> rand
    val handle_thm = GEN heap_inv handle_thm

    (* Save the theorem *)
    val thm_name = "EvalM_" ^(dest_const fun_tm |> fst)
    val handle_spec = save_thm(thm_name, handle_thm)
    val _ = print ("Saved theorem __ \"" ^thm_name ^"\"\n")
in handle_spec end;

fun add_raise_handle_functions exceptions_functions exn_ri_def = let
    val (raise_functions, handle_functions) = unzip exceptions_functions

    (* Extract information from the exception refinement invariant *)
    val exn_ri_cases = CONJUNCTS exn_ri_def
    val EXN_RI_tm = List.hd exn_ri_cases |> concl |> strip_forall |> snd |> lhs |> rator |> rator
    val exn_ri_cons = List.map (rator o rand o rator o lhs o snd o strip_forall o concl) exn_ri_cases
    val exn_ri_types = List.map (type_of o rand o rand o rator o lhs o snd
				 o strip_forall o concl) exn_ri_cases
    fun safe_register_type ty = if can get_type_inv ty then ()
				else register_type ty
    val _ = mapfilter safe_register_type exn_ri_types
    val exn_ri_deep_cons = List.map (rand o rator o rhs o fst o dest_conj o snd
				     o strip_exists o rhs o snd o strip_forall o concl) exn_ri_cases
    val (exn_ri_cons_names, exn_ri_deep_types) = unzip(List.map (dest_pair o rand) exn_ri_deep_cons)
    fun zip4 (x1::l1) (x2::l2) (x3::l3) (x4::l4) = (x1, x2, x3, x4)::(zip4 l1 l2 l3 l4)
      | zip4 [] [] [] [] = []
    val exn_info = zip4 exn_ri_cons  exn_ri_cons_names exn_ri_types exn_ri_deep_types
    val exn_type = type_of EXN_RI_tm |> dest_type |> snd |> List.hd

    (* Link the raise definitions with the appropriate information *)
    val raise_funct_pairs = List.map (fn x => (x, concl x |> strip_forall |> snd |> rhs
		|> dest_abs |> snd |> dest_pair |> fst |> rand |> rator)) raise_functions
    val raise_info = List.map (fn(d, tm) => tryfind (fn (x1, x2, x3, x4) => if x1 = tm
			then (d, x2, x3, x4) else failwith "") exn_info) raise_funct_pairs

    (* Prove the raise specifications *)
    val raise_specs = List.map (prove_raise_spec exn_ri_def EXN_RI_tm) raise_info

    (* Link the handle definitions with the appropriate information *)
    fun get_handle_cons handle_fun_def = let
	val exn_cases = concl handle_fun_def |> strip_forall |> snd |> rhs |> dest_abs |> snd |>
                    rand |> strip_abs |> snd |> rand |> dest_abs |> snd
	val cases_list = strip_comb exn_cases |> snd |> List.tl
	val cases_cons = TypeBase.constructors_of exn_type
	val cases_pairs = zip cases_cons cases_list

	val (SOME handled_cons) = List.find (fn (x, y) => not(can (Term.match_term failure_pat) y))
                           cases_pairs
    in fst handled_cons end handle Bind => failwith "get_handled_cons"

    val handle_funct_pairs = List.map (fn x => (x, get_handle_cons x)) handle_functions
    val handle_info = List.map (fn(d, tm) => tryfind (fn (x1, x2, x3, x4) => if x1 = tm
			then (d, x1, x3, x4) else failwith "") exn_info) handle_funct_pairs

    (* Prove the handle specifications *)
    val handle_specs = List.map (prove_handle_spec exn_ri_def EXN_RI_tm) handle_info

    (* Store the proved theorems *)
    fun extract_pattern th = let
	  val pat = concl th |> strip_forall |> snd |> strip_imp |> snd |> rator |> rand |> rand
      in (pat, th) end
    val _ = exn_raises := ((List.map extract_pattern raise_specs) @ (!exn_raises))
    val _ = exn_handles := ((List.map extract_pattern handle_specs) @ (!exn_handles))
in zip raise_specs handle_specs end;

(*-----*)

(* support for datatypes... *)

(*
  val _ = set_goal([],goal)
*)
local
  val IF_T = Q.prove(`(if T then x else y) = x:'a`,SIMP_TAC std_ss [])
  val IF_F = Q.prove(`(if F then x else y) = y:'a`,SIMP_TAC std_ss [])
  val evaluate_Mat =
    ``evaluate c x env (Mat e pats) (xx,res)``
    |> (ONCE_REWRITE_CONV [evaluate_cases] THENC SIMP_CONV (srw_ss()) [])
  val evaluate_match_Conv =
    ``evaluate_match c x env args ((Pcon xx pats,exp2)::pats2)
                     errv (yyy,y)``
    |> (ONCE_REWRITE_CONV [evaluate_cases] THENC
       SIMP_CONV (srw_ss()) [pmatch_def])
in
fun derive_case_of ty = let
  (* TODO : clean that *)
  fun smart_full_name_of_type ty =
    if let val r = dest_thy_type ty in #Tyop r = "cpn" andalso #Thy r = "toto" end then ("order", "")
    else (full_name_of_type ty, #Thy (dest_thy_type ty))
  fun get_name ty = let
      val (n, thy) = (smart_full_name_of_type ty)
      val name = (clean_uppercase n) ^ "_TYPE"
      val name_thy = (clean_uppercase thy) ^"_"^name
  in (name, name_thy) end
  val (name, name_thy) = if ty <> unit_ty then get_name ty else ("UNIT_TYPE", "UNIT_TYPE")
  val inv_def = tryfind (fn thy_name => fetch thy_name (name ^ "_def"))
			(!type_theories)
      handle HOL_ERR _ =>
	     tryfind (fn thy_name => fetch thy_name (name_thy ^ "_def"))
		     (!type_theories)
      handle  HOL_ERR _ => let
	  val thms = DB.find (name ^ "_def") |> List.map (fst o snd)
	  val inv_ty = mk_type("fun", [ty, v_bool_ty])
	  fun is_valid th = let
	      val th_body = CONJUNCTS th |> List.hd |> concl |> strip_forall
				      |> snd |> dest_eq |> fst
	      val ctm = th_body |> strip_comb |> fst
	      val ctm_name = dest_const ctm |> fst
	      val ctm_rator = rator(rator th_body)
	  in if ((ctm_name = name) orelse (ctm_name = name_thy)) andalso
	     (can (match_type (type_of ctm_rator)) inv_ty) then th
	     else failwith ""
	  end
      in tryfind is_valid thms end
  (* *)
  val case_th = get_nchotomy_of ty
  val pat = Eval_pat (* ``Eval env exp (P (res:'a))`` *)
  val pure_tm = case_of ty |> concl
  (* Find a variable for the store invariant *)
  val pure_tm_vars = all_vars pure_tm
  val H_var = mk_var("H", mk_type("fun", [!refs_type, hprop_ty]))
  val H_var = variant pure_tm_vars H_var
  (* Convert the Eval predicates to EvalM predicates *)
  fun Eval_to_EvalM tm = let
    val (m,i) = match_term pat tm
    val res = mk_var("res", M_type a_ty)
    val st = mk_var("st",!refs_type)
    (* val tm1 = subst m (inst i ``EvalM env st exp (MONAD P ^(!EXN_TYPE) ^res) ^H_var``) *)
    val tm0 = ISPECL_TM [!EXN_TYPE,res,H_var] derive_case_EvalM_abs
    val tm1 = subst m (inst i tm0)
    val ty1 = tm |> rand |> rand |> type_of
    val monad_ret_type = M_type ty1
    val y1 = tm |> rand |> rand |> inst [ty1|->monad_ret_type]
    val y0 = tm1 |> rator |> rand |> rand
    in subst [y0 |-> y1] tm1 end
    handle HOL_ERR _ =>
    if is_comb tm then let
      val (x,y) = dest_comb tm
      in mk_comb(Eval_to_EvalM x, Eval_to_EvalM y) end
    else if is_abs tm then let
      val (x,y) = dest_abs tm
      in mk_abs(x, Eval_to_EvalM y) end
    else tm
  val (x1,x2) = dest_imp pure_tm
  val (x2,x3) = dest_imp x2
  val (x3,x4) = dest_imp x3
  val hyps = list_dest dest_conj x3
  fun map_tl f [] = []
    | map_tl f (x::xs) = x :: List.map f xs
  val z3 = map_tl Eval_to_EvalM hyps |> list_mk_conj
  val z4 = Eval_to_EvalM x4
  val goal = mk_imp(x1,mk_imp(x2,mk_imp(z3,z4)))
  val x_var = tryfind (fn x => if fst(dest_var x) = "x" then x else failwith "") (free_vars goal)
  val init_tac =
        PURE_REWRITE_TAC [CONTAINER_def]
        \\ REPEAT STRIP_TAC \\ STRIP_ASSUME_TAC (ISPEC x_var case_th)
  val case_tac =
        Q.PAT_X_ASSUM `b0 ==> Eval env exp something`
           (MP_TAC o REWRITE_RULE [TAG_def,inv_def,Eval_def])
        \\ FULL_SIMP_TAC (srw_ss()) []
        \\ REPEAT STRIP_TAC
        \\ NTAC 2 (POP_ASSUM MP_TAC)
        \\ POP_ASSUM (STRIP_ASSUME_TAC o remove_primes o
             SPEC_ALL o REWRITE_RULE [TAG_def,inv_def,EvalM_def])
        \\ FULL_SIMP_TAC std_ss [ALL_DISTINCT] \\ FULL_SIMP_TAC std_ss [inv_def]
        \\ REPEAT STRIP_TAC
        \\ FULL_SIMP_TAC std_ss [ALL_DISTINCT] \\ FULL_SIMP_TAC std_ss [inv_def]
        \\ FULL_SIMP_TAC std_ss [EvalM_def,PULL_FORALL] \\ REPEAT STRIP_TAC
        \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) []
        \\ SIMP_TAC (std_ss ++ DNF_ss) [] \\ disj1_tac
        \\ first_x_assum(qspec_then`(s with refs := s.refs ++ junk).refs`strip_assume_tac)
        \\ drule evaluate_empty_state_IMP
        \\ strip_tac \\ asm_exists_tac
        \\ ASM_SIMP_TAC std_ss []
        \\ REWRITE_TAC[evaluate_match_Conv,pmatch_def,LENGTH]
        \\ fs[pmatch_def,pat_bindings_def,write_def,
              lookup_cons_def,same_tid_def,namespaceTheory.id_to_n_def,same_ctor_def]
        \\ ONCE_REWRITE_TAC[GSYM APPEND_ASSOC]
        \\ first_x_assum (match_mp_tac o MP_CANON)
        \\ fs[]
(*
  val _ = set_goal([],goal)
*)
  val tac = init_tac THEN case_tac
  val case_lemma = prove(goal,tac)
  val case_lemma = case_lemma |> PURE_REWRITE_RULE [TAG_def]
  val case_lemma = GEN H_var case_lemma
  in case_lemma end
  handle HOL_ERR _ => 
  (print ("derive_case_of error: " ^(type_to_string ty));
   raise (ERR "derive_case_of" ("failed on type : " ^(type_to_string ty))));

fun get_general_type ty =
  if can dest_type ty andalso not (List.null (snd (dest_type ty))) then let
      val (ty_cons, ty_args) = dest_type ty
      fun generate_varnames c i n =
	if n = 0 then [] else
	if Char.isAlpha c then (implode [#"'", c])::(generate_varnames (Char.succ c) i (n-1)) else
	("'a"^(Int.toString i))::(generate_varnames c (i+1) (n-1))
      val ty_names = generate_varnames #"a" 1 (List.length ty_args)
      val ty_args = List.map mk_vartype ty_names
  in mk_type(ty_cons, ty_args) end
  else ty
end

val mem_derive_case_ref = ref ([] : (hol_type * thm) list);
fun mem_derive_case_of ty =
  let
    fun lookup x [] = fail()
    | lookup x ((y,z)::ys) = if can (match_type y) x then z else lookup x ys
  in lookup ty (!mem_derive_case_ref) |> ISPEC (!H) end handle HOL_ERR _ =>
  (let
      val ty = get_general_type ty
      val th = derive_case_of ty
      val _ = (mem_derive_case_ref := (ty,th)::(!mem_derive_case_ref))
      val th = ISPEC (!H) th
  in th end);

val nsLookup_val_pat = ``nsLookup (env : env_val) (Short (vname : tvarN)) = SOME (loc : v)``
fun compute_dynamic_refs_bindings all_access_specs = let
    val store_vars = FVL [(!H)] empty_varset;
    fun get_dynamic_init_bindings spec = let
	val spec = SPEC_ALL spec |> UNDISCH_ALL
	val pat = nsLookup_val_pat
	val lookup_assums = List.filter (can (match_term pat)) (hyp (UNDISCH_ALL spec))
	fun get_name_loc tm = ((rand o rand o rand o rator) tm, (rand o rand) tm)
	val bindings = List.map get_name_loc lookup_assums
	val bindings = List.filter (fn (x, y) => HOLset.member(store_vars, y)) bindings
    in bindings end

    val all_bindings = List.concat(List.map get_dynamic_init_bindings all_access_specs)
    val bindings_map = List.foldl (fn ((n, v), m) => Redblackmap.insert(m, v, n))
				  (Redblackmap.mkDict Term.compare) all_bindings
    val store_varsl = strip_comb (!H) |> snd
    val final_bindings = List.map (fn x => (Redblackmap.find (bindings_map, x), x)) store_varsl
in final_bindings end

(* Initialize the translation by giving the appropriate values to the above references *)
fun init_translation (translation_parameters : monadic_translation_parameters) refs_funs arrays_funs exn_funs store_pred_exists_thm EXN_TYPE_def add_type_theories store_pinv_def_opt =
  let
      val {store_pred_def = store_pred_def,
           refs_specs  = refs_specs,
           arrays_specs = arrays_specs} = translation_parameters

      val _ = H_def := store_pred_def
      val _ = default_H := (concl store_pred_def |> strip_forall |> snd |> dest_eq |> fst)
      val _ = H := (!default_H)
      val _ = dynamic_init_H := (not (List.null (free_vars (!H))))
      val _ = refs_type := (type_of (!H) |> dest_type |> snd |> List.hd)
      val _ = EXN_TYPE_def_ref := EXN_TYPE_def
      val _ = EXN_TYPE := (EXN_TYPE_def |> CONJUNCTS |> List.hd |> concl |> strip_forall |> snd |> dest_eq |> fst |> strip_comb |> fst)
      val _ = exn_type := (type_of (!EXN_TYPE) |> dest_type |> snd |> List.hd)
      val _ = aM := (ty_antiq (M_type a_ty))
      val _ = bM := (ty_antiq (M_type b_ty))
      val _ = VALID_STORE_THM := store_pred_exists_thm
      val _ = type_theories := (current_theory()::(add_type_theories@["ml_translator"]))
      val _ = store_pinv_def := store_pinv_def_opt

      (* Exceptions *)
      val _ = exn_raises := []
      val _ = exn_handles := []
      val _ = exn_functions_defs := exn_funs

      (* Access functions for the references and the arrays *)
      fun get_access_info spec = let
	  val pat = concl spec |> strip_forall |> snd |> strip_imp |> snd |> rator |> rand |> rand
	  val spec = SPEC_ALL spec |> UNDISCH_ALL
      in (pat, spec) end
      val all_refs_specs = List.concat(List.map (fn (x, y) => [x, y]) refs_specs)
      val all_arrays_specs = List.concat (List.map (fn (x1, x2, x3, x4) =>
			     [x1, x2, x3, x4]) arrays_specs)
      val all_access_specs = all_refs_specs @ all_arrays_specs
      val _ = access_patterns := List.map get_access_info all_access_specs
      val _ = refs_functions_defs := refs_funs
      val _ = arrays_functions_defs := arrays_funs

      (* Data types *)
      val _ = mem_derive_case_ref := []

      (* Dynamic specs *)
      val _ = dynamic_v_thms := Net.empty

      (* Dynamic init environment *)
      val _ = dynamic_refs_bindings := (if (!dynamic_init_H) then
        compute_dynamic_refs_bindings all_access_specs else [])
  in () end;

(* user-initialisation functions *)
fun start_static_init_fixed_store_translation refs_init_list arrays_init_list store_hprop_name state_type exn_ri_def exn_functions add_type_theories store_pinv_opt = let
    val (monad_translation_params, store_trans_result) = translate_static_init_fixed_store refs_init_list arrays_init_list store_hprop_name state_type exn_ri_def store_pinv_opt

    val refs_funs_defs = List.map(fn (_, _, x, y) => (x, y)) refs_init_list
    val arrays_funs_defs = List.map (fn (_, _, x1, x2, x3, x4, x5, x6) => (x1, x2, x3, x4, x5, x6)) arrays_init_list
    val store_pinv_def_opt = case store_pinv_opt of SOME (th,_) => SOME th | NONE => NONE
    val store_pred_exists_thm = SOME(#store_pred_exists_thm store_trans_result)
    val _ = init_translation monad_translation_params refs_funs_defs arrays_funs_defs exn_functions store_pred_exists_thm exn_ri_def add_type_theories store_pinv_def_opt
    val exn_specs = if List.length exn_functions > 0 then
			add_raise_handle_functions exn_functions exn_ri_def
		    else []
in (monad_translation_params, store_trans_result, exn_specs) end

fun start_dynamic_init_fixed_store_translation refs_manip_list arrays_manip_list store_hprop_name state_type exn_ri_def exn_functions add_type_theories store_pinv_def_opt = let
    val monad_translation_params = translate_dynamic_init_fixed_store refs_manip_list arrays_manip_list store_hprop_name state_type exn_ri_def store_pinv_def_opt
    val refs_funs_defs = List.map(fn (_, x, y) => (x, y)) refs_manip_list
    val arrays_funs_defs = List.map (fn (_, x1, x2, x3, x4, x5, x6) => (x1, x2, x3, x4, x5, x6)) arrays_manip_list
    val store_pred_exists_thm = NONE
    val _ = init_translation monad_translation_params refs_funs_defs arrays_funs_defs exn_functions store_pred_exists_thm exn_ri_def add_type_theories store_pinv_def_opt
    val exn_specs = if List.length exn_functions > 0 then
			add_raise_handle_functions exn_functions exn_ri_def
		    else []
in (monad_translation_params, exn_specs) end

fun inst_case_thm_for tm = let
  val (_,_,names) = TypeBase.dest_case tm
  val names = List.map fst names
  val th = mem_derive_case_of ((repeat rator tm) |> type_of |> domain) |> UNDISCH
  val pat = th |> UNDISCH_ALL |> concl |> rator |> rand |> rand
  val (ss,i) = match_term pat tm
  val th = INST ss (INST_TYPE i th)
  val ii = List.map (fn {redex = x, residue = y} => (x,y)) i
  val ss = List.map (fn (x,y) => (inst i (smart_get_type_inv x) |-> smart_get_type_inv y)) ii
  val th = INST ss th
  val th = CONV_RULE (DEPTH_CONV BETA_CONV) th
  fun args tm = let val (x,y) = dest_comb tm in args x @ [y] end
                handle HOL_ERR _ => []
  val ns = List.map (fn n => (n,args n)) names
  fun rename_var prefix ty v =
    mk_var(prefix ^ implode (tl (explode (fst (dest_var v)))),ty)
  val ts = find_terms (can (match_term ``ml_translator$CONTAINER (b:bool)``)) (concl th)
           |> List.map (rand o rand)
           |> List.map (fn tm => (tm,List.map (fn x => (x,rename_var "n" string_ty x,
                                                rename_var "v" v_ty x))
                    (dest_args tm handle HOL_ERR _ => [])))
  val ns = List.map (fn (tm,xs) => let
      val aa = snd (first (fn (pat,_) => can (match_term tm) pat) ns)
      in zip aa xs end) ts |> flatten
  val ms = List.map (fn (b,(x,n,v)) => n |-> stringSyntax.fromMLstring (fst (dest_var b))) ns
  val th = INST ms th
  val ks = List.map (fn (b,(x,n,v)) => (fst (dest_var x), fst (dest_var b))) ns @
           List.map (fn (b,(x,n,v)) => (fst (dest_var v), fst (dest_var b) ^ "{value}")) ns
  fun rename_bound_conv tm = let
    val (v,x) = dest_abs tm
    val (s,ty) = dest_var v
    val new_s = snd (first (fn (z,_) => z = s) ks)
    in ALPHA_CONV (mk_var(new_s,ty)) tm end handle HOL_ERR _ => NO_CONV tm
  val th = CONV_RULE (DEPTH_CONV rename_bound_conv) th
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV) EVAL) th
  val th = MP th TRUTH
  in th end;

(*
val tm = (!last_fail)
val original_tm = tm;

val tm = dest_conj hyps |> snd
sat_hyps tm
*)

val EvalM_pat = ``EvalM env st e p H``
fun inst_case_thm tm m2deep = let
  val tm = if can dest_monad_type (type_of tm) then (inst_monad_type tm) else tm
  val th = inst_case_thm_for tm
  val th = CONV_RULE (RATOR_CONV (PURE_REWRITE_CONV [CONJ_ASSOC])) th
  val (hyps,rest) = dest_imp (concl th)
  fun list_dest_forall tm = let
    val (v,tm) = dest_forall tm
    val (vs,tm) = list_dest_forall tm
    in (v::vs,tm) end handle HOL_ERR _ => ([],tm)
  fun take n xs = List.take(xs, n)
  fun simp_env tm =
    if can (match_term EvalM_pat) tm then
	REPEATC ((PURE_ONCE_REWRITE_CONV [EvalM_Var_SIMP]) THENC (SIMP_CONV list_ss string_rewrites)) tm
    else NO_CONV tm
  fun sat_hyp tm = let
    val (vs,x) = list_dest_forall tm
    val (x,y) = dest_imp x
    val z = get_Eval_arg y
    val lemma = if can dest_monad_type (type_of z)
                then m2deep z
                else hol2deep z
    val lemma = D lemma
    val new_env = get_Eval_env y
    val env = v_env
    val lemma = INST [env|->new_env] lemma
    val (x1,x2) = dest_conj x handle HOL_ERR _ => (T,x)
    val (z1,z2) = dest_imp (concl lemma)
    val thz =
      QCONV (SIMP_CONV std_ss [ASSUME x1,Eval_Var_SIMP] THENC
             ONCE_REWRITE_CONV [EvalM_Var_SIMP] THENC
             ONCE_REWRITE_CONV [EvalM_Var_SIMP] THENC
             REWRITE_CONV [lookup_cons_write,lookup_var_write] THENC
             DEPTH_CONV stringLib.string_EQ_CONV THENC
             SIMP_CONV std_ss []) z1 |> DISCH x1
    val lemma = MATCH_MP sat_hyp_lemma (CONJ thz lemma)
    val bs = take (length vs div 2) vs
    fun LIST_UNBETA_CONV [] = ALL_CONV
      | LIST_UNBETA_CONV (x::xs) =
          UNBETA_CONV x THENC RATOR_CONV (LIST_UNBETA_CONV xs)
    val lemma = CONV_RULE ((RATOR_CONV o RAND_CONV o RAND_CONV)
                  (LIST_UNBETA_CONV (rev bs))) lemma
    val lemma = GENL vs lemma
    (* Clean the environments in the lemma *)
    val lemma = CONV_RULE ((STRIP_QUANT_CONV o RATOR_CONV o RAND_CONV) (DEPTH_CONV simp_env)) lemma
    (* Return *)
    val _ = can (match_term tm) (concl lemma) orelse failwith("sat_hyp failed")
    in lemma end handle HOL_ERR _ => (print ((term_to_string tm) ^ "\n\n"); last_fail := tm; fail())
  fun sat_hyps tm = if is_conj tm then let
    val (x,y) = dest_conj tm
    in CONJ (sat_hyps x) (sat_hyps y) end else sat_hyp tm
  val lemma = sat_hyps hyps
  val th = MATCH_MP th lemma
  val th = CONV_RULE (RATOR_CONV (DEPTH_CONV BETA_CONV THENC
                                  REWRITE_CONV [])) th
  in th |> UNDISCH_ALL end handle Empty => failwith "empty";

(* PMATCH *)
val IMP_EQ_T = Q.prove(`a ==> (a <=> T)`,fs [])
val BETA_PAIR_THM = Q.prove(`(\(x, y). f x y) (x, y) = (\x y. f x y) x y`, fs[])

val var_assum = ``Eval env (Var n) (a (y:'a))``
val nsLookup_assum = ``nsLookup env name = opt``
val lookup_cons_assum = ``lookup_cons name env = opt``
val eqtype_assum = ``EqualityType A``
fun prove_EvalMPatBind goal m2deep = let
  val (vars,rhs_tm) = repeat (snd o dest_forall) goal
                      |> rand |> get_Eval_arg |> rator
                      |> dest_pabs
  val res = m2deep rhs_tm
  val exp = res |> concl |> get_Eval_exp
  val th = D res
  (* *)
  val is_var_assum = can (match_term var_assum)
  fun is_lookup_eqtype_assum x =
      can (match_term nsLookup_assum) x
      orelse can (match_term lookup_cons_assum) x
      orelse can (match_term eqtype_assum) x
  val vs = find_terms is_var_assum (concl th)
  val assums = find_terms is_lookup_eqtype_assum (concl th)
  val all_assums = append vs assums
  fun delete_assum tm =
    if mem tm (all_assums) then MATCH_MP IMP_EQ_T (ASSUME tm)
    else NO_CONV tm
  val th = CONV_RULE ((RATOR_CONV) (DEPTH_CONV delete_assum)) th
  val th = CONV_RULE ((RATOR_CONV) (SIMP_CONV bool_ss [])) th
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV)
              (PairRules.UNPBETA_CONV vars)) th
  val p = th |> concl |> dest_imp |> fst |> rator
  val p2 = goal |> dest_forall |> snd |> dest_forall |> snd
                |> dest_imp |> fst |> rand |> rator
  val ws = free_vars vars
  val vs = List.filter (fn tm => not (mem (rand (rand tm)) ws)) vs |> mk_set
  val new_goal = goal |> subst [mk_var("e",exp_ty)|->exp,p2 |-> p]
  val all_assums = (append vs assums)
  val all_assums = List.foldl (fn (x,s) => HOLset.add (s,x)) empty_tmset all_assums |> HOLset.listItems
  val num_assums = List.length all_assums
  val new_goal = List.foldr mk_imp new_goal all_assums
  (*
    set_goal([],new_goal)
  *)
  val th = TAC_PROOF (([],new_goal),
    NTAC num_assums STRIP_TAC \\ STRIP_TAC
    (**)
    \\ FULL_SIMP_TAC pure_ss [FORALL_PROD,BETA_PAIR_THM, UNCURRY_DEF]
    \\ CONV_TAC (DEPTH_CONV BETA_CONV)
    \\ REPEAT STRIP_TAC
    (* \\ fs [FORALL_PROD] \\ REPEAT STRIP_TAC *)
    \\ MATCH_MP_TAC (D res) \\ fs []
    \\ fs [EvalPatBind_def,Pmatch_def]
    \\ REPEAT (POP_ASSUM MP_TAC)
    \\ NTAC num_assums STRIP_TAC
    \\ CONV_TAC ((RATOR_CONV o RAND_CONV) EVAL) (* Expand the refin. inv. *)
    \\ STRIP_TAC \\ fs [] \\ rfs []
    \\ fs [Pmatch_def,PMATCH_option_case_rwt]
    \\ BasicProvers.EVERY_CASE_TAC \\ fs []
    \\ rpt (CHANGED_TAC(SRW_TAC [] [Eval_Var_SIMP,Once EvalM_Var_SIMP,lookup_cons_write,lookup_var_write]))
    \\ TRY (first_x_assum match_mp_tac >> METIS_TAC[])
    \\ fs[GSYM FORALL_PROD]
    \\ EVAL_TAC)
  in UNDISCH_ALL th end handle HOL_ERR e => failwith ("prove_EvalMPatBind failed: (" ^ #message e ^ ")");

val pmatch_index = ref 1;
fun pmatch_m2deep tm m2deep = let
  val (x,ts) = dest_pmatch_K_T tm
  val v = genvar (type_of x)
  val x_res = hol2deep x |> D
  val x_type = type_of x
  val x_inv = get_type_inv x_type
  val pmatch_type = type_of tm
  val pmatch_inv = get_m_type_inv pmatch_type
  val x_exp = x_res |> UNDISCH |> concl |> rator |> rand
  val nil_lemma = EvalM_PMATCH_NIL
		  |> ISPEC_EvalM
                  |> ISPEC pmatch_inv
                  |> ISPEC x_exp
                  |> ISPEC v
                  |> ISPEC x_inv
  val cons_lemma = EvalM_PMATCH
		   |> ISPEC_EvalM
                   |> ISPEC pmatch_inv
                   |> ISPEC x_inv
                   |> ISPEC x_exp
                   |> ISPEC v
  fun prove_hyp conv th =
    MP (CONV_RULE ((RATOR_CONV o RAND_CONV) conv) th) TRUTH
  val assm = nil_lemma |> concl |> dest_imp |> fst

(*
DEBUG:

val th = nil_lemma

val n = 19;
val xs = drop (ts,n);
val (pat,rhs_tm) = el n ts;
val th = trans xs

val i = ref (List.length ts)
val xs_ref = ref ts
val th_ref = ref nil_lemma
*)
  val index_str = Int.toString (!pmatch_index)
  val _ = pmatch_index := (!pmatch_index + 1)
  val n = List.length ts
  fun trans [] = nil_lemma
    | trans ((pat,rhs_tm)::xs) = let
    val th = trans xs
    val i_str = Int.toString (n - (List.length xs))
    val _ = print ("pmatch " ^index_str ^ " " ^ i_str  ^ "\n")
    (* DEBUG
    val _ = (i := !i - 1)
    val _ = th_ref := th
    val _ = xs_ref := xs
    val _ = print ((Int.toString (!i)) ^ "\n")
    DEBUG *)
    val p = pat |> dest_pabs |> snd |> hol2deep
                |> concl |> rator |> rand |> to_pattern
    val lemma = cons_lemma |> Q.GEN `p` |> ISPEC p
    val lemma = prove_hyp EVAL lemma
    val lemma = lemma |> Q.GEN `pat` |> ISPEC pat
    val lemma = prove_hyp (SIMP_CONV (srw_ss()) [FORALL_PROD]) lemma
    val lemma = UNDISCH lemma
    val th = UNDISCH th
             |> CONV_RULE ((RATOR_CONV o RAND_CONV) (UNBETA_CONV v))
    val th = MATCH_MP lemma th
    val th = remove_primes th
    val goal = fst (dest_imp (concl th))
    val th = MP th (prove_EvalPatRel goal hol2deep)
    val th = remove_primes th
    val th = th |> Q.GEN `res` |> ISPEC rhs_tm
    val goal = fst (dest_imp (concl th))
    val th = MATCH_MP th (prove_EvalMPatBind goal m2deep)
    val th = remove_primes th
    val th = CONV_RULE ((RATOR_CONV o RAND_CONV)
          (SIMP_CONV std_ss [FORALL_PROD,patternMatchesTheory.PMATCH_ROW_COND_def])) th
    val th = DISCH assm th
    in th end

  val th = trans ts
  val _ = pmatch_index := (!pmatch_index - 1)
  val th = MY_MATCH_MP th (UNDISCH x_res) (* strange bug with MATCH_MP: the side function variable is sometimes renamed?? *)
  val th = UNDISCH_ALL th
  in th end handle HOL_ERR e =>
  failwith ("pmatch_m2deep failed (" ^ #message e ^ ")");

(*
DEBUG:

val j = !i + 1;
val j = 3
val xs = drop(ts, j)
val (pat,rhs_tm) = List.hd (List.drop(ts, j-1))
val th = !th_ref
*)

(* ---- *)

fun inst_EvalM_env v th = let
  val thx = th
  val name = fst (dest_var v)
  val str = stringLib.fromMLstring name
  val inv = smart_get_type_inv (type_of v)
  val tys = Type.match_type (type_of v) (type_of inv |> dest_type |> snd |> List.hd)
  val v = Term.inst tys v
  val ri = mk_comb(inv, v)
  (* val assum = ``Eval env (Var (Short ^str)) ^ri`` 
  val new_env = ``write ^str (v:v) ^v_env`` *)
  val assum = ISPECL_TM [str,ri] Eval_name_RI_abs
  val new_env = mk_write str v_var v_env
  val old_env = new_env |> rand
  fun simp_EvalM_env tm =
    if can (match_term EvalM_pat) tm then
	REPEATC ((PURE_ONCE_REWRITE_CONV [EvalM_Var_SIMP]) THENC (DEPTH_CONV stringLib.string_EQ_CONV) THENC (SIMP_CONV bool_ss [])) tm
    else NO_CONV tm
  val th = thx |> UNDISCH_ALL |> REWRITE_RULE [GSYM SafeVar_def]
               |> DISCH_ALL |> DISCH assum |> SIMP_RULE bool_ss []
               |> INST [old_env|->new_env]
               |> SIMP_RULE bool_ss [Eval_Var_SIMP,lookup_var_write]
               (* |> ONCE_REWRITE_RULE [EvalM_Var_SIMP]
               |> ONCE_REWRITE_RULE [EvalM_Var_SIMP] *)
               |> REWRITE_RULE [lookup_cons_write,lookup_var_write]
               |> CONV_RULE (DEPTH_CONV stringLib.string_EQ_CONV)
               |> SIMP_RULE bool_ss [SafeVar_def]
  val new_assum = fst (dest_imp (concl th))
  (**)
  val th1 = th |> UNDISCH
	       |> PURE_REWRITE_RULE[AND_IMP_INTRO]
	       |>  CONV_RULE ((RATOR_CONV o RAND_CONV) (DEPTH_CONV simp_EvalM_env))
	       (***)
	       |> UNDISCH_ALL
               |> CONV_RULE ((RATOR_CONV o RAND_CONV o RAND_CONV) (UNBETA_CONV v))
               |> DISCH new_assum
  in th1 end

fun remove_ArrowM_EqSt th = let
  val st_var = th |> concl |> rator |> rand |> rator |> rator |> rand |> rand
  val th = GEN st_var th |> MATCH_MP ArrowM_EqSt_elim
in th end handle HOL_ERR _ => th;

fun inst_new_state_var thms th = let
    val fvs = FVL (List.map (concl o DISCH_ALL) thms) empty_varset
    val current_state_var = UNDISCH_ALL th |> concl |> get_EvalM_state
    val basename = "st"
    fun find_new_state_var i = let
	val name = basename ^(Int.toString i)
	val state_var = mk_var(name, !refs_type)
    in if not (HOLset.member (fvs, state_var))
       then state_var else find_new_state_var (i+1)
    end
    val nstate_var = find_new_state_var 1
    val th = Thm.INST [current_state_var |-> nstate_var] th
in th end;

fun remove_ArrowM_EqSt th = let
  val st_var = th |> concl |> rator |> rand |> rator |> rator |> rand |> rand
  val th = GEN st_var th |> MATCH_MP ArrowM_EqSt_elim
in th end handle HOL_ERR _ => th;

fun inst_new_state_var thms th = let
    val fvs = FVL (List.map (concl o DISCH_ALL) thms) empty_varset
    val current_state_var = UNDISCH_ALL th |> concl |> get_EvalM_state
    val basename = "st"
    fun find_new_state_var i = let
	val name = basename ^(Int.toString i)
	val state_var = mk_var(name, !refs_type)
    in if not (HOLset.member (fvs, state_var))
       then state_var else find_new_state_var (i+1)
    end
    val nstate_var = find_new_state_var 1
    val th = Thm.INST [current_state_var |-> nstate_var] th
in th end;

fun apply_EvalM_Fun v th fix = let
  val th1 = inst_EvalM_env v th
  val th2 = inst_new_state_var [th1] th1
  val th3 = if fix then MATCH_MP EvalM_Fun_Eq (GEN v_var th2)
                   else MATCH_MP EvalM_Fun (GEN v_var (FORCE_GEN v th2))
  in th3 end;

fun apply_EvalM_Recclosure recc fname v th = let
  val vname = fst (dest_var v)
  val vname_str = stringLib.fromMLstring vname
  val fname_str = stringLib.fromMLstring fname
  val FORALL_CONV = RAND_CONV o ABS_CONV
  val is_monad_only = not (can (match_term (SPEC_ALL ArrowM_def |> concl |> dest_eq |> fst)) (concl th |> rator |> rand |> rator))
  val lemma = if is_monad_only
    then ISPECL [!H, recc,fname_str] EvalM_Recclosure_ALT2 |> UNDISCH
    else ISPECL [!H, recc,fname_str] EvalM_Recclosure_ALT
  val lemma = lemma |> CONV_RULE ((FORALL_CONV o FORALL_CONV o
                           RATOR_CONV o RAND_CONV) EVAL)              
  val pat1 = lemma |> concl |> find_term (can (match_term (ml_translatorLib.get_term "find_recfun")))
  val lemma = SIMP_RULE std_ss [EVAL pat1] lemma
  val inv = smart_get_type_inv (type_of v)
  val pat = EvalM_def |> SPEC_ALL |> concl |> dest_eq |> fst |> rator |> rator |> rator |> rator
  val pat = lemma |> concl |> find_term (can (match_term pat))
  val new_env = pat |> rand
  val old_env = v_env
  val tys = Type.match_type (type_of v) (type_of inv |> dest_type |> snd |> List.hd)
  val v = Term.inst tys v
  val assum = subst [old_env|->new_env]
              (ISPECL_TM [vname_str,mk_comb(inv,v)] Eval_name_RI_abs)
              (* ``Eval env (Var (Short ^vname_str)) (^inv ^v)`` *)
  val state_var = UNDISCH_ALL th |> concl |> get_EvalM_state
  val thx = th |> UNDISCH_ALL |> REWRITE_RULE [GSYM SafeVar_def]
               |> DISCH_ALL |> DISCH assum
               |> INST [old_env|->new_env]
               |> SIMP_RULE pure_ss [EvalM_Var_SIMP_ArrowM, Eval_Var_SIMP,lookup_var_write,lookup_cons_write]
               |> CONV_RULE (DEPTH_CONV stringLib.string_EQ_CONV)
               |> REWRITE_RULE [SafeVar_def]
  val new_assum = fst (dest_imp (concl thx))
  val th1 = thx |> UNDISCH |> REWRITE_RULE [ASSUME new_assum]
		|> UNDISCH_ALL
                |> CONV_RULE ((RATOR_CONV o RAND_CONV o RAND_CONV) (UNBETA_CONV v)) (* RATOR_CONV *)
                |> DISCH new_assum
  val th2 = if not is_monad_only
	    then MATCH_MP lemma (Q.INST [`env`|->`cl_env`]
					(GENL [state_var, v_var] th1))
    else let
      val assum = DISCH_ALL th1 |> concl |> dest_imp |> fst
      val A = mk_abs(state_var, assum)
      val A_eq = BETA_CONV (mk_comb(A,state_var))
      val th = (Q.INST [`env`|->`cl_env`] (GENL [state_var, v_var] (th1 |> DISCH_ALL))) |> SIMP_RULE pure_ss [Once(GSYM A_eq)]
      val th = MATCH_MP (ISPECL [!H, recc,fname_str] EvalM_Recclosure_ALT3 |> SPEC_ALL) th
			|> SIMP_RULE pure_ss [A_eq] |> UNDISCH
      val th = CONV_RULE ((RATOR_CONV o RAND_CONV) EVAL) th
      val th = SIMP_RULE std_ss [EVAL pat1] th
    in th end
  val assum = ASSUME (fst (dest_imp (concl th2)))
  val th3 = D th2 |> REWRITE_RULE [assum]
                  |> SIMP_RULE pure_ss [Eval_Var_SIMP, EvalM_Var_SIMP_ArrowM,lookup_var_write,FOLDR,write_rec_def]
                  |> CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV)
                  |> REWRITE_RULE [Eval_Var_SIMP, EvalM_Var_SIMP_ArrowM, lookup_var_write,FOLDR]
                  |> CONV_RULE (DEPTH_CONV stringLib.string_EQ_CONV)
                  |> REWRITE_RULE [SafeVar_def]
  val lemma = UNDISCH EvalM_Eq_Recclosure
  val lemma_lhs = lemma |> concl |> dest_eq |> fst
  fun replace_conv tm = let
    val (i,t) = match_term lemma_lhs tm
    val th9 = INST i (INST_TYPE t lemma)
    val name = lemma_lhs |> inst t |> subst i |> rand |> rand
    in INST [mk_var("name",string_ty)|->name] th9 end handle HOL_ERR _ => NO_CONV tm
  val th4 = CONV_RULE (QCONV (DEPTH_CONV replace_conv)) th3
in th4 end;

(* Adapted from ml_translatorLib *)
val check_inv_fail = ref T;

fun check_inv name tm result = let
  val tm2 = get_Eval_arg (concl result)
  in if aconv tm2 tm then result else let
    val _ = (check_inv_fail := tm)
    val _ = (show_types_verbosely := true)
    val _ = print ("\n\nhol2deep failed at '" ^ name ^ "'\n\ntarget:\n\n")
    val _ = print_term tm
    val _ = print "\n\nbut derived:\n\n"
    val _ = print_term tm2
    val _ = print "\n\n\n"
    val _ = (show_types_verbosely := false)
    in failwith("checkinv") end end
(* end of adaptation *)

(* COPY/PASTE from ml_translatorLib *)
fun rm_fix res = let
  val lemma1 = mk_thm([],ml_translatorLib.get_term "eq remove")
  val lemma2 = mk_thm([],get_term "EqSt remove")
  val tm2 = QCONV (REWRITE_CONV [lemma1,lemma2]) res
		  |> concl |> dest_eq |> snd
  in tm2 end
(* End of COPY/PASTE from ml_translatorLib *)

fun force_remove_fix thx = let
  val pat = Eq_def |> SPEC_ALL |> concl |> dest_eq |> fst
  val xs = List.map rand (find_terms (can (match_term pat)) (concl thx))
  val s = SIMP_RULE std_ss [EvalM_FUN_FORALL_EQ,M_FUN_QUANT_SIMP]
  val thx = List.foldr (fn (x,th) => s (FORCE_GEN x th)) thx xs

  val thx = UNDISCH_ALL thx |> PURE_REWRITE_RULE[ArrowM_def]
  val thc = concl thx |> rator |> rand |> rator |> rand
  val st_opt = get_EqSt_var thc
in case st_opt of
       SOME st => HO_MATCH_MP EvalM_FUN_FORALL (GEN st thx)
			      |> SIMP_RULE std_ss [M_FUN_QUANT_SIMP]
			      |> PURE_REWRITE_RULE[GSYM ArrowM_def]
     | NONE => PURE_REWRITE_RULE[GSYM ArrowM_def] thx
end

(* ---- *)
fun var_hol2deep tm =
  if is_var tm andalso can get_arrow_type_inv (type_of tm) then let
    val (name,ty) = dest_var tm
    val inv = get_arrow_type_inv ty
    val inv = ONCE_REWRITE_CONV [ArrowM_def] inv |> concl |> rand |> rand
    val str = stringSyntax.fromMLstring name
    val result = ISPECL_TM [str,mk_comb(inv,tm)] Eval_name_RI_abs |> ASSUME
    in check_inv "var" tm result end
  else hol2deep tm;

(* raise, handle *)
fun get_pattern patterns tm = tryfind (fn(pat, th) => if can (match_term pat) tm then (pat, th) else failwith "get_pattern") patterns;

fun print_tm_msg msg tm =
  print (msg  ^(term_to_string tm) ^ "\n\n");

val H_STAR_TRUE = Q.prove(`(H * &T = H) /\ (&T * H = H)`, fs[SEP_CLAUSES])

fun inst_EvalM_bind th1 th2 = let
    val vs = concl th2 |> dest_imp |> fst
    val v = rand vs
    val z = rator vs |> rand
    val th2' = Dfilter (UNDISCH th2) vs
    val a2 = concl th2' |> dest_imp |> fst
    val a2 = mk_comb(mk_abs(z, a2), z)
    val a2_eq = BETA_CONV a2 |> GSYM
    val th2' = CONV_RULE ((RATOR_CONV o RAND_CONV) (PURE_ONCE_REWRITE_CONV[a2_eq])) th2'
    val th2' = DISCH vs th2' |> GENL[z, v]
    val x = concl th1 |> rator |> rand |> rand
    val st_var = mk_var("st", !refs_type)
    val n_st = my_list_mk_comb(SND_const, [mk_comb(x,st_var)])
    val th2' = INST [st_var |-> n_st] th2'
    val th1' = D th1
    val result = MATCH_MP EvalM_bind (CONJ th1' th2')
    val result = UNDISCH result
in result end;

fun inst_EvalM_handle EvalM_th tm m2deep = let
    val x = tm |> rator |> rand
    val (v,y) = tm |> rand |> dest_abs
    val th1 = m2deep x
    val th2 = m2deep y
    val th3 = inst_EvalM_env v th2
    val type_assum = concl th3 |> dest_imp |> fst
    val th4 = Dfilter (UNDISCH th3) type_assum
    val assums = concl th4 |> dest_imp |> fst
    val state_var = th4 |> concl |> dest_imp |> snd |> get_EvalM_state
    val t = rator type_assum |> rand
    val v = rand type_assum
    val assums_abs = list_mk_comb(list_mk_abs([state_var, t], assums), [state_var, t])
    val assums_eq = ((RATOR_CONV BETA_CONV) THENC BETA_CONV) assums_abs
    val th5 = CONV_RULE ((RATOR_CONV o RAND_CONV) (PURE_ONCE_REWRITE_CONV [GSYM assums_eq])) th4 |> DISCH type_assum |> GENL[state_var, t, v]
    val lemma = EvalM_th |> SPEC_ALL |> UNDISCH
    val th6 = CONJ (D th1) th5
    val result = (MATCH_MP lemma th6 handle HOL_ERR _ => HO_MATCH_MP th4 th3)
    val result = CONV_RULE ((RATOR_CONV o RAND_CONV) (DEPTH_CONV BETA_CONV)) result |> UNDISCH
in result end;

fun inst_EvalM_otherwise tm m2deep = let
    val x = tm |> rator |> rand
    val y = tm |> rand
    val th1 = m2deep x
    val th2 = m2deep y
  fun simp_EvalM_env tm =
    if can (match_term EvalM_pat) tm then
	REPEATC ((PURE_ONCE_REWRITE_CONV [EvalM_Var_SIMP]) THENC (DEPTH_CONV stringLib.string_EQ_CONV) THENC (SIMP_CONV bool_ss [])) tm
    else NO_CONV tm
    val th2 = th2 |> UNDISCH_ALL |> REWRITE_RULE [GSYM SafeVar_def]
		  |> DISCH_ALL |> Q.INST [`env`|->`write "v" i env`]
                  |> REWRITE_RULE [Eval_Var_SIMP,lookup_cons_write]
		  |> UNDISCH_ALL
		  |> HYP_CONV_RULE (fn x => true) (DEPTH_CONV simp_EvalM_env)
		  |> DISCH_ALL
                  |> REWRITE_RULE [lookup_cons_write,lookup_var_write]
                  |> CONV_RULE (DEPTH_CONV stringLib.string_EQ_CONV)
                  |> REWRITE_RULE []
                  |> REWRITE_RULE [SafeVar_def] |> D
    val st2 = concl th2 |> dest_imp |> snd |> get_EvalM_state
    val assums = concl th2 |> dest_imp |> fst
    val assums_eq = mk_comb(mk_abs(st2, assums), st2) |> BETA_CONV
    val th3 = CONV_RULE ((RATOR_CONV o RAND_CONV) (PURE_ONCE_REWRITE_CONV [GSYM assums_eq])) th2 |> Q.GEN `i` |> GEN st2 
    val th4 = CONJ (D th1) th3
    val result = MATCH_MP (SPEC_ALL EvalM_otherwise) th4
    val result = CONV_RULE ((RATOR_CONV o RAND_CONV) (DEPTH_CONV BETA_CONV)) result |> UNDISCH
in result end;

fun inst_gen_eq_vars th = let
    (* Instantiate the variables in the occurences of Eq *)
    val pat = Eq_def |> SPEC_ALL |> concl |> dest_eq |> fst
    val xs = find_terms (can (match_term pat)) (concl th) |> List.map rand
    val ss = List.map (fn v => v |-> genvar(type_of v)) xs
    val th = INST ss th
    (* Instantiate the variable in EqSt *)
    val thc = UNDISCH_ALL th |> PURE_REWRITE_RULE[ArrowM_def]
			    |> concl |> rand |> rator |> rand |> rand
    val state_var_opt = get_EqSt_var thc
    val th = case state_var_opt of NONE => th 
      | SOME v => INST [v |-> genvar(type_of v)] th
    (* *)
in th end

fun m2deep_previously_translated th tm = let
    val th = inst_gen_eq_vars th
    val res = th |> UNDISCH_ALL |> concl |> rand
    val inv = smart_get_type_inv (type_of tm)
    val target = mk_comb(inv,tm)
    val (ss,ii) = match_term res target handle HOL_ERR _ =>
      match_term (rm_fix res) (rm_fix target) handle HOL_ERR _ => ([],[])
    val result = INST ss (INST_TYPE ii th)
		      |> MY_MATCH_MP (ISPEC_EvalM Eval_IMP_PURE |> SPEC_ALL)
                      |> REWRITE_RULE [GSYM ArrowM_def]
in result end

(* normal function application *)
val nsLookup_assum = ``nsLookup env name = opt``
val lookup_cons_assum = ``lookup_cons name env = opt``
val eqtype_assum = ``EqualityType A``
fun m2deep_normal_fun_app tm m2deep = let
    val (f,x) = dest_comb tm
    val thf = m2deep f |> (CONV_RULE ((RATOR_CONV o RAND_CONV o RATOR_CONV o RATOR_CONV o RAND_CONV) (PURE_REWRITE_CONV [ArrowM_def])))
    val (thx,is_monad) =
	((hol2deep x |> MATCH_MP (ISPEC_EvalM Eval_IMP_PURE) |> D,false)
	      handle e => (D(m2deep x),true))
    (* If the argument is monadic, clean it by removing Eq and EqSt*)
    val is_var_assum = can (match_term var_assum)
    fun is_var_lookup_eqtype_assum x =
      can (match_term var_assum) x
      orelse can (match_term nsLookup_assum) x
      orelse can (match_term lookup_cons_assum) x
      orelse can (match_term eqtype_assum) x
    val assums = find_terms is_var_lookup_eqtype_assum (concl thx)
    fun delete_assums tm =
      if mem tm assums then MATCH_MP IMP_EQ_T (ASSUME tm)
      else NO_CONV tm
    val thx = CONV_RULE ((RATOR_CONV) (DEPTH_CONV delete_assums)) thx
    val thx = CONV_RULE ((RATOR_CONV o RAND_CONV)
              (SIMP_CONV (srw_ss()) [CONTAINER_def])) thx
    val thx =  MP thx TRUTH
	       handle HOL_ERR _ => failwith "normal function application"
    val thx = force_remove_fix thx |> PURE_REWRITE_RULE[ArrowM_def]

    (* Compute the result *)
    val result = MATCH_MP (MATCH_MP EvalM_ArrowM thf
                 |> PURE_REWRITE_RULE[ArrowM_def]) thx
		 handle HOL_ERR _ =>
                 MY_MATCH_MP (MATCH_MP EvalM_ArrowM thf)
			     (MATCH_MP EvalM_Eq thx)
		 handle HOL_ERR _ => let
      val state_var = concl thf |> get_EvalM_state
      val thc = PURE_REWRITE_RULE[ArrowM_def] thf |> concl
				 |> rator |> rand |> rator |> rand
      val eq_state_var_opt = get_EqSt_var thc
      in case eq_state_var_opt of NONE =>
				  failwith "m2deep: function application" 
         | SOME v => MY_MATCH_MP (MATCH_MP EvalM_ArrowM_EqSt
					   (INST [v |-> state_var] thf))
				 (MATCH_MP EvalM_Eq thx)
      end
    val result = PURE_REWRITE_RULE [GSYM ArrowM_def] result
in result end

val nsLookup_closure_pat = ``nsLookup env1.v (Short name1) =
		             SOME (Closure env2 name2 exp)``
val nsLookup_recclosure_pat = ``nsLookup env1.v (Short name1) =
                                SOME (Recclosure env2 exps name2)``
fun abbrev_nsLookup_code th = let
    (* Prevent the introduction of abbreviations for already abbreviated code *)
    val th = HYP_CONV_RULE (fn x => true) (PURE_REWRITE_CONV (List.map GSYM (!local_code_abbrevs))) th
    val pat1 = nsLookup_closure_pat
    val pat2 = nsLookup_recclosure_pat
    fun can_match_pat tm = can (match_term pat1) tm orelse
			   can (match_term pat2) tm
    val lookup_assums = List.filter can_match_pat (hyp th)
    val get_fun_name =
	stringSyntax.fromHOLstring o rand o rand o rand o rator
    fun get_code tm =
	if can (match_term pat1) tm then (rand o rand o rand) tm
	else (rand o rator o rand o rand) tm
    val name_code_pairs =
	List.map(fn x => (get_fun_name x, get_code x)) lookup_assums
		|> List.filter (not o is_const o snd)

    fun find_abbrev (name, code) = let
	val n = Theory.temp_binding ("[[ " ^ name ^ "_code ]]")
	val code_def = new_definition(n,mk_eq(mk_var(n,type_of code),code))
    in code_def end
    val abbrevs = List.map find_abbrev name_code_pairs
    val _ = local_code_abbrevs := List.concat [abbrevs, !local_code_abbrevs]
    val th = HYP_CONV_RULE (fn x => true) (PURE_REWRITE_CONV (List.map GSYM abbrevs)) th
in th end

fun remove_local_code_abbrevs th = let
        val th = HYP_CONV_RULE (fn x => true) (PURE_REWRITE_CONV (!local_code_abbrevs)) th |> CONV_RULE (PURE_REWRITE_CONV (!local_code_abbrevs))
in th end

fun undef_local_code_abbrevs () = let
    val undef = (delete_const o fst o dest_const o rand o rator o concl)
    val _ = mapfilter undef (!local_code_abbrevs)
    val _ = local_code_abbrevs := []
in () end

fun m2deep tm =
  (* variable *)
  if is_var tm then let
    (* val _ = print_tm_msg "is_var\n" tm DEBUG *)
    val (name,ty) = dest_var tm
    val inv = get_arrow_type_inv ty
    val inv = ONCE_REWRITE_CONV [ArrowM_def] inv |> concl |> rand |> rand
    val str = stringSyntax.fromMLstring name
    val result = ISPECL_TM [str,mk_comb(inv,tm)] Eval_name_RI_abs |> ASSUME
    val result = MATCH_MP (ISPEC_EvalM Eval_IMP_PURE) result |> RW [GSYM ArrowM_def]
    in check_inv "var" tm result end else
  (* raise *)
  if can (get_pattern (!exn_raises)) tm then let
    (* val _ = print_tm_msg "raise custom pattern\n" tm DEBUG *)
    val (_, EvalM_th) = get_pattern (!exn_raises) tm
    val ty = dest_monad_type (type_of tm)
    val inv = smart_get_type_inv (#2 ty)
    val th = hol2deep (rand tm)
    val asms = List.mapPartial (Lib.total DECIDE) (hyp th)
    val th = List.foldl (Lib.uncurry PROVE_HYP) th asms
    val result = ISPEC_EvalM EvalM_th |> SPEC (rand tm) |> ISPEC inv
                 |> UNDISCH |> Lib.C MATCH_MP th
    in check_inv "raise custom pattern" tm result end else
  (* handle *)
  if can (get_pattern (!exn_handles)) tm then let
    (* val _ = print_tm_msg "handle custom pattern\n" tm DEBUG *)
        val (_, EvalM_th) = get_pattern (!exn_handles) tm
    val result = inst_EvalM_handle EvalM_th tm m2deep
    in check_inv "handle custom pattern" tm result end
  (* return *)
  else if can (match_term return_pat) tm then let
    (* val _ = print_tm_msg "return\n" tm DEBUG *)
    val th = hol2deep (rand tm)
    val result = MATCH_MP (ISPEC_EvalM_MONAD EvalM_return) th
    in check_inv "return" tm result end
  (* bind *)
  else if can (match_term bind_pat) tm then let
    (* val _ = print_tm_msg "monad_bind\n" tm DEBUG *)
    val x1 = tm |> rator |> rand
    val (v,x2) = tm |> rand |> dest_abs
    val th1 = m2deep x1
    val th2 = m2deep x2
    val th2 = inst_EvalM_env v th2
    val result = inst_EvalM_bind th1 th2
  in check_inv "bind" tm result end else
  (* otherwise *)
  if can (match_term otherwise_pat) tm then let
    (* val _ = print_tm_msg "otherwise\n" tm DEBUG *)
    val result = inst_EvalM_otherwise tm m2deep
    in check_inv "otherwise" tm result end else
  (* abs *)
  if is_abs tm then let
    (* val _ = print_tm_msg "abs\n" tm DEBUG *)
    val (v,x) = dest_abs tm
    val thx = m2deep x
    val result = apply_EvalM_Fun v thx false
    in check_inv "abs" tm result end else
  (* let expressions *)
  if can dest_let tm andalso is_abs (fst (dest_let tm)) then let
    (* val _ = print_tm_msg "let expressions\n" tm DEBUG *)
    val (x,y) = dest_let tm
    val (v,x) = dest_abs x
    val th1 = hol2deep y
    val th2 = m2deep x
    val th2 = inst_EvalM_env v th2
    val th2 = th2 |> GEN v_var
    val z = th1 |> concl |> rand |> rand
    val th2 = INST [v|->z] th2
    val result = MATCH_MP (ISPEC_EvalM EvalM_Let) (CONJ th1 th2)
    in check_inv "let" tm result end else
  (* data-type pattern-matching *)
  ( (* print_tm_msg "data-type pattern-matching\n" tm; DEBUG *) inst_case_thm tm m2deep) handle HOL_ERR _ =>
  (* previously translated term for dynamic store initialisation *)
  if can lookup_dynamic_v_thm tm then let
    (* val _ = print_tm_msg "previously translated - dynamic\n" tm DEBUG *)
      val th = lookup_dynamic_v_thm tm |> abbrev_nsLookup_code
      val result = m2deep_previously_translated th tm
    in check_inv "lookup_dynamic_v_thm" tm result end else
  (* previously translated term *)
  if can lookup_v_thm tm then let
    (* val _ = print_tm_msg "previously translated\n" tm DEBUG *)
      val th = lookup_v_thm tm
      val result = m2deep_previously_translated th tm
    in check_inv "lookup_v_thm" tm result end else
  (* if statements *)
  if can (match_term if_statement_pat) tm then let
    (* val _ = print_tm_msg "if\n" tm DEBUG *)
    val (t,x1,x2) = dest_cond tm
    val th0 = hol2deep t
    val th1 = m2deep x1
    val th2 = m2deep x2
    val th = MATCH_MP (ISPEC_EvalM EvalM_If) (LIST_CONJ [D th0, D th1, D th2])
    val result = UNDISCH th
    in check_inv "if" tm result end else
  (* access functions *)
  if can (first (fn (pat,_) => can (match_term pat) tm)) (!access_patterns) then let
      (* val _ = print_tm_msg "access function\n" tm DEBUG *)
      val (pat,spec) = (first (fn (pat,_) => can (match_term pat) tm)) (!access_patterns)
      (* Substitute the parameters, and link the parameters to their expressions *)
      val (tms, _) = match_term pat tm (* the type subst shouldn't be used *)
      val pat = Term.subst tms pat
      val th = Thm.INST tms spec

      fun retrieve_params_exps_pair asm =
	if can (match_term Eval_pat2) asm then let
	    val param = rand asm |> rand
	    val exp = rator asm |> rand
	in (param, exp) end else failwith ""

      val params_exps_pairs = mapfilter retrieve_params_exps_pair (hyp th)
      val params_exps_map = List.foldr (fn ((x, y), d) => Redblackmap.insert (d, x, y))
				       (Redblackmap.mkDict Term.compare) params_exps_pairs

      (* Translate the parameters *)
      val args = strip_comb pat |> snd
      val args_evals = List.map hol2deep args

      (* Substitute the translated expressions of the parameters *)
      val eval_concls = List.map concl args_evals
      fun subst_expr (eval_th, th) = let
	  val (param, trans_param) = retrieve_params_exps_pair eval_th
	  val expr_var = Redblackmap.find (params_exps_map, param)
      in Thm.INST [expr_var |-> trans_param] th end handle NotFound => th
      val th = List.foldr subst_expr th eval_concls

      (* Remove the Eval assumptions *)
      val result = List.foldl (fn (eval_th, th) => MP (DISCH (concl eval_th) th) eval_th)
			      th args_evals
  in check_inv "access ref/array" tm result end else
  (* recursive pattern *)
  if can match_rec_pattern tm then let
    (* val _ = print_tm_msg "recursive pattern\n" tm DEBUG *)
    val (lhs,fname,pre_var) = match_rec_pattern tm
    val (pre_var, pre_var_args) = strip_comb pre_var
    val pre_var = mk_var(dest_var pre_var |> fst,
		mk_type("fun", [!refs_type,dest_var pre_var |> snd]))
    val state_var = mk_var("st", !refs_type)
    val state_eq_var = genvar(!refs_type)
    val pre_var = list_mk_comb (pre_var, state_eq_var::pre_var_args)
    fun dest_args tm = rand tm :: dest_args (rator tm) handle HOL_ERR _ => []
    val xs = dest_args tm
    val f = repeat rator lhs
    val str = stringLib.fromMLstring fname
    fun mk_fix tm = let
      val inv_type = type_of tm
      val inv = smart_get_type_inv inv_type
      val eq = ISPECL [inv, tm] Eq_def |> concl |> dest_eq |> fst
    in mk_PURE eq end
    fun mk_fix_st tm = let
      val inv_type = type_of tm
      val inv = smart_get_type_inv inv_type
      val eq = ISPECL [inv, tm] Eq_def |> concl |> dest_eq |> fst
      val pure = mk_PURE eq
      val eq_st = ISPECL [pure, state_eq_var] EqSt_def
			 |> concl |> dest_eq |> fst
    in eq_st end
    fun mk_m_arrow x y = my_list_mk_comb(ArrowM_const, [!H,x,y])
    fun mk_inv [] res = res
      | mk_inv (x::xs) res = mk_inv xs (mk_m_arrow (mk_fix x) res)
    val res = mk_m_arrow (mk_fix_st (hd xs)) (get_m_type_inv (type_of tm))
    val inv = mk_inv (tl xs) res
    val ss = fst (match_term lhs tm)
    val tys = match_type (type_of f) (type_of inv |> dest_type |> snd |> List.hd)
    val f = Term.inst tys f

    val pre = subst ss pre_var
    val h = ISPECL_TM [pre,str,inv,f,!H] PreImp_EvalM_abs |> ASSUME
            |> RW [PreImp_def] |> UNDISCH |> SPEC state_eq_var
    val h = INST [state_eq_var |-> state_var] h
    val ys = List.map (fn tm => MATCH_MP (ISPEC_EvalM Eval_IMP_PURE)
                             (MATCH_MP Eval_Eq (var_hol2deep tm))) xs
    fun apply_arrow h [] = h
      | apply_arrow h (x::xs) = let
	  val th = apply_arrow h xs
      in MATCH_MP (MATCH_MP EvalM_ArrowM th) x
      handle HOL_ERR _ => MATCH_MP (MATCH_MP EvalM_ArrowM_EqSt th) x end
    val result = apply_arrow h ys
    in check_inv "rec_pattern" tm result end else
  (* PMATCH *)
  if is_pmatch tm then let
    (* val _ = print_tm_msg "PMATCH\n" tm DEBUG *)
    val original_tm = tm
    val lemma = pmatch_preprocess_conv tm
    val tm = lemma |> concl |> rand
    val result = pmatch_m2deep tm m2deep
    val result = result |> CONV_RULE (RATOR_CONV (RAND_CONV (RAND_CONV (K (GSYM lemma)))))
    in check_inv "pmatch_m2deep" original_tm result end else
  (* normal function applications *)
  if is_comb tm then let
    (* val _ = print_tm_msg "normal function application\n" tm DEBUG *)
    val result = m2deep_normal_fun_app tm m2deep
    in check_inv "comb" tm result end else
  failwith ("cannot translate: " ^ term_to_string tm);

fun EvalM_P_CONV CONV tm =
  if is_imp tm then (RAND_CONV o RATOR_CONV o RAND_CONV) CONV tm
  else (RATOR_CONV o RAND_CONV) CONV tm;

(* Remove Eq *)
local
    val PURE_ArrowP_Eq_tm = get_term "PURE ArrowP eq";
    fun remove_Eq_aux th = let
	val th = RW [ArrowM_def] th
	val pat = PURE_ArrowP_Eq_tm
	fun dest_EqArrows tm =
	  if can (match_term pat) tm
	  then (rand o rand o rand o rator o rand) tm :: dest_EqArrows ((rand o rand) tm)
	  else []
	val rev_params = th |> concl |> rator |> rand |> rator |> dest_EqArrows |> List.rev
	fun f (v,th) =
	  HO_MATCH_MP EvalM_FUN_FORALL (GEN v th) |> SIMP_RULE std_ss [M_FUN_QUANT_SIMP]
	val th = List.foldr f th rev_params handle HOL_ERR _ => th
	val th = RW [GSYM ArrowM_def] th
    in th end handle HOL_ERR _ => th

    fun remove_EqSt th = let
	val th = UNDISCH_ALL th |> PURE_REWRITE_RULE[ArrowM_def]
	val thc = concl th |> rator |> rand |> rator |> rand
	val st_opt = get_EqSt_var thc
    in case st_opt of
	   SOME st => HO_MATCH_MP EvalM_FUN_FORALL (GEN st th)
				  |> SIMP_RULE std_ss [M_FUN_QUANT_SIMP]
				  |> PURE_REWRITE_RULE[GSYM ArrowM_def]
	 | NONE => th |> PURE_REWRITE_RULE[GSYM ArrowM_def]
    end handle HOL_ERR _ => th
in
    val remove_Eq = remove_Eq_aux o remove_EqSt
end

val Eq_pat = ``Eq a x``
val EqSt_pat = ``EqSt a x``
fun remove_Eq_from_v_thm th = let
  fun try_each f [] th = th
    | try_each f (x::xs) th = try_each f xs (f x th handle HOL_ERR _ => th)
  fun foo v th = let
    val th = th |> GEN v
                |> HO_MATCH_MP FUN_FORALL_INTRO
                |> SIMP_RULE std_ss [FUN_QUANT_SIMP]
		|> PURE_REWRITE_RULE[ArrowM_def]
		|> SIMP_RULE std_ss [M_FUN_QUANT_SIMP]
		|> PURE_REWRITE_RULE[GSYM ArrowM_def]
  in th end

  (* Remove EqSt *)
  val pat = EqSt_pat
  val tms = find_terms (can (match_term pat)) (concl th)
  val vs = tms |> List.map rand
  val th = try_each foo vs th (* should be at most one element in vs *)

  (* Remove Eq *)
  val pat = Eq_pat
  val tms = find_terms (can (match_term pat)) (concl th)
  val vs = tms |> List.map rand
  in try_each foo vs th end

val EVAL_T_F = LIST_CONJ [EVAL ``ml_translator$CONTAINER ml_translator$TRUE``,
			  EVAL ``ml_translator$CONTAINER ml_translator$FALSE``];

fun get_manip_functions_defs () = let
    val defs_list = List.foldl (fn ((x, y), l) => x::y::l) [] (!exn_functions_defs)
    val defs_list = List.foldl (fn ((x, y), l) => x::y::l) defs_list (!refs_functions_defs)
    val defs_list = List.foldl (fn ((x1, x2, x3, x4, x5, x6), l) => x1::x2::x3::x4::x5::x6::l)
			       defs_list (!arrays_functions_defs)
in defs_list end

(* *)
fun extract_precondition_non_rec th pre_var =
  if not (is_imp (concl th)) then (th,NONE) else let
    val rw_thms = case (!store_pinv_def) of SOME th => th::(get_manip_functions_defs ())
						| NONE => (get_manip_functions_defs ())
    val rw_thms = FALSE_def::TRUE_def::rw_thms
    val c = (REWRITE_CONV [CONTAINER_def, PRECONDITION_def] THENC
             ONCE_REWRITE_CONV [GSYM PRECONDITION_def] THENC
             SIMP_CONV (srw_ss()) rw_thms)
    val c = (RATOR_CONV o RAND_CONV) c
    val th = CONV_RULE c th
    val rhs = th |> concl |> dest_imp |> fst |> rand
    in if rhs = T then
      (UNDISCH_ALL (SIMP_RULE std_ss [EVAL (``ml_translator$PRECONDITION T``)] th),NONE)
    else let
    val def_tm = mk_eq(pre_var,rhs)
    val pre_def = quietDefine [ANTIQUOTE def_tm]
    val c = REWR_CONV (GSYM pre_def)
    val c = (RATOR_CONV o RAND_CONV o RAND_CONV) c
    val th = CONV_RULE c th |> UNDISCH_ALL
    val pre_def = clean_precondition pre_def
  in (th,SOME pre_def) end end
(* *)

val PreImp_PRECONDITION_T_SIMP = Q.prove(
 `PreImp T a /\ PRECONDITION T <=> a`,
 fs[PreImp_def, PRECONDITION_def]);

fun extract_precondition_rec thms = let
(* val (fname,ml_fname,def,th) = List.hd thms *)
  fun rephrase_pre (fname,ml_fname,def,th) = let
    val (lhs,_) = dest_eq (concl def)
    val pre_var = get_monad_pre_var th lhs fname
    val th = SIMP_RULE bool_ss [CONTAINER_NOT_ZERO] th
    val th = ex_rename_bound_vars_rule th
    val th = CONV_RULE ((RATOR_CONV o RAND_CONV)
               (REWRITE_CONV [GSYM AND_IMP_INTRO])) th
    val tm = concl th |> dest_imp |> fst
    val rw0 = ASSUME (ml_translatorLib.get_term "remove lookup_cons")
    val tm0 = QCONV (REWRITE_CONV [rw0]) tm |> concl |> rand
    val rw1 = ASSUME (ml_translatorLib.get_term "precond = T")
    val tm1 = QCONV (REWRITE_CONV [rw1]) tm0 |> concl |> rand
    val pat = EvalM_def |> SPEC_ALL |> concl |> dest_eq |> fst
    val (tms, tys) = match_term (rand pat) (!H)
    val pat = Term.inst tys pat |> Term.subst tms
    val rw2 = ASSUME (list_mk_forall(free_vars pat,pat))
    val tm2 = QCONV (REWRITE_CONV [rw0,rw2,PreImp_def]) tm |> concl |> rand
  in (fname,ml_fname,def,th,pre_var,tm1,tm2,rw2) end
  val thms = List.map rephrase_pre thms
(*
val (fname,ml_fname,def,th,pre_var,tm1,tm2,rw2) = hd thms
*)
  (* check whether the precondition is T *)
  fun get_subst (fname,ml_fname,def,th,pre_var,tm1,tm2,rw2) = let
    val pre_v = repeat rator pre_var
    val true_pre = list_mk_abs ((dest_args pre_var), T)
    in pre_v |-> true_pre end
  val ss = List.map get_subst thms
  val rw_thms = case (!store_pinv_def) of SOME th => th::(get_manip_functions_defs ())
					| NONE => (get_manip_functions_defs ())
  fun is_true_pre (fname,ml_fname,def,th,pre_var,tm1,tm2,rw2) =
    ((tm2 |> subst ss
          |> QCONV (REWRITE_CONV ([rw2,PreImp_def,PRECONDITION_def,CONTAINER_def]@rw_thms))
          |> concl |> rand) = T)
  val no_pre = (not o (List.exists (fn x => not x))) (List.map is_true_pre thms)

  (* if no pre then remove pre_var from thms *)
  in if no_pre then let
    fun remove_pre_var (fname,ml_fname,def,th,pre_var,tm1,tm2,rw2) = let
      val th5 = INST ss th
                |> SIMP_RULE bool_ss [PRECONDITION_EQ_CONTAINER]
                |> PURE_REWRITE_RULE [PreImp_def,PRECONDITION_def]
                |> CONV_RULE (DEPTH_CONV BETA_CONV THENC
                                (RATOR_CONV o RAND_CONV) (REWRITE_CONV []))
      in (fname,ml_fname,def,th5,(NONE:thm option)) end
    in List.map remove_pre_var thms end else let
(*
  val (fname,ml_fname,def,th,pre_var,tm1,tm2,rw2) = hd thms
*)
  (* Link the EvalM predicates to their "equivalent" pre vars *)
    fun get_pre_var_EvalM_pair (fname,ml_fname,def,th,pre_var,tm1,tm2,rw2) = let
	val EvalM_tm = UNDISCH_ALL th |> concl
	val pre_var = get_monad_pre_var th (concl def |> dest_eq |> fst) ml_fname
    in (pre_var, EvalM_tm) end
    val pre_var_EvalM_pairs = List.map get_pre_var_EvalM_pair thms
    (* Those rewrites won't be used for any proof: only to generate appropriate terms to define the precondition *)
    val pre_var_EvalM_rws = List.map (fn (x, y) => mk_thm([],
        mk_eq(mk_forall(get_EvalM_state y,y), x))) pre_var_EvalM_pairs

  (* Remove the occurences of PreImp and PreCond *)
  fun replace_EvalM (fname,ml_fname,def,th,pre_var,tm1,tm2,rw2) = let
    val rw1 = mk_thm([], ``(PreImp a b /\ PRECONDITION a) <=> b``)
    val rws = rw1::pre_var_EvalM_rws
    val assum = concl th |> dest_imp |> fst
    val st = concl th |> dest_imp |> snd |> get_EvalM_state
    val tm = UNDISCH th |> GEN st |> DISCH assum
		     |> PURE_REWRITE_RULE rws |> concl
  in tm end
  val no_quant_pres = List.map replace_EvalM thms
  (* Define the pre conds *)
  val all_pre_vars = List.map ((repeat rator) o fst) pre_var_EvalM_pairs
  val (all_pres_list, vsl) = List.map (fn tm => let
      val vs = op_set_diff aconv (free_vars tm) all_pre_vars
      val def_tm = list_mk_forall(vs, tm)
    in (def_tm, vs) end) no_quant_pres |> unzip
  val all_pres = list_mk_conj all_pres_list
  val (_,pre_ind,pre_def) = Hol_reln [ANTIQUOTE all_pres]
  (* Clean the pre_cond def *)
  val clean_pre_def = pre_def |> PURE_REWRITE_RULE [CONTAINER_def,PRECONDITION_def]
  val name = clean_pre_def |> SPEC_ALL |> CONJUNCTS |> hd |> SPEC_ALL
               |> concl |> dest_eq |> fst |> repeat rator |> dest_const |> fst
  val _ = delete_binding (name ^ "_rules") handle NotFound => ()
  val _ = delete_binding (name ^ "_ind") handle NotFound => ()
  val _ = delete_binding (name ^ "_strongind") handle NotFound => ()
  val _ = delete_binding (name ^ "_cases") handle NotFound => ()
  val _ = save_thm(name ^ "_def", clean_pre_def)
(* For every pre_cond, prove that: pre_cond ==> EvalM ... *)
(*
      val (pre_var_tm, EvalM_tm) = hd pre_var_EvalM_pairs
*)
  fun create_pre_var_EvalM_subst (pre_var_tm, EvalM_tm) = let
    val (pre_var, args) = strip_comb pre_var_tm
    val (pre_var_name, pre_var_type) = dest_var pre_var
    val pre_var = mk_var(pre_var_name ^"'", pre_var_type)
    val st = get_EvalM_state EvalM_tm
    val EvalM_abs = list_mk_abs(args, mk_forall(st,EvalM_tm))
  in (pre_var |-> EvalM_abs) end
  val pre_var_EvalM_subst = List.map create_pre_var_EvalM_subst pre_var_EvalM_pairs
  val inst_pre_ind = Thm.INST pre_var_EvalM_subst (SPEC_ALL pre_ind)
			    |> CONV_RULE (DEPTH_CONV BETA_CONV)
  fun create_pre_var_T_subst (pre_var_tm, _) = let
    val (pre_var, args) = strip_comb pre_var_tm
    val TRUE = concl TRUE_def |> rand
    val t_abs = list_mk_abs(args, TRUE)
  in (pre_var |-> t_abs) end
  val pre_var_T_subst = List.map create_pre_var_T_subst pre_var_EvalM_pairs
(*
  val (fname,ml_fname,def,th,pre_var,tm1,tm2,rw2) = hd thms
*)
  fun inst_EvalM_thm (vs, (fname,ml_fname,def,th,pre_var,tm1,tm2,rw2)) = let
    val th1 = Thm.INST pre_var_T_subst th
		       |> CONV_RULE (DEPTH_CONV BETA_CONV)
		       |> PURE_REWRITE_RULE[PreImp_PRECONDITION_T_SIMP]
    val assum = concl th1 |> dest_imp |> fst
    val st = concl th1 |> dest_imp |> snd |> get_EvalM_state
    val th2 = UNDISCH th1 |> GEN st |> DISCH assum
    val th3 = GENL vs th2
  in th3 end
  val EvalM_thms = List.map inst_EvalM_thm (zip vsl thms) |> LIST_CONJ
  val thms2 = MATCH_MP inst_pre_ind EvalM_thms |> CONJUNCTS
  val pre_defs = clean_pre_def |> CONJUNCTS |> List.map SPEC_ALL
  (* clean up *)
  fun clean ((pre,lemma), (fname,ml_fname,def,th,pre_var,tm1,tm2,rw2)) = let
      val th1 = SPEC_ALL lemma
      val assum = concl th1 |> dest_imp |> fst
      val th2 = UNDISCH th1 |> SPEC_ALL |> DISCH assum
      val precond_eq = ISPEC assum PRECONDITION_def
      val th3 = PURE_ONCE_REWRITE_RULE[GSYM precond_eq] th2
  in (fname,ml_fname,def,th3,SOME pre) end
  val thms3 = List.map clean (zip (zip pre_defs thms2) thms)
in thms3 end end
handle HOL_ERR _ => failwith "extract_precondition_rec failed";

(* Adapted from translatorLib *)
(* val (fname,ml_fname,def,th,v) = List.hd thms *)
fun abbrev_code (fname,ml_fname,def,th,v) = let
  val th = th |> UNDISCH_ALL
  val exp = th |> concl |> rator |> rator |> rand
  val n = Theory.temp_binding ("[[ " ^ fname ^ "_code ]]")
  val code_def = new_definition(n,mk_eq(mk_var(n,type_of exp),exp))
  val th = CONV_RULE ((RATOR_CONV o RATOR_CONV o RAND_CONV) (K (GSYM code_def))) th
  in (code_def,(fname,ml_fname,def,th,v)) end
(* End of adaptation from translatorLib *)

(* Some definitions might have polymorphic state and exceptions:
   those types need to be instantiated before translation *)
fun instantiate_monadic_types def = let
    val original_def = def
    (* Retrieve the state and exceptions types *)
    val def = List.hd (CONJUNCTS def)
    val ty = concl def |> strip_forall |> snd |> rhs |> type_of
    val state_ty = dest_type ty |> snd |> List.hd
    val exn_ty = dest_type ty |> snd |> List.last |> dest_type |> snd |> List.hd
			     |> dest_type |> snd |> List.last
    (* Instantiate them to the proper types *)
    val def = if is_vartype state_ty then let
		  val def = Thm.INST_TYPE[state_ty |-> !refs_type] original_def
		  val _ = print "Instantiated polymorphic monadic state\n"
	      in def end
	      else original_def
    val def = if is_vartype exn_ty then let
		  val def = Thm.INST_TYPE[exn_ty |-> !exn_type] def
		  val _ = print "Instantiated polymorphic monadic exceptions\n"
	      in def end
		  else def
in def end;

fun get_monadic_types_inst tm = let
    (* Retrieve the state and exceptions types *)
    val ty = type_of tm
    val state_ty = dest_type ty |> snd |> List.hd
    val exn_ty = dest_type ty |> snd |> List.last |> dest_type |> snd |> List.hd
			     |> dest_type |> snd |> List.last
    (* Instantiate them to the proper types *)
    val tys = if is_vartype state_ty then [state_ty |-> !refs_type] else []
    val tys = if is_vartype exn_ty then (exn_ty |-> !exn_type)::tys else tys
in tys end;

(* Register a type which is neither the monadic state type nor the exc type *)
fun register_pure_type ty =
    if (!refs_type) = ty orelse can (match_type ``:('a, 'b) ml_monadBase$exc``) ty then ()
    else register_type ty;

(* Preprocess the monadic defs *)
fun preprocess_monadic_def def = let
    val (is_rec,defs,ind) = preprocess_def def
in (is_rec,defs,ind) end

(* Apply the induction in the case of a recursive function without preconditions *)
fun apply_ind thms ind = let
    fun the (SOME x) = x | the _ = failwith("the of NONE")
    (* val (fname,ml_fname,def,th,pre) = hd thms *)
    fun get_goal (fname,ml_fname,def,th,pre) = let
	val th = REWRITE_RULE [CONTAINER_def] th
	val hs = hyp th
	val rev_params = def |> concl |> dest_eq |> fst |> rev_param_list
	val state_var = th |> UNDISCH_ALL |> concl |> rator
			   |> rator |> rator |> rand
	val forall_st_tm = mk_forall(state_var, th |> UNDISCH_ALL |> concl)
	(* *)
	val st_eq_tm = REWRITE_RULE[ArrowM_def ]th |> UNDISCH_ALL |> concl |> rator |> rand |> rator |> rand |> get_EqSt_var |> the
	val forall_st_tm = mk_forall(st_eq_tm, forall_st_tm)
        (* *)
	val hyp_tm = list_mk_abs(rev rev_params, forall_st_tm)
	val goal = list_mk_forall(rev rev_params, forall_st_tm)
    in (hyp_tm,(th,(hs,goal))) end
    val goals = List.map get_goal thms
    val gs = goals |> List.map (snd o snd o snd) |> list_mk_conj
    val hs = goals |> List.map (fst o snd o snd) |> flatten
		   |> all_distinct |> list_mk_conj
    val goal = mk_imp(hs,gs)
    val ind_thm = (the ind)
		      |> rename_bound_vars_rule "i" |> SIMP_RULE std_ss []
		      |> ISPECL (goals |> List.map fst)
		      |> CONV_RULE (DEPTH_CONV BETA_CONV)
    fun POP_MP_TACs ([],gg) = ALL_TAC ([],gg)
      | POP_MP_TACs (ws,gg) =
        POP_ASSUM (fn th => (POP_MP_TACs THEN MP_TAC th)) (ws,gg)
    val pres = List.map (fn (_,_,_,_,pre) => case pre of SOME x => x | _ => TRUTH) thms

      (*  val lhs = fst o dest_eq;  val rhs = snd o dest_eq; *)
    fun split_ineq_orelse_tac tac (asms,concl) = (asms,concl) |>
    let
        val (asms',concl) = strip_imp concl
        val asms = asms'@asms
        fun is_ineq t = is_neg t andalso is_eq(rand t)
        fun is_disj_of_ineq t = all is_ineq (strip_disj t)
        fun is_all_disj_of_ineq t = is_disj_of_ineq(snd(strip_forall t))
        val var_equalities =
            List.map strip_conj asms
            |> List.concat
            |> List.filter is_eq
            |> List.filter (is_var o lhs)
            |> List.filter (is_var o rhs)
        fun eq_closure l [] = l
          | eq_closure l (f::r) =
            let val (lhs,rhs) = (lhs f, rhs f) in
              if List.exists (fn x => term_eq lhs x) l then
                eq_closure (rhs::l) r
              else if List.exists (fn x => term_eq rhs x) l then
                eq_closure (lhs::l) r
              else
                eq_closure l r
            end
        fun case_split_vars (l,r) =
          if can (match_term r) l then
            match_term r l
            |> fst
            |> List.filter (fn {residue,...} => not(is_var residue))
            |> List.map (fn {redex,...} => redex)
          else if is_comb r andalso
                  not(TypeBase.is_constructor(fst(strip_comb r))) then
            [r]
          else
            []
      in
        case List.find is_all_disj_of_ineq asms of
            NONE => tac
          | SOME asm =>
            let val asm' = snd(strip_forall asm)
                val disjuncts = strip_disj asm'
                val lsrs = List.map (dest_eq o rand) disjuncts
                val vars =
                    List.map case_split_vars lsrs
                    |> List.filter (not o null)
                    |> List.map hd
                    |> mlibUseful.setify
            in
              case vars of
                  [] => tac
                | l => List.foldr (fn (x,t) => primCases_on x \\ t) ALL_TAC l
            end
      end
(*
      set_goal([],goal)
*)
    val lemma =
      auto_prove "ind" (goal,
        STRIP_TAC
        \\ MATCH_MP_TAC ind_thm
        \\ REPEAT STRIP_TAC
        \\ FIRST (List.map MATCH_MP_TAC (List.map (fst o snd) goals))
        \\ REPEAT STRIP_TAC
        \\ POP_MP_TACs
        \\ SIMP_TAC (srw_ss()) [ADD1,TRUE_def,FALSE_def]
        \\ SIMP_TAC std_ss [UNCURRY_SIMP]
        \\ SIMP_TAC std_ss [GSYM FORALL_PROD]
        \\ METIS_TAC [])
      handle HOL_ERR _ =>
      auto_prove "ind" (goal,
        STRIP_TAC
        \\ MATCH_MP_TAC ind_thm
        \\ REPEAT STRIP_TAC
        \\ FIRST (List.map MATCH_MP_TAC (List.map (fst o snd) goals))
        \\ REPEAT STRIP_TAC
        \\ fs[NOT_NIL_EQ_LENGTH_NOT_0] (*For arithmetic-based goals*)
        \\ METIS_TAC[])
      handle HOL_ERR _ =>
      auto_prove "ind" (goal,
        STRIP_TAC
        \\ SIMP_TAC std_ss [FORALL_PROD]
        \\ (MATCH_MP_TAC ind_thm ORELSE
            MATCH_MP_TAC (SIMP_RULE bool_ss [FORALL_PROD] ind_thm))
        \\ REPEAT STRIP_TAC
        \\ FIRST (List.map MATCH_MP_TAC (List.map (fst o snd) goals))
        \\ FULL_SIMP_TAC (srw_ss()) [ADD1]
        \\ REPEAT STRIP_TAC
        \\ FULL_SIMP_TAC (srw_ss()) [ADD1]
        \\ FULL_SIMP_TAC std_ss [UNCURRY_SIMP]
        \\ METIS_TAC [])
      handle HOL_ERR _ =>
      auto_prove "ind" (goal,
        STRIP_TAC
        \\ SIMP_TAC std_ss [FORALL_PROD]
        \\ (MATCH_MP_TAC ind_thm ORELSE
            MATCH_MP_TAC (SIMP_RULE bool_ss [FORALL_PROD] ind_thm))
        \\ REPEAT STRIP_TAC
        \\ MATCH_MP_TAC PreImp_IMP
        \\ CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV pres))
        \\ (STRIP_TAC THENL (List.map MATCH_MP_TAC (List.map (fst o snd) goals)))
        \\ FULL_SIMP_TAC (srw_ss()) [ADD1]
        \\ REPEAT STRIP_TAC
        \\ FULL_SIMP_TAC (srw_ss()) [ADD1]
        \\ FULL_SIMP_TAC std_ss [UNCURRY_SIMP,PRECONDITION_def]
        \\ METIS_TAC [])
      handle HOL_ERR _ =>
      auto_prove "ind" (mk_imp(hs,ind_thm |> concl |> rand),
        STRIP_TAC
        \\ MATCH_MP_TAC ind_thm
        \\ REPEAT STRIP_TAC
        \\ FIRST (List.map MATCH_MP_TAC (List.map (fst o snd) goals))
        \\ REPEAT STRIP_TAC
        \\ FULL_SIMP_TAC (srw_ss()) [ADD1]
        \\ METIS_TAC [])
      handle HOL_ERR e =>
        auto_prove "ind" (goal,
        STRIP_TAC
        \\ MATCH_MP_TAC ind_thm
        \\ REPEAT STRIP_TAC
        \\ FIRST (List.map MATCH_MP_TAC (List.map (fst o snd) goals))
        \\ REPEAT STRIP_TAC
        \\ POP_MP_TACs
        \\ SIMP_TAC (srw_ss()) [ADD1,TRUE_def,FALSE_def]
        \\ SIMP_TAC std_ss [UNCURRY_SIMP]
        \\ SIMP_TAC std_ss [GSYM FORALL_PROD]
        \\ rpt(split_ineq_orelse_tac(metis_tac [])))
    val results = UNDISCH lemma |> CONJUNCTS |> List.map SPEC_ALL
    val thms = List.map (fn (th, (fname,ml_fname,def,_,pre)) => (fname,ml_fname,def,th,pre)) (zip results thms)
in thms end;

(*
 * m_find_untranslated
 * A function which attempts to find constants which can't be translated.
 * For debugging purposes only.
 *)

val knwn_consts = [
 ``st_ex_bind``,``st_ex_return``,``$otherwise``,``COND``,``LET``,
 ``PMATCH``,``PMATCH_ROW``,``BIT1``,``BIT2``,``NUMERAL``,``ZERO``,``CONS``,
 ``[]``,``()``,``UNCURRY``,``CHR``,``integer$int_of_num``,``$/\``,``$=``
 ]
fun m_find_untranslated def = let
    val fconsts = SPEC_ALL def |> CONJUNCTS
	|> List.map (fst o strip_comb o fst o dest_eq o concl o SPEC_ALL)
    val user_consts = List.map (fst o strip_comb o fst)
	   ((!access_patterns)@(!exn_raises)@(!exn_handles))
    val all_knwn_consts = List.foldl (fn (x,s) => HOLset.add(s,x)) empty_tmset (fconsts@user_consts@knwn_consts) |> HOLset.listItems
    val defs = SPEC_ALL def |> CONJUNCTS
			|> List.map (snd o dest_eq o concl o SPEC_ALL)
    fun find_consts a (d::defs) = let
	val atoms = all_atoms d |> HOLset.filter is_const
	val atoms = HOLset.union(atoms,a)
    in find_consts atoms defs end
      | find_consts a [] = a
    val consts = find_consts empty_tmset defs
    fun insert (x,m) = let
	val info = dest_thy_const x
	val str = (#Thy info) ^"$" ^(#Name info)
    in Redblackmap.insert(m,str,x) end
    val consts_map = HOLset.foldl insert
				 (Redblackmap.mkDict String.compare)
				 consts
    val consts = Redblackmap.listItems consts_map |> List.map snd
    fun is_unknwn x = not(List.exists (same_const x) all_knwn_consts)
    val consts = List.filter is_unknwn consts

    (* Test whether the constants can be translated or not *)
    fun translatable x = (can lookup_v_thm x) orelse
			 (can lookup_dynamic_v_thm x) orelse
			 (can hol2deep x)
    val untrans_consts = List.filter (not o translatable) consts
in untrans_consts end

(* Update precondition *)
val PRECONDITION_pat = ``ml_translator$PRECONDITION x``
val is_PRECONDITION = can (match_term PRECONDITION_pat)
fun update_precondition new_pre = let
  val v_thms = get_v_thms_ref()
  
  fun update_aux (name,ml_name,tm,th,pre,module)= let
    val th1 = D th
    val th2 = PURE_REWRITE_RULE [new_pre,PRECONDITION_T] th1
  in if aconv (concl th1) (concl th2)
    then (name,ml_name,tm,th,pre,module) else let
      val th2 = REWRITE_RULE [] th2 |> UNDISCH_ALL
      val th = remove_Eq_from_v_thm th2
      val thm_name = name ^ "_v_thm"
      val _ = print ("Updating " ^ thm_name ^ "\n")
      val _ = save_thm(thm_name,th)
      val new_pre = if can (find_term is_PRECONDITION) (concl (SPEC_ALL (DISCH_ALL th)))
                    then new_pre else TRUTH
     in (name,ml_name,tm,th,new_pre,module) end end
  val _ = (v_thms := map update_aux (!v_thms))
  val _ = (dynamic_v_thms := Net.map update_aux (!dynamic_v_thms))
in new_pre end

(*
 * m_translate_main
 *)
fun m_translate_main (* m_translate *) def = (let
    val original_def = def
    (* Instantiate the monadic type if necessary - the state and the exceptions can't be polymorphic *)
    val def = instantiate_monadic_types def

    (* Start the translation *)
    val _ = H := (!default_H)
    val _ = pmatch_index := 1
    val _ = undef_local_code_abbrevs ()
    fun the (SOME x) = x | the _ = failwith("the of NONE")
    (* perform preprocessing -- reformulate def, register types *)
    val _ = register_term_types register_pure_type (concl def)
    val (is_rec,defs,ind) = preprocess_def def
    val info = List.map get_info defs
    val msg = comma (List.map (fn (fname,_,_,_,_) => fname) info)
    (* val (fname,ml_fname,lhs,rhs,def) = List.hd info *)
    (* derive deep embedding *)
    fun compute_deep_embedding info = let
	val _ = List.map (fn (fname,ml_fname,lhs,_,_) =>
			     install_rec_pattern lhs fname ml_fname) info
	val thms = List.map (fn (fname,ml_fname,lhs,rhs,def) =>
				(fname,ml_fname,m2deep rhs,def)) info
	val _ = uninstall_rec_patterns ()
    in thms end
(*
val _ = List.map (fn (fname,ml_fname,lhs,_,_) =>
        install_rec_pattern lhs fname ml_fname) info
val (fname,ml_name,lhs,rhs,def) = el 1 info
can (find_term is_arb) (rhs |> rand |> rator)
*)
    val _ = print ("Translating " ^ msg ^ "\n")
    val thms = compute_deep_embedding info
    (* postprocess raw certificates *)
(*
val (fname,ml_fname,th,def) = List.hd thms
*)
    fun optimise_and_abstract (fname,ml_fname,th,def) = let
	val rev_params = def |> concl |> dest_eq |> fst |> rev_param_list
	val no_params = List.length rev_params = 0
	(* replace rhs with lhs *)
	val th = th |> CONV_RULE (EvalM_P_CONV
				      (REWRITE_CONV [CONTAINER_def] THENC
						    ONCE_REWRITE_CONV [GSYM def]))
	(* optimised generated code - do nothing *)
	val th = D th
	(* val th = clean_assumptions (D th) *)
	val (th,v) = if no_params then (th,T) else let 
            val params = (if is_rec then butlast rev_params else rev_params)
	    val (x, xs) = (hd params, tl params)
	    val v = List.last rev_params
	    val th1 = apply_EvalM_Fun x th true
	    val th2 = List.foldl (fn (v,th) => apply_EvalM_Fun v th true
                       |> remove_ArrowM_EqSt) th1 xs
	    in (th2,v) end handle Empty => (th, List.last rev_params)
    in (fname,ml_fname,def,th,v) end
    val thms = List.map optimise_and_abstract thms
    (* final phase: extract precondition, perform induction, store cert *)
    val (is_fun,results) = if not is_rec then let
      (* non-recursive case *)
      val _ = length thms = 1 orelse failwith "multiple non-rec definitions"
      val (code_def,(fname,ml_fname,def,th,v)) = abbrev_code (hd thms)
      val fname = get_unique_name fname
      (* remove parameters *)
      val th = DISCH_ALL th |> PURE_REWRITE_RULE[GSYM AND_IMP_INTRO] |> UNDISCH_ALL
      val th = D (clean_assumptions (D th))
      val th = CONV_RULE (QCONV (DEPTH_CONV ETA_CONV)) th
      val th = CONV_RULE ((RATOR_CONV o RAND_CONV)
			  (SIMP_CONV std_ss [EVAL_T_F])) th
      val th = clean_assumptions (D th)
      val (lhs,rhs) = dest_eq (concl def)

      (* Precondition *)
      val pre_var = get_monad_pre_var th lhs fname
      val rev_params = def |> concl |> dest_eq |> fst |> rev_param_list
      val (th,pre) = extract_precondition_non_rec th pre_var
      (* Remove Eq *)
      val th = remove_Eq th
      (* simpliy EqualityType *)
      val th = SIMP_EqualityType_ASSUMS th
      (* store for later use *)
      val is_fun = code_def |> SPEC_ALL |> concl |> rand |> strip_comb |> fst |> same_const Fun_const
      val th = PURE_REWRITE_RULE[code_def] th
      val th =
	if is_fun then
	  th
	  |> INST [v_env |-> cl_env_tm]
          |> PURE_REWRITE_RULE[ArrowM_def, code_def]
	  |> MATCH_MP EvalM_Fun_Var_intro
          |> PURE_REWRITE_RULE[GSYM ArrowM_def]
	  |> SPEC (stringSyntax.fromMLstring ml_fname)
	  |> UNDISCH
	  |> remove_local_code_abbrevs
	else let val _ = failwith "Monadic translation of constants not supported" in th end
      val _ = undef_local_code_abbrevs ()
      in
	(is_fun,[(fname,ml_fname,def,th,pre)])
      end
    else (* is_rec *) let
      (* introduce Recclosure *)
      val (code_defs,thms) = let val x = List.map abbrev_code thms
                             in unzip x end
      (* introduce Recclosure *)
      fun mk_Recclosure_part (fname,ml_fname,def,th,v) = let
	  val fname = ml_fname |> stringLib.fromMLstring
	  val name = v |> dest_var |> fst |> stringLib.fromMLstring
	  val body = th |> UNDISCH_ALL |> concl |> rator |> rator |> rand
      in pairSyntax.list_mk_pair[fname,name,body] end
      val parts = List.map mk_Recclosure_part thms
      val recc = listSyntax.mk_list(parts,type_of (hd parts))
(*
val (fname,ml_fname,def,th,v) = List.hd thms
*)
      val env2 = mk_var("env2", venvironment)
      val shadow_env = mk_var("shadow_env", venvironment)
      fun apply_recc (fname,ml_fname,def,th,v) = let
	  val th = apply_EvalM_Recclosure recc ml_fname v th
	  val th = clean_assumptions th
	  val th = CONV_RULE (QCONV (DEPTH_CONV ETA_CONV)) th
	  val th = INST [env2|->cl_env_tm,shadow_env|->cl_env_tm] th |> RW []
			|> CONV_RULE ((RATOR_CONV o RAND_CONV) (SIMP_CONV std_ss [EVAL_T_F]))
	  val th = clean_assumptions th |>  move_VALID_REFS_PRED_to_assums
      in (fname,ml_fname,def,th) end
      val thms = List.map apply_recc thms

      (* collect precondition *)
      val thms = extract_precondition_rec thms

      (* Apply the induction if necessary:
         recursive functions with no preconditions *)
      val thms = case #5 (hd thms) of
		     SOME _ => thms 
		   | NONE => apply_ind thms ind
(*
val (fname,ml_fname,def,th,pre) = List.hd thms
*)
      (* clean up *)
      fun fix (fname,ml_fname,def,th,pre) = let
        (* val th = let
          val thi = MATCH_MP IMP_PreImp_THM th
          val thi = CONV_RULE ((RATOR_CONV o RAND_CONV)
                    (ONCE_REWRITE_CONV [force_thm_the pre] THENC
                     SIMP_CONV std_ss [PRECONDITION_def])) thi
          val thi = MP thi TRUTH
        in thi end handle HOL_ERR _ => th *)
        (* val th = RW [PreImp_def, CONTAINER_def] th |> UNDISCH_ALL *)
	val th = remove_Eq th
	val th = SIMP_EqualityType_ASSUMS th
	val th = th |> DISCH_ALL |> REWRITE_RULE ((GSYM AND_IMP_INTRO)::code_defs) |> UNDISCH_ALL |> SPEC_ALL |> UNDISCH_ALL |> remove_local_code_abbrevs
      in (fname,ml_fname,def,th,pre) end
      val results = List.map fix thms
      val _ = List.map (delete_const o fst o dest_const o fst o dest_eq o concl) code_defs
      val _ = undef_local_code_abbrevs ()
  in (true,results) end
  fun check results = let
    val th = LIST_CONJ (List.map #4 results)
    val f = can (find_term (can (match_term (ml_translatorLib.get_term "WF")))) (th |> D |> concl)
    in if f then failwith "WF" else (is_rec,is_fun,results) end
  in check results end handle UnableToTranslate tm => let
    val _ = print "\n\nCannot translate term:  "
    val _ = print_term tm
    val _ = print "\n\nwhich has type:\n\n"
    val _ = print_type (type_of tm)
    val _ = print "\n\n"
    in raise UnableToTranslate tm end)
  handle e => let
   val names =
     def |> SPEC_ALL |> CONJUNCTS
         |> List.map (fst o dest_const o repeat rator o fst o dest_eq o concl o SPEC_ALL)
         |> all_distinct handle HOL_ERR _ => ["<unknown name>"]
   val _ = print ("Failed translation: " ^ comma names ^ "\n")
   in raise e end

(*
 * m_translate
 *)

val LOOKUP_VAR_pat = ``LOOKUP_VAR name env exp``;
fun m_translate def =
  let
      val (is_rec,is_fun,results) = m_translate_main (* m_translate *) def
  in
    if is_rec then
    let
      val recc = results |> List.map (fn (fname,_,def,th,pre) => th) |> hd |> hyp
        |> first (can (match_term LOOKUP_VAR_pat))
        |> rand |> rator |> rand
      val ii = INST [cl_env_tm |-> get_curr_env()]
      val v_names = List.map (fn x => find_const_name (#1 x ^ "_v")) results
      val _ = if not (!dynamic_init_H) then ml_prog_update (add_Dletrec recc v_names) else ()
      val v_defs = List.take(get_curr_v_defs (), length v_names)
      val jj = INST (if !dynamic_init_H  then [] else [v_env |-> get_curr_env()])
      (*
      val (fname,ml_fname,def,th,pre) = hd results
      *)
      fun inst_envs (fname,ml_fname,def,th,pre) = let
	  val lemmas = LOOKUP_VAR_def :: List.map GSYM v_defs
	  val th = th |> ii |> jj
	  val state_var = concl th |> get_EvalM_state
	  val th = GEN state_var th |>
                   (CONV_RULE ((QUANT_CONV o RATOR_CONV o RAND_CONV o
				RATOR_CONV o RATOR_CONV o RAND_CONV)
				   (PURE_REWRITE_CONV [ArrowM_def])))
	  val th = (MATCH_MP EvalM_Var_ArrowP th
		   handle HOL_ERR _ => MATCH_MP EvalM_Var_ArrowP_EqSt th)
		   |> PURE_REWRITE_RULE [GSYM ArrowM_def]
	  val assum = concl th |> dest_imp |> fst
	  val v = th |> hyp |> first (can (match_term assum)) |> rand
	  val th = INST [rand assum |-> v] th |> UNDISCH
	  val th = D th |> REWRITE_RULE lemmas
		     |> SIMP_RULE std_ss [lookup_var_def]
		     |> clean_assumptions |> UNDISCH_ALL
	  val pre_def = (case pre of NONE => TRUTH | SOME pre_def => pre_def)
	  val th =
	      if !dynamic_init_H then let val _ = add_dynamic_v_thms(fname,ml_fname,th,pre_def)
	      in th end
	      else let val _ = add_v_thms (fname,ml_fname,th,pre_def)
	      in save_thm(fname ^ "_v_thm", th) end
      in th end
      val thms = List.map inst_envs results
    in LIST_CONJ thms end
    else (* not is_rec *) let
      val (fname,ml_fname,def,th,pre) = hd results
    in
      if is_fun then let
        val th = th |> INST [cl_env_tm |-> get_curr_env()]
        val n = ml_fname |> stringSyntax.fromMLstring
        val lookup_var_assum = th |> hyp
          |> first (can (match_term(LOOKUP_VAR_def |> SPEC n |> SPEC_ALL |> concl |> lhs)))
	val state_var = concl th |> get_EvalM_state
        val lemma = th |> DISCH lookup_var_assum
                       |> GENL [state_var, v_env]
                       |> MATCH_MP LOOKUP_VAR_EvalM_ArrowM_IMP
                       |> D |> clean_assumptions |> UNDISCH_ALL
	val pre_def = (case pre of NONE => TRUTH | SOME pre_def => pre_def)
	val th =
          if !dynamic_init_H then let
              val th = lemma |> Q.INST [`cl_env`|->`^(get_curr_env())`]
			     |> DISCH_ALL
	      val _ = add_dynamic_v_thms(fname,ml_fname,th,pre_def)
          in th end
          else let
	      val v = lemma |> concl |> rand |> rator |> rand
	      val exp = lemma |> concl |> rand |> rand
	      val v_name = find_const_name (fname ^ "_v")
	      val _ = ml_prog_update (add_Dlet_Fun n v exp v_name)
	      val v_def = hd (get_curr_v_defs ())
	      val v_thm = lemma |> CONV_RULE (RAND_CONV (REWR_CONV (GSYM v_def)))
	      val _ = add_v_thms (fname,ml_fname,v_thm,pre_def)
	  in save_thm(fname ^ "_v_thm",v_thm) end
        in th end
      else let val _ = failwith "Monadic translation of constants not supported" in th end end
  end
  handle UnableToTranslate tm => let
    val _ = print "\n\nml_translate: cannot translate term:  "
    val _ = print_term tm
    val _ = print "\n\nwhich has type:\n\n"
    val _ = print_type (type_of tm)
    val _ = print "\n\n"
  in raise UnableToTranslate tm end
    | HOL_ERR err => let
    val _ = print "\n\nml_translate: unexpected error when translating definition:\n\n"
    val _ = print_thm def
    val _ = print "\n\n"
    in raise (HOL_ERR err) end;

(*
 * m_translate_run
 *)

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

fun compute_env_index env = let
    val env_name = dest_var env |> fst
    val env_index_str = String.extract(env_name, String.size local_environment_var_name, NONE)
    val index = string_to_int env_index_str
in index end;

fun instantiate_local_environment th = let
    (* Instantiate a new environment - we need env to have the proper shape : merge_env ... *)
    val env = concl th |> rator |> rator |> rator |> rator |> rand
    val new_env = get_curr_env()
    val th = Thm.INST [env |-> new_env] th
in th end

fun clean_lookup_assums th = let
    val th = remove_local_code_abbrevs th
    val th = HYP_CONV_RULE (fn x => true) (SIMP_CONV list_ss (build_rec_env_def::lookup_var_write::LOOKUP_ASSUM_SIMP::FOLDR::string_rewrites)) th
    val th = HYP_CONV_RULE (fn x => true) (PURE_REWRITE_CONV (List.map GSYM (!local_code_abbrevs))) th
    val th = MP (DISCH ``T`` th ) TRUTH handle HOL_ERR _ => th
in th end

val nsLookup_pat = ``nsLookup (env : v sem_env).v (Short name) = SOME exp``
fun create_local_fun_defs th = let
    (* Retrieve the lookup assumptions for the functions definitions *)
    val assums =  List.filter (can (match_term nsLookup_pat)) (hyp th)
    fun get_name_expr tm = ((rand o rand o rand o rator)tm,(rand o rand)tm)
    val lookup_info = List.map get_name_expr assums

    (* Remove the variables and the non-monadic functions, retrieve the closure environment *)
    val lookup_info = List.filter(fn (x, y) => not(is_var y)) lookup_info

    fun get_clenv_var expr = let
	val clenv = rator expr |> rator |> rand
	val _ = if is_var clenv andalso type_of clenv = venvironment then ()
		else failwith "get_env_var"
    in clenv end
    fun get_clenv_index_var (name, expr) = let
	val clenv = get_clenv_var expr
	val index = compute_env_index clenv
    in (index, (clenv, name, expr)) end
    val lookup_info = mapfilter get_clenv_index_var lookup_info

    (* Sort the lookup assumptions, eliminate the redundant definitions
       (introduced by the mutually recursive functions *)
    val insert_map = (fn ((i, info),m) => Redblackmap.insert(m, i, info))
    val env_clos_map = Redblackmap.mkDict (Int.compare)
    val env_clos_map = List.foldl insert_map env_clos_map lookup_info
    val defs_info = Redblackmap.listItems env_clos_map
    fun assum_order (i1 : int, _) (i2 : int, _) = i1 > i2
    val defs_info = Lib.sort assum_order defs_info
    val defs_info = List.map #2 defs_info

    (* Create the function definitions (Let expressions) *)
    val current_env = concl th |> rator |> rator |> rator |> rator |> rand
    val all_envs = List.map #1 defs_info
    val last_env = List.last all_envs
    val all_envs = current_env::(List.take(all_envs, List.length all_envs - 1))
    val defs_env_info = zip all_envs defs_info

    (* val (env_var2, (env_var1, name, fexp)) = List.hd defs_env_info *)
    val i = ref (List.length defs_env_info)
    fun print_countdown () = (print ((Int.toString (!i) ^" ")); i := (!i - 1))
    fun create_fun_let ((env_var2, (env_var1, name, fexp)), th) =
        if is_Recclosure fexp then let
	    (* Print countdown *)
	    val _ = print_countdown ()

	    (* Build the new environment *)
            val funs = rator fexp |> rand
	    val exp = concl th |> rator |> rator |> rand
	    val st = get_EvalM_state (concl th)
	    val P = th |> concl |> rator |> rand
	    val lemma = ISPECL [funs,env_var1,exp,st,P,!H] EvalSt_Letrec_Fun

	    (* Prove the assumption *)
	    val assum = concl lemma |> dest_imp |> fst
	    val assum_th = ((PURE_REWRITE_CONV (!local_code_abbrevs)) THENC EVAL) assum |> EQT_ELIM
	    val lemma = MP lemma assum_th

	    (* Subsitute the new environment *)
	    val nenv = concl lemma |> dest_imp |> fst |> rator |> rator
			     |> rator |> rator |> rand
	    val lemma = MP lemma (INST [env_var2 |-> nenv] th)

	    (* Cleanup *)
	    val lemma = clean_lookup_assums lemma
	in lemma end
	else let
	    (* Closure *)

	    (* Print countdown *)
	    val _ = print_countdown ()

	    (* Build the new environment *)
	    val vname = name
	    val xv = rator fexp |> rand
	    val fexp = rand fexp

	    val Closure_exp = list_mk_comb(Closure_const,[env_var1,xv,fexp])
	    val nenv = mk_write vname Closure_exp env_var1

	    (* Replace the environment and create the Let expression *)
	    val th' = Thm.INST [env_var2 |-> nenv] th
	    val th' = MATCH_MP EvalSt_Let_Fun th' |> clean_lookup_assums
	in th' end
    val _ = print "Defining local functions: "
    val th = List.foldl create_fun_let th defs_env_info
    val _ = print "\n"
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
    val state_var = concl th |> rator |> rator |> rator |> rand
    val monad_state_is_var = is_var state_var
    val th = if monad_state_is_var then let
        val H_eq = ALPHA_CONV state_var (concl th |> rand)
	val th = PURE_ONCE_REWRITE_RULE[H_eq] th
    in th end else th

    val P = concl th |> rator |> rand
    val STATE_RI = get_type_inv (type_of state_var)
    
    val loc_info = !dynamic_refs_bindings

    (* val ((loc_name, loc)::loc_info) = loc_info; *)
    fun create_local_refs ((loc_name, loc)::loc_info) th = let
	val exp = concl th |> rator |> rator |> rand
	val originalH = concl th |> rand
	val (state_var,H_part) = dest_abs originalH
	val (H_part1, H_part2) = dest_star H_part
	val H_part2 = mk_abs(state_var, H_part2)

	val state_field = rand H_part1
	val get_ref_fun = mk_abs(state_var, state_field)
	val TYPE = get_type_inv (type_of state_field)
	val Eval_state_field = hol2deep state_field
	val get_ref_exp = concl Eval_state_field |> get_Eval_exp
	val st_name = stringLib.fromMLstring (dest_var state_var |> fst)
	val env = concl th |> rator |> rator |> rator |> rator |> rand
	val STATE_TYPE = get_type_inv (!refs_type)

	val nenv = mk_write loc_name loc env
	val gen_th = INST[env |-> nenv] th |> clean_lookup_assums |> GEN loc
        val is_array = concl th |> rand |> dest_abs |> snd |> dest_star
			     |> fst |> strip_comb |> fst
			     |> same_const RARRAY_REL_const

	val lemma = if is_array then
            ISPECL[exp, get_ref_fun, loc_name, STATE_TYPE,
		   rand TYPE, st_name, env, H_part2, P, state_var]
		  EvalSt_Alloc |> BETA_RULE |> UNDISCH |> UNDISCH
	else MATCH_MP (ISPECL[exp, get_ref_exp, get_ref_fun, loc_name,
		    TYPE, st_name, env, H_part2, P, state_var]
		   EvalSt_Opref |> BETA_RULE) Eval_state_field
	val th = MY_MATCH_MP lemma gen_th
    in create_local_refs loc_info th end
      | create_local_refs [] th = th

    val th = create_local_refs loc_info th

    (* Transform the EvalSt predicate to an Eval predicate *)
    val th = MATCH_MP EvalSt_to_Eval th
in th end

fun create_constant_state th state_var = let
    (* Rewrite the data-type in an appropriate manner *)
    val ty = type_of state_var
    val type_name = dest_type ty |> fst
    val rw_thms = DB.find (type_name ^ "_component_equality")
			  |> List.map (fst o snd)
    val pat = SPEC_ALL (TypeBase.one_one_of ty) |> concl |> dest_eq
		       |> fst |> dest_eq |> fst
    val eqns = mk_eq(pat,state_var) |> SIMP_CONV (srw_ss()) rw_thms
    val ss = concl eqns |> rand |> list_dest dest_conj
                 |> List.map ((fn (x,y) => x |-> y) o dest_eq)
    val rw_state_var = Term.subst ss pat
    val state_var_eq = prove(mk_eq(rw_state_var,state_var),fs rw_thms)

    (* Instantiate the environment *)
    val env = get_Eval_env (concl th)
    val v = genvar v_ty
    val nenv = mk_write (stringLib.fromMLstring "state") v env
    val th1 = INST [env |-> nenv] th
		   |> UNDISCH_ALL |> PURE_REWRITE_RULE [GSYM SafeVar_def]
		   |> DISCH_ALL
		   |> CONV_RULE (SIMP_CONV bool_ss [lookup_cons_write,lookup_var_write,Eval_Var_SIMP])
		   |> CONV_RULE (DEPTH_CONV stringLib.string_EQ_CONV)
		   |> SIMP_RULE bool_ss []
		   |> UNDISCH_ALL
		   |> PURE_REWRITE_RULE [SafeVar_def]

    (* Apply the theorem *)
    val STATE_INV = get_type_inv (type_of state_var)
    val INV_pat = list_mk_comb(STATE_INV, [state_var,v_var])
    val assum = List.hd (List.filter (can (match_term INV_pat)) (hyp th1))
    val th2 = DISCH assum th1 |> GEN v

    val Eval_state = hol2deep rw_state_var
	             |> PURE_REWRITE_RULE [state_var_eq]
    val old_env = concl Eval_state |> get_Eval_env
    val Eval_state = INST [old_env |-> env] Eval_state
    val th3 = CONJ Eval_state th2
    val th4 = MATCH_MP Eval_Let th3
              |> CONV_RULE ((RAND_CONV (PURE_REWRITE_CONV[LET_DEF]))
				THENC (DEPTH_CONV BETA_CONV))
in th4 end

(* val (vname,x) = List.last params_bindings *)
fun apply_Eval_Fun_Eq ((vname,x), th) = let
    val env = get_Eval_env (concl th)
    val v = genvar v_ty
    val tms = FVL [x,v] empty_varset
    val nenv = mk_write vname v env
    val th = INST [env |-> nenv] th |> clean_lookup_assums

    val A = mk_var("A",mk_type("fun",[type_of x,v_bool_ty]))
    val pat = list_mk_comb(A,[x,v_var])
    val assum = List.filter (can (fn y => Term.raw_match [] tms pat y ([], []))) (hyp th) |> hd
    val x = assum |> rator |> rand
    val th = CONV_RULE ((RAND_CONV o RAND_CONV) (UNBETA_CONV x)) th
             |> DISCH assum |> GEN v
    val th = MATCH_MP Eval_Fun_Eq th
in th end
				     
fun m_translate_run_abstract_parameters th def params_evals = let
    val params_bindings = List.map(fn x => (concl x |> rator |> rator |> rand |> rand |> rand, concl x |> rator |> rand |> rand)) params_evals
    val th = PURE_REWRITE_RULE [GSYM def] th
    val th = List.foldr apply_Eval_Fun_Eq th params_bindings

    (* Rewrite the function in the theorem *)
    val f = concl th |> rand |> rand
    val fc = SPEC_ALL def |> concl |> dest_eq |> fst |> strip_comb |> fst
    val f_eq = prove(mk_eq(f,fc), rpt (irule EQ_EXT >> rw[]) >> rw[])
    val th = PURE_REWRITE_RULE [f_eq] th
in th end

fun inst_gen_eq_vars2 st th = let
    (* Instantiate the variables in the occurences of Eq*)
    val pat = Eq_def |> SPEC_ALL |> concl |> dest_eq |> fst
    val xs = find_terms (can (match_term pat)) (concl th) |> List.map rand
    val ss = List.map (fn v => v |-> genvar(type_of v)) xs
    val th = INST ss th
    (* Instantiate the variable in EqSt *)
    val thc = UNDISCH_ALL th |> PURE_REWRITE_RULE[ArrowM_def]
	|> concl |> rator |> rand |> rator |> rand
    val state_var_opt = get_EqSt_var thc
    val th = case state_var_opt of NONE => th 
      | SOME v => INST [v |-> st] th
    (* *)
in th end;

fun m_translate_run def = let
    (* Instantiate the monadic state and exceptions if they are polymorphic *)
    val tys = get_monadic_types_inst (def |> concl |> strip_forall |> snd |> rhs |> rator |> rand)
    val _ = if List.length tys > 0 then print "m_translate_run: instantiated monadic types\n" else ()
    val def = Thm.INST_TYPE tys def
    val _ = undef_local_code_abbrevs ()

    (* preprocessing: register types *)
    val _ = register_term_types register_type (concl def)

    (* Decompose the definition *)
    val (def_lhs, def_rhs) = concl def |> strip_forall |> snd |> dest_eq

    val fname = repeat rator def_lhs |> dest_const |> fst |> get_unique_name
    val _ = print ("Translating monadic run: " ^ fname ^ "\n")
    val fname_str = stringLib.fromMLstring fname

    val Mvar = mk_var("M", poly_M_type)
    val Svar = mk_var("S", a_ty)
    val (tms, tys) = match_term (my_list_mk_comb(run_const,[Mvar,Svar])) def_rhs
    val monad_tm = Term.subst tms (Term.inst tys Mvar)
    val state_var = Term.subst tms (Term.inst tys Svar)
    val (monad_f, monad_params) = strip_comb monad_tm

    (* Construct the Eval predicates for the parameters *)
    fun var_create_Eval tm = let
	val (name,ty) = dest_var tm
	val inv = get_type_inv ty
	val str = stringSyntax.fromMLstring name
	val result = ISPECL_TM [str,mk_comb(inv,tm)] Eval_name_RI_abs |> ASSUME
	val result = MATCH_MP (ISPEC_EvalM Eval_IMP_PURE) result
	val st = concl result |> get_EvalM_state
	val result = INST [st |-> state_var] result
    in check_inv "var" tm result end
    val params_evals = List.map var_create_Eval monad_params

    (* Get the monadic specification *)
    val _ = local_code_abbrevs := []
    val monad_th = lookup_dynamic_v_thm monad_f
    fun inst_state_type th = let
	val ty = concl th |> dest_forall |> fst |> type_of
		       |> dest_type |> snd |> hd
    in INST_TYPE [ty |-> !refs_type] th end
    val monad_th = (MATCH_MP (inst_state_type Eval_IMP_PURE)  monad_th)
                 |> ISPEC (!H)
		 |> PURE_REWRITE_RULE[GSYM ArrowM_def]
		 |> abbrev_nsLookup_code
    val monad_th = INST [concl monad_th |> get_EvalM_state |-> state_var] monad_th

    (* Insert the parameters *)
    val monad_th = inst_gen_eq_vars2 state_var monad_th
		   handle HOL_ERR _ => monad_th
    fun insert_param (x, th) =
      MY_MATCH_MP(MATCH_MP EvalM_ArrowM_EqSt_Eq th) x
      handle HOL_ERR _ => MY_MATCH_MP(MATCH_MP EvalM_ArrowM_Eq th) x
      handle HOL_ERR _ => MY_MATCH_MP(MATCH_MP EvalM_ArrowM th) x
    val monad_th = List.foldl insert_param monad_th params_evals

    (* Add the state parameter Eval assumption *)
    val monad_state_is_var = is_var state_var
    val env = concl monad_th |> get_Eval_env
    val STATE_RI = get_type_inv (type_of state_var)
    val monad_th = if monad_state_is_var then let
	val state_var_name = stringLib.fromMLstring(dest_var state_var |> fst)
	val exp1 = my_list_mk_comb(Short_const,[state_var_name])
	val tys = Type.match_type (type_of exp1)
                  (type_of Var_const |> dest_type |> snd |> List.hd)
	val exp = mk_comb(Var_const,Term.inst tys exp1)
	val Eval_state_var_assum = my_list_mk_comb(Eval_const,
                            [env,exp,mk_comb(STATE_RI,state_var)])
	val monad_th = ADD_ASSUM Eval_state_var_assum monad_th
      in monad_th end
      else monad_th

    (* Translate the run construct *)
    val x = concl monad_th |> get_Eval_arg
    val exp = concl monad_th |> get_Eval_exp
    val MONAD_TYPE = concl monad_th |> rator |> rand |> rator
    val EXN_TYPE = rand MONAD_TYPE
    val TYPE = rator MONAD_TYPE |> rand
    val vname = stringSyntax.fromMLstring "vname"
    val (exn_cons_names, exn_module_name) = get_exn_constructs ()
    val cons_names = listSyntax.mk_list(exn_cons_names, string_ty)
    val th = case exn_module_name of
		 SOME module_name =>
		 ISPECL [cons_names, module_name, vname, TYPE, EXN_TYPE, x, exp,
			 !H, state_var, env] EvalM_to_EvalSt_MODULE
	       | NONE =>
		 ISPECL [cons_names, vname, TYPE, EXN_TYPE, x, exp,
			 !H, state_var, env] EvalM_to_EvalSt_SIMPLE

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
    val EXN_rw = prove(mk_eq(EXC_TYPE_aux_const, EXC_TYPE_tm), EXC_RI_prove_tac)

    val th = List.foldl (fn (a, th) => MP th a) th [distinct_th, vname_th1, vname_th2]
    val th = PURE_REWRITE_RULE[EXN_rw] th
    val th = MATCH_MP th monad_th

    (* Undischarge the EVERY lookup assumptions *)
    val every_lookup_assum = concl th |> dest_imp |> fst
    val every_lookup_rw = SIMP_CONV list_ss [] every_lookup_assum
    val th = SIMP_RULE bool_ss [every_lookup_rw, GSYM AND_IMP_INTRO] th |> UNDISCH_ALL

    (* Replace the environment *)
    val th = instantiate_local_environment th

    (* Create the local function definitions *)
    val th = create_local_fun_defs th

    (* Create the store *)
    val th = create_local_references th 

    (* Abstract the parameters *)
    val th = if monad_state_is_var then th
	     else create_constant_state th state_var
    val all_params = strip_comb def_lhs |> snd
    val params_evals = List.map var_create_Eval all_params
    val th = m_translate_run_abstract_parameters th def params_evals

    (* Instantiate the environment 0 *)
    val global_env = get_env(get_curr_prog_state())
    val env = concl th |> get_Eval_env
    val th = INST [env |-> global_env] th

    (* clean up the assumptions *)
    fun add_T_imp th =
	if (is_imp o concl) th then th
	else DISCH (concl TRUTH) th
    val th = clean_assumptions (D th) |> add_T_imp

    (* Introduce the precondition *)
    val th = CONV_RULE ((RATOR_CONV o RAND_CONV) (SIMP_CONV (srw_ss()) [EQ_def,PRECONDITION_def])) (D th)
    val precond = concl th |> dest_imp |> fst
    val is_precond_T = same_const (concl TRUTH) precond
    val (th,pre) = if is_precond_T then (MP th TRUTH, TRUTH)
	     else let
		 val pre_type = List.foldr (fn (x,y) =>
                     mk_type("fun", [x,y])) bool_ty
                     (List.map type_of all_params)
		 val pre_var = mk_var(fname ^"_side", pre_type)
		 val pre = list_mk_comb (pre_var, all_params)
		 val def_tm = mk_eq(pre,precond)
		 val pre_def = quietDefine [ANTIQUOTE def_tm]
		 val pre_eq = SPEC (SPEC_ALL pre_def |> concl |> lhs)
				   PRECONDITION_def
		 val th = CONV_RULE ((RATOR_CONV o RAND_CONV)
			((PURE_REWRITE_CONV [GSYM pre_def]) THENC
                        (PURE_ONCE_REWRITE_CONV[GSYM pre_eq]))) th
				    |> UNDISCH
             in (th, pre_def) end

    (* Expand the abbreviated expressions and the handle_mult term *)
    val th = PURE_REWRITE_RULE[handle_mult_def, handle_one_def] th
			      |> remove_local_code_abbrevs
    val _ = undef_local_code_abbrevs()

    (* Store the spec *)
    val th = PURE_REWRITE_RULE[Eval_Fun_rw] th
    val v = th |> concl |> rand |> rator |> rand
    val e = th |> concl |> rand |> rand
    val v_name = find_const_name (fname ^ "_v")
    val _ = ml_prog_update (add_Dlet_Fun fname_str v e v_name)
    val s = get_curr_prog_state ()
    val v_def = hd (get_v_defs s)
    val th = th |> REWRITE_RULE [GSYM v_def]
    val th = remove_Eq_from_v_thm th

    (* Store the certificate for later use *)
    val _ = add_v_thms (fname,fname,th,pre)
    val th = save_thm(fname ^ "_v_thm",th)
    val _ = print ("Saved theorem ____ :" ^fname ^ "_v_thm\n")
in th end

(*
   Code for loading and storing the monadic translator state,
   as the things in ml_translatorLib does not include the
   bits and pieces specific to the monadic translator (i.e.
   exceptions, refs, et caetera.

   Installs a hook to fire off on export_theory (like in the standard
   translator) and recursively calls on translation_extends to load all
   the standard translator state as well.

*)
fun check_uptodate_term tm =
  if Theory.uptodate_term tm then () else let
    val t = find_term (fn tm => is_const tm
      andalso not (Theory.uptodate_term tm)) tm
    val _ = print "\n\nFound out-of-date term: "
    val _ = print_term t
    val _ = print "\n\n"
    in () end


(* Code for resuming a monadic translation.

   Packs all the monadic state into a theorem when the theory is exported.
   The translation can then be resumed by a call to m_translation_extends,
   which acts as a stand-in to translation_extends from the standard translator.

   The following fields are currently *not* saved:

   - dynamic_v_thms
   - dynamic_refs_bindings
   - num_local_environment_vars
*)

local
  open packLib

  val suffix = "_monad_translator_state_thm"

  (* --- Packing --- *)

  fun pack_part0 () =
    pack_5tuple
      pack_type                                  (* refs_type           *)
      pack_type                                  (* exn_type            *)
      pack_term                                  (* aM                  *)
      pack_term                                  (* bM                  *)
      (pack_option pack_thm)                     (* VALID_STORE_THM     *)
        (!refs_type, !exn_type, !aM, !bM, !VALID_STORE_THM)
  fun pack_part1 () =
    pack_6tuple
      pack_thm                                   (* EXN_TYPE_def_ref    *)
      pack_term                                  (* EXN_TYPE            *)
      (pack_list pack_string)                    (* type_theories       *)
      (pack_list (pack_pair pack_term pack_thm)) (* exn_handles         *)
      (pack_list (pack_pair pack_term pack_thm)) (* exn_raises          *)
      (pack_list (pack_pair pack_thm pack_thm))  (* exn_functions_defs  *)
        ( !EXN_TYPE_def_ref, !EXN_TYPE, !type_theories
        , !exn_handles, !exn_raises, !exn_functions_defs )
  fun pack_part2 () =
    pack_6tuple
      pack_term                                  (* default_H           *)
      pack_thm                                   (* H_def               *)
      pack_term                                  (* H                   *)
      (pack_list (pack_pair pack_term pack_thm)) (* access_patterns     *)
      (pack_list (pack_pair pack_thm pack_thm))  (* refs_functions_defs *)
      (pack_list (pack_6tuple
                  pack_thm pack_thm pack_thm
                  pack_thm pack_thm pack_thm))   (* arrays_functions_defs *)
        ( !default_H, !H_def, !H, !access_patterns
        , !refs_functions_defs, !arrays_functions_defs )

  fun pack_state () =
    let
      val name      = Theory.current_theory () ^ suffix
      val name_tm   = stringSyntax.fromMLstring name
      val tag_lemma = ISPEC (mk_var("b",bool)) (ISPEC name_tm TAG_def) |> GSYM

      val p = pack_triple I I I (pack_part0 (), pack_part1 (), pack_part2 ())

      val th = PURE_ONCE_REWRITE_RULE [tag_lemma] p
      val _ = check_uptodate_term (concl th)
    in
      save_thm(name,th)
    end

  (* --- Unpacking --- *)

  fun unpack_types th =
    let
      val (rty, ety, am, bm, vst) =
        unpack_5tuple unpack_type unpack_type unpack_term
                      unpack_term (unpack_option unpack_thm) th
      val _ = (refs_type := rty)
      val _ = (exn_type := ety)
      val _ = (aM := am)
      val _ = (bM := bm)
      val _ = (VALID_STORE_THM := vst)
    in () end

  fun unpack_state1 th =
    let
      val (etdr, et, tt, eh, er, efd) =
        unpack_6tuple
          unpack_thm
          unpack_term
          (unpack_list unpack_string)
          (unpack_list (unpack_pair unpack_term unpack_thm))
          (unpack_list (unpack_pair unpack_term unpack_thm))
          (unpack_list (unpack_pair unpack_thm unpack_thm)) th

      (* Need to add the current theory to type_theories or we cannot
         access definitions generated after extending! *)
      val curr_thy =
        case List.find (fn thy => thy = current_theory ()) tt of
          NONE => [current_theory ()]
        | _ => []

      val _ = (EXN_TYPE_def_ref := etdr)
      val _ = (EXN_TYPE := et)
      val _ = (type_theories := tt @ curr_thy)
      val _ = (exn_handles := eh)
      val _ = (exn_raises := er)
      val _ = (exn_functions_defs := efd)
    in () end

  fun unpack_state2 th =
    let
      val (dh, hd, h, ap, rfd, afd) =
        unpack_6tuple
          unpack_term
          unpack_thm
          unpack_term
          (unpack_list (unpack_pair unpack_term unpack_thm))
          (unpack_list (unpack_pair unpack_thm unpack_thm))
          (unpack_list (unpack_6tuple unpack_thm unpack_thm unpack_thm
                                      unpack_thm unpack_thm unpack_thm)) th
      val _ = (default_H := dh)
      val _ = (H_def := hd)
      val _ = (H := h)
      val _ = (access_patterns := ap)
      val _ = (refs_functions_defs := rfd)
      val _ = (arrays_functions_defs := afd)
    in () end

  fun unpack_state name =
    let
      val th = fetch name (name ^ suffix)
      val th = PURE_ONCE_REWRITE_RULE [TAG_def] th
      val (tys, st1, st2) = unpack_triple I I I th
      val _ = unpack_types tys
      val _ = unpack_state1 st1
      val _ = unpack_state2 st2
    in () end

  val finalised = ref false
in (* Borrowed from ml_translatorLib *)
  fun finalise_reset () = (finalised := false)
  fun finalise_translation () =
    if !finalised then () else let
      val _ = (finalised := true)
      val _ = pack_state ()
      (* val _ = print_translation_output () *) (* TODO: Would this be useful? *)
      in () end

  val _ = Theory.register_hook
            ( "cakeML.ml_monad_translator"
            , (fn TheoryDelta.ExportTheory _ => finalise_translation ()
                  | _                        => ()))

  fun m_translation_extends name = let
    val _ = print ("Loading monadic translator state from: " ^ name ^ " ... ")
    val _ = unpack_state name
    val _ = print "done.\n"
    val _ = translation_extends name
    in () end;

end

(*
val lhs = fst o dest_eq;
val rhs = snd o dest_eq;
*)

end
