structure ml_monad_translatorLib :> ml_monad_translatorLib = struct

open preamble
open astTheory libTheory semanticPrimitivesTheory bigStepTheory
     ml_translatorTheory ml_progTheory ml_progLib
     ml_pmatchTheory ml_monadBaseTheory ml_monad_translatorTheory ml_translatorTheory
open terminationTheory
open ml_monadStoreLib cfTacticsLib
open Net List
open ml_translatorLib

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;

fun primCases_on tm = Cases_on [ANTIQUOTE tm]

val _ = (print_asts := true);

val _ = (use_full_type_names := false);

val polymorph_monad_type = ``:'a -> ('b, 'c) exc # 'a``;
fun dest_monad_type ty =
  let val s = (match_type polymorph_monad_type ty) in
      (type_subst s ``:'a``, type_subst s ``:'b``, type_subst s ``:'c``) end;

(* Some constants *)
val venvironment = mk_environment v_ty;
val env_tm = mk_var("env",venvironment);
val cl_env_tm = mk_var("cl_env",venvironment);
val string_ty = ``:tvarN``;
(* ---- *)

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
val refs_type = ref ``:unit``;

(* The exception refinement invariant and type *)
val EXN_TYPE_def_ref = ref UNIT_TYPE_def;
val EXN_TYPE = ref ``UNIT_TYPE``;
val exn_type = ref ``:unit``;

(* Some functions to generate monadic types *)
fun M_type ty = ``:^(!refs_type) -> (^ty, ^(!exn_type)) exc # ^(!refs_type)``;
val aM = ref (ty_antiq (M_type ``:'a``));
val bM = ref (ty_antiq (M_type ``:'b``));

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
val dynamic_specs = ref (Net.empty : (string * string * thm) net);

fun add_dynamic_spec name ml_name spec = let
    val spec = UNDISCH_ALL spec
    val hol_fun = concl spec |> rator |> rand
    val _ = dynamic_specs := (Net.insert (hol_fun, (name, ml_name, spec)) (!dynamic_specs))
    val _ = print("Added a dynamic specification for " ^(dest_const hol_fun |> fst) ^"\n")
in () end;

fun lookup_dynamic_v_thm tm = let
    val matches = Net.match tm (!dynamic_specs)
    val (name, ml_name, th) = tryfind (fn (n, n', x) => if (concl x |> rator |> rand |> same_const tm) then (n, n', x) else failwith "") matches
    val th = MATCH_MP Eval_Var_Short th
    val v_name = stringSyntax.fromMLstring ml_name
    val th = SPECL [stringSyntax.fromMLstring ml_name, env_tm] th |> UNDISCH_ALL
in th end;

(* The environment extension for dynamically initialized stores *)
val dynamic_init_env = ref (NONE : term option);

(* Some minor functions *)
fun ISPEC_EvalM th = ISPEC (!H) th;
fun ISPEC_EvalM_EXN_TYPE th = ISPEC (!EXN_TYPE) th;
fun ISPEC_EvalM_MONAD th = ISPECL[!H, !EXN_TYPE] th;
fun ISPEC_EvalM_VALID th = case (!VALID_STORE_THM) of
			   SOME store_th => MP (ISPEC (!H) th) store_th
			    | NONE => UNDISCH (ISPEC (!H) th)
fun prove_VALID_STORE_assum th =
  case (!VALID_STORE_THM) of
      SOME store_th => (MP (DISCH (concl store_th) th) store_th handle HOL_ERR _ => th)
    | NONE => th

fun inst_monad_type tm =
  let
      val ty_subst = Type.match_type polymorph_monad_type (type_of tm)
      val a = Type.type_subst ty_subst ``:'a``
      val c = Type.type_subst ty_subst ``:'c``
      val tm' = Term.inst [a |-> !refs_type, c |-> !exn_type] tm
  in
      tm'
  end;
(* ---- *)

fun get_m_type_inv ty =
  let
      val result_type = dest_monad_type ty |> #2
      val MONAD_type = M_type result_type
      val MONAD_type = ``:(^result_type -> v -> bool) -> (^(!exn_type) -> v -> bool) ->
			  (^MONAD_type, ^(!refs_type)) H``
      val MONAD_RI = mk_const("MONAD", MONAD_type)
  in
      ``^MONAD_RI ^(get_type_inv result_type) ^(!EXN_TYPE)``
  end
  handle HOL_ERR _ => failwith "unknown type";

fun mk_PURE_tm ty = mk_const("PURE", ``:(^ty -> v -> bool) -> (^ty, ^(!refs_type)) H``);

fun type_to_PURE_INV ty = let
  val PURE_tm = mk_const("PURE", ``:(^ty -> v -> bool) -> (^ty, ^(!refs_type)) H``)
  in mk_comb (PURE_tm, get_type_inv ty) end;

fun get_arrow_type_inv ty =
  if can dest_monad_type ty then get_m_type_inv ty else let
    val (ty1,ty2) = dest_fun_type ty
    val i1 = get_arrow_type_inv ty1 handle HOL_ERR _ =>
             type_to_PURE_INV ty1
    val i2 = get_arrow_type_inv ty2
  in ``ArrowM ^(!H) ^i1 ^i2`` end;

fun smart_get_type_inv ty =
  if not (can dest_monad_type ty) andalso
     can get_arrow_type_inv ty then let
    val inv = get_arrow_type_inv ty
    in ONCE_REWRITE_CONV [ArrowM_def] inv |> concl |> rand |> rand end
  else get_type_inv ty;

val ArrowP_PURE_pat = ``ArrowP H a (PURE b)``;
val ArrowP_EqSt_pat = ``ArrowP H (EqSt a st) b``;
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
      in (foldl (fn (x,y) => mk_comb(y,x)) v args) end end

(* Retrieves the parameters given to Eval or EvalM *)
val Eval_tm = ``Eval``;
val EvalM_tm = ``EvalM``;
fun get_Eval_arg e = if same_const (strip_comb e |> fst) Eval_tm then e |> rand |> rand
		     else e |> rator |> rand |> rand;
fun get_Eval_env e = if same_const (strip_comb e |> fst) Eval_tm then e |> rator |> rator |> rand
		     else e |> rator |> rator |> rator |> rator |> rand;
fun get_Eval_exp e = if same_const (strip_comb e |> fst) Eval_tm then e |> rator |> rand
		     else e |> rator |> rator |> rand;
fun remove_Eval_storePred e = if same_const (strip_comb e |> fst) Eval_tm then e
		     else e |> rator;
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
		   |> INST_TYPE [``:'ffi``|->``:unit``]) >>
      rw[do_con_check_def,build_conv_def] >>
      fs [lookup_cons_def] >>
      fs[exn_ri_def,namespaceTheory.id_to_n_def] >>
      asm_exists_tac \\ fs[] >>
      PURE_REWRITE_TAC[GSYM APPEND_ASSOC] \\ fs[REFS_PRED_FRAME_append]

    val goal =
    ``!H x a.
      (lookup_cons ^cons_name env = SOME (1,^deep_type)) ==>
      Eval env exp1 (^refin_inv x) ==>
      EvalM env st (Raise (Con (SOME (Short ^cons_name)) [exp1]))
        (MONAD a ^EXN_RI_tm (^fun_tm x)) H``
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

val failure_pat_tm = ``\v. (Failure(C v), state_var)``;
fun add_raise_handle_functions exceptions_functions exn_ri_def = let
    val (raise_functions, handle_functions) = unzip exceptions_functions

    (* Extract information from the exception refinement invariant *)
    val exn_ri_cases = CONJUNCTS exn_ri_def
    val EXN_RI_tm = List.hd exn_ri_cases |> concl |> strip_forall |> snd |> lhs |> rator |> rator
    val exn_ri_cons = List.map (rator o rand o rator o lhs o snd o strip_forall o concl) exn_ri_cases
    val exn_ri_types = List.map (type_of o rand o rand o rator o lhs o snd
				 o strip_forall o concl) exn_ri_cases
    val _ = mapfilter register_type exn_ri_types
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

	val (SOME handled_cons) = List.find (fn (x, y) => not(can (Term.match_term failure_pat_tm) y))
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
fun derive_case_of ty = let
  fun smart_full_name_of_type ty =
    if let val r = dest_thy_type ty in #Tyop r = "cpn" andalso #Thy r = "toto" end then "order"
    else full_name_of_type ty
  fun get_name ty = clean_uppercase (smart_full_name_of_type ty) ^ "_TYPE"
  val name = if ty <> ``:unit`` then get_name ty else "UNIT_TYPE"
  val inv_def = tryfind (fn thy_name => fetch thy_name (name ^ "_def"))
                        (!type_theories)
  val case_th = get_nchotomy_of ty
  val pat = ``Eval env exp (P (res:'a))``
  val pure_tm = case_of ty |> concl
  (* Find a variable for the store invariant *)
  val pure_tm_vars = all_vars pure_tm
  val H_var = mk_var("H", mk_type("fun", [!refs_type, ``:hprop``]))
  val H_var = variant pure_tm_vars H_var
  (* Convert the Eval predicates to EvalM predicates *)
  fun Eval_to_EvalM tm = let
    val (m,i) = match_term pat tm
    val res = mk_var("res", M_type ``:'a``)
    val tm1 = subst m (inst i ``EvalM env exp (MONAD P ^(!EXN_TYPE) ^res) ^H_var``)
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
  val evaluate_Mat =
    ``evaluate c x env (Mat e pats) (xx,res)``
    |> (ONCE_REWRITE_CONV [evaluate_cases] THENC SIMP_CONV (srw_ss()) [])
  val evaluate_match_Conv =
    ``evaluate_match c x env args
         ((Pcon xx pats,exp2)::pats2) errv (yyy,y)``
    |> (ONCE_REWRITE_CONV [evaluate_cases] THENC
        SIMP_CONV (srw_ss()) [pmatch_def])
  val IF_T = Q.prove(`(if T then x else y) = x:'a`,SIMP_TAC std_ss []);
  val IF_F = Q.prove(`(if F then x else y) = y:'a`,SIMP_TAC std_ss []);
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
  handle HOL_ERR _ => raise (ERR "derive_case_of" ("failed on type : " ^(type_to_string ty)));

(* fun type_mem f = let
  val memory = ref []
  fun lookup x [] = fail()
    | lookup x ((y,z)::ys) = if can (match_type y) x then z else lookup x ys
  in (fn ty => lookup ty (!memory) handle HOL_ERR _ => let
              val th = f ty
              val _ = (memory := (ty,th)::(!memory))
              in th end, memory) end; *)
(* val (mem_derive_case_of, mem_derive_case_ref) = type_mem derive_case_of; *)

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
  else ty;

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

fun mk_list (l, ty) = let
    val ty_aq = ty_antiq ty
    val empty_list = ``[] : ^ty_aq list``
    val cons_tm = ``$CONS : ^ty_aq -> ^ty_aq list -> ^ty_aq list``
    val hol_l = List.foldr (fn (x, l) => mk_comb(mk_comb(cons_tm, x), l)) empty_list l
in hol_l end;

fun compute_dynamic_env_ext all_access_specs = let
    val store_vars = FVL [(!H)] empty_varset;
    fun get_dynamic_init_bindings spec = let
	val spec = SPEC_ALL spec |> UNDISCH_ALL
	val pat = ``nsLookup (env : env_val) (Short (vname : tvarN)) = SOME (loc : v)``
	val lookup_assums = List.filter (can (match_term pat)) (hyp (UNDISCH_ALL spec))
	val bindings = List.map(fn x => let val (tms, tys) = match_term pat x in
	    (Term.subst tms ``(vname : tvarN)``, Term.subst tms ``(loc : v)``) end) lookup_assums
	val bindings = List.filter (fn (x, y) => HOLset.member(store_vars, y)) bindings
    in bindings end

    val all_bindings = List.concat(List.map get_dynamic_init_bindings all_access_specs)
    val bindings_map = List.foldl (fn ((n, v), m) => Redblackmap.insert(m, v, n))
				  (Redblackmap.mkDict Term.compare) all_bindings
    val store_varsl = strip_comb (!H) |> snd
    val final_bindings = List.map (fn x => (Redblackmap.find (bindings_map, x), x)) store_varsl
    val hol_bindings = List.map mk_pair final_bindings
    val dynamic_store = mk_list(hol_bindings, ``:tvarN # v``)
    val dynamic_store = ``<| v := Bind ^dynamic_store []; c := Bind [] []|> : v sem_env``
in dynamic_store end;

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
      val _ = aM := (ty_antiq (M_type ``:'a``))
      val _ = bM := (ty_antiq (M_type ``:'b``))
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
      val _ = dynamic_specs := Net.empty

      (* Dynamic init environment *)
      val _ = dynamic_init_env := (if (!dynamic_init_H) then
				      SOME (compute_dynamic_env_ext all_access_specs) else NONE)
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
           |> List.map (fn tm => (tm,List.map (fn x => (x,rename_var "n" ``:string`` x,
                                                rename_var "v" ``:v`` x))
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
is_conj tm

val tm = y;
val tm = z;
*)

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
  fun sat_hyp tm = let
    val (vs,x) = list_dest_forall tm
    val (x,y) = dest_imp x
    val z = get_Eval_arg y
    val lemma = if can dest_monad_type (type_of z)
                then m2deep z
                else hol2deep z
    val lemma = D lemma
    val new_env = get_Eval_env y
    val env = env_tm
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

val forall_pat = ``!x. P``;
fun prove_EvalMPatBind goal m2deep = let
  val (vars,rhs_tm) = repeat (snd o dest_forall) goal
                      |> rand |> get_Eval_arg |> rator
                      |> dest_pabs
  val res = m2deep rhs_tm
  val exp = res |> concl |> get_Eval_exp
  val th = D res
  val var_assum = ``Eval env (Var n) (a (y:'a))``
  val is_var_assum = can (match_term var_assum)
  val vs = find_terms is_var_assum (concl th |> remove_Eval_storePred)
  fun delete_var tm =
    if mem tm vs then MATCH_MP IMP_EQ_T (ASSUME tm) else NO_CONV tm
  val th = CONV_RULE ((RATOR_CONV) (DEPTH_CONV delete_var)) th
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV)
              (PairRules.UNPBETA_CONV vars)) th
  val p = th |> concl |> dest_imp |> fst |> rator
  val p2 = goal |> dest_forall |> snd |> dest_forall |> snd
                |> dest_imp |> fst |> rand |> rator
  val ws = free_vars vars
  val vs = List.filter (fn tm => not (mem (rand (rand tm)) ws)) vs |> mk_set
  val new_goal = goal |> subst [``e:ast$exp``|->exp,p2 |-> p]
  val new_goal = List.foldr mk_imp new_goal vs
  (*
    set_goal([],new_goal)
  *)
  val th = TAC_PROOF (([],new_goal),
    NTAC (length vs) STRIP_TAC \\ STRIP_TAC
    \\ fs [FORALL_PROD] \\ REPEAT STRIP_TAC
    \\ MATCH_MP_TAC (D res) \\ fs []
    \\ fs [EvalPatBind_def,Pmatch_def]
    \\ REPEAT (POP_ASSUM MP_TAC)
    \\ NTAC (length vs) STRIP_TAC
    \\ CONV_TAC ((RATOR_CONV o RAND_CONV) EVAL)
    \\ STRIP_TAC \\ fs [] \\ rfs []
    \\ fs [Pmatch_def,PMATCH_option_case_rwt]
    \\ BasicProvers.EVERY_CASE_TAC \\ fs []
    \\ rpt (CHANGED_TAC(SRW_TAC [] [Eval_Var_SIMP,Once EvalM_Var_SIMP,lookup_cons_write,lookup_var_write]))
    \\ TRY (first_x_assum match_mp_tac >> METIS_TAC[])
    (* Because of EvalM_bind *)
    (* \\ rpt (qpat_x_assum `^forall_pat` IMP_RES_TAC) *)
    (* --------------------- *)
    \\ fs[GSYM FORALL_PROD]
    \\ EVAL_TAC)
  in UNDISCH_ALL th end handle HOL_ERR e => failwith "prove_EvalMPatBind failed";

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

val i = ref (List.length ts)
val xs_ref = ref ts
val th_ref = ref nil_lemma
*)

  fun trans [] = nil_lemma
    | trans ((pat,rhs_tm)::xs) = let
    val th = trans xs
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
  val th = MATCH_MP th (UNDISCH x_res)
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
  val assum = ``Eval env (Var (Short ^str)) ^ri``
  val new_env = ``write ^str (v:v) ^env_tm``
  val old_env = new_env |> rand
  val th = thx |> UNDISCH_ALL |> REWRITE_RULE [GSYM SafeVar_def]
               |> DISCH_ALL |> DISCH assum |> SIMP_RULE bool_ss []
               |> INST [old_env|->new_env]
               |> SIMP_RULE bool_ss [Eval_Var_SIMP,lookup_var_write]
               |> ONCE_REWRITE_RULE [EvalM_Var_SIMP]
               |> ONCE_REWRITE_RULE [EvalM_Var_SIMP]
               |> REWRITE_RULE [lookup_cons_write,lookup_var_write]
               |> CONV_RULE (DEPTH_CONV stringLib.string_EQ_CONV)
               |> SIMP_RULE bool_ss [SafeVar_def]
  val new_assum = fst (dest_imp (concl th))
  val th1 = th |> UNDISCH_ALL
               |> CONV_RULE ((RATOR_CONV o RAND_CONV o RAND_CONV) (UNBETA_CONV v))
               |> DISCH new_assum
  in th1 end;

(* 
	val (th,v) = if no_params then (th,T) else
                     (List.foldr (fn (v,th) => apply_EvalM_Fun v th true) th
				 (rev (if is_rec then butlast rev_params else rev_params)),
                      List.last rev_params)

val v = List.last (rev (if is_rec then butlast rev_params else rev_params))
*)

(* fun remove_EqSt th = let
  val st_var = UNDISCH_ALL th |> concl |> get_EvalM_state
  val th = GEN st_var th |> MATCH_MP ArrowP_EqSt_elim
in th end handle HOL_ERR _ => th; *)

fun remove_ArrowM_EqSt th = let
  val st_var = th |> concl |> rator |> rand |> rator |> rator |> rand |> rand
  val th = GEN st_var th |> MATCH_MP ArrowM_EqSt_elim
in th end handle HOL_ERR _ => th;

fun apply_EvalM_Fun v th fix = let
  val th1 = inst_EvalM_env v th
  val th2 = inst_new_state_var [th1] th1
  val th3 = if fix then MATCH_MP EvalM_Fun_Eq (GEN ``v:v`` th2)
                   else MATCH_MP EvalM_Fun (GEN ``v:v`` (FORCE_GEN v th2))
  val th4 = remove_ArrowM_EqSt th3
  in th4 end;

fun apply_EvalM_Recclosure recc fname v th = let
  val vname = fst (dest_var v)
  val vname_str = stringLib.fromMLstring vname
  val fname_str = stringLib.fromMLstring fname
  val FORALL_CONV = RAND_CONV o ABS_CONV
  val lemma = ISPECL [!H, recc,fname_str] EvalM_Recclosure_ALT
              |> CONV_RULE ((FORALL_CONV o FORALL_CONV o
                            RATOR_CONV o RAND_CONV) EVAL)
  val pat = lemma |> concl |> find_term (can (match_term (get_term "find_recfun")))
  val lemma = SIMP_RULE std_ss [EVAL pat] lemma
  val inv = smart_get_type_inv (type_of v)
  val pat = EvalM_def |> SPEC_ALL |> concl |> dest_eq |> fst |> rator |> rator |> rator
  val pat = lemma |> concl |> find_term (can (match_term pat))
  val new_env = pat |> rand
  val old_env = env_tm
  val tys = Type.match_type (type_of v) (type_of inv |> dest_type |> snd |> List.hd)
  val v = Term.inst tys v
  val assum = subst [old_env|->new_env]
                 ``Eval env (Var (Short ^vname_str)) (^inv ^v)``
  val EvalM_SIMP_th = ISPEC (!H) EvalM_Var_SIMP_PURE |> UNDISCH
  val thx = th |> UNDISCH_ALL |> REWRITE_RULE [GSYM SafeVar_def]
               |> DISCH_ALL |> DISCH assum (* |> SIMP_RULE bool_ss [] *)
               |> INST [old_env|->new_env]
               |> PURE_REWRITE_RULE [ArrowM_def, EvalM_SIMP_th, Eval_Var_SIMP,
                                     lookup_var_write,lookup_cons_write]
               |> CONV_RULE (DEPTH_CONV stringLib.string_EQ_CONV)
               |> REWRITE_RULE [SafeVar_def]
               |> PURE_REWRITE_RULE[GSYM ArrowM_def]
  val new_assum = fst (dest_imp (concl thx))
  val th1 = thx |> UNDISCH |> REWRITE_RULE [ASSUME new_assum]
		|> UNDISCH_ALL
                |> CONV_RULE ((RATOR_CONV o RAND_CONV o RAND_CONV) (UNBETA_CONV v)) (* RATOR_CONV *)
                |> DISCH new_assum
  val th2 = MATCH_MP lemma (Q.INST [`env`|->`cl_env`] (GEN ``v:v`` th1))
  val assum = ASSUME (fst (dest_imp (concl th2)))
  val th3 = Dfilter th2 |> REWRITE_RULE [assum]
	          |> PURE_REWRITE_RULE[ArrowM_def]
                  |> REWRITE_RULE [Eval_Var_SIMP, EvalM_SIMP_th,
				   lookup_var_write,FOLDR,write_rec_def]
                  |> CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV)
                  |> REWRITE_RULE [Eval_Var_SIMP, EvalM_SIMP_th, lookup_var_write,FOLDR]
                  |> CONV_RULE (DEPTH_CONV stringLib.string_EQ_CONV)
                  |> REWRITE_RULE [SafeVar_def]
		  |> PURE_REWRITE_RULE[GSYM ArrowM_def]
  val lemma = case !VALID_STORE_THM of
		  SOME th => MP (ISPEC (!H) EvalM_Eq_Recclosure) th |> UNDISCH
		| NONE => UNDISCH_ALL (ISPEC (!H) EvalM_Eq_Recclosure)
  val lemma_lhs = lemma |> concl |> dest_eq |> fst
  fun replace_conv tm = let
    val (i,t) = match_term lemma_lhs tm
    val th9 = INST i (INST_TYPE t lemma)
    val name = lemma_lhs |> inst t |> subst i |> rand |> rand
    in INST [mk_var("name",string_ty)|->name] th9 end handle HOL_ERR _ => NO_CONV tm
  val th4 = CONV_RULE (QCONV (DEPTH_CONV replace_conv)) th3
  in th4 end

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
  val lemma = mk_thm([],get_term "eq remove")
  val tm2 = QCONV (REWRITE_CONV [lemma]) res |> concl |> dest_eq |> snd
  in tm2 end

fun MY_MATCH_MP th1 th2 = let
  val tm1 = fst (dest_imp (concl th1))
  val tm2 = concl th2
  val (s,i) = match_term tm1 tm2
  in MP (INST s (INST_TYPE i th1)) th2 end;
(* End of COPY/PASTE from ml_translatorLib *)

fun force_remove_fix thx = let
  val pat = Eq_def |> SPEC_ALL |> concl |> dest_eq |> fst
  val xs = List.map rand (find_terms (can (match_term pat)) (concl thx))
  val s = SIMP_RULE std_ss [EvalM_FUN_FORALL_EQ,M_FUN_QUANT_SIMP]
  val thx = List.foldr (fn (x,th) => s (FORCE_GEN x th)) thx xs
  in thx end;

(* ---- *)
fun var_hol2deep tm =
  if is_var tm andalso can get_arrow_type_inv (type_of tm) then let
    val (name,ty) = dest_var tm
    val inv = get_arrow_type_inv ty
    val inv = ONCE_REWRITE_CONV [ArrowM_def] inv |> concl |> rand |> rand
    val str = stringSyntax.fromMLstring name
    val result = ASSUME (mk_comb(``Eval env (Var (Short ^str))``,mk_comb(inv,tm)))
    in check_inv "var" tm result end
  else hol2deep tm;

(* raise, handle *)
fun get_pattern patterns tm = tryfind (fn(pat, th) => if can (match_term pat) tm then (pat, th) else failwith "get_pattern") patterns;

fun print_tm_msg msg tm =
  print (msg  ^(term_to_string tm) ^ "\n\n");

val H_STAR_TRUE = Q.prove(`(H * &T = H) /\ (&T * H = H)`, fs[SEP_CLAUSES])

fun instantiate_EvalM_bind th1 th2 = let
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
    val n_st = ``SND (^x ^st_var)``
    val th2' = INST [st_var |-> n_st] th2'
    val th1' = D th1
    val result = MATCH_MP EvalM_bind (CONJ th1' th2')
    val result = UNDISCH result
in result end;

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

fun instantiate_EvalM_handle EvalM_th tm m2deep = let
    val x = tm |> rator |> rand
    val (v,y) = tm |> rand |> dest_abs
    val th1 = m2deep x
    val th2 = m2deep y
    (* val st1 = concl th1 |> rator |> rator |> rator |> rand
    val st2 = concl th2 |> rator |> rator |> rator |> rand *)
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

fun instantiate_EvalM_otherwise tm m2deep = let
    val x = tm |> rator |> rand
    val y = tm |> rand
    val th1 = m2deep x
    val th2 = m2deep y
    val th2 = th2 |> DISCH_ALL |> Q.INST [`env`|->`write "v" i env`]
                  |> REWRITE_RULE [Eval_Var_SIMP2,lookup_cons_write]
                  |> ONCE_REWRITE_RULE [EvalM_Var_SIMP]
                  |> ONCE_REWRITE_RULE [EvalM_Var_SIMP]
                  |> REWRITE_RULE [lookup_cons_write,lookup_var_write]
                  |> CONV_RULE (DEPTH_CONV stringLib.string_EQ_CONV)
                  |> REWRITE_RULE []
                  |> D
    val st2 = concl th2 |> dest_imp |> snd |> get_EvalM_state
    val assums = concl th2 |> dest_imp |> fst
    val assums_eq = mk_comb(mk_abs(st2, assums), st2) |> BETA_CONV
    val th3 = CONV_RULE ((RATOR_CONV o RAND_CONV) (PURE_ONCE_REWRITE_CONV [GSYM assums_eq])) th2 |> Q.GEN `i` |> GEN st2 
    val th4 = CONJ (D th1) th3
    val result = MATCH_MP (SPEC_ALL EvalM_otherwise) th4
    val result = CONV_RULE ((RATOR_CONV o RAND_CONV) (DEPTH_CONV BETA_CONV)) result |> UNDISCH
in result end;

(* val previously_translated_state_var_index = ref 1;
fun previously_transl_state_var () = let
    val i = !previously_translated_state_var_index
    val name = "st" ^(Int.toString i)
    val st_v = mk_var(name, !refs_type)
    val _ = (previously_translated_state_var_index := i + 1)
in st_v end; *)

fun m2deep tm =
  (* variable *)
  if is_var tm then let
    (* val _ = print_tm_msg "is_var\n" tm DEBUG *)
    val (name,ty) = dest_var tm
    val inv = get_arrow_type_inv ty
    val inv = ONCE_REWRITE_CONV [ArrowM_def] inv |> concl |> rand |> rand
    val str = stringSyntax.fromMLstring name
    val result = ASSUME (mk_comb(``Eval env (Var (Short ^str))``,mk_comb(inv,tm)))
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
    val result = instantiate_EvalM_handle EvalM_th tm m2deep
    in check_inv "handle custom pattern" tm result end
  (* return *)
  else if can (match_term ``(st_ex_return x): ^(!aM)``) tm then let
    (* val _ = print_tm_msg "return\n" tm DEBUG *)
    val th = hol2deep (rand tm)
    val result = MATCH_MP (ISPEC_EvalM_MONAD EvalM_return) th
    in check_inv "return" tm result end
  (* bind *)
  else if can (match_term ``(st_ex_bind (x:^(!bM)) f): ^(!aM)``) tm then let
    (* val _ = print_tm_msg "monad_bind\n" tm DEBUG *)
    val x1 = tm |> rator |> rand
    val (v,x2) = tm |> rand |> dest_abs
    val th1 = m2deep x1
    val th2 = m2deep x2
    val th2 = inst_EvalM_env v th2
    val result = instantiate_EvalM_bind th1 th2
  in check_inv "bind" tm result end else
  (* otherwise *)
  if can (match_term ``(x: ^(!aM)) otherwise (y: ^(!aM))``) tm then let
    (* val _ = print_tm_msg "otherwise\n" tm DEBUG *)
    val result = instantiate_EvalM_otherwise tm m2deep
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
    val th2 = th2 |> GEN ``v:v``
    val z = th1 |> concl |> rand |> rand
    val th2 = INST [v|->z] th2
    val result = MATCH_MP (ISPEC_EvalM EvalM_Let) (CONJ th1 th2)
    in check_inv "let" tm result end else
  (* data-type pattern-matching *)
  ( (* print_tm_msg "data-type pattern-matching\n" tm; DEBUG *) inst_case_thm tm m2deep) handle HOL_ERR _ =>
  (* previously translated term for dynamic store initialisation *)
  if can lookup_dynamic_v_thm tm then let
    (* val _ = print_tm_msg "previously translated - dynamic\n" tm DEBUG *)
    val th = lookup_dynamic_v_thm tm
    val inv = smart_get_type_inv (type_of tm)
    val target = mk_comb(inv,tm)
    val (ss,ii) = match_term (th |> concl |> rand) target
    val H_var = concl Eval_IMP_PURE |> dest_forall |> fst
    val H_var = mk_var(dest_var H_var |> fst, type_of(!H))
    val Eval_IMP_PURE_spec = ISPEC H_var Eval_IMP_PURE
    val result = INST ss (INST_TYPE ii th)
                 |> MATCH_MP Eval_IMP_PURE_spec
                 |> REWRITE_RULE [GSYM ArrowM_def]
		 |> Thm.INST [H_var |-> !H]
    in check_inv "lookup_dynamic_v_thm" tm result end else
  (* previously translated term *)
  if can lookup_v_thm tm then let
    (* val _ = print_tm_msg "previously translated\n" tm DEBUG *)
      val th = lookup_v_thm tm
      (* Instantiate the variables in the occurences of Eq*)
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
      val res = th |> UNDISCH_ALL |> concl |> rand
      val inv = smart_get_type_inv (type_of tm)
      val target = mk_comb(inv,tm)
      val (ss,ii) = match_term res target handle HOL_ERR _ =>
         match_term (rm_fix res) (rm_fix target) handle HOL_ERR _ => ([],[])
      val result = INST ss (INST_TYPE ii th)
		      |> MATCH_MP (ISPEC_EvalM Eval_IMP_PURE)
                      |> REWRITE_RULE [GSYM ArrowM_def]
    in check_inv "lookup_v_thm" tm result end else
  (* if statements *)
  if can (match_term ``if b then x: ^(!aM) else y: ^(!aM)``) tm then let
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
	if can (match_term ``Eval env exp P``) asm then let
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
    fun dest_args tm = rand tm :: dest_args (rator tm) handle HOL_ERR _ => []
    val xs = dest_args tm
    val f = repeat rator lhs
    val str = stringLib.fromMLstring fname
    fun mk_fix tm = let
      val inv_type = type_of tm
      val inv = smart_get_type_inv inv_type
      val eq = ``Eq ^inv ^tm``
      val PURE_tm = mk_PURE_tm inv_type
      in ``^PURE_tm (Eq ^inv ^tm)`` end
    fun mk_m_arrow x y = ``ArrowM ^(!H) ^x ^y``
    fun mk_inv [] res = res
      | mk_inv (x::xs) res = mk_inv xs (mk_m_arrow (mk_fix x) res)
    val inv = mk_inv xs (get_m_type_inv (type_of tm))
    val ss = fst (match_term lhs tm)
    val tys = match_type (type_of f) (type_of inv |> dest_type |> snd |> List.hd)
    val f = Term.inst tys f

    val pre = subst ss pre_var
    val h = ASSUME ``PreImp ^pre (EvalM env (Var (Short ^str)) (^inv ^f) ^(!H))``
            |> RW [PreImp_def] |> UNDISCH
    val ys = List.map (fn tm => MATCH_MP (ISPEC_EvalM Eval_IMP_PURE)
                             (MATCH_MP Eval_Eq (var_hol2deep tm))) xs
    fun apply_arrow hyp [] = hyp
      | apply_arrow hyp (x::xs) =
          MATCH_MP (MATCH_MP (ISPEC_EvalM EvalM_ArrowM) (apply_arrow hyp xs)) x
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
    val (f,x) = dest_comb tm
    val thf = m2deep f
    val thx = hol2deep x |> MATCH_MP (ISPEC_EvalM Eval_IMP_PURE)
	      handle e => m2deep x
    val thx = force_remove_fix thx
    val result = MATCH_MP (MATCH_MP EvalM_ArrowM thf) thx
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
    in check_inv "comb" tm result end else
  failwith ("cannot translate: " ^ term_to_string tm);

fun get_curr_prog_state () = let
  val k = ref init_state
  val _ = ml_prog_update (fn s => (k := s; s))
  in !k end

fun EvalM_P_CONV CONV tm =
  if is_imp tm then (RAND_CONV o RATOR_CONV o RAND_CONV) CONV tm
  else (RATOR_CONV o RAND_CONV) CONV tm;

val local_environment_var_name = "local_environment_var_";
val num_local_environment_vars = ref 0;
val local_environment_var_0 = mk_var("local_environment_var_0", ``:v sem_env``);
fun get_curr_env () =
  case !dynamic_init_env of
      SOME env => let
       val _ = num_local_environment_vars := ((!num_local_environment_vars) +1)
       val env_var = mk_var(local_environment_var_name ^(int_to_string (!num_local_environment_vars)),
                            ``:v sem_env``)
   in ``merge_env ^env_var (merge_env ^env ^local_environment_var_0)`` end
      | NONE => get_env (get_curr_prog_state ());

val PURE_ArrowP_Eq_tm = ``PURE(ArrowP H (PURE (Eq a x)) b)``;
fun remove_Eq th = let
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
in th end handle HOL_ERR _ => th;

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

fun extract_precondition_rec thms = let
(* val (fname,ml_fname,def,th) = List.hd thms *)
  fun rephrase_pre (fname,ml_fname,def,th) = let
    val (lhs,_) = dest_eq (concl def)
    val pre_var = get_pre_var lhs fname
    val th = SIMP_RULE bool_ss [CONTAINER_NOT_ZERO] th
    val th = ex_rename_bound_vars_rule th
    val th = CONV_RULE ((RATOR_CONV o RAND_CONV)
               (REWRITE_CONV [GSYM AND_IMP_INTRO])) th
    val tm = concl th |> dest_imp |> fst
    val rw0 = ASSUME (get_term "remove lookup_cons")
    val tm0 = QCONV (REWRITE_CONV [rw0]) tm |> concl |> rand
    val rw1 = ASSUME (get_term "precond = T")
    val tm1 = QCONV (REWRITE_CONV [rw1]) tm0 |> concl |> rand
    val pat = EvalM_def |> SPEC_ALL |> concl |> dest_eq |> fst
    val (tms, tys) = match_term (rand pat) (!H)
    val pat = Term.inst tys pat |> Term.subst tms
    val rw2 = ASSUME (list_mk_forall(free_vars pat,pat))
    val tm2 = QCONV (REWRITE_CONV [rw0,rw2,PreImp_def]) tm |> concl |> rand
  in (fname,ml_fname,def,th,pre_var,tm1,tm2,rw2) end
  val thms = List.map rephrase_pre thms
(*
val (fname,def,th,pre_var,tm1,tm2,rw2) = hd thms
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
  fun separate_pre (fname,ml_fname,def,th,pre_var,tm1,tm2,rw2) = let
    val lemma = derive_split (th |> concl |> dest_imp |> fst)
    val lemma = MATCH_MP combine_lemma (CONJ lemma th)
                |> CONV_RULE ((RATOR_CONV o RAND_CONV)
                     (PURE_REWRITE_CONV [PRECONDITION_def]))
    in (fname,ml_fname,def,lemma,pre_var) end;
  val thms2 = List.map separate_pre thms
  val all_pre_vars = List.map (fn (fname,ml_fname,def,lemma,pre_var) =>
                            repeat rator pre_var) thms2
(*
val (fname,ml_fname,def,lemma,pre_var) = hd thms2
*)
  val all_pres = List.map (fn (fname,ml_fname,def,lemma,pre_var) => let
    val tm = lemma |> concl |> dest_imp |> fst
    val vs = diff (free_vars tm) all_pre_vars
    val ws = tl (list_dest dest_comb pre_var)
    val ws = ws @ diff vs ws
    in list_mk_forall(ws,mk_imp(tm,pre_var)) end) thms2
    |> list_mk_conj
  val (_,_,pre_def) = Hol_reln [ANTIQUOTE all_pres]
  val clean_pre_def = pre_def |> PURE_REWRITE_RULE [CONTAINER_def]
  val name = clean_pre_def |> SPEC_ALL |> CONJUNCTS |> hd |> SPEC_ALL
               |> concl |> dest_eq |> fst |> repeat rator |> dest_const |> fst
  val _ = delete_binding (name ^ "_rules") handle NotFound => ()
  val _ = delete_binding (name ^ "_ind") handle NotFound => ()
  val _ = delete_binding (name ^ "_strongind") handle NotFound => ()
  val _ = delete_binding (name ^ "_cases") handle NotFound => ()
  val _ = save_thm(name ^ "_def", clean_pre_def)
  val pre_defs = pre_def |> CONJUNCTS |> List.map SPEC_ALL
  val thms3 = zip pre_defs thms2
  fun get_sub (pre,(fname,ml_fname,def,lemma,pre_var)) = let
    val x = pre_var |> repeat rator
    val y = pre |> concl |> dest_eq |> fst |> repeat rator
    in x |-> y end
  val ss = List.map get_sub thms3
  (* val pat = ``PURE (arrowP (****)
  fun list_dest_Eq_Arrow tm =
    if can (match_term pat) tm then
      (tm |> rator |> rand |> rand) :: list_dest_Eq_Arrow (rand tm)
    else [] *)
  val pat = PURE_ArrowP_Eq_tm
  fun list_dest_Eq_Arrow tm =
    if can (match_term pat) tm
    then (rand o rand o rand o rator o rand) tm :: list_dest_Eq_Arrow ((rand o rand) tm)
    else []
(*
val (pre,(fname,ml_fname,def,lemma,pre_var)) = hd thms3
*)
  fun compact_pre (pre,(fname,ml_fname,def,lemma,pre_var)) = let
    val vs = pre |> concl |> dest_eq |> fst |> list_dest dest_comb |> tl
    val ws = lemma |> UNDISCH_ALL |> PURE_REWRITE_RULE[ArrowM_def] |> concl |> rator |> rand |> rator |> list_dest_Eq_Arrow
    val i = List.map (fn (x,y) => x |-> y) (zip vs ws) handle HOL_ERR _ => []
    val c = (RATOR_CONV o RAND_CONV) (REWR_CONV (SYM (INST i pre)))
    val lemma = lemma |> INST ss |> CONV_RULE c
                      |> MATCH_MP IMP_PreImp_LEMMA
    val pre = pre |> PURE_REWRITE_RULE [CONTAINER_def]
    in (fname,ml_fname,def,lemma,SOME pre) end
  val thms4 = List.map compact_pre thms3
  in thms4 end end

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

(*
 * m_translate_main
 *)
fun m_translate_main (* m_translate *) def = (let
    val original_def = def
    (* Instantiate the monadic type if necessary - the state and the exceptions can't be polymorphic *)
    val def = instantiate_monadic_types def
    (* Register the types - TODO *)

    (* Start the translation *)
    val _ = H := (!default_H)
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
val _ = List.map (fn (fname,ml_name,lhs,_,_) => install_rec_pattern lhs fname) info
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
	val (th,v) = if no_params then (th,T) else
                     (List.foldr (fn (v,th) => apply_EvalM_Fun v th true) th
				 (rev (if is_rec then butlast rev_params else rev_params)),
                      List.last rev_params)
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
      val is_fun = code_def |> SPEC_ALL |> concl |> rand |> strip_comb |> fst |> same_const ``ast$Fun``
      val th = PURE_REWRITE_RULE[code_def] th
      val th =
	if is_fun then
	  th
	  |> INST [env_tm |-> cl_env_tm]
          |> PURE_REWRITE_RULE[ArrowM_def, code_def]
	  |> MATCH_MP EvalM_Fun_Var_intro
          |> PURE_REWRITE_RULE[GSYM ArrowM_def]
	  |> SPEC (stringSyntax.fromMLstring ml_fname)
	  |> UNDISCH
	else let val _ = failwith "Monadic translation of constants not supported" in th end
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

      (* apply induction *)
      val thms = List.map (fn (fname,ml_fname,def,th,v) =>
			      (fname, ml_fname, def, PURE_REWRITE_RULE[GSYM ArrowM_def] th, v)) thms
      fun get_goal (fname,ml_fname,def,th,pre) = let
	  val th = REWRITE_RULE [CONTAINER_def] th
	  val hs = hyp th
	  val rev_params = def |> concl |> dest_eq |> fst |> rev_param_list
	  val hyp_tm = list_mk_abs(rev rev_params, th |> UNDISCH_ALL |> concl)
	  val goal = list_mk_forall(rev rev_params, th |> UNDISCH_ALL |> concl)
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
(*
val (th,(fname,ml_fname,def,_,pre)) = hd (zip results thms)
*)
    (* clean up *)
    fun fix (th,(fname,ml_fname,def,_,pre)) = let
      val th = let
        val thi = MATCH_MP IMP_PreImp_THM th
        val thi = CONV_RULE ((RATOR_CONV o RAND_CONV)
                    (ONCE_REWRITE_CONV [force_thm_the pre] THENC
                     SIMP_CONV std_ss [PRECONDITION_def])) thi
        val thi = MP thi TRUTH
        in thi end handle HOL_ERR _ => th
      val th = RW [PreImp_def] th |> UNDISCH_ALL
      val th = remove_Eq th
      val th = SIMP_EqualityType_ASSUMS th
      val th = th |> DISCH_ALL |> REWRITE_RULE ((GSYM AND_IMP_INTRO)::code_defs) |> UNDISCH_ALL
      in (fname,ml_fname,def,th,pre) end
    val results = List.map fix (zip results thms)
    val _ = List.map (delete_const o fst o dest_const o fst o dest_eq o concl) code_defs
  in (true,results) end
  fun check results = let
    val th = LIST_CONJ (List.map #4 results)
    val f = can (find_term (can (match_term (get_term "WF")))) (th |> D |> concl)
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

fun m_translate def =
  let
      val (is_rec,is_fun,results) = m_translate_main (* m_translate *) def
  in
    if is_rec then
    let
      val recc = results |> List.map (fn (fname,_,def,th,pre) => th) |> hd |> hyp
        |> first (can (find_term (fn tm => tm = Recclosure_tm)))
        |> rand |> rator |> rand
      val ii = INST [cl_env_tm |-> get_curr_env()]
      val v_names = List.map (fn x => find_const_name (#1 x ^ "_v")) results
      val _ = if not (!dynamic_init_H) then ml_prog_update (add_Dletrec recc v_names) else ()
      val v_defs = List.take(get_curr_v_defs (), length v_names)
      val jj = INST (if !dynamic_init_H  then [] else [env_tm |-> get_curr_env()])
      (*
      val (fname,ml_fname,def,th,pre) = hd results
      *)
      fun inst_envs (fname,ml_fname,def,th,pre) = let
	  val lemmas = LOOKUP_VAR_def :: List.map GSYM v_defs
	  val th = th |> ii |> jj |> prove_VALID_STORE_assum |> D |> REWRITE_RULE lemmas
		      |> PURE_REWRITE_RULE[ArrowM_def]
		      |> SIMP_RULE std_ss [ISPEC_EvalM_VALID EvalM_Var]
		      |> SIMP_RULE std_ss [lookup_var_def]
		      |> clean_assumptions |> UNDISCH_ALL
		      |> PURE_REWRITE_RULE[GSYM ArrowM_def]
	  val pre_def = (case pre of NONE => TRUTH | SOME pre_def => pre_def)
	  val th =
	      if !dynamic_init_H then let val _ = add_dynamic_spec fname ml_fname th
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
                       |> GENL [state_var, env_tm]
                       |> MATCH_MP LOOKUP_VAR_EvalM_ArrowM_IMP
                       |> D |> clean_assumptions |> UNDISCH_ALL
	val th = if !dynamic_init_H then let
		     val th = lemma |> Q.INST [`cl_env`|->`^(get_curr_env())`] |> DISCH_ALL
		     val _ = add_dynamic_spec fname ml_fname th
		 in th end
		 else let
		     val v = lemma |> concl |> rand |> rator |> rand
		     val exp = lemma |> concl |> rand |> rand
		     val v_name = find_const_name (fname ^ "_v")
		     val _ = ml_prog_update (add_Dlet_Fun n v exp v_name)
		     val v_def = hd (get_curr_v_defs ())
		     val v_thm = lemma |> CONV_RULE (RAND_CONV (REWR_CONV (GSYM v_def)))
		     val pre_def = (case pre of NONE => TRUTH | SOME pre_def => pre_def)
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

fun create_local_defs th = let
    (* Retrieve the lookup assumptions for the functions definitions *)
    val LOCAL_ENV = mk_var("LOCAL_ENV", ``:v sem_env``)
    val NAME = mk_var("NAME", ``:tvarN``)
    val EXPR = mk_var("EXPR", ``:v``)
    val pat = ``nsLookup ^LOCAL_ENV.v (Short ^NAME) = SOME ^EXPR``
    val substs =  mapfilter (match_term pat) (hyp th)
    val lookup_info = List.map (fn (tms, _) => (Term.subst tms NAME, Term.subst tms EXPR)) substs

    (* Remove the variables and the non-monadic functions, retrieve the closure environment *)
    val lookup_info = List.filter(fn (x, y) => not(is_var y)) lookup_info

    fun get_clenv_var expr = let
	val clenv = rator expr |> rator |> rand |> rator |> rand
	val _ = if is_var clenv andalso type_of clenv = ``:v sem_env`` then ()
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
    val current_env = concl th |> rator |> rator |> rator |> rator |> rand |> rator |> rand
    val all_envs = List.map #1 defs_info
    val last_env = List.last all_envs
    val all_envs = current_env::(List.take(all_envs, List.length all_envs - 1))
    val defs_env_info = zip all_envs defs_info

    (* val (env_var2, (env_var1, name, fexp)) = List.hd defs_env_info *)
    fun create_fun_let ((env_var2, (env_var1, name, fexp)), th) =
        if is_Recclosure fexp then let
	    (* Build the new environment *)
	    val env0 = rator fexp |> rator |> rand |> rand
	    val env1 = env_var1
            val funs = rator fexp |> rand
	    val exp = concl th |> rator |> rator |> rator |> rand

	    (* Instantiate the EvalSt theorem, simplify the assumptions *)
	    val EvalSt_th = ISPECL[funs, env0, env1, exp] EvalSt_Letrec_Fun |> SPEC_ALL
	    val assum = concl EvalSt_th |> dest_imp |> fst
	    val assum_th = EVAL assum |> EQT_ELIM
	    val EvalSt_th = MP EvalSt_th assum_th
	    val new_merged_env = concl EvalSt_th |> dest_imp |> fst |> rator |> rator
				       |> rator |> rator |> rand
	    val new_env = new_merged_env |> rator |> rand
	    val th' = Thm.INST [env_var2 |-> new_env] th
	    val th' = MATCH_MP EvalSt_th th'

	    (* Clean up the assumptions *)
	    (* val pat = ``nsLookup ^new_merged_env.v (Short ^NAME) = SOME ^EXPR``
	    val assums =  List.filter (can (match_term pat)) (hyp th')
	    val assums_thms = List.map (EQT_ELIM o EVAL) assums
			      handle HOL_ERR _ =>
				     raise (ERR "create_local_defs"
						"unable to prove the lookup assumptions")
	    val th' = List.foldr (fn (a, th) => MP (DISCH (concl a) th) a) th' assums_thms *)
	in th' end
	else let
	    (* Closure *)
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
	in th' end
    val th = List.foldl create_fun_let th defs_env_info

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
    val [assum] = List.filter (can (fn y => Term.raw_match [] tms ``(A ^x (xv : v)):bool`` y ([], []))) (hyp th)
    val th = DISCH assum th
    val v = rand assum
    val th = GENL[v, x] th
    val th = MATCH_MP Eval_Fun th
in th end

fun m_translate_run def = let
    (* preprocessing: register types *)
    val _ = register_term_types register_type (concl def)

    (* Instantiate the monadic state and exceptions if they are polymorphic *)
    val tys = get_monadic_types_inst (def |> concl |> strip_forall |> snd |> rhs |> rator |> rand)
    val _ = if List.length tys > 0 then print "m_translate_run: instantiated monadic types\n" else ()
    val def = Thm.INST_TYPE tys def

    (* Decompose the definition *)
    val (def_lhs, def_rhs) = concl def |> strip_forall |> snd |> dest_eq

    val fname = repeat rator def_lhs |> dest_const |> fst |> get_unique_name
    val _ = print ("Translating monadic run: " ^ fname ^ "\n")
    val fname_str = stringLib.fromMLstring fname

    val Mvar = mk_var("M", ``: 'a -> ('b, 'c) exc # 'a``)
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

    (* Add the state parameter Eval assumption *)
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
    val EXN_rw = prove(``EXC_TYPE_aux = ^EXC_TYPE_tm``, EXC_RI_prove_tac)

    val th = List.foldl (fn (a, th) => MP th a) th [distinct_th, vname_th1, vname_th2]
    val th = PURE_REWRITE_RULE[EXN_rw] th
    val th = MP th monad_th

    (* Undischarge the lookup assumptions *)
    val every_lookup_assum = concl th |> dest_imp |> fst
    val every_lookup_rw = SIMP_CONV list_ss [] every_lookup_assum
    val th = SIMP_RULE bool_ss [every_lookup_rw, GSYM AND_IMP_INTRO] th |> UNDISCH_ALL

    (* Replace the environment *)
    val th = instantiate_local_environment th

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
    val nsLookup_assums_rws = List.map (fn x => EVAL x |> EQT_ELIM handle HOL_ERR _ => raise (ERR "m_translate_run" (Eval_error_msg x))) nsLookup_assums

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
    val _ = print ("Saved theorem ____ :" ^fname ^ "_v_thm\n")
in th end

(*
   Code for loading and storing the monadic translator state,
   as the things in ml_translatorLib does not include the
   bits and pieces specific to the monadic translator (i.e.
   exceptions, refs, et cetera.

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

   - dynamic_specs
   - dynamic_init_env

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
