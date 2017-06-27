structure ml_monad_translatorLib = struct

open preamble
open astTheory libTheory semanticPrimitivesTheory bigStepTheory
     ml_translatorTheory ml_translatorLib ml_progTheory ml_progLib
     ml_pmatchTheory holKernelTheory ml_monadBaseTheory ml_monad_translatorTheory ml_translatorTheory
open terminationTheory
open ml_monadStoreLib

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;

val _ = (print_asts := true);

val _ = (use_full_type_names := false);

val polymorph_monad_type = ``:'a -> ('b, 'c) exc # 'a``;
fun dest_monad_type ty =
  let val s = (match_type polymorph_monad_type ty) in
      (type_subst s ``:'a``, type_subst s ``:'b``, type_subst s ``:'c``) end;

(* Should be moved somewhere else *)
fun list_dest f tm =
  let val (x,y) = f tm in list_dest f x @ list_dest f y end
  handle HOL_ERR _ => [tm];
val dest_fun_type = dom_rng
fun domain ty = ty |> dest_fun_type |> fst

fun dest_args tm =
  let val (x,y) = dest_comb tm in dest_args x @ [y] end
  handle HOL_ERR _ => []

fun D th = let
  val th = th |> DISCH_ALL |> PURE_REWRITE_RULE [AND_IMP_INTRO]
  in if is_imp (concl th) then th else DISCH T th end

val env_tm = mk_var("env",semanticPrimitivesSyntax.mk_environment semanticPrimitivesSyntax.v_ty)

(* The store predicate *) 
val H = ref ``\refs. emp``;

(* The type of the references object *)
val refs_type = ref ``:unit``;

(* The exception refinement invariant and type *)
val EXN_TYPE = ref ``UNIT_TYPE``;
val exn_type = ref ``:unit``;

(* Some functions to generate monad types *)
fun M_type ty = ``:^(!refs_type) -> (^ty, ^(!exn_type)) exc # ^(!refs_type)``;
val aM = ref (ty_antiq (M_type ``:'a``));
val bM = ref (ty_antiq (M_type ``:'b``));

(* The theorem stating that there exists a store stasfying the store predicate *)
val VALID_STORE_THM = ref (prove(``T``, fs[]));

(* Additional theories where to look for refinement invariants *)
val type_theories = ref ([current_theory(), "ml_translator"] : string list);

(* Theorems proved by the user to handle exceptions *)
val exn_handles = ref ([] : (term * thm) list);
val exn_raises = ref ([] : (term * thm) list);

(* The information about the access functions *)
val read_refs = ref ([] : (term * term * thm) list);
val write_refs = ref ([] : (term * term * thm) list);

fun ISPEC_EvalM th = ISPEC (!H) th handle HOL_ERR _ =>  SPEC (!H) th;
fun ISPEC_EvalM_EXN_TYPE th = ISPEC (!EXN_TYPE) th handle HOL_ERR _ =>  SPEC (!EXN_TYPE) th;
fun ISPEC_EvalM_MONAD th = ISPEC_EvalM th |> ISPEC_EvalM_EXN_TYPE;

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

fun mk_PURE_tm ty = let
  val PURE_tm = mk_const("PURE", ``:(^ty -> v -> bool) -> (^ty, ^(!refs_type)) H``)
  in mk_comb (PURE_tm, get_type_inv ty) end;

fun get_arrow_type_inv ty =
  if can dest_monad_type ty then get_m_type_inv ty else let
    val (ty1,ty2) = dest_fun_type ty
    val i1 = get_arrow_type_inv ty1 handle HOL_ERR _ =>
             mk_PURE_tm ty1
    val i2 = get_arrow_type_inv ty2
  in ``ArrowM ^(!H) ^i1 ^i2`` end;

fun smart_get_type_inv ty =
  if not (can dest_monad_type ty) andalso
     can get_arrow_type_inv ty then let
    val inv = get_arrow_type_inv ty
    in ONCE_REWRITE_CONV [ArrowM_def] inv |> concl |> rand |> rand end
  else get_type_inv ty;

(* Retrieves the parameters given to Eval or EvalM *)
val Eval_tm = ``Eval``;
val EvalM_tm = ``EvalM``;
fun get_Eval_arg e = if same_const (strip_comb e |> fst) Eval_tm then e |> rand |> rand
		     else e |> rator |> rand |> rand;
fun get_Eval_env e = if same_const (strip_comb e |> fst) Eval_tm then e |> rator |> rator |> rand
		     else e |> rator |> rator |> rator |> rand;
fun get_Eval_exp e = if same_const (strip_comb e |> fst) Eval_tm then e |> rator |> rand
		     else e |> rator |> rator |> rand;
fun remove_Eval_storePred e = if same_const (strip_comb e |> fst) Eval_tm then e
		     else e |> rator;
(* ---- *)

(* support for datatypes... *)

(*
  val _ = set_goal([],goal)
*)	      
fun derive_case_of ty = let
  fun smart_full_name_of_type ty =
    if let val r = dest_thy_type ty in #Tyop r = "cpn" andalso #Thy r = "toto" end then "order"
    else full_name_of_type ty
  fun get_name ty = clean_uppercase (smart_full_name_of_type ty) ^ "_TYPE"
  val name = get_name ty
  val inv_def = tryfind (fn thy_name => fetch thy_name (name ^ "_def"))
                        (!type_theories)
  val case_th = get_nchotomy_of ty
  val pat = ``Eval env exp (P (res:'a))``
  fun Eval_to_EvalM tm = let
    val (m,i) = match_term pat tm
    val res = mk_var("res", M_type ``:'a``)
    val tm1 = subst m (inst i ``EvalM env exp (MONAD P ^(!EXN_TYPE) ^res) ^(!H)``)
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
  val pure_tm = case_of ty |> concl
  val (x1,x2) = dest_imp pure_tm
  val (x2,x3) = dest_imp x2
  val (x3,x4) = dest_imp x3
  val hyps = list_dest dest_conj x3
  fun map_tl f [] = []
    | map_tl f (x::xs) = x :: List.map f xs
  val z3 = map_tl Eval_to_EvalM hyps |> list_mk_conj
  val z4 = Eval_to_EvalM x4
  val goal = mk_imp(x1,mk_imp(x2,mk_imp(z3,z4)))
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
        \\ REPEAT STRIP_TAC \\ STRIP_ASSUME_TAC (Q.SPEC `x` case_th)
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
  in case_lemma end;

fun type_mem f = let
  val memory = ref []
  fun lookup x [] = fail()
    | lookup x ((y,z)::ys) = if can (match_type y) x then z else lookup x ys
  in (fn ty => lookup ty (!memory) handle HOL_ERR _ => let
              val th = f ty
              val _ = (memory := (ty,th)::(!memory))
              in th end, memory) end;

val (mem_derive_case_of, mem_derive_case_ref) = type_mem derive_case_of;

(* Initialize the translation by giving the appropriate values to the above references *)
fun init_translation (store_trans_res : store_translation_result) exn_thms add_type_theories =
  let
      val {init_values_thms = init_values_thms,
	   locations_thms  = locations_thms,
	   store_pred_def = store_pred_def,
	   store_pred_validity = store_pred_validity,
	   store_pred_exists_thm = store_pred_exists_thm,
	   get_specs = get_specs,
	   set_specs = set_specs} = store_trans_res
      val _ = H := (concl store_pred_def |> dest_eq |> fst)
      val _ = refs_type := (type_of (!H) |> dest_type |> snd |> List.hd)
      val _ = EXN_TYPE := (List.hd get_specs |> concl |> dest_imp |> snd |> rator |> rand |> rator |> rand)
      val _ = exn_type := (type_of (!EXN_TYPE) |> dest_type |> snd |> List.hd)
      val _ = aM := (ty_antiq (M_type ``:'a``))
      val _ = bM := (ty_antiq (M_type ``:'b``))
      val _ = VALID_STORE_THM := store_pred_exists_thm
      val _ = type_theories := (current_theory()::(add_type_theories@["ml_translator"]))

      (* Exceptions *)
      fun is_exc_raise_thm th =
          (List.length (concl th |> strip_forall |> snd |> strip_imp |> fst) = 2)
      val (raise_thms, handle_thms) = List.partition is_exc_raise_thm exn_thms
      fun extract_pattern th = let
	  val pat = concl th |> strip_forall |> snd |> strip_imp |> snd |> rator |> rand |> rand
      in (pat, th) end
      val _ = exn_raises := (List.map extract_pattern raise_thms)
      val _ = exn_handles := (List.map extract_pattern handle_thms)

      (* Access functions *)
      fun get_read_info (location_thm, get_spec) = let
	  val get_fun = concl get_spec |> rand |> rator |> rand |> rand
	  val loc = concl location_thm |> dest_eq |> fst
      in (get_fun, loc, get_spec) end
      val get_funs_info = zip locations_thms get_specs
      val _ = read_refs := (List.map get_read_info get_funs_info)

      fun get_write_info (location_thm, set_spec) = let
	  val set_fun = concl set_spec |> rand |> rand |> rator |> rand |> rand
	  val loc = concl location_thm |> dest_eq |> fst
      in (set_fun, loc, set_spec) end
      val set_funs_info = zip locations_thms set_specs
      val _ = write_refs := (List.map get_write_info set_funs_info)

      (* Data types *)
      val _ = mem_derive_case_ref := []
  in () end;

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
val tm = rhs
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
  in th end handle Empty => failwith "empty";

(* PMATCH *)

val IMP_EQ_T = Q.prove(`a ==> (a <=> T)`,fs [])

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
  val vs = filter (fn tm => not (mem (rand (rand tm)) ws)) vs |> mk_set
  val new_goal = goal |> subst [``e:exp``|->exp,p2 |-> p]
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
  fun trans [] = nil_lemma
    | trans ((pat,rhs_tm)::xs) = let
    val th = trans xs
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

fun apply_EvalM_Fun v th fix = let
  val th1 = inst_EvalM_env v th
  val th2 = if fix then MATCH_MP (ISPEC_EvalM EvalM_Fun_Eq) (GEN ``v:v`` th1)
                   else MATCH_MP (ISPEC_EvalM EvalM_Fun) (GEN ``v:v`` (FORCE_GEN v th1))
  in th2 end;

fun apply_EvalM_Recclosure fname v th = let
  val vname = fst (dest_var v)
  val vname_str = stringLib.fromMLstring vname
  val fname_str = stringLib.fromMLstring fname
  val body = th |> UNDISCH_ALL |> concl |> rator |> rator |> rand (* |> concl |> rator |> rand *)
  val inv = smart_get_type_inv (type_of v)
  val new_env = ``write ^vname_str v (write_rec
                    [(^fname_str,^vname_str,^body)] env env)``
  val old_env = env_tm
  val tys = Type.match_type (type_of v) (type_of inv |> dest_type |> snd |> List.hd)
  val v = Term.inst tys v
  val assum = subst [old_env|->new_env]
              ``Eval env (Var (Short ^vname_str)) (^inv ^v)``
  val thx = th |> UNDISCH_ALL |> REWRITE_RULE [GSYM SafeVar_def]
               |> DISCH_ALL |> DISCH assum |> SIMP_RULE bool_ss []
               |> INST [old_env|->new_env]
               |> SIMP_RULE bool_ss [Eval_Var_SIMP]
               |> ONCE_REWRITE_RULE [EvalM_Var_SIMP]
               |> ONCE_REWRITE_RULE [EvalM_Var_SIMP]
               |> REWRITE_RULE [lookup_cons_write,lookup_var_write,write_rec_one]
               |> CONV_RULE (DEPTH_CONV stringLib.string_EQ_CONV)
               |> REWRITE_RULE [GSYM write_rec_one]
               |> SIMP_RULE bool_ss [SafeVar_def]
  val new_assum = fst (dest_imp (concl thx))
  val th1 = thx |> UNDISCH_ALL
                |> CONV_RULE ((RATOR_CONV o RAND_CONV o RAND_CONV) (UNBETA_CONV v)) (* RATOR_CONV *)
                |> DISCH new_assum
  val th2 = MATCH_MP (ISPEC_EvalM EvalM_Recclosure) (Q.INST [`env`|->`cl_env`] (GEN ``v:v`` th1))
  val assum = ASSUME (fst (dest_imp (concl th2)))
  val th3 = D th2 |> REWRITE_RULE [assum]
  val lemma = MATCH_MP Eval_Eq_Recclosure assum
  val lemma_lhs = lemma |> concl |> dest_eq |> fst
  fun replace_conv tm = let
    val (i,t) = match_term lemma_lhs tm
    in INST i (INST_TYPE t lemma) end handle HOL_ERR _ => NO_CONV tm
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

(* DEBUG
fun print_tm_msg msg tm =
  print (msg  ^(term_to_string tm) ^ "\n\n");

exception BREAKPOINT of term;
DEBUG *)

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
    val x = tm |> rator |> rand
    val (v,y) = tm |> rand |> dest_abs
    val th1 = m2deep x
    val th2 = m2deep y
    val th3 = inst_EvalM_env v th2 |> Q.GEN`v` |> FORCE_GEN v
    val lemma = ISPEC_EvalM EvalM_th |> SPEC_ALL |> UNDISCH
    val th4 = MATCH_MP lemma th1
    val result = MATCH_MP th4 th3 handle HOL_ERR _ => HO_MATCH_MP th4 th3
    in check_inv "handle custom pattern" tm result end
  (* return *)
  else if can (match_term ``(st_ex_return x): ^(!aM)``) tm then let
    (* val _ = print_tm_msg "return\n" tm DEBUG *)
    val th = hol2deep (rand tm)
    val result = MATCH_MP (ISPEC_EvalM_MONAD EvalM_return) th
    in check_inv "return" tm result end
  (* bind *)
  else if can (match_term ``(st_ex_bind (x:^(!bM)) f): ^(!aM)``) tm then let
    (* val _ = print_tm_msg "bind\n" tm DEBUG *)
    val x1 = tm |> rator |> rand
    val (v,x2) = tm |> rand |> dest_abs
    val th1 = m2deep x1
    val th2 = m2deep x2
    val th2 = inst_EvalM_env v th2
    val vs = th2 |> concl |> dest_imp |> fst
    val th2 = th2 |> GEN (rand vs) |> FORCE_GEN (rand (rator vs))
    val result = MATCH_MP (ISPEC_EvalM_MONAD EvalM_bind) (CONJ th1 th2)
    in check_inv "bind" tm result end else
  (* otherwise *)
  if can (match_term ``(x: ^(!aM)) otherwise (y: ^(!aM))``) tm then let
    (* val _ = print_tm_msg "otherwise\n" tm DEBUG *)
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
                  |> UNDISCH_ALL |> Q.GEN `i`
    val lemma = Q.SPEC `"v"` (ISPEC_EvalM_MONAD EvalM_otherwise)
    val result = MATCH_MP (MATCH_MP lemma th1) th2
    in check_inv "otherwise" tm result end else
  (* try *)
  if can (match_term ``try (f:'a-> ^(!bM)) x msg``) tm then let
    (* val _ = print_tm_msg "try\n" tm DEBUG *)
    val lemma = tm |> SIMP_CONV (srw_ss()) [try_def]
    val th = m2deep (lemma |> concl |> rand)
    val result = th |> RW [GSYM lemma]
    in check_inv "try" tm result end else
  (* IGNORE_BIND *)
  if can (match_term ``IGNORE_BIND (f:'a -> 'b # 'a) (g:'a -> 'c # 'a)``) tm then let
    (* val _ = print_tm_msg "IGNORE_BIND\n" tm DEBUG *)
    val lemma = tm |> SIMP_CONV std_ss [state_transformerTheory.IGNORE_BIND_DEF]
    val th = m2deep (lemma |> concl |> rand)
    val result = th |> RW [GSYM lemma]
    in check_inv "IGNORE_BIND" tm result end else
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
  ((* print_tm_msg "data-type pattern-matching\n" tm; *) inst_case_thm tm m2deep) handle HOL_ERR _ =>
  (* previously translated term *) 
  if can lookup_v_thm tm then let
    (* val _ = print_tm_msg "previously translated\n" tm DEBUG *)
    val th = lookup_v_thm tm
    val inv = smart_get_type_inv (type_of tm)
    val target = mk_comb(inv,tm)
    val (ss,ii) = match_term (th |> concl |> rand) target
    val result = INST ss (INST_TYPE ii th)
                 |> MATCH_MP (ISPEC_EvalM Eval_IMP_PURE)
                 |> REWRITE_RULE [GSYM ArrowM_def]
    in check_inv "lookup_v_thm" tm result end else
  (* if *)
  if can (match_term ``if b then x: ^(!aM) else y: ^(!aM)``) tm then let
    (* val _ = print_tm_msg "if\n" tm DEBUG *)
    val (t,x1,x2) = dest_cond tm
    val th0 = hol2deep t
    val th1 = m2deep x1
    val th2 = m2deep x2
    val th = MATCH_MP (ISPEC_EvalM EvalM_If) (LIST_CONJ [D th0, D th1, D th2])
    val result = UNDISCH th
    in check_inv "if" tm result end else
  (* ref: get_the_(...) *)
  if can (first (fn (t,_,_) => same_const t tm)) (!read_refs) then let
    (* val _ = print_tm_msg "ref get_the(...)\n" tm DEBUG *)
    val (_,t,result) = first (fn (t,_,_) => same_const t tm) (!read_refs)
    val result = result |> UNDISCH_ALL
    in check_inv "get" tm result end else
  (* ref: set_the_(...) *)
  if can (first (fn (t,_,_) => can (match_term t) tm)) (!write_refs) then let
    (* val _ = print_tm_msg "ref: set_the(...)\n" tm DEBUG *)
    val (_,t,result) = (first (fn (t,_,_) => can (match_term t) tm)) (!write_refs)
    val th = result |> UNDISCH
    val result = MATCH_MP th (hol2deep (tm |> rand))
    in check_inv "set" tm result end else
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
      (* TODO: move that *)
      val PURE_tm = Term.inst [``:'a`` |-> inv_type, ``:'b`` |-> !refs_type] ``PURE : ('a -> v -> bool) -> ('a, 'b) H``
      in ``^PURE_tm (Eq ^inv ^tm)`` end
    fun mk_m_arrow x y = ``ArrowM ^(!H) ^x ^y``
    fun mk_inv [] res = res
      | mk_inv (x::xs) res = mk_inv xs (mk_m_arrow (mk_fix x) res)
    val inv = mk_inv xs (get_m_type_inv (type_of tm))
    val ss = fst (match_term lhs tm)
    val pre = T
    val tys = match_type (type_of f) (type_of inv |> dest_type |> snd |> List.hd)
    val f' = Term.inst tys f
    val h = ASSUME ``PreImp ^pre (EvalM env (Var (Short ^str)) (^inv ^f') ^(!H))``
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
    val result = hol2deep x |> MATCH_MP (ISPEC_EvalM Eval_IMP_PURE)
                            |> MATCH_MP (MATCH_MP (ISPEC_EvalM EvalM_ArrowM) thf)
                 handle e =>
                 m2deep x |> MATCH_MP (MATCH_MP (ISPEC_EvalM EvalM_ArrowM) thf)
    in check_inv "comb" tm result end else
  failwith ("cannot translate: " ^ term_to_string tm);

fun get_curr_prog_state () = let
  val k = ref init_state
  val _ = ml_prog_update (fn s => (k := s; s))
  in !k end

fun EvalM_P_CONV CONV tm =
  if is_imp tm then (RAND_CONV o RATOR_CONV o RAND_CONV) CONV tm
  else (RATOR_CONV o RAND_CONV) CONV tm;
				 
fun m_translate def = let
  val original_def = def
  fun the (SOME x) = x | the _ = failwith("the of NONE")
  (* perform preprocessing -- reformulate def *)
  val (is_rec,defs,ind) = preprocess_def def
  val _ = length defs = 1 orelse failwith "no support for mutual recursion"
  val def = hd defs
  val (lhs,rhs) = dest_eq (concl def)
  val fname = repeat rator lhs |> dest_const |> fst |> get_unique_name
  val _ = print ("Translating monadic " ^ fname ^ "\n")
  val fname_str = stringLib.fromMLstring fname
  (* read off information *)
  fun rev_param_list tm = rand tm :: rev_param_list (rator tm) handle HOL_ERR _ => []
  val rev_params = def |> concl |> dest_eq |> fst |> rev_param_list
  val no_params = (length rev_params = 0)
  (* derive deep embedding *)
  val rhs = if can dest_monad_type (type_of rhs) then inst_monad_type rhs else rhs
  val _ = install_rec_pattern lhs fname fname
  val th = m2deep rhs
  val _ = uninstall_rec_patterns ()
  (* replace rhs with lhs in th *)
  val th = CONV_RULE (EvalM_P_CONV
             (REWRITE_CONV [CONTAINER_def] THENC ONCE_REWRITE_CONV [GSYM def])) th
  (* abstract parameters *)
  val th = clean_assumptions (D th)
  val (th,v) = if no_params then (th,T) else
                 (List.foldr (fn (v,th) => apply_EvalM_Fun v th true) th
                    (rev (if is_rec then butlast rev_params else rev_params)),
                  last rev_params)
  val th = if not is_rec then D (clean_assumptions th)
           else apply_EvalM_Recclosure fname v th |> clean_assumptions
  val th = CONV_RULE (QCONV (DEPTH_CONV ETA_CONV)) th
  val th = if is_rec then Q.INST [`shaddow_env`|->`cl_env`] th
                     else Q.INST [`shaddow_env`|->`env`] th
  val th = th |> REWRITE_RULE [lookup_cons_write]
  (* collect precondition *)
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV)
                      (SIMP_CONV std_ss [EVAL ``CONTAINER TRUE``,
                                         EVAL ``CONTAINER FALSE``])) th
  val th = clean_assumptions th
  val (th,pre) = if no_params then (th,NONE) else
                  (th |> REWRITE_RULE [PreImp_def,PRECONDITION_def],NONE)
  (* apply induction *)
  val th = if not is_rec then th else let
    val th = REWRITE_RULE [CONTAINER_def] th
    val hs = hyp th
    val hyp_tm = list_mk_abs(rev rev_params, th |> UNDISCH_ALL |> concl)
    val goal = list_mk_forall(rev rev_params, th |> UNDISCH_ALL |> concl)
    val goal = mk_imp(list_mk_conj hs,goal)
    val ind_thm = (the ind)
    val ind_thm = rename_bound_vars_rule "i" ind_thm
                  |> SIMP_RULE std_ss []
(*
    set_goal([],goal)
*)
    val lemma = prove(goal,
      STRIP_TAC
      \\ SIMP_TAC std_ss [FORALL_PROD]
      \\ MATCH_MP_TAC (SPEC hyp_tm ind_thm |> CONV_RULE (DEPTH_CONV BETA_CONV))
      \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC th
      \\ FULL_SIMP_TAC (srw_ss()) [ADD1,write_rec_one]
      \\ REPEAT STRIP_TAC
      \\ MATCH_MP_TAC IND_HELP
      \\ Q.EXISTS_TAC `env`
      \\ ASM_SIMP_TAC std_ss []
      \\ FULL_SIMP_TAC (srw_ss()) [ADD1]
      \\ FULL_SIMP_TAC std_ss [UNCURRY_SIMP]
      \\ METIS_TAC [])
    val th = UNDISCH lemma |> SPECL (rev rev_params)
    val th = RW [PreImp_def] th |> UNDISCH_ALL
    in th end
  (* remove Eq *)
  val th = RW [ArrowM_def] th
  fun update_params_type th params = let
      val fvs = free_vars (concl th)
      val tmap = List.foldl (fn(x, m) => Redblackmap.insert(m, dest_var x |> fst, x))
                (Redblackmap.mkDict String.compare) fvs
      val params = List.map (fn x => Redblackmap.find (tmap, dest_var x |> fst)) params
  in params end
  val rev_params = update_params_type th rev_params
  fun f (v,th) =
    HO_MATCH_MP (ISPEC_EvalM EvalM_FUN_FORALL) (GEN v th) |> SIMP_RULE std_ss [M_FUN_QUANT_SIMP]
  val th = List.foldr f th rev_params handle HOL_ERR _ => th
  val th = RW [GSYM ArrowM_def] th
  (* simpliy EqualityType *)
  val th = SIMP_EqualityType_ASSUMS th
  (* abbreviate code *)
  val th = th |> DISCH_ALL |> REWRITE_RULE [GSYM AND_IMP_INTRO] |> UNDISCH_ALL
  val th = RW [ArrowM_def] th
  val th = if is_rec then let
      val recc = (first (can (find_term
                    (fn tm => tm = rator ``Recclosure ^env_tm``)))
                        (hyp th)) |> rand |> rator |> rand
      val v_names = List.map (fn x => find_const_name (x ^ "_v"))
                      (recc |> listSyntax.dest_list |> fst
                            |> List.map (stringSyntax.fromHOLstring o rand o rator))
      val _ = ml_prog_update (add_Dletrec recc v_names)
      val s = get_curr_prog_state ()
      val v_def = hd (get_v_defs s)
      val cl_env = v_def |> concl |> rand |> rator |> rator |> rand
      val th = th |> Q.INST [`cl_env`|->`^cl_env`]
                  |> DISCH_ALL |> REWRITE_RULE [GSYM v_def]
                  |> clean_assumptions |> DISCH_ALL
                  |> REWRITE_RULE [GSYM AND_IMP_INTRO] |> UNDISCH_ALL
      val th = th |> DISCH (first (can (match_term ``LOOKUP_VAR _ _ _``)) (hyp th))
      val th = MATCH_MP (MP (ISPEC_EvalM LOOKUP_VAR_EvalM_IMP) (!VALID_STORE_THM)) (Q.GEN `env` th)
      in th end
    else let
      val th = th |> Q.INST [`env`|->`^(get_env (get_curr_prog_state ()))`]
                  |> D |> clean_assumptions |> UNDISCH_ALL
      val th = th |> MATCH_MP (MP (ISPEC_EvalM EvalM_Fun_PURE_IMP) (!VALID_STORE_THM))
      val v = th |> concl |> rand |> rator |> rand
      val e = th |> concl |> rand |> rand
      val v_name = find_const_name (fname ^ "_v")
      val _ = ml_prog_update (add_Dlet_Fun fname_str v e v_name)
      val s = get_curr_prog_state ()
      val v_def = hd (get_v_defs s)
      val th = th |> REWRITE_RULE [GSYM v_def]
      in th end
  val th = RW [GSYM ArrowM_def] th
  (* store certificate for later use *)
  val pre = (case pre of NONE => TRUTH | SOME pre_def => pre_def)
  val _ = add_v_thms (fname,fname,th,pre)
  val th = save_thm(fname ^ "_v_thm",th)
  in th end
    handle UnableToTranslate tm => let
    val _ = print "\n\nml_translate: cannot translate term:  "
    val _ = print_term tm
    val _ = print "\n\nwhich has type:\n\n"
    val _ = print_type (type_of tm)
    val _ = print "\n\n"
    in raise UnableToTranslate tm end
    | HOL_ERR err => let
    val _ = print "\n\nml_translate: unexpected error when translating term:\n\n"
    val _ = print_thm def
    val _ = print "\n\n"
    in raise (HOL_ERR err) end;

end
