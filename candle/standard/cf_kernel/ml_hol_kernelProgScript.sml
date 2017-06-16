open preamble
open astTheory libTheory semanticPrimitivesTheory bigStepTheory
     ml_translatorTheory ml_translatorLib ml_progTheory ml_progLib
     ml_pmatchTheory holKernelTheory ml_monadProgTheory
open terminationTheory
local open holKernelPmatchTheory in end

val _ = new_theory "ml_hol_kernelProg";

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;

val _ = (print_asts := true);

val _ = translation_extends "ml_monadProg";

val _ = (use_full_type_names := false);

fun dest_monad_type ty =
  let val s = (match_type ``:('a, 'b) M`` ty) in
      (type_subst s ``:'a``, type_subst s ``:'b``) end;

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

(* H and refs_type are constants here - TODO: move them *)
val H = ``HOL_STORE``;
val refs_type = type_of H |> dest_type |> snd |> List.hd;
fun M_type ty = mk_type ("fun", [refs_type, mk_type("prod", [mk_type("hol_result", [ty]), refs_type])])
val aM = ty_antiq (M_type ``:'a``);
val bM = ty_antiq (M_type ``:'b``);

val VALID_STORE_THM = HOL_STORE_EXISTS;
(* ---- *)

(* ---- *)
(* TODO: move HOL_MONAD_tm *)
val HOL_MONAD_POLY_tm = ``HOL_MONAD : ('a -> v -> bool) -> (('a, 'b) M, 'b) H``;
val HOL_MONAD_tm = Term.inst [``:'b`` |-> refs_type] HOL_MONAD_POLY_tm;
fun get_m_type_inv ty =
  let
      val monad_type = dest_monad_type ty |> fst
      val HOL_MONAD_tm' = Term.inst [``:'a`` |-> monad_type] HOL_MONAD_tm
  in
      ``^HOL_MONAD_tm' ^(get_type_inv monad_type)``
  end
  handle HOL_ERR _ => failwith "unknown type";

val PURE_tm = ``PURE : ('a -> v -> bool) -> ('a, 'b) H``;
fun mk_PURE_tm ty = let
  val PURE_tm' = Term.inst [``:'a`` |-> ty, ``:'b`` |-> refs_type] PURE_tm
  in mk_comb (PURE_tm', get_type_inv ty) end;

fun get_arrow_type_inv ty =
  if can dest_monad_type ty then get_m_type_inv ty else let
    val (ty1,ty2) = dest_fun_type ty
    val i1 = get_arrow_type_inv ty1 handle HOL_ERR _ =>
             mk_PURE_tm ty1
             (* ``PURE ^(get_type_inv ty1)`` *)
    val i2 = get_arrow_type_inv ty2
    in ``ArrowM ^H ^i1 ^i2`` end

fun smart_get_type_inv ty =
  if not (can dest_monad_type ty) andalso
     can get_arrow_type_inv ty then let
    val inv = get_arrow_type_inv ty
    in ONCE_REWRITE_CONV [ArrowM_def] inv |> concl |> rand |> rand end
  else get_type_inv ty

(* Retrieves the parameters given to Eval or EvalM *)
val Eval_tm = ``Eval``;
val EvalM_tm = ``EvalM``;
fun get_Eval_arg e = if same_const (strip_comb e |> fst) Eval_tm then e |> rand |> rand
		     else e |> rator |> rand |> rand;
fun get_Eval_env e = if same_const (strip_comb e |> fst) Eval_tm then e |> rator |> rator |> rand
		     else e |> rator |> rator |> rator |> rand;

(* ---- *)

(* support for datatypes... *)

(* where are :hol_type, :hol_term and :def? *)
(*
val ty = ``:'b # 'c``; val th = derive_case_of ty;
val ty = ``:'a list``; val th = derive_case_of ty;
val ty = ``:type``; val th = derive_case_of ty;
val ty = ``:term``; val th = derive_case_of ty;
val ty = ``:thm``; val th = derive_case_of ty;
val ty = ``:update``; val th = derive_case_of ty;
*)

(******************************************************************************************
 *
 * Pattern matching
 *
 ******************************************************************************************)

(*
  val _ = set_goal([],goal)
*)	      
fun derive_case_of ty = let
  fun smart_full_name_of_type ty =
    if let val r = dest_thy_type ty in #Tyop r = "cpn" andalso #Thy r = "toto" end then "order"
    else full_name_of_type ty
  fun get_name ty = clean_uppercase (smart_full_name_of_type ty) ^ "_TYPE"
  val name = get_name ty
  val inv_def = fetch "ml_monadProg" (name ^ "_def") handle HOL_ERR _ =>
                fetch "ml_translator" (name ^ "_def")
  val case_th = get_nchotomy_of ty
(*
  val tm = ``Eval (write n1_2 v1_2 (write n1_1 v1_1 env)) exp1
      (return_type (f1 x1_1 x1_2))``
*)
  val pat = ``Eval env exp (P (res:'a))``
  (* TODO: Add support for H, add type of refs in `'a M` *)
  fun Eval_to_EvalM tm = let
    val (m,i) = match_term pat tm
    val monad_type1 = type_subst [``:'b`` |-> refs_type] ``:('a, 'b) M``
    val res = mk_var("res", monad_type1)
    val tm1 = subst m (inst i ``EvalM env exp (HOL_MONAD P ^res) ^H``)
    val ty1 = tm |> rand |> rand |> type_of
    val monad_type2 = type_subst [``:'a`` |-> ty1] monad_type1
    val y1 = tm |> rand |> rand |> inst [ty1|->monad_type2]
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
    | map_tl f (x::xs) = x :: map f xs
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
  in fn ty => lookup ty (!memory) handle HOL_ERR _ => let
              val th = f ty
              val _ = (memory := (ty,th)::(!memory))
              in th end end

val mem_derive_case_of = type_mem derive_case_of;

val ty = ``:'b # 'c``; val _ = mem_derive_case_of ty;
val ty = ``:'a list``; val _ = mem_derive_case_of ty;
val ty = ``:'a option``; val _ = mem_derive_case_of ty;
val ty = ``:type``; val _ = mem_derive_case_of ty;
val ty = ``:term``; val _ = mem_derive_case_of ty;
val ty = ``:thm``; val _ = mem_derive_case_of ty;
val ty = ``:update``; val _ = mem_derive_case_of ty;

(*
val tm = ``case l of [] => ex_return F | x::l' => ex_return T``;
inst_case_thm_for tm;
*)

fun inst_case_thm_for tm = let
  val (_,_,names) = TypeBase.dest_case tm
  val names = map fst names
  val th = mem_derive_case_of ((repeat rator tm) |> type_of |> domain) |> UNDISCH
  val pat = th |> UNDISCH_ALL |> concl |> rator |> rand |> rand
  val (ss,i) = match_term pat tm
  val th = INST ss (INST_TYPE i th)
  val ii = map (fn {redex = x, residue = y} => (x,y)) i
  val ss = map (fn (x,y) => (inst i (smart_get_type_inv x) |-> smart_get_type_inv y)) ii
  val th = INST ss th
  val th = CONV_RULE (DEPTH_CONV BETA_CONV) th
  fun args tm = let val (x,y) = dest_comb tm in args x @ [y] end
                handle HOL_ERR _ => []
  val ns = map (fn n => (n,args n)) names
  fun rename_var prefix ty v =
    mk_var(prefix ^ implode (tl (explode (fst (dest_var v)))),ty)
  (* I think it is ml_translator$CONTAINER and not address$CONTAINER *)
  val ts = find_terms (can (match_term ``ml_translator$CONTAINER (b:bool)``)) (concl th)
           |> map (rand o rand)
           |> map (fn tm => (tm,map (fn x => (x,rename_var "n" ``:string`` x,
                                                rename_var "v" ``:v`` x))
                    (dest_args tm handle HOL_ERR _ => [])))
  val ns = map (fn (tm,xs) => let
      val aa = snd (first (fn (pat,_) => can (match_term tm) pat) ns)
      in zip aa xs end) ts |> flatten
  val ms = map (fn (b,(x,n,v)) => n |-> stringSyntax.fromMLstring (fst (dest_var b))) ns
  val th = INST ms th
  val ks = map (fn (b,(x,n,v)) => (fst (dest_var x), fst (dest_var b))) ns @
           map (fn (b,(x,n,v)) => (fst (dest_var v), fst (dest_var b) ^ "{value}")) ns
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
val original_tm = tm
val tm = (!last_fail)
sat_hyp tm
val tm = z
*)
fun inst_case_thm tm m2deep = let
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
    val z = get_Eval_arg y (* y |> rand |> rand *)
    val lemma = if can dest_monad_type (type_of z)
                then m2deep z
                else hol2deep z
    val lemma = D lemma
    val new_env = get_Eval_env y (* y |> rator |> rator |> rand *)
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
    in lemma end handle HOL_ERR _ => (print_term tm; last_fail := tm; fail())
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

val prove_EvalMPatBind_fail = ref T;
val goal = !prove_EvalMPatBind_fail;

fun prove_EvalMPatBind goal m2deep = let
  val (vars,rhs_tm) = repeat (snd o dest_forall) goal
                      |> rand |> rand |> rand |> rator
                      |> dest_pabs
  val res = m2deep rhs_tm
  val exp = res |> concl |> rator |> rand
  val th = D res
  val var_assum = ``Eval env (Var n) (a (y:'a))``
  val is_var_assum = can (match_term var_assum)
  val vs = find_terms is_var_assum (concl th |> rator)
  fun delete_var tm =
    if mem tm vs then MATCH_MP IMP_EQ_T (ASSUME tm) else NO_CONV tm
  val th = CONV_RULE (RATOR_CONV (DEPTH_CONV delete_var)) th
  val th = CONV_RULE ((RATOR_CONV o RAND_CONV)
              (PairRules.UNPBETA_CONV vars)) th
  val p = th |> concl |> dest_imp |> fst |> rator
  val p2 = goal |> dest_forall |> snd |> dest_forall |> snd
                |> dest_imp |> fst |> rand |> rator
  val ws = free_vars vars
  val vs = filter (fn tm => not (mem (rand (rand tm)) ws)) vs |> mk_set
  val new_goal = goal |> subst [``e:exp``|->exp,p2 |-> p]
  val new_goal = foldr mk_imp new_goal vs
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
    (*
    \\ TRY (SRW_TAC [] [Eval_Var_SIMP,Once EvalM_Var_SIMP,PreImp_def]
      \\ SRW_TAC [] [Eval_Var_SIMP,Once EvalM_Var_SIMP]
      \\ EVAL_TAC \\ NO_TAC)
      *)
    \\ BasicProvers.EVERY_CASE_TAC \\ fs []
    \\ rpt (CHANGED_TAC(SRW_TAC [] [Eval_Var_SIMP,Once EvalM_Var_SIMP,lookup_cons_write,lookup_var_write]))
    \\ TRY (first_x_assum match_mp_tac >> METIS_TAC[])
    \\ fs[GSYM FORALL_PROD]
    \\ EVAL_TAC)
  in UNDISCH_ALL th end handle HOL_ERR e =>
  (prove_EvalMPatBind_fail := goal;
   failwith "prove_EvalMPatBind failed");

val pmatch_m2deep_fail = ref T;
val tm = !pmatch_m2deep_fail;

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
		  |> ISPEC H
                  |> ISPEC pmatch_inv
                  |> ISPEC x_exp
                  |> ISPEC v
                  |> ISPEC x_inv
  val cons_lemma = EvalM_PMATCH
		   |> ISPEC H
                   |> ISPEC pmatch_inv
                   |> ISPEC x_inv
                   |> ISPEC x_exp
                   |> ISPEC v
  fun prove_hyp conv th =
    MP (CONV_RULE ((RATOR_CONV o RAND_CONV) conv) th) TRUTH
  val assm = nil_lemma |> concl |> dest_imp |> fst
  fun trans [] = nil_lemma
    | trans ((pat,rhs_tm)::xs) = let
    (*
    val ((pat,rhs_tm)::xs) = List.drop(ts,1)
    *)
    val th = trans xs
    val p = pat |> dest_pabs |> snd |> hol2deep
                |> concl |> rator |> rand |> to_pattern
    val lemma = cons_lemma |> Q.GEN `p` |> ISPEC p
    val lemma = prove_hyp EVAL lemma
    val lemma = lemma |> Q.GEN `pat` |> ISPEC pat
    val lemma = prove_hyp (SIMP_CONV (srw_ss()) [FORALL_PROD]) lemma
    val lemma = UNDISCH lemma
    val th = UNDISCH th
             |> CONV_RULE ((RATOR_CONV o RAND_CONV) (UNBETA_CONV v)) (* <- Not sure *)
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
  (pmatch_m2deep_fail := tm;
   failwith ("pmatch_m2deep failed (" ^ #message e ^ ")"));

(* ---- *)

fun inst_EvalM_env v th = let
  val thx = th
  val name = fst (dest_var v)
  val str = stringLib.fromMLstring name
  val inv = smart_get_type_inv (type_of v)
  val assum = ``Eval env (Var (Short ^str)) (^inv ^v)``
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
val v = List.hd l
val fix = true
apply_EvalM_Fun (List.hd l) th true
*)
(* MATCH_MP th1 th2 fails when:
   th1 = `!y. (!x. P x y) ==> Q
   th2 = `!x. P x (f x)`
   because of name conflicts.
   MATCH_MP_ABS_RENAME renames the abstractions in th1 to prevent that from happening.
 *)
(* fun MATCH_MP_FORALL_RENAME th1 th2 =
  let
      val th1_hyp = ISPEC H EvalM_Fun_Eq |> concl |> dest_imp |> fst |> strip_forall |> snd
      (* val (quant_vars, th1_spec_hyp) = strip_forall th1_hyp *)
      val (tms, tys) = match_term th1_hyp (concl th2);
      val fvs = FVL (concl (SPEC_ALL th2)::(List.map (fn {redex = _, residue = x} => x) tms)) empty_varset
      val fvl = HOLset.listItems fvs

      fun rename_foralls_conv fvl tm =
	if is_forall tm then let
	    val (x, tm') = dest_forall tm
  	    val x' = variant fvl x
	    val conv_f = RAND_CONV ((ABS_CONV (rename_foralls_conv (x'::fvl))) THENC (ALPHA_CONV x'))
	in
	    conv_f tm
	end
	else REFL tm
      val ren_th1 = CONV_RULE ((RATOR_CONV o RAND_CONV) (rename_foralls_conv fvl)) th1
      val subst_th1 = Thm.INST tms (Thm.INST_TYPE tys ren_th1)
  in
      MP subst_th1 th2
  end*)

fun apply_EvalM_Fun v th fix = let
  val th1 = inst_EvalM_env v th
  val th2 = if fix then MATCH_MP (ISPEC H EvalM_Fun_Eq) (GEN ``v:v`` th1)
                   else MATCH_MP (ISPEC H EvalM_Fun) (GEN ``v:v`` (FORCE_GEN v th1))
  in th2 end;

(* val th1 = (ISPEC H EvalM_Fun_Eq);
val th2 = (GEN ``v:v`` (inst_EvalM_env v th));
MATCH_MP_FORALL_RENAME (ISPEC H EvalM_Fun_Eq) (GEN ``v:v`` (inst_EvalM_env v th)) *)

(*
apply_EvalM_Recclosure fname v th
*)

fun apply_EvalM_Recclosure fname v th = let
  val vname = fst (dest_var v)
  val vname_str = stringLib.fromMLstring vname
  val fname_str = stringLib.fromMLstring fname
  val body = th |> UNDISCH_ALL |> concl |> rator |> rator |> rand (* |> concl |> rator |> rand *)
  val inv = smart_get_type_inv (type_of v)
  val new_env = ``write ^vname_str v (write_rec
                    [(^fname_str,^vname_str,^body)] env env)``
  val old_env = env_tm
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
  val th2 = MATCH_MP (ISPEC H EvalM_Recclosure) (Q.INST [`env`|->`cl_env`] (GEN ``v:v`` th1))
  val assum = ASSUME (fst (dest_imp (concl th2)))
  val th3 = D th2 |> REWRITE_RULE [assum]
  val lemma = MATCH_MP Eval_Eq_Recclosure assum
  val lemma_lhs = lemma |> concl |> dest_eq |> fst
  fun replace_conv tm = let
    val (i,t) = match_term lemma_lhs tm
    in INST i (INST_TYPE t lemma) end handle HOL_ERR _ => NO_CONV tm
  val th4 = CONV_RULE (QCONV (DEPTH_CONV replace_conv)) th3
  in th4 end;

(* Copy-paste from ml_translatorLib *)
(* check_inv "failwith" tm result DEBUG
val name = "failwith" *)
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

(* end of copy-paste *)
				   
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

(* TODO: automate *)
val read_refs =
  [(``get_the_type_constants``,``the_type_constants``,get_the_type_constants_thm),
   (``get_the_term_constants``,``the_term_constants``,get_the_term_constants_thm),
   (``get_the_axioms``,``the_axioms``,get_the_axioms_thm),
   (``get_the_context``,``the_context``,get_the_context_thm)];

val write_refs =
  [(``set_the_type_constants x``,``the_type_constants``,set_the_type_constants_thm),
   (``set_the_term_constants x``,``the_term_constants``,set_the_term_constants_thm),
   (``set_the_axioms x``,``the_axioms``,set_the_axioms_thm),
   (``set_the_context x``,``the_context``,set_the_context_thm)];

(*
val tm = rhs
val tm = !last_m2deep_tm
*)

(* DEBUG *)
val last_m2deep_tm = ref ``T``;
(* END DEBUG *)

(*
val tm = x1
val tm = f
*)

(* DEBUG *)
fun print_tm_msg msg tm =
  print (msg  ^(term_to_string tm) ^ "\n\n");
(* END DEBUG *)

(*
val tm = ``v5 : 'b -> 'a holKernel$M``
val tm = ``list_CASE l (ex_return 128) (\x y. ex_return 256)``
 *)

val tm = map_term;
exception BREAKPOINT of term;

fun m2deep tm =
  (* variable *)
  if is_var tm then let
    val _ = print_tm_msg "is_var\n" tm (* DEBUG *)
    val (name,ty) = dest_var tm
    val inv = get_arrow_type_inv ty
    val inv = ONCE_REWRITE_CONV [ArrowM_def] inv |> concl |> rand |> rand
    val str = stringSyntax.fromMLstring name
    val result = ASSUME (mk_comb(``Eval env (Var (Short ^str))``,mk_comb(inv,tm)))
    val result = MATCH_MP (ISPEC H Eval_IMP_PURE) result |> RW [GSYM ArrowM_def]
    in check_inv "var" tm result end else
  (* failwith *)
  if can (match_term ``(failwith s): ^aM``) tm then let
    val _ = print_tm_msg "failwith\n" tm (* DEBUG *)
    val ty = dest_monad_type (type_of tm)
    val inv = smart_get_type_inv (fst ty) (* !!! *)
    val th = hol2deep (rand tm)
    val asms = List.mapPartial (Lib.total DECIDE) (hyp th)
    val th = List.foldl (Lib.uncurry PROVE_HYP) th asms
    val result = EvalM_failwith |> ISPEC H |> SPEC (rand tm) |> ISPEC inv
                 |> UNDISCH |> Lib.C MATCH_MP th
    in check_inv "failwith" tm result end else
  (* raise_clash *)
  if can (match_term ``(raise_clash t): ^aM``) tm then let
    val _ = print_tm_msg "raise clash\n" tm (* DEBUG *)
    val ty = dest_monad_type (type_of tm)
    val inv = smart_get_type_inv (fst ty) (* !!! *)
    val th = hol2deep (rand tm)
    val result = EvalM_raise_clash |> ISPEC H |> SPEC (rand tm) |> ISPEC inv
                 |> UNDISCH |> Lib.C MATCH_MP th
    in check_inv "raise_clash" tm result end
  (* return *)
  else if can (match_term ``(ex_return x): ^aM``) tm then let
    val _ = print_tm_msg "return\n" tm (* DEBUG *)
    val th = hol2deep (rand tm)
    val result = MATCH_MP (ISPEC H EvalM_return) th
    in check_inv "return" tm result end
  (* bind *)
  else if can (match_term ``(ex_bind (x:^bM) f): ^aM``) tm then let
    val _ = print_tm_msg "bind\n" tm (* DEBUG *)
    val x1 = tm |> rator |> rand
    val (v,x2) = tm |> rand |> dest_abs
    val th1 = m2deep x1
    val th2 = m2deep x2
    val th2 = inst_EvalM_env v th2
    val vs = th2 |> concl |> dest_imp |> fst
    val th2 = th2 |> GEN (rand vs) |> FORCE_GEN (rand (rator vs))
    val result = MATCH_MP (ISPEC H EvalM_bind) (CONJ th1 th2)
    in check_inv "bind" tm result end else
  (* otherwise *)
  if can (match_term ``(x: ^aM) otherwise (y: ^aM)``) tm then let
    val _ = print_tm_msg "otherwise\n" tm (* DEBUG *)
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
    val lemma = Q.SPEC `"v"` (ISPEC H EvalM_otherwise)
    val result = MATCH_MP (MATCH_MP lemma th1) th2
    in check_inv "otherwise" tm result end else
  (* handle_clash *)
  if can (match_term ``handle_clash (x: ^aM) y``) tm then let
    val _ = print_tm_msg "handle clash\n" tm (* DEBUG *)
    val x = tm |> rator |> rand
    val (v,y) = tm |> rand |> dest_abs
    val th1 = m2deep x
    val th2 = m2deep y
    val th3 = inst_EvalM_env v th2 |> Q.GEN`v` |> FORCE_GEN v
    val lemma = ISPEC H EvalM_handle_clash |> SPEC_ALL |> UNDISCH
    val th4 = MATCH_MP lemma th1
    val result = MATCH_MP th4 th3 handle HOL_ERR _ => HO_MATCH_MP th4 th3
    in check_inv "handle_clash" tm result end else
  (* try *)
  if can (match_term ``try (f:'a-> ^bM) x msg``) tm then let
    val _ = print_tm_msg "try\n" tm (* DEBUG *)
    val lemma = tm |> SIMP_CONV (srw_ss()) [try_def]
    val th = m2deep (lemma |> concl |> rand)
    val result = th |> RW [GSYM lemma]
    in check_inv "try" tm result end else
  (* IGNORE_BIND *)
  if can (match_term ``IGNORE_BIND (f:'a -> 'b # 'a) (g:'a -> 'c # 'a)``) tm then let
    val _ = print_tm_msg "IGNORE_BIND\n" tm (* DEBUG *)
    val lemma = tm |> SIMP_CONV std_ss [state_transformerTheory.IGNORE_BIND_DEF]
    val th = m2deep (lemma |> concl |> rand)
    val result = th |> RW [GSYM lemma]
    in check_inv "IGNORE_BIND" tm result end else
  (* abs *)
  if is_abs tm then let
    val _ = print_tm_msg "abs\n" tm (* DEBUG *)
    val (v,x) = dest_abs tm
    val thx = m2deep x
    val result = apply_EvalM_Fun v thx false
    in check_inv "abs" tm result end else
  (* let expressions *)
  if can dest_let tm andalso is_abs (fst (dest_let tm)) then let
    val _ = print_tm_msg "let expressions\n" tm (* DEBUG *)
    val (x,y) = dest_let tm
    val (v,x) = dest_abs x
    val th1 = hol2deep y
    val th2 = m2deep x
    val th2 = inst_EvalM_env v th2
    val th2 = th2 |> GEN ``v:v``
    val z = th1 |> concl |> rand |> rand
    val th2 = INST [v|->z] th2
    val result = MATCH_MP (ISPEC H EvalM_Let) (CONJ th1 th2)
    in check_inv "let" tm result end else
  (* data-type pattern-matching *)
  (print_tm_msg "data-type pattern-matching\n" tm (* DEBUG *); inst_case_thm tm m2deep) handle HOL_ERR _ =>
  (* previously translated term *)
  if can lookup_v_thm tm then let
    val _ = print_tm_msg "previously translated\n" tm (* DEBUG *)
    val th = lookup_v_thm tm
    val inv = smart_get_type_inv (type_of tm)
    val target = mk_comb(inv,tm)
    val (ss,ii) = match_term (th |> concl |> rand) target
    val result = INST ss (INST_TYPE ii th)
                 |> MATCH_MP (ISPEC H Eval_IMP_PURE)
                 |> REWRITE_RULE [GSYM ArrowM_def]
    in check_inv "lookup_v_thm" tm result end else
  (* if *)
  if can (match_term ``if b then x: ^aM else y: ^aM``) tm then let
    val _ = print_tm_msg "if\n" tm (* DEBUG *)
    val (t,x1,x2) = dest_cond tm
    val th0 = hol2deep t
    val th1 = m2deep x1
    val th2 = m2deep x2
    val th = MATCH_MP (ISPEC H EvalM_If) (LIST_CONJ [D th0, D th1, D th2])
    val result = UNDISCH th
    in check_inv "if" tm result end else
  (* ref: get_the_(...) *)
  if can (first (fn (t,_,_) => t = tm)) read_refs then let
    val _ = print_tm_msg "ref get_the(...)\n" tm (* DEBUG *)
    val (_,t,result) = first (fn (t,_,_) => t = tm) read_refs
    val result = result |> UNDISCH_ALL
    in check_inv "get" tm result end else
  (* ref: set_the_(...) *)
  if can (first (fn (t,_,_) => can (match_term t) tm)) write_refs then let
    val _ = print_tm_msg "ref: set_the(...)\n" tm (* DEBUG *)
    val (_,t,result) = (first (fn (t,_,_) => can (match_term t) tm)) write_refs
    val th = result |> UNDISCH
    val result = MATCH_MP th (hol2deep (tm |> rand))
    in check_inv "set" tm result end else
  (* recursive pattern *)
  if can match_rec_pattern tm then let
    val _ = print_tm_msg "recursive pattern\n" tm (* DEBUG *)
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
      val PURE_tm = Term.inst [``:'a`` |-> inv_type, ``:'b`` |-> refs_type] ``PURE : ('a -> v -> bool) -> ('a, 'b) H``
      in ``^PURE_tm (Eq ^inv ^tm)`` end
    fun mk_m_arrow x y = ``ArrowM ^H ^x ^y``
    fun mk_inv [] res = res
      | mk_inv (x::xs) res = mk_inv xs (mk_m_arrow (mk_fix x) res)
(*
val x = hd xs
val res = (get_m_type_inv (type_of tm))
*)
    val inv = mk_inv xs (get_m_type_inv (type_of tm))
    val ss = fst (match_term lhs tm)
    val pre = T (* subst ss (rec_pre_var ()) *)
    val h = ASSUME ``PreImp ^pre (EvalM env (Var (Short ^str)) (^inv ^f) ^H)``
            |> RW [PreImp_def] |> UNDISCH
(*
val original_tm
val tm = List.last xs
*)
    val ys = map (fn tm => MATCH_MP (ISPEC H Eval_IMP_PURE)
                             (MATCH_MP Eval_Eq (var_hol2deep tm))) xs
    fun apply_arrow hyp [] = hyp
      | apply_arrow hyp (x::xs) =
          MATCH_MP (MATCH_MP (ISPEC H EvalM_ArrowM) (apply_arrow hyp xs)) x
          (* MATCH_MP (MATCH_MP EvalM_ArrowM (apply_arrow hyp xs)) x *)
    val result = apply_arrow h ys
    in check_inv "rec_pattern" tm result end else
  (* PMATCH *)
  if is_pmatch tm then let
    val _ = print_tm_msg "PMATCH\n" tm (* DEBUG *)
    val original_tm = tm
    val lemma = pmatch_preprocess_conv tm
    val tm = lemma |> concl |> rand
    val result = pmatch_m2deep tm m2deep
    val result = result |> CONV_RULE (RAND_CONV (RAND_CONV (K (GSYM lemma))))
    in check_inv "pmatch_m2deep" original_tm result end else
  (* normal function applications *)
  if is_comb tm then let
    val _ = print_tm_msg "normal function application\n" tm (* DEBUG *)
    val (f,x) = dest_comb tm
    val thf = m2deep f
    val result = hol2deep x |> MATCH_MP (ISPEC H Eval_IMP_PURE)
                            |> MATCH_MP (MATCH_MP (ISPEC H EvalM_ArrowM) thf)
                 handle e =>
                 m2deep x |> MATCH_MP (MATCH_MP (ISPEC H EvalM_ArrowM) thf)
    in check_inv "comb" tm result end else
  (last_m2deep_tm := tm; failwith ("cannot translate: " ^ term_to_string tm));

fun get_curr_prog_state () = let
  val k = ref init_state
  val _ = ml_prog_update (fn s => (k := s; s))
  in !k end

(*
val def = FST;
val def = !last_def;
val def = map_def;
*)

(* DEBUG *)
val last_def = ref assoc_def;
(* END DEBUG *)

(* Performs a conversion of the form: (\x. M x) = M *)
fun ABS_PREDICATE_CONV tm =
  if is_abs tm then let
      val (x, body) = dest_abs tm
      val P = rator body
      val spec_ETA_THM = ISPEC P ETA_THM
  in spec_ETA_THM end
  handle HOL_ERR _ => raise (ERR "ABS_PREDICATE_CONV" "not valid term")
  else raise (ERR "ABS_PREDICATE_CONV" "not valid term");
				 
fun m_translate def = let
  val original_def = def
  (* DEBUG *)
  val _ = (last_def := original_def)			 
  (* END DEBUG *)
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
  (* val _ = register_term_types (concl def) *)
  fun rev_param_list tm = rand tm :: rev_param_list (rator tm) handle HOL_ERR _ => []
  val rev_params = def |> concl |> dest_eq |> fst |> rev_param_list
  val no_params = (length rev_params = 0)
  (* derive deep embedding *)
  val _ = install_rec_pattern lhs fname fname
  val th = m2deep rhs
  val _ = uninstall_rec_patterns ()
  (* replace rhs with lhs in th *)
  val th = CONV_RULE ((RAND_CONV o RAND_CONV)
             (REWRITE_CONV [CONTAINER_def] THENC ONCE_REWRITE_CONV [GSYM def])) th
  (* abstract parameters *)
  val th = clean_assumptions (D th)
  val (th,v) = if no_params then (th,T) else
                 (foldr (fn (v,th) => apply_EvalM_Fun v th true) th
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
      \\ FULL_SIMP_TAC std_ss [GSYM original_def, addressTheory.CONTAINER_def]
      \\ qpat_x_assum `EvalM env n x H` (ASSUME_TAC o (CONV_RULE (DEPTH_CONV ABS_PREDICATE_CONV)))
      \\ METIS_TAC [])
    val th = UNDISCH lemma |> SPECL (rev rev_params)
    val th = RW [PreImp_def] th |> UNDISCH_ALL
    in th end
  (* remove Eq *)
  val th = RW [ArrowM_def] th
  fun f (v,th) =
    HO_MATCH_MP (ISPEC H EvalM_FUN_FORALL) (GEN v th) |> SIMP_RULE std_ss [M_FUN_QUANT_SIMP]
  val th = foldr f th rev_params handle HOL_ERR _ => th
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
      val v_names = map (fn x => find_const_name (x ^ "_v"))
                      (recc |> listSyntax.dest_list |> fst
                            |> map (stringSyntax.fromHOLstring o rand o rator))
      val _ = ml_prog_update (add_Dletrec recc v_names)
      val s = get_curr_prog_state ()
      val v_def = hd (get_v_defs s)
      val cl_env = v_def |> concl |> rand |> rator |> rator |> rand
      val th = th |> Q.INST [`cl_env`|->`^cl_env`]
                  |> DISCH_ALL |> REWRITE_RULE [GSYM v_def]
                  |> clean_assumptions |> DISCH_ALL
                  |> REWRITE_RULE [GSYM AND_IMP_INTRO] |> UNDISCH_ALL
      val th = th |> DISCH (first (can (match_term ``LOOKUP_VAR _ _ _``)) (hyp th))
      val th = MATCH_MP (MP (ISPEC H LOOKUP_VAR_EvalM_IMP) VALID_STORE_THM) (Q.GEN `env` th) (* HERE!! *)
      in th end
    else let
      val th = th |> Q.INST [`env`|->`^(get_env (get_curr_prog_state ()))`]
                  |> D |> clean_assumptions |> UNDISCH_ALL
      val th = th |> MATCH_MP (MP (ISPEC H EvalM_Fun_PURE_IMP) VALID_STORE_THM)
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
  (* DEBUG *)
    | HOL_ERR err => let
    val _ = print "\n\nml_translate: unexpected error when translating term:\n\n"
    val _ = print_thm def
    val _ = print "\n\n"
    in raise (HOL_ERR err) end;

(* --- perform translation --- *)

val res = translate FST;
val res = translate SND;
val res = translate listTheory.LENGTH;
val res = translate listTheory.MAP;
val res = translate MEMBER_def;
val res = translate listTheory.EVERY_DEF;
val res = translate listTheory.EXISTS_DEF;
val res = translate listTheory.FILTER;
val res = translate listTheory.APPEND;
(* TODO: want builtin support for these *)
val res = translate mlstringTheory.explode_aux_def;
val res = translate mlstringTheory.explode_def;
val explode_aux_side_thm = Q.prove(
  `∀s n m. n + m = strlen s ==> explode_aux_side s n m `,
  Induct_on`m` \\ rw[Once (theorem"explode_aux_side_def")]);
val explode_side_thm = Q.prove(
  `explode_side x`,
  rw[definition"explode_side_def",explode_aux_side_thm])
  |> update_precondition
val res = translate mlstringTheory.strcat_def;
val res = translate stringTheory.string_lt_def
val res = translate stringTheory.string_le_def
val res = Q.prove(`mlstring_lt x1 x2 = string_lt (explode x1) (explode x2)`,
                simp [inv_image_def, mlstringTheory.mlstring_lt_inv_image])
          |> translate
val res = translate totoTheory.TO_of_LinearOrder
val res = translate mlstringTheory.compare_aux_def
val res = translate mlstringTheory.compare_def

(* Copy and paste from mlstringProg *)
val compare_aux_side_def = theorem"compare_aux_side_def";
val compare_side_def = definition"compare_side_def";

val compare_aux_side_thm = Q.prove (
  `!s1 s2 ord n len. (n + len =
    if strlen s1 < strlen s2
      then strlen s1
    else strlen s2) ==> compare_aux_side s1 s2 ord n len`,
  Induct_on `len` \\ rw [Once compare_aux_side_def]
);

val compare_side_thm = Q.prove (
  `!s1 s2. compare_side s1 s2`,
  rw [compare_side_def, compare_aux_side_thm] ) |> update_precondition
(* end copy and paste *)

val res = translate comparisonTheory.pair_cmp_def
val res = translate comparisonTheory.list_cmp_def
(* -- *)
val res = translate (subset_def |> REWRITE_RULE [MEMBER_INTRO]);
val res = translate (holSyntaxExtraTheory.subtract_def |> REWRITE_RULE [MEMBER_INTRO]);
val res = translate (holSyntaxExtraTheory.insert_def |> REWRITE_RULE [MEMBER_INTRO]);
val res = translate holSyntaxExtraTheory.itlist_def;
val res = translate holSyntaxExtraTheory.union_def;
val res = translate mk_vartype_def;
val res = translate is_type_def;
val res = translate is_vartype_def;
val res = translate holKernelPmatchTheory.rev_assocd_def;
val res = translate holKernelTheory.type_subst_def;
val res = translate alphavars_def;
val res = translate holKernelPmatchTheory.raconv_def;
val res = translate aconv_def;
val res = translate holKernelPmatchTheory.is_var_def;
val res = translate holKernelPmatchTheory.is_const_def;
val res = translate holKernelPmatchTheory.is_abs_def;
val res = translate holKernelPmatchTheory.is_comb_def;
val res = translate mk_var_def;
val res = translate holSyntaxExtraTheory.frees_def;
val res = translate combinTheory.o_DEF;
val res = translate freesl_def;
val res = translate (freesin_def |> REWRITE_RULE [MEMBER_INTRO]);
val res = translate holKernelPmatchTheory.vfree_in_def;
val res = translate tyvars_def;
val res = translate type_vars_in_term_def;
val res = translate holSyntaxExtraTheory.variant_def;
val res = translate vsubst_aux_def;
val res = translate holKernelPmatchTheory.is_eq_def;
val res = translate dest_thm_def;
val res = translate hyp_def;
val res = translate concl_def;
val res = translate sortingTheory.PART_DEF;
val res = translate sortingTheory.PARTITION_DEF;
val res = translate sortingTheory.QSORT_DEF;

val type_compare_def = tDefine "type_compare" `
  (type_compare t1 t2 =
     case (t1,t2) of
     | (Tyvar x1,Tyvar x2) => mlstring$compare x1 x2
     | (Tyvar x1,Tyapp _ _) => Less
     | (Tyapp x1 a1,Tyvar _) => Greater
     | (Tyapp x1 a1,Tyapp x2 a2) =>
         case mlstring$compare x1 x2 of
         | Equal => type_list_compare a1 a2
         | other => other) /\
  (type_list_compare ts1 ts2 =
     case (ts1,ts2) of
     | ([],[]) => Equal
     | ([],t2::ts2) => Less
     | (t1::ts1,[]) => Greater
     | (t1::ts1,t2::ts2) =>
         (case type_compare t1 t2 of
          | Equal => type_list_compare ts1 ts2
          | other => other))`
  (WF_REL_TAC `measure (\x. case x of
                  INR (x,_) => type1_size x
                | INL (x,_) => type_size x)`)

val type_cmp_thm = Q.prove(
  `(type_cmp = type_compare) /\
    (list_cmp type_cmp = type_list_compare)`,
  fs [FUN_EQ_THM]
  \\ HO_MATCH_MP_TAC (fetch "-" "type_compare_ind")
  \\ REPEAT STRIP_TAC \\ fs []
  \\ ONCE_REWRITE_TAC [holSyntaxExtraTheory.type_cmp_thm]
  \\ ONCE_REWRITE_TAC [type_compare_def]
  \\ REPEAT BasicProvers.CASE_TAC
  \\ fs [comparisonTheory.pair_cmp_def,comparisonTheory.list_cmp_def])
  |> CONJUNCT1;

val _ = add_preferred_thy "-";
val _ = save_thm("type_cmp_ind",
          (fetch "-" "type_compare_ind") |> RW [GSYM type_cmp_thm]);
val res = translate (type_compare_def |> RW [GSYM type_cmp_thm]);

val term_compare_def = Define `
  term_compare t1 t2 =
     case (t1,t2) of
       (Var x1 ty1,Var x2 ty2) =>
         (case mlstring$compare x1 x2 of
            Less => Less
          | Equal => type_cmp ty1 ty2
          | Greater => Greater)
     | (Var x1 ty1,Const v52 v53) => Less
     | (Var x1 ty1,Comb v54 v55) => Less
     | (Var x1 ty1,Abs v56 v57) => Less
     | (Const x1' ty1',Var v66 v67) => Greater
     | (Const x1' ty1',Const x2' ty2') =>
         (case mlstring$compare x1' x2' of
            Less => Less
          | Equal => type_cmp ty1' ty2'
          | Greater => Greater)
     | (Const x1' ty1',Comb v70 v71) => Less
     | (Const x1' ty1',Abs v72 v73) => Less
     | (Comb s1 t1,Var v82 v83) => Greater
     | (Comb s1 t1,Const v84 v85) => Greater
     | (Comb s1 t1,Comb s2 t2) =>
         (case term_compare s1 s2 of
            Less => Less
          | Equal => term_compare t1 t2
          | Greater => Greater)
     | (Comb s1 t1,Abs v88 v89) => Less
     | (Abs s1' t1',Var v98 v99) => Greater
     | (Abs s1' t1',Const v100 v101) => Greater
     | (Abs s1' t1',Comb v102 v103) => Greater
     | (Abs s1' t1',Abs s2' t2') =>
         case term_compare s1' s2' of
           Less => Less
         | Equal => term_compare t1' t2'
         | Greater => Greater`;

val term_cmp_thm = Q.prove(
  `term_cmp = term_compare`,
  fs [FUN_EQ_THM]
  \\ HO_MATCH_MP_TAC (fetch "-" "term_compare_ind")
  \\ REPEAT STRIP_TAC \\ fs []
  \\ ONCE_REWRITE_TAC [holSyntaxExtraTheory.term_cmp_thm]
  \\ ONCE_REWRITE_TAC [term_compare_def]
  \\ REPEAT BasicProvers.CASE_TAC
  \\ fs [comparisonTheory.pair_cmp_def])

val _ = add_preferred_thy "-";
val _ = save_thm("term_cmp_ind",
          (fetch "-" "term_compare_ind") |> RW [GSYM term_cmp_thm]);
val res = translate (term_compare_def |> RW [GSYM term_cmp_thm]);

val res = translate holKernelPmatchTheory.codomain_def;
val res = translate holSyntaxTheory.typeof_def;
val res = translate holSyntaxTheory.ordav_def;
val res = translate holSyntaxTheory.orda_def;
val res = translate holSyntaxTheory.term_remove_def;
val res = translate holSyntaxTheory.term_union_def;

(* DEBUG *)
val tm = (map_def (* rec *) |> m_translate; ``T``) handle BREAKPOINT tm => tm;
val def = map_def;
(* END DEBUG *)

val def = assoc_def   (* rec *) |> m_translate
val def = map_def    (* rec *) |> m_translate
val def = forall_def (* rec *) |> m_translate (* BUG *)
val def = dest_type_def |> m_translate
val def = dest_vartype_def |> m_translate
val def = holKernelPmatchTheory.dest_var_def |> m_translate (* BUG *)
val def = holKernelPmatchTheory.dest_const_def |> m_translate (* ... *)
val def = holKernelPmatchTheory.dest_comb_def |> m_translate
val def = holKernelPmatchTheory.dest_abs_def |> m_translate
val def = holKernelPmatchTheory.rator_def |> m_translate
val def = holKernelPmatchTheory.rand_def |> m_translate
val def = holKernelPmatchTheory.dest_eq_def |> m_translate
val def = holKernelPmatchTheory.mk_abs_def |> m_translate
val def = get_type_arity_def |> m_translate
val def = mk_type_def |> m_translate
val def = mk_fun_ty_def |> m_translate
val def = holKernelPmatchTheory.type_of_def |> m_translate
val def = get_const_type_def |> m_translate
val def = holKernelPmatchTheory.mk_comb_def |> m_translate
val def = can_def |> m_translate
val def = mk_const_def |> m_translate
val def = image_def |> m_translate

val fdM_def = new_definition("fdM_def",``fdM = first_dup``)
val fdM_intro = SYM fdM_def
val fdM_ind = save_thm("fdM_ind",REWRITE_RULE[MEMBER_INTRO]first_dup_ind)
val fdM_eqs = REWRITE_RULE[MEMBER_INTRO,fdM_intro]first_dup_def
val def = fdM_eqs |> translate
val def = REWRITE_RULE[fdM_intro]add_constants_def |> m_translate
val def = add_def_def |> m_translate
val def = new_constant_def |> m_translate
val def = add_type_def |> m_translate
val def = new_type_def |> m_translate
val def = holKernelPmatchTheory.EQ_MP_def |> m_translate
val def = ASSUME_def |> m_translate
val def = new_axiom_def |> m_translate
val def = vsubst_def |> m_translate
val def = inst_aux_def (* rec *) |> m_translate
val def = inst_def |> m_translate
val def = mk_eq_def |> m_translate
val def = REFL_def |> m_translate
val def = holKernelPmatchTheory.TRANS_def |> m_translate
val def = holKernelPmatchTheory.MK_COMB_def |> m_translate
val def = holKernelPmatchTheory.ABS_def |> m_translate
val def = holKernelPmatchTheory.BETA_def |> m_translate
val def = DEDUCT_ANTISYM_RULE_def |> m_translate
val def = new_specification_def |> m_translate
val def = new_basic_definition_def |> m_translate
val def = (INST_TYPE_def |> SIMP_RULE std_ss [LET_DEF]) |> m_translate
val def = (INST_def |> SIMP_RULE std_ss [LET_DEF]) |> m_translate
val def = new_basic_type_definition_def |> m_translate
val def = holKernelPmatchTheory.SYM_def |> m_translate
val def = PROVE_HYP_def |> m_translate
val def = list_to_hypset_def |> translate
val def = ALPHA_THM_def |> m_translate

val _ = ml_prog_update (close_module NONE); (* TODO: needs signature SOME ... *)

(* extract the interesting thm *)

val _ = Globals.max_print_depth := 10;

fun define_abbrev_conv name tm = let
  val def = define_abbrev true name tm
  in GSYM def |> SPEC_ALL end

val candle_prog_thm =
  get_thm (get_curr_prog_state ())
  |> REWRITE_RULE [ML_code_def]
  |> CONV_RULE ((RATOR_CONV o RATOR_CONV o RAND_CONV)
                (EVAL THENC define_abbrev_conv "candle_code"))
  |> CONV_RULE ((RATOR_CONV o RAND_CONV)
                (EVAL THENC define_abbrev_conv "candle_init_env"))
  |> CONV_RULE ((RAND_CONV)
                (EVAL THENC define_abbrev_conv "candle_init_state"))
  |> curry save_thm "candle_prog_thm"

val _ = export_theory();
