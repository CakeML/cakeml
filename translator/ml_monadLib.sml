structure ml_monadLib :> ml_monadLib =
struct

open HolKernel boolLib bossLib;

open MiniMLTheory MiniMLTerminationTheory;
open Print_astTheory Print_astTerminationTheory intLib;
open ml_translatorTheory ml_translatorLib;
open arithmeticTheory listTheory combinTheory pairTheory;
open integerTheory intLib ml_optimiseTheory;

infix \\ val op \\ = op THEN;

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;

open hol_kernelTheory;
open ml_monadTheory;

val _ = translation_extends "ml_monad";

fun dest_monad_type ty = type_subst (match_type ``:'a M`` ty) ``:'a``;


(* ---- *)

(* support for datatypes... *)

(*
val ty = ``:'a # 'b``; val _ = derive_case_of ty;
val ty = ``:'a list``; val _ = derive_case_of ty;
val ty = ``:hol_type``; val _ = derive_case_of ty;
val ty = ``:term``; val _ = derive_case_of ty;
val ty = ``:thm``; val _ = derive_case_of ty;
val ty = ``:def``; val _ = derive_case_of ty;
*)

fun derive_case_of ty = let
  val (ty,ret_ty) = dest_fun_type (type_of_cases_const ty)
  val name = get_name ty
  val inv_def = fetch "ml_monad" (name ^ "_def")
  val case_th = get_nchotomy_of ty
  val inv_lhs = inv_def |> SPEC_ALL |> CONJUNCTS |> hd |> SPEC_ALL
                        |> concl |> dest_eq |> fst
  fun list_mk_type [] ret_ty = ret_ty
    | list_mk_type (x::xs) ret_ty = mk_type("fun",[type_of x,list_mk_type xs ret_ty])
  val cases_th = TypeBase.case_def_of ty
  val (x1,x2) = cases_th |> CONJUNCTS |> hd |> concl |> repeat (snd o dest_forall)
                         |> dest_eq
  val ty1 = x1 |> repeat rator |> type_of |> domain
  val ty2 = x2 |> type_of
  val cases_th = INST_TYPE [ty2 |-> ``:'return_type M``] cases_th
                 |> INST_TYPE (match_type ty1 ty)
  fun replace_match_exp f tm = let
    val (x,y) = dest_comb tm
    in if is_const x then mk_comb(x,f y) else mk_comb(replace_match_exp f x,y) end
  val cases_tm =
    cases_th |> CONJUNCTS |> hd |> concl |> repeat (snd o dest_forall)
             |> dest_eq |> fst |> replace_match_exp (fn tm => mk_arb (type_of tm))
  fun rename [] = []
    | rename (x::xs) = let val k = "f" ^ int_to_string (length xs + 1)
                       in (x,mk_var(k,type_of x)) :: rename xs end
  val vs = rev (rename (free_vars cases_tm))
  val cases_tm = subst (map (fn (x,y) => x |-> y) vs) cases_tm
  val exp = cases_tm |> replace_match_exp (fn tm => mk_var ("x",type_of tm))
  val input_var = filter (fn x => not (mem x (free_vars cases_tm))) (free_vars exp) |> hd
  val ret_ty = type_of exp
  val xs = rev (map rand (find_terms is_eq (concl case_th)))
  fun add_nums [] = []
    | add_nums (x::xs) = (x,length xs+1) :: add_nums xs
  val ys = rev (add_nums (rev (zip (map snd vs) xs)))
  fun str_tl s = implode (tl (explode s))
  fun list_app x [] = x
    | list_app x (y::ys) = list_app (mk_comb(x,y)) ys
  fun mk_vars ((f,tm),n) = let
    val xs = rev (free_vars tm)
    val fxs = list_app f xs
    val pxs = list_app (mk_var("b" ^ int_to_string n,list_mk_type xs ``:bool``)) xs
    val xs = map (fn x => let val s = str_tl (fst (dest_var x)) in
                          (x,mk_var("n" ^ s,``:string``),
                             mk_var("v" ^ s,``:v``)) end) xs
    val exp = mk_var("exp" ^ int_to_string n, ``:exp``)
    in (n,f,fxs,pxs,tm,exp,xs) end
  val ts = map mk_vars ys
  (* patterns *)
  val patterns = map (fn (n,f,fxs,pxs,tm,exp,xs) => let
    val str = tag_name name (repeat rator tm |> dest_const |> fst)
    val str = stringSyntax.fromMLstring str
    val vars = map (fn (x,n,v) => ``Pvar ^n NONE``) xs
    val vars = listSyntax.mk_list(vars,``:pat``)
    in ``(Pcon ^str ^vars, ^exp)`` end) ts
  val patterns = listSyntax.mk_list(patterns,``:pat # exp``)
  val ret_inv = get_type_inv ``:'return_type``
  val exp_var = mk_var("exp", ``:exp``)
  val result = ``EvalM env (Mat ^exp_var ^patterns) (HOL_MONAD ^ret_inv ^exp)``
  (* assums *)
  val vs = map (fn (n,f,fxs,pxs,tm,exp,xs) => map (fn (x,_,_) => x) xs) ts |> flatten
  val b0 = mk_var("b0",``:bool``)
  fun mk_container tm = mk_comb(``CONTAINER:bool->bool``,tm)
  val tm = b0::map (fn (n,f,fxs,pxs,tm,exp,xs) => mk_imp(mk_container(mk_eq(input_var,tm)),pxs)) ts
           |> list_mk_conj
  val tm = list_mk_forall(vs,tm)
  val result = mk_imp(``TAG () ^tm``,result)
  (* tags *)
  fun find_inv tm =
    if type_of tm = ty then (mk_comb(rator (rator inv_lhs),tm)) else
      (mk_comb(get_type_inv (type_of tm),tm))
  fun mk_hyp (n,f,fxs,pxs,tm,exp,xs) = let
    val env = mk_var("env",``:envE``)
    val env = foldr (fn ((x,n,v),y) =>
      listSyntax.mk_cons(pairSyntax.mk_pair(n,
        pairSyntax.mk_pair(v,``NONE:(num # t) option``)),y)) env (rev xs)
    val tm = map (fn (x,n,v) => mk_comb(find_inv x,v)) xs @ [pxs]
    val tm = if tm = [] then T else list_mk_conj tm
    val tm = mk_imp(tm,``EvalM ^env ^exp (HOL_MONAD ^ret_inv ^fxs)``)
    val vs = map (fn (x,_,_) => x) xs @ map (fn (_,_,v) => v) xs
    val tm = list_mk_forall(vs,tm)
    val n = numSyntax.term_of_int n
    val tm = ``TAG ^n ^tm``
    in tm end;
  (* all_distincts *)
  fun mk_alld (n,f,fxs,pxs,tm,exp,xs) = let
    val tt = listSyntax.mk_list(map (fn (_,x,_) => x) xs,``:string``)
    val tt = mk_comb(``ALL_DISTINCT:string list -> bool``,tt)
    in tt end
  val tt = list_mk_conj(map mk_alld ts) handle HOL_ERR _ => T
  (* goal *)
  fun smart_mk_comb (f,x) = let
    val ty1 = dest_type (type_of f) |> snd |> hd
    val ty2 = input_var |> type_of
    in mk_comb(f,inst (match_type ty2 ty1) x) end
  val hyps = map mk_hyp ts
  val x = smart_mk_comb(rator (rator inv_lhs),input_var)
  val hyp0 = ``TAG 0 (b0 ==> Eval env ^exp_var ^x)``
  val hyps = list_mk_conj(hyp0::hyps)
  val goal = mk_imp(tt,mk_imp(hyps,result))
  val init_tac =
        PURE_REWRITE_TAC [CONTAINER_def]
        \\ REPEAT STRIP_TAC \\ STRIP_ASSUME_TAC (Q.SPEC `x` case_th)
  fun case_tac n =
        Q.PAT_ASSUM `TAG 0 bbb` (MP_TAC o REWRITE_RULE [TAG_def,inv_def,Eval_def])
        \\ FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
        \\ Q.PAT_ASSUM `TAG () bbb` (STRIP_ASSUME_TAC o remove_primes o
             SPEC_ALL o REWRITE_RULE [TAG_def,inv_def,EvalM_def])
        \\ FULL_SIMP_TAC std_ss [ALL_DISTINCT] \\ FULL_SIMP_TAC std_ss [inv_def]
        \\ Q.PAT_ASSUM `TAG ^(numSyntax.term_of_int n) bbb`
             (STRIP_ASSUME_TAC o REWRITE_RULE [TAG_def])
        \\ REPEAT (Q.PAT_ASSUM `TAG xxx yyy` (K ALL_TAC))
        \\ FULL_SIMP_TAC std_ss [EvalM_def,PULL_FORALL] \\ REPEAT STRIP_TAC
        \\ Q.PAT_ASSUM `!xx. bb` (MP_TAC o SPEC_ALL)
        \\ ASM_SIMP_TAC std_ss [] \\ STRIP_TAC
        \\ Q.LIST_EXISTS_TAC [`s2`,`res'`,`refs2`]
        \\ FULL_SIMP_TAC std_ss [] \\ ASM_SIMP_TAC (srw_ss()) []
        \\ ONCE_REWRITE_TAC [evaluate'_cases] \\ SIMP_TAC (srw_ss()) []
        \\ DISJ1_TAC \\ Q.LIST_EXISTS_TAC [`res`,`s`] \\ STRIP_TAC
        THEN1 (FULL_SIMP_TAC std_ss [evaluate'_empty_store_IMP])
        \\ NTAC (2 * length ts) (ASM_SIMP_TAC (srw_ss())
             [Once evaluate'_cases,pmatch'_def,bind_def,
              pat_bindings_def,add_tvs_def])
  val tac = init_tac THENL (map (fn (n,f,fxs,pxs,tm,exp,xs) => case_tac n) ts)
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

val ty = ``:'a # 'b``; val _ = mem_derive_case_of ty;
val ty = ``:'a list``; val _ = mem_derive_case_of ty;
val ty = ``:hol_type``; val _ = mem_derive_case_of ty;
val ty = ``:term``; val _ = mem_derive_case_of ty;
val ty = ``:thm``; val _ = mem_derive_case_of ty;
val ty = ``:def``; val _ = mem_derive_case_of ty;

fun inst_case_thm_for tm = let
  val (_,_,names) = TypeBase.dest_case tm
  val names = map fst names
  val th = mem_derive_case_of ((repeat rator tm) |> type_of |> domain)
  val pat = th |> UNDISCH_ALL |> concl |> rand |> rand
  val (ss,i) = match_term pat tm
  val th = INST ss (INST_TYPE i th)
  val ii = map (fn {redex = x, residue = y} => (x,y)) i
  val ss = map (fn (x,y) => (inst i (get_type_inv x) |-> get_type_inv y)) ii
  val th = INST ss th
  val th = CONV_RULE (DEPTH_CONV BETA_CONV) th
  fun args tm = let val (x,y) = dest_comb tm in args x @ [y] end
                handle HOL_ERR _ => []
  val ns = map (fn n => (n,args n)) names
  fun rename_var prefix ty v =
    mk_var(prefix ^ implode (tl (explode (fst (dest_var v)))),ty)
  val ts = find_terms (can (match_term ``CONTAINER (b:bool)``)) (concl th)
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

fun inst_case_thm tm m2deep = let
  val th = inst_case_thm_for tm
  val th = CONV_RULE (RATOR_CONV (PURE_REWRITE_CONV [CONJ_ASSOC])) th
  val (hyps,rest) = dest_imp (concl th)
  fun list_dest_forall tm = let
    val (v,tm) = dest_forall tm
    val (vs,tm) = list_dest_forall tm
    in (v::vs,tm) end handle HOL_ERR _ => ([],tm)
  fun take 0 xs = [] | take n xs = hd xs :: take (n-1) (tl xs)
  fun sat_hyp tm = let
    val (vs,x) = list_dest_forall tm
    val (x,y) = dest_imp x
    val z = y |> rand |> rand
    val lemma = if can dest_monad_type (type_of z)
                then m2deep z
                else hol2deep z
    val lemma = D lemma
    val new_env = y |> rator |> rator |> rand
    val env = mk_var("env",``:envE``)
    val lemma = INST [env|->new_env] lemma
    val (x1,x2) = dest_conj x handle HOL_ERR _ => (T,x)
    val (z1,z2) = dest_imp (concl lemma)
    val thz =
      QCONV (SIMP_CONV std_ss [ASSUME x1,Eval_Var_SIMP,lookup_def] THENC
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


(* ---- *)

val tm = ``if x = 6 then ex_return (5:num) else ex_return (n+5)``

val tm = ``case x of Tyapp _ _ => ex_return (5:num)
                   | Tyvar v => ex_return (n+5)``

fun m2deep tm =
  (* failwith *)
  if can (match_term ``(failwith str):'a M``) tm then let
    val ty = dest_monad_type (type_of tm)
    val inv = get_type_inv ty
    val result = EvalM_failwith |> SPEC (rand tm) |> ISPEC inv
    in check_inv "failwith" tm result end
  (* return *)
  else if can (match_term ``(ex_return x):'a M``) tm then let
    val th = hol2deep (rand tm)
    val result = MATCH_MP EvalM_return th
    in check_inv "return" tm result end
  (* bind *)
  else if can (match_term ``(ex_bind (x:'b M) f):'a M``) tm then let
    val x1 = tm |> rator |> rand
    val (v,x2) = tm |> rand |> dest_abs
    val th1 = m2deep x1
    val th2 = m2deep x2
    val th2 = inst_Eval_env v th2
    val vs = th2 |> concl |> dest_imp |> fst
    val th2 = th2 |> GEN (rand vs) |> GEN (rand (rator vs))
    val result = MATCH_MP EvalM_bind (CONJ th1 th2)
    in check_inv "bind" tm result end else
  (* data-type pattern-matching *)
  inst_case_thm tm m2deep handle HOL_ERR _ =>
  (* if *)
  if can (match_term ``if b then x:'a M else y:'a M``) tm then let
    val (t,x1,x2) = dest_cond tm
    val th0 = hol2deep t
    val th1 = m2deep x1
    val th2 = m2deep x2
    val th = MATCH_MP EvalM_If (LIST_CONJ [D th0, D th1, D th2])
    val result = UNDISCH th
    in check_inv "if" tm result end else
  hd []









(* ---- *)

val def = assoc_def

fun m_translate def = let
  val original_def = def
  fun the (SOME x) = x | the _ = failwith("the of NONE")
  (* perform preprocessing -- reformulate def *)
  val (is_rec,def,ind) = preprocess_def def
  val (lhs,rhs) = dest_eq (concl def)
  val fname = repeat rator lhs |> dest_const |> fst |> get_unique_name
  val _ = print ("Translating monadic " ^ fname ^ "\n")
  val fname_str = stringLib.fromMLstring fname
  (* read off information *)
  val _ = register_term_types (concl def)
  fun rev_param_list tm = rand tm :: rev_param_list (rator tm) handle HOL_ERR _ => []
  val rev_params = def |> concl |> dest_eq |> fst |> rev_param_list
  val no_params = (length rev_params = 0)
  (* derive deep embedding *)
  val pre_var = install_rec_pattern lhs fname
  val th = hol2deep rhs
  val _ = uninstall_rec_pattern ()
  in () end;

(*

  preprocess_def def
  get_type_arity_def
  mk_type_def
  dest_type_def
  mk_fun_ty_def
  type_of_def
  mk_comb_def

*)

end
