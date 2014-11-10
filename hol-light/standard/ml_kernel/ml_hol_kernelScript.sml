open HolKernel Parse boolLib bossLib;

val _ = new_theory "ml_hol_kernel";

open astTheory libTheory bigStepTheory semanticPrimitivesTheory;
open terminationTheory;
open ml_translatorTheory ml_translatorLib;
open arithmeticTheory listTheory combinTheory pairTheory;
open integerTheory intLib ml_optimiseTheory;

infix \\ val op \\ = op THEN;

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;

open holKernelTheory;
open ml_monadTheory;

val _ = translation_extends "ml_monad";

val _ = (use_full_type_names := false);

fun dest_monad_type ty = type_subst (match_type ``:'a M`` ty) ``:'a``;

(* ---- *)

fun get_m_type_inv ty =
  ``HOL_MONAD ^(get_type_inv (dest_monad_type ty))`` handle HOL_ERR _ =>
  failwith "unknown type";

fun get_arrow_type_inv ty =
  if can dest_monad_type ty then get_m_type_inv ty else let
    val (ty1,ty2) = dest_fun_type ty
    val i1 = get_arrow_type_inv ty1 handle HOL_ERR _ =>
             ``PURE ^(get_type_inv ty1)``
    val i2 = get_arrow_type_inv ty2
    in ``^i1 -M-> ^i2`` end

fun smart_get_type_inv ty =
  if not (can dest_monad_type ty) andalso
     can get_arrow_type_inv ty then let
    val inv = get_arrow_type_inv ty
    in ONCE_REWRITE_CONV [ArrowM_def] inv |> concl |> rand |> rand end
  else get_type_inv ty

(* ---- *)

(* support for datatypes... *)

(*
val ty = ``:'b # 'c``; val _ = derive_case_of ty;
val ty = ``:'a list``; val _ = derive_case_of ty;
val ty = ``:hol_type``; val _ = derive_case_of ty;
val ty = ``:hol_term``; val _ = derive_case_of ty;
val ty = ``:thm``; val _ = derive_case_of ty;
val ty = ``:def``; val _ = derive_case_of ty;
*)

fun derive_case_of ty = let
  fun get_name ty = clean_uppercase (full_name_of_type ty) ^ "_TYPE"
  val name = get_name ty
  val inv_def = fetch "ml_monad" (name ^ "_def")
  val case_th = get_nchotomy_of ty
(*
  val tm = ``Eval (write n1_2 v1_2 (write n1_1 v1_1 env)) exp1
      (return_type (f1 x1_1 x1_2))``
*)
  val pat = ``Eval env exp (P (res:'a))``
  fun Eval_to_EvalM tm = let
    val (m,i) = match_term pat tm
    val tm1 = subst m (inst i ``EvalM env exp (HOL_MONAD P (res:'a M))``)
    val ty1 = tm |> rand |> rand |> type_of
    val y1 = tm |> rand |> rand |> inst [ty1|->``:^ty1 M``]
    val y0 = tm1 |> rand |> rand
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
  fun nums [] = [] | nums (x::xs) = 1 + length xs :: nums xs
  val ts = nums (tl hyps) |> rev
  val evaluate_Mat =
    ``evaluate c x env (Mat e pats) (xx,res)``
    |> (ONCE_REWRITE_CONV [evaluate_cases] THENC SIMP_CONV (srw_ss()) [])
  val evaluate_match_Conv =
    ``evaluate_match c x env args
         ((Pcon xx pats,exp2)::pats2) errv (yyy,y)``
    |> (ONCE_REWRITE_CONV [evaluate_cases] THENC
        SIMP_CONV (srw_ss()) [pmatch_def])
  val IF_T = prove(``(if T then x else y) = x:'a``,SIMP_TAC std_ss []);
  val IF_F = prove(``(if F then x else y) = y:'a``,SIMP_TAC std_ss []);
  val n = 1
  val init_tac =
        PURE_REWRITE_TAC [CONTAINER_def]
        \\ REPEAT STRIP_TAC \\ STRIP_ASSUME_TAC (Q.SPEC `x` case_th)
  fun case_tac n =
        Q.PAT_ASSUM `b0 ==> Eval env exp something`
           (MP_TAC o REWRITE_RULE [TAG_def,inv_def,Eval_def])
        \\ FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
        \\ NTAC 3 (POP_ASSUM MP_TAC)
        \\ POP_ASSUM (STRIP_ASSUME_TAC o remove_primes o
             SPEC_ALL o REWRITE_RULE [TAG_def,inv_def,EvalM_def])
        \\ FULL_SIMP_TAC std_ss [ALL_DISTINCT] \\ FULL_SIMP_TAC std_ss [inv_def]
        \\ REPEAT STRIP_TAC
        \\ FULL_SIMP_TAC std_ss [ALL_DISTINCT] \\ FULL_SIMP_TAC std_ss [inv_def]
        \\ REPEAT (Q.PAT_ASSUM `!x.bbb` (STRIP_ASSUME_TAC o SPEC_ALL))
        \\ REPEAT (Q.PAT_ASSUM `bb ==> bbb` (fn th =>
             if mem ("b" ^ int_to_string n)
                (free_vars (concl th) |> map (fst o dest_var))
             then ASSUME_TAC (UNDISCH_ALL (RW [GSYM AND_IMP_INTRO] th))
             else ALL_TAC))
        \\ FULL_SIMP_TAC std_ss [EvalM_def,PULL_FORALL] \\ REPEAT STRIP_TAC
        \\ Q.PAT_ASSUM `!xx. bb` (MP_TAC o SPEC_ALL)
        \\ ASM_SIMP_TAC std_ss [] \\ STRIP_TAC
        \\ Q.LIST_EXISTS_TAC [`s2`,`res'`,`refs2`]
        \\ FULL_SIMP_TAC std_ss [] \\ ASM_SIMP_TAC (srw_ss()) []
        \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) []
        \\ DISJ1_TAC \\ Q.LIST_EXISTS_TAC [`res`,`(0,s)`] \\ STRIP_TAC
        THEN1 (IMP_RES_TAC evaluate_empty_store_IMP \\ FULL_SIMP_TAC std_ss [])
        \\ PairCases_on `env`
        \\ REWRITE_TAC [evaluate_match_Conv,LENGTH,pmatch_def]
        \\ FULL_SIMP_TAC (srw_ss()) [pmatch_def,pat_bindings_def,
              lookup_alist_mod_env_def,lookup_cons_def,same_tid_def,id_to_n_def,
              same_ctor_def,write_def]
(*
  val _ = set_goal([],goal)
  val n = 1
  val n = 2
*)
  val tac = init_tac THENL (map case_tac ts)
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

fun inst_case_thm_for tm = let
  val (_,_,names) = TypeBase.dest_case tm
  val names = map fst names
  val th = mem_derive_case_of ((repeat rator tm) |> type_of |> domain) |> UNDISCH
  val pat = th |> UNDISCH_ALL |> concl |> rand |> rand
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

(*
val tm = (!last_fail)
*)

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
    val env = mk_var("env",``:all_env``)
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

(* ---- *)

fun inst_EvalM_env v th = let
  val thx = th
  val name = fst (dest_var v)
  val str = stringLib.fromMLstring name
  val inv = smart_get_type_inv (type_of v)
  val assum = ``Eval env (Var (Short ^str)) (^inv ^v)``
  val new_env = ``write ^str (v:v) (env:all_env)``
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
               |> CONV_RULE ((RAND_CONV o RAND_CONV) (UNBETA_CONV v))
               |> DISCH new_assum
  in th1 end;

fun apply_EvalM_Fun v th fix = let
  val th1 = inst_EvalM_env v th
  val th2 = if fix then MATCH_MP EvalM_Fun_Eq (GEN ``v:v`` th1)
                   else MATCH_MP EvalM_Fun (GEN ``v:v`` (FORCE_GEN v th1))
  in th2 end;

fun apply_EvalM_Recclosure fname v th = let
  val vname = fst (dest_var v)
  val vname_str = stringLib.fromMLstring vname
  val fname_str = stringLib.fromMLstring fname
  val body = th |> UNDISCH_ALL |> concl |> rator |> rand
  val inv = smart_get_type_inv (type_of v)
  val new_env = ``write ^vname_str v (write_rec
                    [(^fname_str,^vname_str,^body)] env)``
  val old_env = ``env:all_env``
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
                |> CONV_RULE ((RAND_CONV o RAND_CONV) (UNBETA_CONV v))
                |> DISCH new_assum
  val th2 = MATCH_MP EvalM_Recclosure (Q.INST [`env`|->`cl_env`] (GEN ``v:v`` th1))
  val assum = ASSUME (fst (dest_imp (concl th2)))
  val th3 = D th2 |> REWRITE_RULE [assum]
  val lemma = MATCH_MP Eval_Eq_Recclosure assum
  val lemma_lhs = lemma |> concl |> dest_eq |> fst
  fun replace_conv tm = let
    val (i,t) = match_term lemma_lhs tm
    in INST i (INST_TYPE t lemma) end handle HOL_ERR _ => NO_CONV tm
  val th4 = CONV_RULE (QCONV (DEPTH_CONV replace_conv)) th3
  in th4 end;

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
*)

fun m2deep tm =
  (* variable *)
  if is_var tm then let
    val (name,ty) = dest_var tm
    val inv = get_arrow_type_inv ty
    val inv = ONCE_REWRITE_CONV [ArrowM_def] inv |> concl |> rand |> rand
    val str = stringSyntax.fromMLstring name
    val result = ASSUME (mk_comb(``Eval env (Var (Short ^str))``,mk_comb(inv,tm)))
    val result = MATCH_MP Eval_IMP_PURE result |> RW [GSYM ArrowM_def]
    in check_inv "var" tm result end else
  (* failwith *)
  if can (match_term ``(failwith str):'a M``) tm then let
    val ty = dest_monad_type (type_of tm)
    val inv = smart_get_type_inv ty
    val th = hol2deep (rand tm)
    val asms = List.mapPartial (Lib.total DECIDE) (hyp th)
    val th = List.foldl (Lib.uncurry PROVE_HYP) th asms
    val result = EvalM_failwith |> SPEC (rand tm) |> ISPEC inv
                 |> UNDISCH |> Lib.C MATCH_MP th
    in check_inv "failwith" tm result end else
  (* raise_clash *)
  if can (match_term ``(raise_clash t):'a M``) tm then let
    val ty = dest_monad_type (type_of tm)
    val inv = smart_get_type_inv ty
    val th = hol2deep (rand tm)
    val result = EvalM_raise_clash |> SPEC (rand tm) |> ISPEC inv
                 |> UNDISCH |> Lib.C MATCH_MP th
    in check_inv "raise_clash" tm result end
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
    val th2 = inst_EvalM_env v th2
    val vs = th2 |> concl |> dest_imp |> fst
    val th2 = th2 |> GEN (rand vs) |> FORCE_GEN (rand (rator vs))
    val result = MATCH_MP EvalM_bind (CONJ th1 th2)
    in check_inv "bind" tm result end else
  (* otherwise *)
  if can (match_term ``(x:'a M) otherwise (y:'a M)``) tm then let
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
    val lemma = Q.SPEC `"v"` EvalM_otherwise
    val result = MATCH_MP (MATCH_MP lemma th1) th2
    in check_inv "otherwise" tm result end else
  (* handle_clash *)
  if can (match_term ``handle_clash (x:'a M) y``) tm then let
    val x = tm |> rator |> rand
    val (v,y) = tm |> rand |> dest_abs
    val th1 = m2deep x
    val th2 = m2deep y
    val th3 = inst_EvalM_env v th2 |> Q.GEN`v` |> FORCE_GEN v
    val lemma = SPEC_ALL EvalM_handle_clash |> UNDISCH
    val th4 = MATCH_MP lemma th1
    val result = MATCH_MP th4 th3 handle HOL_ERR _ => HO_MATCH_MP th4 th3
    in check_inv "handle_clash" tm result end else
  (* try *)
  if can (match_term ``try (f:'a->'b M) x msg``) tm then let
    val lemma = tm |> SIMP_CONV (srw_ss()) [try_def]
    val th = m2deep (lemma |> concl |> rand)
    val result = th |> RW [GSYM lemma]
    in check_inv "try" tm result end else
  (* IGNORE_BIND *)
  if can (match_term ``IGNORE_BIND (f:'a -> 'b # 'a) (g:'a -> 'c # 'a)``) tm then let
    val lemma = tm |> SIMP_CONV std_ss [state_transformerTheory.IGNORE_BIND_DEF]
    val th = m2deep (lemma |> concl |> rand)
    val result = th |> RW [GSYM lemma]
    in check_inv "IGNORE_BIND" tm result end else
  (* abs *)
  if is_abs tm then let
    val (v,x) = dest_abs tm
    val thx = m2deep x
    val result = apply_EvalM_Fun v thx false
    in check_inv "abs" tm result end else
  (* let expressions *)
  if can dest_let tm andalso is_abs (fst (dest_let tm)) then let
    val (x,y) = dest_let tm
    val (v,x) = dest_abs x
    val th1 = hol2deep y
    val th2 = m2deep x
    val th2 = inst_EvalM_env v th2
    val th2 = th2 |> GEN ``v:v``
    val z = th1 |> concl |> rand |> rand
    val th2 = INST [v|->z] th2
    val result = MATCH_MP EvalM_Let (CONJ th1 th2)
    in check_inv "let" tm result end else
  (* data-type pattern-matching *)
  inst_case_thm tm m2deep handle HOL_ERR _ =>
  (* previously translated term *)
  if can lookup_cert tm then let
    val th = lookup_cert tm
    val inv = smart_get_type_inv (type_of tm)
    val target = mk_comb(inv,tm)
    val (ss,ii) = match_term (th |> concl |> rand) target
    val result = INST ss (INST_TYPE ii th)
                 |> MATCH_MP Eval_IMP_PURE
                 |> REWRITE_RULE [GSYM ArrowM_def]
    in check_inv "lookup_cert" tm result end else
  (* if *)
  if can (match_term ``if b then x:'a M else y:'a M``) tm then let
    val (t,x1,x2) = dest_cond tm
    val th0 = hol2deep t
    val th1 = m2deep x1
    val th2 = m2deep x2
    val th = MATCH_MP EvalM_If (LIST_CONJ [D th0, D th1, D th2])
    val result = UNDISCH th
    in check_inv "if" tm result end else
  (* ref: get_the_(...) *)
  if can (first (fn (t,_,_) => t = tm)) read_refs then let
    val (_,t,result) = first (fn (t,_,_) => t = tm) read_refs
    val th = get_cert (t |> dest_const |> fst) |> fst |> SPEC_ALL |> UNDISCH_ALL
    val th = MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] Eval_Var_SWAP_ENV)
                      (th |> Q.INST [`env`|->`shaddow_env`]) |> UNDISCH_ALL
             handle HOL_ERR _ => th
    val result = MATCH_MP result th
    in check_inv "get" tm result end else
  (* ref: set_the_(...) *)
  if can (first (fn (t,_,_) => can (match_term t) tm)) write_refs then let
    val (_,t,result) = (first (fn (t,_,_) => can (match_term t) tm)) write_refs
    val th = get_cert (t |> dest_const |> fst) |> fst |> SPEC_ALL |> UNDISCH_ALL
    val th = MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] Eval_Var_SWAP_ENV)
                      (th |> Q.INST [`env`|->`shaddow_env`]) |> UNDISCH_ALL
             handle HOL_ERR _ => th
    val result = MATCH_MP result th
    val result = MATCH_MP result (hol2deep (tm |> rand))
    in check_inv "set" tm result end else
  (* recursive pattern *)
  if can match_rec_pattern tm then let
    val (lhs,fname,pre_var) = match_rec_pattern tm
    fun dest_args tm = rand tm :: dest_args (rator tm) handle HOL_ERR _ => []
    val xs = dest_args tm
    val f = repeat rator lhs
    val str = stringLib.fromMLstring fname
    fun mk_fix tm = let
      val inv = smart_get_type_inv (type_of tm)
      in ``PURE (Eq ^inv ^tm)`` end
    fun mk_m_arrow x y = ``ArrowM ^x ^y``
    fun mk_inv [] res = res
      | mk_inv (x::xs) res = mk_inv xs (mk_m_arrow (mk_fix x) res)
(*
val x = hd xs
val res = (get_m_type_inv (type_of tm))
*)
    val inv = mk_inv xs (get_m_type_inv (type_of tm))
    val ss = fst (match_term lhs tm)
    val pre = T (* subst ss (rec_pre_var ()) *)
    val h = ASSUME ``PreImp ^pre (EvalM env (Var (Short ^str)) (^inv ^f))``
            |> RW [PreImp_def] |> UNDISCH
    val ys = map (fn tm => MATCH_MP Eval_IMP_PURE
                             (MATCH_MP Eval_Eq (var_hol2deep tm))) xs
    fun apply_arrow hyp [] = hyp
      | apply_arrow hyp (x::xs) =
          MATCH_MP (MATCH_MP EvalM_ArrowM (apply_arrow hyp xs)) x
    val result = apply_arrow h ys
    in check_inv "rec_pattern" tm result end else
  (* normal function applications *)
  if is_comb tm then let
    val (f,x) = dest_comb tm
    val thf = m2deep f
    val result = hol2deep x |> MATCH_MP Eval_IMP_PURE
                            |> MATCH_MP (MATCH_MP EvalM_ArrowM thf)
                 handle e =>
                 m2deep x |> MATCH_MP (MATCH_MP EvalM_ArrowM thf)
    in check_inv "comb" tm result end else
  failwith ("cannot translate: " ^ term_to_string tm);

val def = assoc_def;

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
  (* val _ = register_term_types (concl def) *)
  fun rev_param_list tm = rand tm :: rev_param_list (rator tm) handle HOL_ERR _ => []
  val rev_params = def |> concl |> dest_eq |> fst |> rev_param_list
  val no_params = (length rev_params = 0)
  (* derive deep embedding *)
  val pre_var = install_rec_pattern lhs fname
  val th = m2deep rhs
  val _ = uninstall_rec_patterns ()
  (* replace rhs with lhs in th *)
  val th = CONV_RULE ((RAND_CONV o RAND_CONV)
             (REWRITE_CONV [CONTAINER_def] THENC ONCE_REWRITE_CONV [GSYM def])) th
  (* abstract parameters *)
  val th = clean_lookup_cons (D th)
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
  (* DeclAssumExists *)
  val decl_assum_ex = let
    val fs = find_term (can (match_term ``write_rec funs``)) (concl th) |> rand
    val c = REWRITE_CONV [MAP] THENC EVAL
    val th = DeclAssumExists_SNOC_Dletrec |> SPEC fs |> SPEC_ALL
             |> CONV_RULE ((RATOR_CONV o RAND_CONV) c)
    val th = MP th TRUTH
    in th end handle HOL_ERR _ => DeclAssumExists_SNOC_Dlet_Fun
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
      \\ METIS_TAC []);
    val th = UNDISCH lemma |> SPECL (rev rev_params)
    val th = RW [PreImp_def] th |> UNDISCH_ALL
    in th end
  (* remove Eq *)
  val th = RW [ArrowM_def] th
  fun f (v,th) =
    HO_MATCH_MP EvalM_FUN_FORALL (GEN v th) |> SIMP_RULE std_ss [M_FUN_QUANT_SIMP]
  val th = foldr f th rev_params handle HOL_ERR _ => th
  val th = RW [GSYM ArrowM_def] th
  (* simpliy EqualityType *)
  val th = SIMP_EqualityType_ASSUMS th
  (* abbreviate code *)
  val th = th |> DISCH_ALL |> REWRITE_RULE [GSYM AND_IMP_INTRO] |> UNDISCH_ALL
  val th = RW [ArrowM_def] th
  val th = if is_rec then
             th |> DISCH (first (can (find_term (fn tm => tm = rator ``Recclosure (ARB:all_env)``))) (hyp th))
                |> Q.INST [`cl_env`|->`env`,`env`|->`env1`] |> DISCH (get_DeclAssum ())
                |> Q.GEN `env` |> Q.GEN `env1`
                |> REWRITE_RULE [AND_IMP_INTRO]
                |> MATCH_MP M_DeclAssum_Dletrec_INTRO |> Q.SPEC `env` |> UNDISCH_ALL
           else
             th |> DISCH (get_DeclAssum ()) |> Q.GEN `env`
                |> MATCH_MP M_DeclAssum_Dlet_INTRO
                |> SPEC fname_str |> Q.SPEC `env` |> UNDISCH_ALL
  val th = RW [GSYM ArrowM_def] th
  val th = MATCH_MP EvalM_ArrowM_IMP th
  (* store certificate for later use *)
  val pre = (case pre of NONE => TRUTH | SOME pre_def => pre_def)
  val th = store_cert th [pre] decl_assum_ex |> Q.SPEC `env` |> UNDISCH_ALL
  val _ = print_fname fname original_def
  in th end handle UnableToTranslate tm => let
    val _ = print "\n\nCannot translate term:  "
    val _ = print_term tm
    val _ = print "\n\nwhich has type:\n\n"
    val _ = print_type (type_of tm)
    val _ = print "\n\n"
    in raise UnableToTranslate tm end;

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
val res = translate mlstringTheory.strcat_def;
val res = translate (subset_def |> REWRITE_RULE [MEMBER_INTRO]);
val res = translate (subtract_def |> REWRITE_RULE [MEMBER_INTRO]);
val res = translate (insert_def |> REWRITE_RULE [MEMBER_INTRO]);
val res = translate itlist_def;
val res = translate union_def;
val res = translate mk_vartype_def;
val res = translate is_type_def;
val res = translate is_vartype_def;
val res = translate rev_assocd_def;
val res = translate holKernelTheory.type_subst_def;
val res = translate alphavars_def;
val res = translate raconv_def;
val res = translate aconv_def;
val res = translate is_var_def;
val res = translate is_const_def;
val res = translate is_abs_def;
val res = translate is_comb_def;
val res = translate mk_var_def;
val res = translate frees_def;
val res = translate combinTheory.o_DEF;
val res = translate fressl_def;
val res = translate (freesin_def |> REWRITE_RULE [MEMBER_INTRO]);
val res = translate vfree_in_def;
val res = translate tyvars_def;
val res = translate type_vars_in_term_def;
val res = translate variant_def;
val res = translate vsubst_aux_def;
val res = translate is_eq_def;
val res = translate term_remove_def;
val res = translate term_union_def;
val res = translate dest_thm_def;
val res = translate hyp_def;
val res = translate concl_def;
val res = translate sortingTheory.PART_DEF;
val res = translate sortingTheory.PARTITION_DEF;
val res = translate sortingTheory.QSORT_DEF;
(* TODO: want builtin support for these, and strcat above *)
val res = translate stringTheory.string_lt_def
val res = translate stringTheory.string_le_def

val def = assoc_def  (* rec *) |> m_translate
val def = map_def    (* rec *) |> m_translate
val def = forall_def (* rec *) |> m_translate
val def = dest_type_def |> m_translate
val def = dest_vartype_def |> m_translate
val def = dest_var_def |> m_translate
val def = dest_const_def |> m_translate
val def = dest_comb_def |> m_translate
val def = dest_abs_def |> m_translate
val def = rator_def |> m_translate
val def = rand_def |> m_translate
val def = dest_eq_def |> m_translate
val def = mk_abs_def |> m_translate
val def = get_type_arity_def |> m_translate
val def = mk_type_def |> m_translate
val def = mk_fun_ty_def |> m_translate
val def = type_of_def |> m_translate
val def = get_const_type_def |> m_translate
val def = mk_comb_def |> m_translate
val def = can_def |> m_translate
val def = mk_const_def |> m_translate

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
val def = EQ_MP_def |> m_translate
val def = ASSUME_def |> m_translate
val def = new_axiom_def |> m_translate
val def = vsubst_def |> m_translate
val def = inst_aux_def (* rec *) |> m_translate
val def = inst_def |> m_translate
val def = mk_eq_def |> m_translate
val def = REFL_def |> m_translate
val def = TRANS_def |> m_translate
val def = MK_COMB_def |> m_translate
val def = ABS_def |> m_translate
val def = BETA_def |> m_translate
val def = DEDUCT_ANTISYM_RULE_def |> m_translate
val def = new_specification_def |> m_translate
val def = new_basic_definition_def |> m_translate
val def = (INST_TYPE_def |> SIMP_RULE std_ss [LET_DEF]) |> m_translate
val def = (INST_def |> SIMP_RULE std_ss [LET_DEF]) |> m_translate
val def = new_basic_type_definition_def |> m_translate

val kernel_thm = finalise_module_translation ();
val _ = save_thm("kernel_thm", Q.SPEC `NONE` kernel_thm);

val _ = (print_asts := true);

val _ = export_theory();
