(*
  Main entry points to the cv translator
*)
structure cv_transLib :> cv_transLib =
struct

open HolKernel Abbrev Parse boolLib bossLib DefnBase cv_miscLib;
open cv_repTheory cvTheory cv_typeTheory cv_repLib cv_primTheory cv_memLib;

(*--------------------------------------------------------------------------*
   automatic definitions (and termination proofs) for cv functions
 *--------------------------------------------------------------------------*)

fun derive_cv_proj_tac (hs,goal_tm) = let
  val tms = find_terms is_cv_proj goal_tm
  fun add_facts_tac [] = ALL_TAC
    | add_facts_tac (tm::tms) = let
    val (xs,v) = dest_cv_proj tm
    val th = SPECL [v,xs] cv_proj_less_eq
    in assume_tac th THEN add_facts_tac tms end
  in add_facts_tac tms (hs,goal_tm) end

val cv_termination_tac =
  rpt strip_tac
  \\ gvs [cv_termination_simp,arithmeticTheory.DIV_LT_X]
  \\ rewrite_tac [to_cv_proj]
  \\ derive_cv_proj_tac
  \\ gvs [] \\ gvs [cv_proj_def];

(*
val alts = [([[0,2],[1]],3),
            ([[0],[1]],2),
            ([[1],[2],[4]],10)]
*)
fun make_measures alts = let
  fun mk_sum_term [] = numSyntax.zero_tm
    | mk_sum_term (x::xs) = foldl (fn (x,y) => numSyntax.mk_plus(y,x)) x xs
  fun cvs_ty n = pairSyntax.list_mk_prod(List.tabulate(n,K cvSyntax.cv))
  fun access arg nargs tm =
    if arg = 0 then if nargs <= 1 then tm else pairSyntax.mk_fst(tm)
    else access (arg - 1) (nargs - 1) (pairSyntax.mk_snd(tm))
  fun process (combs,nargs) = let
    val input = mk_var("input",cvs_ty nargs)
    fun each combs = let
      val ys = map (fn i => mk_cv_sum_depth (access i nargs input)) combs
      in mk_abs(input,mk_sum_term ys) end
    in map each combs end
  fun combine x y = let
    val x_ty = x |> type_of |> dom_rng |> fst
    val y_ty = y |> type_of |> dom_rng |> fst
    val input = mk_var("input",sumSyntax.mk_sum(x_ty,y_ty))
    in mk_abs(input,sumSyntax.mk_sum_case(x,y,input)) end
  fun every_comb [] = []
    | every_comb [x] = x
    | every_comb (x::xs) = let
       val cs = every_comb xs
       in List.concat (map (fn y => map (combine y) cs) x) end
  fun mk_meas tm = let
    val ty = tm |> type_of |> dom_rng |> fst
    val v = mk_var("x",ty)
    in numSyntax.mk_measure(tm,v,v) |> rator |> rator end
  in map mk_meas (every_comb (map process alts)) end

fun termination_tactic alts = let
  val ms = make_measures alts
  fun one_tac tm =
    WF_REL_TAC [ANTIQUOTE tm] \\ cv_termination_tac \\ NO_TAC
  fun try_each [] t = NO_TAC t
    | try_each (x::xs) t = (one_tac x ORELSE try_each xs) t
  in try_each ms end

fun is_no_arg_fun cv_def_tm =
  not (is_comb (fst (dest_eq cv_def_tm)))
  handle HOL_ERR _ => false;

fun is_tailrecursive cv_def_tm = let
  val fnames = strip_conj cv_def_tm |> map (fst o strip_comb o fst o dest_eq)
  val rhs_list = strip_conj cv_def_tm |> map (snd o dest_eq)
  fun has_rec_call tm =  exists (fn fv => exists (aconv fv) fnames) (free_vars tm)
  fun ok_rhs tm = let
    val (x,y,z) = cvSyntax.dest_cv_if tm
    in not (has_rec_call x) andalso ok_rhs y andalso ok_rhs z end
    handle HOL_ERR _ => let
    val (xs,y) = pairSyntax.dest_anylet tm
    in all (fn (v,x) => not (has_rec_call x)) xs andalso ok_rhs y end
    handle HOL_ERR _ =>
    if has_rec_call tm then (let
      val (c,xs) = strip_comb tm
      in all (not o has_rec_call) xs end
      handle HOL_ERR _ => false)
    else true;
  in all ok_rhs rhs_list end

fun define_cv_function name (def:thm) cv_def_tm (SOME t) =
       tDefine name [ANTIQUOTE cv_def_tm] t
  | define_cv_function name def cv_def_tm NONE =
       if is_no_arg_fun cv_def_tm then let
         val v_str = cv_def_tm |> dest_eq |> fst |> dest_var |> fst
         val new_v_tm = mk_var(v_str, cvSyntax.cv --> cvSyntax.cv)
         val arg_tm = mk_var("cv", cvSyntax.cv)
         val cv_def_tm = mk_eq(mk_comb(new_v_tm,arg_tm), snd (dest_eq cv_def_tm))
         val def = new_definition(name ^ "_def",cv_def_tm)
         in SPEC (cvSyntax.mk_cv_num (numSyntax.term_of_int 0)) def end
       else if is_tailrecursive cv_def_tm then
         tailrecLib.tailrec_define name cv_def_tm
       else (let
         val alts = strip_conj cv_def_tm
                      |> map (length o snd o strip_comb o fst o dest_eq)
                      |> map (fn n => (List.tabulate(n,fn i => [i]),n))
         val t = termination_tactic alts
         in tDefine name [ANTIQUOTE cv_def_tm] t end
       handle HOL_ERR _ => let
         val defn = Defn.Hol_defn name [ANTIQUOTE cv_def_tm]
         val _ = Defn.tgoal defn
         in failwith "You need to prove a termination goal" end)

(*--------------------------------------------------------------------------*
   helper functions
 *--------------------------------------------------------------------------*)

fun from_for ty = cv_typeLib.from_term_for ty;

fun remove_primes th = let
  val prime = "'"
  fun delete_last_prime s =
    if String.isSuffix prime s then substring(s,0,String.size(s)-1) else fail()
  fun loop [] ys i = i
    | loop (x::xs) ys i = let
      val name = (fst o dest_var) x
      val new_name = repeat delete_last_prime name
      in if name = new_name then loop xs (x::ys) i else let
        val new_var = mk_var(new_name,type_of x)
        in loop xs (new_var::ys) ((x |-> new_var) :: i) end end
  val i = loop (free_varsl (concl th :: hyp th)) [] []
  in INST i th end

fun apply_everywhere f tm =
  let val t = (f tm handle HOL_ERR _ => tm)
  in if is_var t then t else
     if is_const t then t else
     if is_abs t then let
       val (v,x) = dest_abs t
       in mk_abs(v,apply_everywhere f x) end
     else mk_comb (apply_everywhere f (rator t), apply_everywhere f (rand t)) end

fun replace_each [] tm = tm
  | replace_each ((pat,dest)::rest) tm = let
  val (i,s) = match_term pat tm
  in replace_each rest (subst i (inst s dest)) end
  handle HOL_ERR e => replace_each rest tm;

(* val var_tm = “n:num” *)
fun mk_cv_rep_var_assum var_tm = let
  val (var_name,ty) = dest_var var_tm
  val f = from_for ty
  val p = mk_var("p_" ^ var_name,bool)
  val cv = mk_var("cv_" ^ var_name,cvSyntax.cv)
  in mk_cv_rep p cv f var_tm end;

fun mk_assum_for def = let
  val lhs_tm = def |> SPEC_ALL |> concl |> dest_eq |> fst
  val (f,args) = strip_comb lhs_tm
  val arg_assums = map mk_cv_rep_var_assum args
  val a = if null arg_assums then T else list_mk_conj arg_assums
  val ps = map cv_rep_pre arg_assums
  val cvs = map cv_rep_cv_tm arg_assums
  val funname = dest_const f |> fst
  val cv_fun_ty = foldr (fn (x,y) => x --> y) cvSyntax.cv (map type_of cvs)
  val cv_fun_tm = mk_var("cv_" ^ funname,cv_fun_ty)
  val cv_lhs = list_mk_comb(cv_fun_tm,cvs)
  val cv_lhs_from = curry list_mk_comb cv_fun_tm
    (map (fn tm => mk_comb(cv_rep_from tm, cv_rep_hol_tm tm)) arg_assums)
  val target_from = from_for (type_of lhs_tm)
  val assum_eq = mk_eq(mk_comb(target_from,lhs_tm),cv_lhs_from)
  val p = list_mk_conj(ps @ [assum_eq])
  val goal = mk_imp(a,mk_cv_rep p cv_lhs target_from lhs_tm)
  val lemma = prove(goal,
    rewrite_tac [cv_rep_def] \\ rpt strip_tac
    \\ full_simp_tac bool_ss [])
  in (def,(lhs_tm,lemma)) end;

fun mk_pre_var one_def = let
  val (v,args) = one_def |> concl |> dest_eq |> fst |> strip_comb
  val name = fst (dest_const v)
  fun mk_funtype arg_tys ret_ty = foldr (op -->) ret_ty arg_tys;
  val pre_v = mk_var(name ^ "_pre", mk_funtype (map type_of args) bool)
  in list_mk_comb(pre_v,args) end

fun match_some_pat [] tm = NONE
  | match_some_pat ((pat,pre)::pats) tm =
      if can (match_term pat) tm then
        SOME (subst (fst (match_term pat tm)) pre)
      else match_some_pat pats tm;

fun replace_all all_pats tm =
  case match_some_pat all_pats tm of
    SOME res => replace_all all_pats res
  | NONE => if is_comb tm then mk_comb(replace_all all_pats (rator tm),
                                       replace_all all_pats (rand tm)) else
            if is_abs tm then mk_abs(fst(dest_abs tm),
                                     replace_all all_pats (snd(dest_abs tm)))
            else tm;

fun make_pre_imp all_pats ex_cv_rep = let
  val args = ex_cv_rep |> UNDISCH_ALL |> concl |> rator |> rand |> rand
                       |> strip_comb |> snd
  in list_mk_forall(args,replace_all all_pats (concl ex_cv_rep)) end;

fun make_ind_abs ex_cv_rep = let
  val c = ex_cv_rep |> UNDISCH_ALL |> concl
  val args = c |> rator |> rand |> rand |> strip_comb |> snd
  in list_mk_abs(args,c) end;

fun genl_args ex_cv_rep = let
  val c = ex_cv_rep |> UNDISCH_ALL |> concl
  val args = c |> rator |> rand |> rand |> strip_comb |> snd
  in GENL args ex_cv_rep end;

fun specl_res ex_cv_rep th = let
  val c = ex_cv_rep |> UNDISCH_ALL |> concl
  val args = c |> rator |> rand |> rand |> strip_comb |> snd
  in SPECL args th end;

fun oneline_ify_all def = let
  val usu = UNDISCH_ALL o SPEC_ALL o UNDISCH_ALL
  val defs = def |> usu |> CONJUNCTS |> map usu
  fun term_nub [] = []
    | term_nub (tm::tms) = tm :: term_nub (filter (not o aconv tm) tms)
  fun get_const def = def |> concl |> dest_eq |> fst |> strip_comb |> fst
  val cs = defs |> map get_const |> term_nub
  val groups = map (fn c => filter (aconv c o get_const) defs) cs
  in map (DefnBase.one_line_ify NONE o LIST_CONJ) groups end

fun fix_missed_args th = let
  fun rhs_imp tm = if is_imp tm then snd (dest_imp tm) else tm
  val (l,r) = th |> concl |> rhs_imp |> dest_eq
  val ys = l |> rand |> strip_comb |> snd
  val xs = if null ys then [] else r |> strip_comb |> snd
  val zs = zip xs ys |> filter (is_var o fst)
  val s = map (fn (v,w) => v |-> mk_comb(from_for (type_of w),w)) zs
  in INST s th end

fun lookup_ind_for_const hd_const =
  case DefnBase.lookup_indn hd_const of
    NONE => failwith "Could not find appropriate induction"
  | SOME (ind,_) => ind;

fun make_ind_thm allow_pre hd_const pre_def_tms =
  if allow_pre then let
    val pre_def_tm = list_mk_conj pre_def_tms
    val (pre_rules,pre_ind,pre_def) = Hol_reln [ANTIQUOTE pre_def_tm]
    in (pre_ind,pre_def) end
  else let
    fun process tm = let
      val (vs,x) = strip_forall tm
      val z = dest_imp x |> snd handle HOL_ERR _ => x
      val c = strip_comb z |> fst
      in (c,list_mk_forall(vs,z)) end
    val xs = map process pre_def_tms
    val cs = list_mk_conj (map snd xs)
    val bs = list_mk_conj pre_def_tms
    val ind_tm = list_mk_forall(map fst xs, mk_imp(bs,cs))
    val other_ind = lookup_ind_for_const hd_const
    (*
    set_goal([],ind_tm)
    *)
    val pre_ind = curry TAC_PROOF ([],ind_tm) (
      rpt gen_tac \\ rpt (disch_then strip_assume_tac)
      \\ match_mp_tac other_ind \\ rpt strip_tac
      \\ last_x_assum irule \\ rpt strip_tac
      \\ gvs [])
    in (pre_ind,TRUTH) end

fun find_def_for const_tm =
  case lookup_userdef const_tm of
    SOME { thm = STDEQNS cv_def, ... } => SPEC_ALL cv_def
  | _ => failwith ("Cannot find definition of " ^ term_to_string const_tm);

fun indent_print_thm prefix suffix th = let
  val m = !max_print_depth
  fun change #"\n" = "\n  "
    | change c = implode [c]
  fun indent_print s = cv_print (String.translate change s)
  in (cv_print (prefix ^ "  ");
      max_print_depth := 15;
      indent_print (thm_to_string th);
      max_print_depth := m;
      cv_print suffix)
     handle HOL_ERR _ =>
      max_print_depth := m end;

fun find_inst_def_for needs_c = let
  val needed_def = find_def_for needs_c
  val _ = cv_print "Recursively calling `cv_auto_trans` on definition:\n"
  val _ = indent_print_thm "\n" "\n\n" needed_def
  val gen_c = needed_def |> SPEC_ALL |> CONJUNCTS |> hd |> SPEC_ALL |> concl
                         |> dest_eq |> fst |> strip_comb |> fst
  val i = match_type (type_of gen_c) (type_of needs_c)
  fun contains_words ty = let
    val {Tyop = name, Thy = thy, Args = args} = dest_thy_type ty
    in (thy = "fcp" andalso name = "cart") orelse
       (thy = "fcp" andalso name = "bit0") orelse
       (thy = "fcp" andalso name = "bit1") orelse
       List.exists contains_words args end
    handle HOL_ERR _ => false
  fun mentions_word_types { residue = r, redex = _ } = contains_words r
  val keep_i = filter mentions_word_types i
  val new_def = INST_TYPE keep_i needed_def
  in new_def end;

fun remove_T_IMP th = MP th TRUTH handle HOL_ERR _=> th;

val clean_name = let
  fun okay_char c = (#"a" <= c andalso c <= #"z") orelse
                    (#"A" <= c andalso c <= #"Z") orelse
                    (#"0" <= c andalso c <= #"9") orelse c = #"_"
  in String.translate (fn c => if okay_char c then implode [c] else "_") end;

(*--------------------------------------------------------------------------*
   main workhorse
 *--------------------------------------------------------------------------*)

(*
  val def = f1_def
  val def = fac_def
  val def = foo_def
  val def = use_foo_def
  val def = even_def
  val def = risky_def
  val def = inc_def
  val def = cond_def
  val def = num_sum_def
  val def = listTheory.HD
  val def = UNZIP_eq
  val def = listTheory.APPEND
  val term_opt = if true then NONE else SOME cheat;
  val allow_pre = true
  val allow_pre = false
*)

fun cv_trans_any allow_pre term_opt def = let
  (* make hyps *)
  val defs = def |> oneline_ify_all |> LIST_CONJ
  val defs = defs |> SPEC_ALL |> CONJUNCTS |> map (UNDISCH_ALL o SPEC_ALL)
  val assums = defs |> map mk_assum_for
  val hyps = map snd assums
  (* bottom up translation *)
(*
  val one_def = el 1 defs
*)
  fun trans_each one_def = let
    val target_tm = one_def |> concl |> dest_eq |> snd
    val th0 = cv_rep_for hyps target_tm
    val th1 = th0 |> CONV_RULE (RAND_CONV (REWR_CONV (SYM one_def)))
    val hs = hyp one_def
    val th2 = foldr (uncurry DISCH) th1 hs
              |> CONV_RULE (REPEATC (REWR_CONV AND_IMP_INTRO))
              |> CONV_RULE (REPEATC (REWR_CONV cv_rep_move))
    val th3 = th2 |> CONV_RULE (cv_rep_pre_conv (DEPTH_CONV BETA_CONV
                                                 THENC REWRITE_CONV []) THENC
                                cv_rep_cv_tm_conv (DEPTH_CONV BETA_CONV))
    in remove_primes th3 end
  val raw_cv_reps = map trans_each defs
  (* define cv function *)
  fun cv_eq_for (th2,(one_def,(_,th3))) = let
    val (_,args) = th2 |> concl |> rand |> strip_comb
    val cv_rhs = th2 |> UNDISCH_ALL |> concl |> cv_rep_cv_tm
    val cv_lhs = th3 |> UNDISCH_ALL |> concl |> cv_rep_cv_tm
    val (_,cv_args) = cv_lhs |> strip_comb
    val s = map2 (fn v => fn cv =>
              mk_comb(from_for (type_of v),v) |-> cv) args cv_args
    in mk_eq(cv_lhs,subst s cv_rhs) end
  val cv_eqs = map cv_eq_for (zip raw_cv_reps assums)
  val cv_def_tm = list_mk_conj cv_eqs
  val name = cv_eqs |> hd |> dest_eq |> fst |> strip_comb
                    |> fst |> dest_var |> fst |> clean_name
  val cv_def = define_cv_function name def cv_def_tm term_opt
  val cv_defs = cv_def |> CONJUNCTS |> map SPEC_ALL
  val _ = cv_print "Defined cv functions:\n"
  val _ = (cv_print "\n"; List.app (indent_print_thm "" "\n\n") cv_defs)
  (* instantiate raw_cv_reps *)
  fun strip_var_arg tm = if is_var (rand tm) then rator tm else fail()
  val cv_consts = cv_defs |> map (repeat strip_var_arg o fst o dest_eq o concl)
  val cv_vars = hyps |> map (fst o strip_comb o
                             cv_rep_cv_tm o concl o UNDISCH_ALL o snd)
  val cv_subst = map2 (fn v => fn c => v |-> c) cv_vars cv_consts
  val inst_cv_reps = raw_cv_reps |> map (INST cv_subst)
                                 |> map2 (fn cv_def => fn th =>
    CONV_RULE (cv_rep_cv_tm_conv (REWR_CONV (SYM cv_def))) th) cv_defs
  val no_pre = (length inst_cv_reps = 1 andalso
                aconv (inst_cv_reps |> hd |> concl |> cv_rep_pre) T)
  val expand_cv_reps = inst_cv_reps |> map (CONV_RULE (REWR_CONV cv_rep_def))
  in
    if no_pre then let
      (* derive final theorems *)
      val res = hd expand_cv_reps
      val result = fix_missed_args res
      val result = remove_T_IMP result
      val _ = cv_print "Storing result:\n"
      val _ = indent_print_thm "\n" "\n\n" result
      val _ = save_thm(name ^ "_thm[cv_rep]", result)
      in TRUTH end
    else let
      (* define pre *)
      val pats = expand_cv_reps |> map (rand o concl)
      val pre_vars = map mk_pre_var defs
      val all_pats = zip pats pre_vars
      val pre_def_tms = map (make_pre_imp all_pats) expand_cv_reps
      val hd_const = raw_cv_reps |> hd |> concl |> rand |> strip_comb |> fst
      val (pre_ind,pre_def) = make_ind_thm allow_pre hd_const pre_def_tms
      (* instantiate pre_ind *)
      val is = map make_ind_abs expand_cv_reps
      val ind_thm = pre_ind |> SPECL is |> CONV_RULE (DEPTH_CONV BETA_CONV)
      val thms = map genl_args expand_cv_reps |> LIST_CONJ
      val res = MP ind_thm thms |> CONJUNCTS
      val res_insts = map2 specl_res expand_cv_reps res
      val result = map fix_missed_args res_insts
      val result = map remove_T_IMP result
      (* derive final theorems *)
      val combined_result = LIST_CONJ result
      val _ = cv_print "Storing result:\n"
      val _ = indent_print_thm "\n" "\n\n" combined_result
      val _ = save_thm(name ^ "_thm[cv_rep]", combined_result)
      in pre_def end
  end

(*--------------------------------------------------------------------------*
   non-recursive version of cv_trans
 *--------------------------------------------------------------------------*)

fun cv_trans_no_loop allow_pre term_opt def =
  cv_trans_any allow_pre term_opt def
  handle NeedsTranslation tm => let
    val target_c = def |> SPEC_ALL |> CONJUNCTS |> hd |> SPEC_ALL |> concl
                       |> dest_eq |> fst |> strip_comb |> fst
    val needs_c = strip_comb tm |> fst
    val _ = print ("Translation of " ^ term_to_string target_c ^ " needs " ^
                   term_to_string needs_c ^ ".\n")
    val _ = print "Stopping.\n"
    in failwith ("Unable to translate " ^ term_to_string needs_c) end

fun cv_trans def = let
  val res = cv_trans_no_loop false NONE def
  in if aconv (concl res) T then () else
       failwith ("Precondition generated! " ^
                 "Use `cv_trans_pre` instead of `cv_trans`.") end

fun cv_trans_pre def = let
  val res = cv_trans_no_loop true NONE def
  in if aconv (concl res) T then
       failwith ("No precondition generated! " ^
                 "Use `cv_trans` instead of `cv_trans_pre`.")
     else res end;

fun cv_trans_rec def tac =
  cv_trans_no_loop false (SOME tac) def;

fun cv_trans_pre_rec def tac =
  cv_trans_no_loop true (SOME tac) def;

(*--------------------------------------------------------------------------*
   recursive version of cv_auto_trans
 *--------------------------------------------------------------------------*)

datatype res = Res of thm | Needs of term;

datatype task = Def of thm | Abbr of thm;

fun total_cv_trans allow_pre term_opt def is_last =
  (if is_last then (Res (cv_trans_any allow_pre term_opt def))
              else (Res (cv_trans_any false NONE def)))
  handle NeedsTranslation tm => Needs tm;

fun get_unused_name s = let
  val cs = constants "-" |> map (fst o dest_const)
  fun loop i = let
    val suggest = s ^ "_" ^ int_to_string i
    in if mem suggest cs then loop (i+1) else suggest end
  in loop 1 end

fun rename_vars prefix tm = let
  val fvs = free_vars tm
  val i = map (fn i => i |-> mk_var(prefix ^ fst (dest_var i), type_of i)) fvs
  in subst i tm end

fun rename_vars_th prefix th = let
  val fvs = free_vars (concl th)
  val i = map (fn i => i |-> mk_var(prefix ^ fst (dest_var i), type_of i)) fvs
  in INST i th end

fun inst_ho_args tm new_def = let
  val tm = tm |> rename_vars "y_"
  val def = new_def |> DefnBase.one_line_ify NONE |> SPEC_ALL |> rename_vars_th "x_"
  val lhs_tm = def |> concl |> dest_eq |> fst
  val (_,i) = match_term lhs_tm tm
  val inst_def = INST_TYPE i def
  val lhs_tm = inst_def |> concl |> dest_eq |> fst
  val (c,args1) = strip_comb lhs_tm
  val args2 = strip_comb tm |> snd
  fun is_fun_type ty =
    case dest_thy_type ty of
      {Args = _, Thy = "min", Tyop = "fun"} => true | _ => false
  val xs = zip args1 args2
  val ys = filter (is_fun_type o type_of o snd) xs
           |> map (fn (x,y) => x |-> y)
  val _ = not (List.null ys) orelse fail()
  val subst_def = inst_def |> INST ys
  val l = subst_def |> concl |> dest_eq |> fst
  val args = free_vars l
  val name = c |> dest_const |> fst |> get_unused_name
  val f = mk_var(name,type_of(list_mk_abs(args,l)))
  val abbrev_def = new_definition(name ^ "_def",mk_eq(list_mk_comb(f,args),l))
  val final_def = subst_def |> PURE_REWRITE_RULE [GSYM abbrev_def]
                            |> CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV)
  val _ = let
    val new_c = final_def |> SPEC_ALL |> concl |> dest_eq |> fst |> strip_comb |> fst
    val temp_name = new_c |> dest_const |> fst |> get_unused_name
    val new_v = mk_var(temp_name, type_of new_c)
    val temp_eq = final_def |> concl |> subst [new_c |-> new_v]
    val _ = Define [ANTIQUOTE temp_eq]
    val _ = Theory.delete_binding (temp_name ^ "_def")
    val ind = fetch "-" (temp_name ^ "_ind")
    val knames = constants_of_defn final_def
    val _ = register_indn(ind,knames)
    val _ = Theory.delete_binding (temp_name ^ "_ind")
    val _ = Theory.delete_const temp_name
    in () end handle HOL_ERR _ => ();
  in [Def final_def, Abbr (SPEC_ALL abbrev_def)] end
  handle HOL_ERR _ => [Def new_def]

fun cv_trans_loop allow_pre term_opt [] = failwith "nothing to do"  (* cannot happen *)
  | cv_trans_loop allow_pre term_opt (Abbr th::defs) = let
      val tm = th |> concl |> dest_eq |> fst
      val th1 = cv_rep_for [] tm
      val th2 = th1 |> CONV_RULE (cv_rep_hol_tm_conv (REWR_CONV th)
                                  THENC REWR_CONV cv_rep_def)
      val c = tm |> strip_comb |> fst |> dest_const |> fst
      val th3 = save_thm(c ^ "_ho[cv_rep]",th2)
      in cv_trans_loop allow_pre term_opt defs end
  | cv_trans_loop allow_pre term_opt (Def def::defs) =
      case total_cv_trans allow_pre term_opt def (null defs) of
        Res th => if null defs then th else cv_trans_loop allow_pre term_opt defs
      | Needs tm => let
         val needs_c = strip_comb tm |> fst
         val new_def = find_inst_def_for needs_c
         val new_tasks = inst_ho_args tm new_def
         val new_defs = new_tasks @ Def def::defs
         in cv_trans_loop allow_pre term_opt new_defs end;

(*
val allow_pre = false
val term_opt = if true then NONE else SOME cheat;
val (Def def::defs) = [Def def]
val Needs tm = total_cv_trans allow_pre term_opt def (null defs)

val (Def def::defs) = new_tasks
val (Abbr th::defs) = defs
*)

fun cv_auto_trans def = let
  val res = cv_trans_loop false NONE [Def def]
  in if aconv (concl res) T then () else
       failwith ("Precondition generated! " ^
                 "Use `cv_trans_pre` instead of `cv_trans`.") end

fun cv_auto_trans_pre def = let
  val res = cv_trans_loop true NONE [Def def]
  in if aconv (concl res) T then
       failwith ("No precondition generated! " ^
                 "Use `cv_trans` instead of `cv_trans_pre`.")
     else res end;

fun cv_auto_trans_rec def tac =
  cv_trans_loop false (SOME tac) [Def def];

fun cv_auto_trans_pre_rec def tac =
  cv_trans_loop true (SOME tac) [Def def];

(*--------------------------------------------------------------------------*
   translate deep embedding constants of the form:
    |- constant_name = <deep embedding data type>
 *--------------------------------------------------------------------------*)

fun cv_trans_deep_embedding eval_conv th =
  let val (top_lhs,_) = concl th |> dest_eq
      val (nm,ty) = dest_const top_lhs
      val from_tm = cv_typeLib.from_term_for ty
      val from_rhs = mk_comb (from_tm, top_lhs)
      val x = mk_var ("x", cvSyntax.cv)
      val f = mk_var (nm ^ "_cv", cvSyntax.cv --> cvSyntax.cv)
      val eq_tm = mk_eq(mk_comb (f, x), from_rhs)
      val defn_thm = new_definition (nm ^ "_cv_def", eq_tm) |> SPEC_ALL
      val (def_lhs,_) = concl defn_thm |> dest_eq
      val cv_thm = CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV th) THENC eval_conv)) defn_thm
      val eq_name = nm ^ "_cv_eq"
      val _ = save_thm (eq_name, cv_thm)
      val _ = DefnBase.register_defn {tag="user", thmname=eq_name}
      val num_0 = cvSyntax.mk_cv_num (numSyntax.term_of_int 0)
      val cv_trans_thm = defn_thm |> INST [x |-> num_0] |> SYM
      val _ = cv_memLib.cv_rep_add cv_trans_thm
  in () end

(*--------------------------------------------------------------------------*
   find all cv_defs for constants in a term
 *--------------------------------------------------------------------------*)

val cv_exp_const =
  cvTheory.cv_exp_def |> SPEC_ALL |> concl |> dest_eq |> fst |> strip_comb |> fst;

fun get_code_eq_for const_tm =
  if aconv cv_exp_const const_tm then cvTheory.cv_exp_eq
  else find_def_for const_tm;

fun get_cv_consts tm = let
  fun uninteresting c = let
    val { Thy = thy_name, Name = name, ... } = dest_thy_const c
    in if thy_name = "bool" then name = "LET" else
       if thy_name = "num" then name = "0" else
       if thy_name = "arithmetic" then
         mem name ["ZERO","BIT1","BIT2","NUMERAL"] else
         if thy_name = "cv" then name <> "cv_exp" else false end
  fun get_consts acc tm =
    if is_var tm then acc else
    if is_const tm then
      (if uninteresting tm then acc else
       if List.exists (aconv tm) acc then acc else
         tm :: acc) else
    if is_abs tm then get_consts acc (snd (dest_abs tm)) else let
      val (x,y) = dest_comb tm
      in get_consts (get_consts acc x) y end;
  val cs = get_consts [] tm
  fun is_okay_type ty = let
    val (n,tys) = dest_type ty
    in if n = "fun" then List.all is_okay_type tys else
       if n = "cv" andalso null tys then true else false end
  val bad = filter (not o is_okay_type o type_of) cs
  val _ = null bad orelse
          failwith ("Encountered non-cv constant: " ^ term_to_string (hd bad))
  in cs end

fun get_code_eq_info const_tm = let
  val cv_def = get_code_eq_for const_tm
  val tm = cv_def |> SPEC_ALL |> concl |> dest_eq |> snd
  in (cv_def, get_cv_consts tm) end

fun cv_eqs_for tm = let
  val init_set = get_cv_consts tm
  fun collect [] found_consts acc = acc
    | collect (c::word_list) found_consts acc =
    if List.exists (aconv c) found_consts then
      collect word_list found_consts acc
    else let
      val (cv_def,uses_cv) = get_code_eq_info c
      in collect (uses_cv @ word_list) (c::found_consts) (cv_def::acc) end
  val res = collect init_set [] []
  in res end

(*--------------------------------------------------------------------------*
   cv_eval
 *--------------------------------------------------------------------------*)

val _ = computeLib.add_funs [cv_fst_def,cv_snd_def];

fun cv_eval_raw tm = let
  val _ = List.null (free_vars tm) orelse failwith "cv_eval needs input to be closed"
  val th = cv_rep_for [] tm
  val ty = type_of tm
  val _ = cv_print "Translating input to a cv term.\n"
  val from_to_thm = cv_time cv_typeLib.from_to_thm_for ty
  val cv_tm = cv_miscLib.cv_rep_cv_tm (concl th)
  val _ = cv_print "Looking for relevant cv code equations.\n"
  val cv_eqs = cv_time cv_eqs_for cv_tm
  val _ = cv_print ("Found " ^ int_to_string (length cv_eqs) ^ " cv code equations to use.\n")
  val cv_conv = cv_computeLib.cv_compute cv_eqs
  val th1 = MATCH_MP cv_rep_eval th
  val th2 = MATCH_MP th1 from_to_thm
  val th3 = th2 |> UNDISCH_ALL
  val _ = cv_print "Calling cv_compute.\n"
  val th4 = cv_time (CONV_RULE (RAND_CONV (RAND_CONV cv_conv))) th3
  val th5 = remove_T_IMP (DISCH_ALL th4)
  in th5 end;

fun cv_eval tm = let
  val th = cv_eval_raw tm
  val _ = cv_print "Using EVAL to convert from cv to original types.\n"
  val th = cv_time (CONV_RULE (RAND_CONV EVAL)) (UNDISCH_ALL th)
  val th = th |> DISCH_ALL |> remove_T_IMP
  in th end;

end
