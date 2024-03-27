(*
  Derives cv_rep theorems (which cv_transLib uses internally).
*)
structure cv_repLib :> cv_repLib =
struct

open HolKernel Abbrev Parse boolLib bossLib;
open cv_repTheory cvTheory cv_typeTheory cv_memLib cv_miscLib;

exception NeedsTranslation of term list * term;

(*--------------------------------------------------------------------------*
   derive cv_rep theorem from HOL term
 *--------------------------------------------------------------------------*)

fun from_for ty = cv_typeLib.from_term_for ty;

fun match_memory hyps tm = let
  fun match [] = NONE
    | match ((pat,th)::rest) =
        SOME (match_term pat tm,th)
        handle HOL_ERR _ => match rest
  in
    case match (hyps @ cv_rep_thms ()) of
       NONE => NONE
     | SOME ((i,s),th) => let
        val th1 = INST i (INST_TYPE s th)
        val from_tm = from_for (type_of tm)
        val curr_from_tm = th1 |> UNDISCH_ALL |> concl |> cv_rep_from
        val (i,s) = match_term curr_from_tm from_tm
        val th2 = INST i (INST_TYPE s th1)
        in SOME th2 end
  end;

val from_to_pat = from_to_def |> SPEC_ALL |> concl |> dest_eq |> fst;
val is_from_to = can (match_term from_to_pat);

(*
val tm = target_tm
val hyps = tl [(T,TRUTH)]
val tm = ``((2w:word8) @@ (4w:word16)) : word64``
val tm = (rand x)
*)

fun tm_to_cv hyps tm = let
  exception LocalException of term list * term * exn;
  fun report_error [] tm e =
        (indent_print_term Silent "Error occured at term:\n" "\n" tm;
         raise e)
    | report_error (t::ts) tm e =
        (indent_print_term Silent "Error occured within:\n" "\n" t;
         report_error ts tm e)
  fun tm_to_cv_debug (stack:term list) (hyps:(term * thm) list) (tm:term) =
   (if is_var tm orelse numSyntax.is_numeral tm then
      ISPECL [from_for (type_of tm), tm] cv_rep_trivial
    else case match_memory hyps tm of
      (*
      val SOME th = match_memory hyps tm
      *)
      SOME th =>
       (if not (is_imp (concl th)) then th else
        let
          val th = th |> CONV_RULE ((RATOR_CONV o RAND_CONV) (DEPTH_CONV BETA_CONV))
          val (l,r) = dest_imp (concl th)
          val xs = strip_conj l
          (*
          val x = el 2 xs
          *)
          fun inst_assum x =
            if not (is_forall x) then
              if not (is_from_to x) then
                tm_to_cv_debug (tm::stack) hyps (rand x)
              else let
                val ty = x |> rand |> type_of |> dest_type |> snd |> last
                in cv_typeLib.from_to_thm_for ty end
            else let
              val (vs,t) = strip_forall x
              val th1 = tm_to_cv_debug (tm::stack) hyps (rand t)
              val args = t |> rator |> rator |> rand |> strip_comb |> snd |> map rand
              val cv_args = args |> map (fn tm => mk_comb(from_for (type_of tm),tm))
              fun LIST_UNBETA_CONV [] = ALL_CONV
                | LIST_UNBETA_CONV xs =
                    UNBETA_CONV (last xs) THENC
                    RATOR_CONV (LIST_UNBETA_CONV (butlast xs))
              val th2 = th1 |> CONV_RULE
                                 ((RATOR_CONV o RATOR_CONV o RAND_CONV)
                                     (LIST_UNBETA_CONV cv_args) THENC
                                  (RATOR_CONV o RATOR_CONV o RATOR_CONV o RAND_CONV)
                                     (LIST_UNBETA_CONV args))
              in GENL vs th2 end
          val thms = map inst_assum xs
          val lemma = LIST_CONJ thms
          fun cv_rep_match_mp ith th = let
              val (l,r) = ith |> concl |> dest_imp
              val _ = if not (can (match_term l) (concl th))
                      then failwith "NO_MATCH (cv_rep_match_mp)" else ()
              val subst = (match_term l) (concl th)
              val res = MP (INST_TY_TERM subst ith) th
            in res end
          val th0 = cv_rep_match_mp th lemma
        in
          if not (is_imp (concl th0)) then th0 else
            failwith ("Oops! Function tm_to_cv should not fail on: " ^
                      term_to_string tm)
        end)
    | NONE =>
        if TypeBase.is_constructor (tm |> repeat rator) then let
          val ty = type_of tm
          val thms = cv_typeLib.rec_define_from_to ty
          in tm_to_cv_debug stack hyps tm end
        else if TypeBase.is_case tm then let
          val ty = tm |> strip_comb |> snd |> hd |> type_of
          val thms = cv_typeLib.rec_define_from_to ty
          in tm_to_cv_debug stack hyps tm end
        else raise (NeedsTranslation (stack, tm)))
    handle HOL_ERR e => raise (LocalException (stack, tm, HOL_ERR e))
  in tm_to_cv_debug [] hyps tm
     handle LocalException (stack, tm, e) => report_error stack tm e
  end

val cv_arith_rewrite_conv =
  REWRITE_CONV [cv_add_def, cv_sub_def, cv_mul_def, cv_div_def, cv_mod_def];

(*
val hyps = tl [(T,TRUTH)]
val tm = target_tm
*)

fun cv_rep_for hyps tm = let
  (* preprocessing *)
  fun fix_case_conv tm =
    if is_var tm orelse is_const tm then ALL_CONV tm
    else if is_abs tm then ABS_CONV fix_case_conv tm
    else if not (TypeBase.is_case tm) then
      (RATOR_CONV fix_case_conv THENC RAND_CONV fix_case_conv) tm
    else let
      val (name,x,_) = TypeBase.dest_case tm
      val { Thy = thy, Name = name, ... } = dest_thy_const name
      in if is_var x orelse (name = "COND" andalso thy = "bool")
         then (RATOR_CONV fix_case_conv THENC
               RAND_CONV fix_case_conv) tm
         else (UNBETA_CONV x THENC
               REWR_CONV (GSYM LET_THM) THENC
               fix_case_conv) tm end;
  fun rename_bound_vars_conv prefix = let
    fun descend_conv n tm =
      if is_var tm orelse is_const tm then ALL_CONV tm else
      if is_comb tm then
        (RATOR_CONV (descend_conv n) THENC RAND_CONV (descend_conv n)) tm
      else let
        val (v,rest) = dest_abs tm
        val new_v = mk_var(prefix ^ int_to_string n, type_of v)
        in (ALPHA_CONV new_v THENC ABS_CONV (descend_conv (n+1))) tm end
    in descend_conv 0 end
  fun fix_lam_pairs_conv tm =
    (if can pairSyntax.dest_pabs tm then let
      fun list_dest_pabs tm =
        let val (pat,rest) = pairSyntax.dest_pabs tm
            val (pats,rest) = list_dest_pabs rest
        in (pat::pats,rest) end handle HOL_ERR _ => ([],tm)
      val (pats,rest) = list_dest_pabs tm
      val new_v = numvariant (free_vars rest)
      val vs = mapi (fn i => fn v => if is_var v then (v,v)
                                     else (v,new_v (mk_var("p_" ^ int_to_string i,type_of v)))) pats
      fun mk_pair_case x v1 v2 rhs = let
        val pat_ty = pairSyntax.pair_case_tm |> type_of |> dest_type |> snd |> tl |> hd |> dest_type |> snd |> hd
        val f_tm = mk_abs(v1,mk_abs(v2,rhs))
        val i = match_type pat_ty (type_of f_tm)
        val right_pair_case  = inst i pairSyntax.pair_case_tm
        in list_mk_comb(right_pair_case,[x,f_tm]) end
      fun mk_tuple_case x pat rhs = let
        val (v1,v2) = pairSyntax.dest_pair pat
        in if is_var v2 then
             mk_pair_case x v1 v2 rhs
           else let
             val gv = genvar(type_of v2)
             val case_tm = mk_tuple_case gv v2 rhs
             in mk_pair_case x v1 gv case_tm end end
      fun create [] rest = rest
        | create ((pat,x)::pats) rest = if is_var pat then create pats rest else let
            val fixed_tm = create pats rest
            in mk_tuple_case x pat fixed_tm end
      val fixed_tm = create vs rest
      val new_tm = list_mk_abs(map snd vs,fixed_tm)
      val goal = mk_eq(tm,new_tm)
      val lemma = TAC_PROOF(([],goal),
        simp_tac std_ss [FUN_EQ_THM,pairTheory.FORALL_PROD,pairTheory.pair_CASE_def])
      in (REWR_CONV lemma THENC ABS_CONV fix_lam_pairs_conv) tm end else fail())
    handle HOL_ERR _ =>
      if is_var tm orelse is_const tm then ALL_CONV tm else
      if is_abs tm then (ABS_CONV fix_lam_pairs_conv) tm else
        (RATOR_CONV fix_lam_pairs_conv THENC RAND_CONV fix_lam_pairs_conv) tm;
  val preprocess_conv = fix_lam_pairs_conv THENC
                        REWRITE_CONV (cv_inline_thms()) THENC
                        remove_fupd_conv THENC
                        fix_case_conv THENC
                        rename_bound_vars_conv "v" THENC
                        REWRITE_CONV [if_eq_zero]
  val after_pre_th = QCONV preprocess_conv tm
  (* main function *)
  val tm = after_pre_th |> concl |> dest_eq |> snd
  val res0 = tm_to_cv hyps tm
  (* postprocessing *)
  val res1 = res0 |> CONV_RULE (cv_rep_hol_tm_conv (K (SYM after_pre_th)))
  val pre_simp_conv = DEPTH_CONV BETA_CONV
                      THENC REWRITE_CONV (cv_pre_thms())
                      THENC REWRITE_CONV [lt_zero,
                         fcpTheory.finite_bit0,fcpTheory.finite_bit1,
                         fcpTheory.finite_one,fcpTheory.finite_sum]
                      THENC REWRITE_CONV [GSYM implies_def]
                      THENC SIMP_CONV std_ss []
                      THENC REWRITE_CONV [implies_def]
  val res2 = res1 |> CONV_RULE (cv_rep_pre_conv pre_simp_conv)
  fun num_needs_eval tm =
    if cvSyntax.is_cv_num tm then
      not (can numSyntax.dest_numeral (rand tm))
    else false
  fun eval_where_needed_conv tm =
    if num_needs_eval tm then EVAL tm else
    if is_var tm orelse is_const tm then ALL_CONV tm else
    if is_abs tm then ABS_CONV eval_where_needed_conv tm else
    if not (is_cond tm) then
      (RATOR_CONV eval_where_needed_conv THENC
       RAND_CONV eval_where_needed_conv) tm
    else let
      val (b,_,_) = dest_cond tm
      val lemma = QCONV EVAL b
      val branch = lemma |> concl |> rand
      val thms = SPEC_ALL boolTheory.COND_CLAUSES |> CONJUNCTS
      val use_th = if aconv branch T then el 1 thms else
                   if aconv branch F then el 2 thms else
                     failwith ("Unable to EVAL term: " ^ term_to_string b)
      in ((RATOR_CONV o RATOR_CONV o RAND_CONV) (K lemma) THENC
          REWR_CONV use_th THENC eval_where_needed_conv) tm end
  fun term_nub [] = []
    | term_nub (tm::tms) = tm :: term_nub (filter (not o aconv tm) tms)
  fun unbeta_where_needed_conv tm = let
    fun is_f_var tm = is_comb tm andalso is_var (rand tm)
    val tms = find_terms is_f_var tm
    fun unbeta_each_conv [] = ALL_CONV
      | unbeta_each_conv (tm :: tms) = UNBETA_CONV tm THENC unbeta_each_conv tms
    in unbeta_each_conv (term_nub tms) tm end
  val cv_tm_simp_conv = DEPTH_CONV BETA_CONV
                        THENC rename_bound_vars_conv "cv"
                        THENC unbeta_where_needed_conv
                        THENC cv_arith_rewrite_conv
                        THENC eval_where_needed_conv
                        THENC DEPTH_CONV BETA_CONV
                        THENC REWRITE_CONV [cv_postprocess]
  val res3 = res2 |> CONV_RULE (cv_rep_cv_tm_conv cv_tm_simp_conv)
  in res3 end

(*
open cv_primTheory
open wordsLib

val hyps = tl [(T,TRUTH)]
val tm = ``((2w:word8) @@ (4w:word16)) : word64``

val tm = ``FOLDR (\(x,y) (z,t). (x + y,z +t)) (0n,0n) xs``

cv_rep_for hyps tm
*)

end
