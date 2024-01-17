(*
  Miscellaneous functions used in cv automation
*)
structure cv_miscLib :> cv_miscLib =
struct

open HolKernel Parse boolLib bossLib cvTheory cv_repTheory;

val cv_rep_hol_tm_conv = RAND_CONV
val cv_rep_from_conv  = RATOR_CONV o RAND_CONV
val cv_rep_cv_tm_conv = RATOR_CONV o RATOR_CONV o RAND_CONV
val cv_rep_pre_conv = RATOR_CONV o RATOR_CONV o RATOR_CONV o RAND_CONV

val cv_rep_hol_tm = rand
val cv_rep_from  = rand o rator
val cv_rep_cv_tm = rand o rator o rator
val cv_rep_pre = rand o rator o rator o rator

fun mk_cv_rep pre cv ret_from r =
  cv_rep_def |> ISPECL [pre,cv,ret_from,r] |> concl |> dest_eq |> fst;

fun is_cv_proj tm = let
  val (c,args) = strip_comb tm
  val { Thy = thy, Name = name, ... } = dest_thy_const c
  in thy = "cv_rep" andalso name = "cv_proj" andalso length args = 2 end
  handle HOL_ERR _ => false;

fun dest_cv_proj tm =
  if is_cv_proj tm then (rand (rator tm), rand tm) else failwith "dest_cv_proj";

val cv_sum_depth_tm = cv_sum_depth_def |> CONJUNCT1 |> SPEC_ALL
                        |> concl |> dest_eq |> fst |> repeat rator;
fun mk_cv_sum_depth tm = mk_comb(cv_sum_depth_tm, tm);

val remove_fupd_conv = let
  fun rpt_ABS_CONV c tm =
    if is_abs tm then ABS_CONV (rpt_ABS_CONV c) tm else c tm;
  fun smart_dest_fupd tm = let
    val (x,y) = dest_comb tm
    val (x1,x2) = dest_comb x
    val (s,upd_ty) = dest_const x1
    val _ = String.isSuffix "_fupd" s orelse fail()
    fun dest_arrow ty =
      case dest_thy_type ty of
        {Args = [d,y], Thy = "min", Tyop = "fun"} => (d,y)
      | _ => fail()
    val ty = upd_ty |> dest_arrow |> snd |> dest_arrow |> fst
    val rest = (snd (smart_dest_fupd y) handle HOL_ERR _ => y)
    in (ty,rest) end
  fun del_fupd_conv tm = let
    val (ty,rest) = smart_dest_fupd tm
    val cases_of_def = TypeBase.nchotomy_of ty
    val case_of_def = TypeBase.case_def_of ty
    val case_tm = TypeBase.case_const_of ty
    val updates_def = TypeBase.updates_of ty
    val f = mk_var("f",ty --> type_of rest)
    val x = mk_var("x",ty)
    val cons_tm = cases_of_def |> SPEC_ALL |> concl |> repeat (snd o dest_exists) |> rand
    val rhs_tm = mk_comb(f,cons_tm)
    val args = strip_comb cons_tm |> snd
    val r_tm = mk_icomb(mk_icomb(case_tm,x),list_mk_abs(args,rhs_tm))
    val goal = mk_eq(mk_comb(f,x),r_tm)
    val to_lemma = TAC_PROOF (([],goal),
      strip_assume_tac (ISPEC x cases_of_def)
      \\ asm_rewrite_tac [case_of_def]
      \\ CONV_TAC (DEPTH_CONV BETA_CONV) \\ rewrite_tac [])
    val y = mk_var("y",type_of rest)
    val goal = mk_eq(mk_icomb(mk_icomb(case_tm,x),list_mk_abs(args,y)),y)
    val remove = TAC_PROOF (([],goal),
      strip_assume_tac (ISPEC x cases_of_def)
      \\ asm_rewrite_tac [case_of_def]
      \\ CONV_TAC (DEPTH_CONV BETA_CONV) \\ rewrite_tac [])
    in (UNBETA_CONV rest THENC REWR_CONV to_lemma THENC
        RAND_CONV (rpt_ABS_CONV BETA_CONV) THENC
        PURE_REWRITE_CONV (remove :: combinTheory.K_THM :: updates_def)) tm end
  in TOP_DEPTH_CONV del_fupd_conv end;

val _ = temp_overload_on("Num",cvSyntax.cv_num_tm);
val _ = temp_overload_on("Pair",cvSyntax.cv_pair_tm);

end
