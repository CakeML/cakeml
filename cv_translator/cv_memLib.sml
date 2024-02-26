(*
  The cv translator's state is handled by this Lib file
*)
structure cv_memLib :> cv_memLib =
struct

open HolKernel Abbrev Parse boolLib bossLib;
open cv_repTheory cvTheory;

val quiet = ref true;
fun cv_print s = if !quiet then () else print s;
fun cv_print_thm th = if !quiet then () else print_thm th;

(* Custom version of Lib.time *)
fun cv_time f x =
  if !quiet then f x else
  let val start = Time.now()
      val res = f x
      val finish = Time.now()
  in
    print ("Took " ^ Time.fmt 1 (finish - start) ^ " seconds.\n");
    res
  end

val cv_ty = cvSyntax.cv
val cv_rep_hol_tm = rand
val cv_rep_hol_tm_conv = RAND_CONV
val cv_rep_cv_tm = rand o rator o rator
val cv_rep_cv_tm_conv = RATOR_CONV o RATOR_CONV o RAND_CONV

fun is_cv_rep tm = let
  val (c,vs) = strip_comb tm
  val { Thy = thy, Name = name, ... } = dest_thy_const c
  in length vs = 4 andalso
     name = "cv_rep" andalso
     thy = "cv_rep" end handle HOL_ERR _ => false;

(*--------------------------------------------------------------------------*
   Reused function
 *--------------------------------------------------------------------------*)

fun register_ThmSetData_list tag_name update_fun = let
  fun update_fun_append th ths = update_fun th @ ths
  fun apply_delta (ThmSetData.ADD(_, th)) xs = update_fun_append th xs
    | apply_delta _                       xs = xs;
  val { get_global_value = the_list, update_global_value = updater, ... } =
      ThmSetData.export_with_ancestry {
        settype = tag_name,
        delta_ops = {apply_to_global = apply_delta,
                     uptodate_delta = K true,
                     thy_finaliser = NONE,
                     initial_value = [],
                     apply_delta = apply_delta}
      };
  in (the_list, fn th => updater (update_fun_append th)) end;

(*--------------------------------------------------------------------------*
   Reformulate in terms of cv_rep (for use by cv_repLib and cv_transLib)
 *--------------------------------------------------------------------------*)

fun formulate_cv_rep th =
  if is_cv_rep (th |> UNDISCH_ALL |> concl) then th else let
  val th0 = (if is_imp (concl th) then th else DISCH T th)
  val th1 = th0 |> CONV_RULE (REWR_CONV (GSYM cv_rep_def))
  val cv_tm = cv_rep_cv_tm (concl th1)
  val cv_vs = cv_tm |> free_vars
  val hol_vs = cv_rep_hol_tm (concl th1) |> free_vars
  val joint = filter (fn v => List.exists (aconv v) hol_vs) cv_vs
  fun lift_each [] th = th
    | lift_each (v::vs) th1 = let
    val name = dest_var v |> fst
    val p = mk_var("p_" ^ name, bool)
    val cv = mk_var("cv_" ^ name, cv_ty)
    val t = find_term (fn tm => is_comb tm andalso aconv (rand tm) v) cv_tm
    val th2 = th1 |> CONV_RULE (cv_rep_cv_tm_conv (UNBETA_CONV t))
    val th3 = MATCH_MP cv_rep_assum th2 |> SPECL [cv,p] |> UNDISCH
    val th4 = th3 |> CONV_RULE (cv_rep_cv_tm_conv BETA_CONV)
    in lift_each vs th4 end
  val th7 = lift_each joint th1
  val th8 = th7 |> DISCH_ALL |> PURE_REWRITE_RULE [AND_IMP_INTRO,GSYM CONJ_ASSOC]
  in th8 end;

fun formulate_cv_reps th = let
  val thms = CONJUNCTS (SPEC_ALL th)
  in map formulate_cv_rep thms end

fun show_cv_rep do_print cv_rep_th = let
  val pat = cv_rep_th |> UNDISCH_ALL |> concl |> rand
  val s = map (fn v => v |-> mk_var("_",type_of v)) (free_vars pat)
  val _ = (if do_print then
             (print "Able to translate: "; print_term (subst s pat))
           else ())
  in (pat, cv_rep_th) end

fun prepare do_print th = let
  val cv_rep_thms = formulate_cv_reps th
  in map (show_cv_rep do_print) cv_rep_thms end

(*--------------------------------------------------------------------------*
   Database for cv_rep, cv_pre, cv_inline, cv_from_to
 *--------------------------------------------------------------------------*)

fun insert_cv_rep th = prepare (not (!quiet)) th;
val (cv_rep_thms, cv_rep_add) = register_ThmSetData_list "cv_rep" insert_cv_rep;

fun insert_cv_pre th = (cv_print "\ncv_pre:\n\n"; cv_print_thm th; cv_print "\n\n"; [th])
val (cv_pre_thms, cv_pre_add) = register_ThmSetData_list "cv_pre" insert_cv_pre;

fun insert_cv_inline th = (cv_print "\ncv_inline:\n\n"; cv_print_thm th; cv_print "\n\n"; [th])
val (cv_inline_thms, cv_inline_add) = register_ThmSetData_list "cv_inline" insert_cv_inline;

fun insert_cv_from_to th = (cv_print "\ncv_from_to:\n\n"; cv_print_thm th; cv_print "\n\n"; [th])
val (cv_from_to_thms, cv_from_to_add) = register_ThmSetData_list "cv_from_to" insert_cv_from_to;

end
