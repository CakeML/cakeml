structure cfHeapsLib :> cfHeapsLib =
struct

open HolKernel Parse boolLib bossLib preamble
open set_sepTheory helperLib ConseqConv
open cfHeapsBaseTheory cfTacticsBaseLib cfHeapsBaseLib
open cfHeapsTheory

infix 3 THEN_DCC
infix 3 ORELSE_DCC

(* Auxiliary functions *)

fun dest_F_pre_post tm =
  (rator (rator tm), rand (rator tm), rand tm)

fun F_pre_post_conv conv_pre conv_post =
  RAND_CONV conv_post THENC
  RATOR_CONV (RAND_CONV conv_pre)

(* [hclean]; similar to [hpull], but for terms of the form [F H Q],
   where F is local *)

fun prove_local_conseq_conv ctx =
  let
    val ctx = map
      (* turn theorems of the context from [|- !x1..xn. P] to
         [|- !x1..xn. T ==> P] *)
      (CONV_RULE (STRIP_QUANT_CONV (REWR_CONV
        (GSYM ConseqConvTheory.IMP_CLAUSES_TX))))
      ctx
    val ctx = (GSYM local_is_local) :: ctx
    val ctx_cc = map (fn thm =>
      CHANGED_CONSEQ_CONV (
        CONSEQ_TOP_REWRITE_CONV ([], [thm], [])
          CONSEQ_CONV_STRENGTHEN_direction)) ctx
  in FIRST_CONSEQ_CONV ctx_cc end

fun hclean_base ctx t =
  let
    val (_, pre, _) = dest_F_pre_post t
    val hs = list_dest dest_star pre
    fun rearrange_conv tm =
      let val rest = filter (fn tm' => tm' <> tm) hs in
        F_pre_post_conv (rearrange_star_conv tm rest) REFL
      end
    fun try_prove_local_cc t =
      THEN_CONSEQ_CONV
        (CONJ1_CONSEQ_CONV (prove_local_conseq_conv ctx))
        (REWR_CONV ConseqConvTheory.AND_CLAUSES_TX) t
      handle HOL_ERR _ => raise UNCHANGED
    fun pull tm =
      if is_cond tm then
        SOME (
          EVERY_CONSEQ_CONV [
            rearrange_conv tm,
            CONSEQ_TOP_HO_REWRITE_CONV
              ([], [hclean_prop, hclean_prop_single], [])
              CONSEQ_CONV_STRENGTHEN_direction,
            try_prove_local_cc
          ],
          IMP_CONCL_CONSEQ_CONV
        )
      else if is_sep_exists tm then
        SOME (
          EVERY_CONSEQ_CONV [
            rearrange_conv tm,
            CONSEQ_TOP_HO_REWRITE_CONV
              ([], [hclean_exists_single], [])
              CONSEQ_CONV_STRENGTHEN_direction,
            CONJ2_CONSEQ_CONV
              (REDEPTH_STRENGTHEN_CONSEQ_CONV (REDEPTH_CONV BETA_CONV)),
            try_prove_local_cc
          ],
          STRIP_FORALL_CONSEQ_CONV
        )
      else
        NONE
  in find_map pull hs end

val hclean_setup_conv =
    F_pre_post_conv (QCONV (SIMP_CONV bool_ss [SEP_CLAUSES])) REFL

fun hclean_one_conseq_conv ctx =
  STRENGTHEN_CONSEQ_CONV hclean_setup_conv THEN_DCC
  STRENGTHEN_CONSEQ_CONV
    (ITERATED_STEP_CONSEQ_CONV (hclean_base ctx))

fun hclean_conseq_conv ctx =
  STRENGTHEN_CONSEQ_CONV hclean_setup_conv THEN_DCC
  STRENGTHEN_CONSEQ_CONV
    (ITERATED_LOOP_CONSEQ_CONV (hclean_base ctx))
  
val hclean_one = ASM_CONSEQ_CONV_TAC hclean_one_conseq_conv
val hclean = ASM_CONSEQ_CONV_TAC hclean_conseq_conv

(* demo:

   g `is_local CF ==>
      CF (H1 * emp * (H2 * SEP_EXISTS y. cond (P y)) * x ~~> Refv xv * H3)
         Q`
   e strip_tac;
   e (hclean_one \\ strip_tac);
   e (hclean_one \\ strip_tac);

   (* or alternatively *)
   e strip_tac;
   e hclean

   g `CF (H * emp) Q : bool`
   e hclean
*)
end
