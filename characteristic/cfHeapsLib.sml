(*
  Conversions etc. over hprops
*)
structure cfHeapsLib :> cfHeapsLib =
struct

open preamble
open set_sepTheory helperLib ConseqConv
open cfHeapsBaseTheory cfHeapsTheory
open evarsConseqConvLib cfTacticsBaseLib cfHeapsBaseLib

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

fun hclean_one_conseq_conv_core ctx t =
  let
    val (_, pre, _) = dest_F_pre_post t
    val hs = list_dest dest_star pre
    fun rearrange_conv tm =
      let val rest = filter (not o aconv tm) hs in
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
          ]
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
          ]
        )
      else
        NONE
  in
    case find_map pull hs of
        NONE => raise UNCHANGED
      | SOME cc => cc t
  end

fun hclean_one_dcc_core ctx =
  STRENGTHEN_CONSEQ_CONV (hclean_one_conseq_conv_core ctx)

val hclean_setup_conv =
    F_pre_post_conv (QCONV heap_clean_conv) REFL

fun hclean_one_conseq_conv ctx =
  STRENGTHEN_CONSEQ_CONV hclean_setup_conv THEN_DCC
  (hclean_one_dcc_core ctx)

fun hclean_conseq_conv ctx =
  STRENGTHEN_CONSEQ_CONV hclean_setup_conv THEN_DCC
  EXT_DEPTH_CONSEQ_CONV
    (CONSEQ_CONV_get_context_congruences CONSEQ_CONV_FULL_CONTEXT)
    CONSEQ_CONV_default_cache_opt NONE true
    [(true, NONE, hclean_one_dcc_core)] ctx

val hclean_one = ASM_CONSEQ_CONV_TAC hclean_one_conseq_conv
val hclean = ASM_CONSEQ_CONV_TAC hclean_conseq_conv

(* demo:

   g `is_local CF ==>
      CF (H1 * emp * (H2 * SEP_EXISTS y. cond (P y)) * x ~~>> Refv xv * H3)
         Q`
   e strip_tac;
   e (hclean_one \\ strip_tac);
   e (hclean_one \\ strip_tac);

   (* or alternatively *)
   e strip_tac;
   e hclean

   g `CF (H * emp) Q : bool`
   e hclean

   g `CF (cond P * A * cond Q : hprop) (J:v -> hprop) : bool`
   e hclean
*)

(** hchange *)

infix then_ecc
infix THEN_DCC

fun hchange_apply_cc lemma_th cont_ecc1 cont_ecc2 =
  CONSEQ_TOP_REWRITE_CONV ([], [hchange_lemma], []) THEN_DCC
  STRENGTHEN_CONSEQ_CONV (
    ecc_conseq_conv (
      (conj_ecc
         (irule_ecc lemma_th)
         (conj_ecc cont_ecc1 cont_ecc2)) then_ecc
      hinst_ecc
    )
  )

(* todo: cf todo in xapply *)

val hcancel_cont_ecc =
  lift_conseq_conv_ecc (hcancel_conseq_conv CONSEQ_CONV_STRENGTHEN_direction)

val hsimpl_cont_ecc =
  lift_conseq_conv_ecc (hsimpl_conseq_conv CONSEQ_CONV_STRENGTHEN_direction)

val id_cont_ecc =
  lift_conseq_conv_ecc REFL_CONSEQ_CONV

fun hchange_core_cc lemma_th cont_ecc1 cont_ecc2 dir t = let
  val _ = cfHeapsBaseLib.dest_sep_imp t
  val cc =
    hpull_conseq_conv THEN_DCC
    DEPTH_CONSEQ_CONV (hchange_apply_cc lemma_th cont_ecc1 cont_ecc2)
in cc dir t end

fun hchange_conseq_conv th =
  hchange_core_cc th hcancel_cont_ecc id_cont_ecc

fun hchanges_conseq_conv th =
  hchange_core_cc th hcancel_cont_ecc hsimpl_cont_ecc

fun hchange_top th = CONSEQ_CONV_TAC (hchange_conseq_conv th)
fun hchanges_top th = CONSEQ_CONV_TAC (hchanges_conseq_conv th)
fun hchange th = DEPTH_CONSEQ_CONV_TAC (hchange_conseq_conv th)
fun hchanges th = DEPTH_CONSEQ_CONV_TAC (hchanges_conseq_conv th)

end
