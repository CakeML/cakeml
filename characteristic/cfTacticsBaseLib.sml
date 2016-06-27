structure cfTacticsBaseLib :> cfTacticsBaseLib =
struct

open HolKernel Parse boolLib bossLib preamble
open set_sepTheory helperLib ConseqConv

(*------------------------------------------------------------------*)
(** ConseqConv++ *)

infixr 3 THEN_DCC
infixr 3 ORELSE_DCC

fun CUSTOM_THEN_CONSEQ_CONV handler1 handler2 (c1:conv) c2 t =
    let
       val thm0_opt =
           SOME (c1 t) handle e => if handler1 e then NONE else raise e

       val t2 =
           if (isSome thm0_opt) then
             CONSEQ_CONV___GET_SIMPLIFIED_TERM (valOf thm0_opt) t
           else t;

       val thm1_opt =
           SOME (c2 t2) handle e => if handler2 e then NONE else raise e
    in
       if (isSome thm0_opt) andalso (isSome thm1_opt) then
         THEN_CONSEQ_CONV___combine (valOf thm0_opt) (valOf thm1_opt) t else
       if (isSome thm0_opt) then valOf thm0_opt else
       if (isSome thm1_opt) then valOf thm1_opt else
       raise UNCHANGED
    end

fun handle_none e = false
fun handle_UNCHANGED e = case e of UNCHANGED => true | _ => false

(* This has different semantics than [ConseqConv.THEN_CONSEQ_CONV], but I
   believe these are the right ones.

   Just like [Conv.THENC], it fails if either the first or the second conversion
   fails, while [ConseqConv.THEN_CONSEQ_CONV] handles a failure just like
   raising [UNCHANGED], which makes it impossible to make the first conversion
   abort a THEN_CONSEQ_CONV.
*)
val THEN_CONSEQ_CONV =
    CUSTOM_THEN_CONSEQ_CONV handle_UNCHANGED handle_UNCHANGED

fun ORELSE_CONSEQ_CONV (c1:conv) (c2:conv) t =
  c1 t handle HOL_ERR _ => c2 t

fun CUSTOM_THEN_DCC THEN_CC DCC1 DCC2 direction =
  THEN_CC (DCC1 direction) (DCC2 direction)

fun (DCC1 THEN_DCC DCC2) =
  CUSTOM_THEN_DCC THEN_CONSEQ_CONV DCC1 DCC2

fun (DCC1 ORELSE_DCC DCC2) direction =
  ORELSE_CONSEQ_CONV (DCC1 direction) (DCC2 direction)

fun EVERY_DCC [] direction t = raise UNCHANGED
  | EVERY_DCC (c1::L) direction t =
    (c1 THEN_DCC (EVERY_DCC L)) direction t

fun mk_binop_conseq_conv mono_thm =
  let
    fun cc_l_r cc1 cc2 t =
      let val (l,r) = dest_conj t
          val thm_l_r = CONJ (cc1 l) (cc2 r)
          val thm = GEN_ALL mono_thm
      in
        HO_MATCH_MP thm thm_l_r
      end
    fun cc_l cc = cc_l_r cc REFL_CONSEQ_CONV
    fun cc_r cc = cc_l_r REFL_CONSEQ_CONV cc
    fun cc_list assoc_left ccL =
      let fun aux ccL =
            case ccL of
                [] => (fn t => raise UNCHANGED)
              | [cc] => cc
              | cc1::cc2::ccs =>
                if assoc_left then
                  cc_l_r (aux (cc2::ccs)) cc1
                else
                  cc_l_r cc1 (aux (cc2::ccs)) in
        if assoc_left then aux (List.rev ccL) else aux ccL
      end
  in
    (cc_l_r, cc_l, cc_r, cc_list)
  end

val (CONJ_CONSEQ_CONV, CONJ1_CONSEQ_CONV, CONJ2_CONSEQ_CONV,
     CONJ_LIST_CONSEQ_CONV) =
    mk_binop_conseq_conv boolTheory.MONO_AND
val CONJ_LIST_CONSEQ_CONV = CONJ_LIST_CONSEQ_CONV false

val (DISJ_CONSEQ_CONV, DISJ1_CONSEQ_CONV, DISJ2_CONSEQ_CONV,
     DISJ_LIST_CONSEQ_CONV) =
    mk_binop_conseq_conv boolTheory.MONO_OR
val DISJ_LIST_CONSEQ_CONV = DISJ_LIST_CONSEQ_CONV false

val (IMP_CONSEQ_CONV, IMP_ASSUM_CONSEQ_CONV, IMP_CONCL_CONSEQ_CONV,
     IMP_LIST_CONSEQ_CONV) =
    mk_binop_conseq_conv boolTheory.MONO_IMP
val IMP_LIST_CONSEQ_CONV = IMP_LIST_CONSEQ_CONV false

fun print_cc t = (print_term t; print "\n\n"; REFL_CONSEQ_CONV t)
fun print_dcc direction t = (
  print_term t;
  print "\n\n";
  REFL_CONSEQ_CONV t
)

fun CHANGED_DCC dcc direction =
  CHANGED_CONSEQ_CONV (dcc direction)

fun QCHANGED_DCC dcc direction =
  QCHANGED_CONSEQ_CONV (dcc direction)

fun TOP_REDEPTH_CONSEQ_CONV dcc =
  let val STRICT_THEN = CUSTOM_THEN_CONSEQ_CONV handle_none handle_UNCHANGED
      val STRICT_THEN_DCC = CUSTOM_THEN_DCC STRICT_THEN
  in
    STRICT_THEN_DCC dcc (REDEPTH_CONSEQ_CONV dcc)
  end

end
