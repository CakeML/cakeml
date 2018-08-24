structure evarsConseqConvLib :> evarsConseqConvLib =
struct

open preamble
open ConseqConv ConseqConvTheory quantHeuristicsTools

val ERR = mk_HOL_ERR "evarsConseqConvLib";

type evars = term list
type term_with_evars = {term: term, evars: evars}
type evars_instantiation = {instantiation: (term, term) subst,
                            new_evars: evars}

type evars_conseq_conv = term_with_evars -> evars_instantiation * thm


fun all_new_evars (old_evars: term list) {instantiation, new_evars} =
  let
    val old_evars_instantiated = List.map (Term.subst instantiation) old_evars
    val new_vars = (free_varsl old_evars_instantiated) @ new_evars
    val all_new_evars = filter (fn v => tmem v (new_evars @ old_evars)) new_vars
  in all_new_evars end

fun all_new_evars_in old_evars inst term =
  let
    val all_new_evars = all_new_evars old_evars inst
    val fvs_term = free_vars term
  in op_intersect aconv all_new_evars fvs_term end

(** The original implementation on which are based ecc_conseq_conv and
    match_mp_ecc is due to Thomas Tuerk. *)

(* todo:
   - be also able to unify types
*)
fun ecc_conseq_conv (ecc: evars_conseq_conv) (t: term): thm =
let
  fun pr s thm = (
    print (s ^ ": "); print_thm thm; print "\n"
  )

  val (evars, t_body) = strip_exists t
  val (inst, thm) = ecc {term = t_body, evars = evars}
  val sub = #instantiation inst
  (* safety check: we allow the instantiation to contain "junk" redexes, but not
     ones that appear in [t_body] and that are not evars *)
  val t_body_fvs = free_vars t_body
  val _ = app (fn {redex, ...} =>
    if not (tmem redex evars) andalso tmem redex t_body_fvs then (
      (* print "redex: "; print_term redex; print "\n"; *)
      raise (ERR "Trying to instantiate something that is not an evar"
                 "ecc_conseq_conv")
    ) else ()) sub

  (* figure out finally existentially quantified vars *)
  val new_evars = all_new_evars evars inst
  (* val _ = ( *)
  (*   print "new_evars:"; *)
  (*   app (fn v => (print " "; print_term v)) new_evars; *)
  (*   print "\n" *)
  (* ) *)

  val t_body' = subst sub t_body
  val thm =
      let
        val (l, r) = (dest_eq o concl) thm
        val (L, R) = EQ_IMP_RULE thm
      in if t_body' ~~ l then R else L end
      handle HOL_ERR _ => thm

  val thm0 = let
    val thma = LIST_EXISTS_INTRO_IMP new_evars thm
  in CONV_RULE (LAND_CONV (TRY_CONV LIST_EXISTS_SIMP_CONV)) thma end
  (* val _ = pr "thm0" thm0 *)

  val thm1 = let
    val thm1a = ASSUME (Term.subst sub t_body)
    (* val _ = pr "thm1a" thm1a *)
    val (_, thm1b) = foldr (fn (v, (t, thm)) =>
      let val t' = mk_exists (v, t) in
        (t', EXISTS (Term.subst sub t', Term.subst sub v) thm)
      end) (t_body, thm1a) evars
    (* val _ = pr "thm1b" thm1b *)
    val thm1c = foldr (fn (v, thm) => SIMPLE_CHOOSE v thm) thm1b new_evars
  in
    DISCH_ALL thm1c
  end
  (* val _ = pr "thm1" thm1 *)
in
  IMP_TRANS thm0 thm1
end

fun match_mp_ecc thm {term = t, evars} =
let
  fun pr s thm = (
    print (s ^ ": "); print_thm thm; print "\n"
  )

  (* make sure variables are distinct, this is important for
     later unification *)
  val rewr_thm = CONV_RULE (VARIANT_CONV (free_vars t)) thm
  (* val _ = pr "rewr_thm" rewr_thm *)

  (* if [rewr_thm] is not of the form [|- !x1..xn. P ==> Q], but
     [|- !x1..xn. P], use [|- !x1..xn. T ==> P] instead *)
  val rewr_thm =
    if not (is_imp (snd (strip_forall (concl rewr_thm)))) then
      CONV_RULE (STRIP_QUANT_CONV (REWR_CONV (GSYM IMP_CLAUSES_TX))) rewr_thm
    else
      rewr_thm

  (* destruct the rewr_thm *)
  val (quant_vars, rewr_concl, rewr_pre) = let
    val (vs, t0) = strip_forall (concl rewr_thm)
    val (t2, t1) = dest_imp_only t0
  in
    (vs, t1, t2)
  end

  val t_rigids = op_set_diff aconv (free_vars t) evars
  val rewr_rigids = op_set_diff aconv (free_vars rewr_concl) quant_vars

  (* val _ = ( *)
  (*   print "t_rigids:"; app (fn v => (print " "; print_term v)) t_rigids; print "\n"; *)
  (*   print "rewr_rigids:"; app (fn v => (print " "; print_term v)) rewr_rigids; print "\n"; *)
  (*   print "quant_vars:"; app (fn v => (print " "; print_term v)) quant_vars; print "\n" *)
  (* ) *)

  (* val _ = (print "rewr_concl: "; print_term rewr_concl; print "\n") *)
  (* val _ = (print "t: "; print_term t; print "\n") *)

  (* Try to unify *)
  val sub = Unify.simp_unify_terms (t_rigids @ rewr_rigids)
              rewr_concl t
  (* val _ = app (fn {redex, residue} => ( *)
  (*   print_term redex; print " -> "; print_term residue; print "\n" *)
  (* )) sub *)
  (* val _ = print "unify success\n" *)

  (* figure out the new evars *)
  val new_evars = let
    val evars' = List.map (Term.subst sub) (quant_vars @ evars)
    val s0 = HOLset.listItems (FVL evars' empty_tmset)
    (* we don't include the old evars that also are new evars *)
    val s1 = Lib.filter (fn v => tmem v quant_vars) s0
  in s1 end
  (* val _ = ( *)
  (*   print "new_evars:"; app (fn v => (print " "; print_term v)) new_evars; print "\n" *)
  (* ) *)

  val thm' = let
    val inst_l = List.map (Term.subst sub) quant_vars
  in ISPECL inst_l rewr_thm end
  (* val _ = pr "thma" thm' *)

  val inst = filter (fn {redex, ...} => tmem redex evars) sub
in
  ({instantiation = inst, new_evars = new_evars}, thm')
end

(** Testing:

  val P_def = Define `P (x : num) (y : bool) = T`
  val Q_def = Define `Q (x : num) (y : num) = T`

  val dummy_imp = Q.prove (`
    !x y z (z' : num). Q x (z + y + z') ==> P (z + x) (y > x)`,
  REWRITE_TAC[P_def]);

  val dummy_imp2 = Q.prove (`
    !x y z. P (z + x) (y > x)`,
  REWRITE_TAC[P_def]);

  val t = ``?(a:'a) x c y. P (5 + (x + 2)) ((c:num) > y)``

  ecc_conseq_conv (match_mp_ecc dummy_imp) t;
  ecc_conseq_conv (match_mp_ecc dummy_imp2) t;
*)

fun irule_ecc thm = match_mp_ecc (IRULE_CANON thm)

fun instantiate_ecc inst_f etm = let
  val inst = inst_f etm
  val th = REFL_CONSEQ_CONV (subst (#instantiation inst) (#term etm))
in
  (inst, th)
end

fun lift_conseq_conv_ecc (cc: conseq_conv) {term, evars} =
  ({instantiation = [], new_evars = []}, cc term)

fun term_subst_then
      (subst1: (term, term) subst)
      (subst2: (term, term) subst):
    (term, term) subst =
  subst2 @
  (List.map (fn {redex,residue} =>
     {redex = redex, residue = Term.subst subst2 residue}
   ) subst1)

infix then_ecc;
infix orelse_ecc;

(* todo: handle eccs raising UNCHANGED *)
fun (ecc1 then_ecc ecc2) {term, evars} =
  let
    val (inst1, thm1) = ecc1 {term = term, evars = evars}
    val subst1 = #instantiation inst1
    val term1 = CONSEQ_CONV___GET_SIMPLIFIED_TERM thm1 (Term.subst subst1 term)
    val evars1 = all_new_evars evars inst1
    val thm1gen = GENL evars1 thm1

    val (inst2, thm2) = ecc2 {term = term1, evars = evars1}
    val subst2 = #instantiation inst2
    val evars2 = all_new_evars evars1 inst2

    val thm1_with_evars2 =
      SPECL (List.map (fn v => Term.subst subst2 v) evars1) thm1gen
    val subst_1_2 = term_subst_then subst1 subst2
    val thm_1_2 = THEN_CONSEQ_CONV___combine
      thm1_with_evars2 thm2 (Term.subst subst_1_2 term)
  in
    ({instantiation = subst_1_2, new_evars = evars2}, thm_1_2)
  end

(* Testing

  val P_def = Define `P (x : num) (y : bool) = T`
  val Q_def = Define `Q (x : num) (y : num) = T`
  val R_def = Define `R (x : num) (y : num) (z: num) (z': num) = T`

  val imp1 = Q.prove (`
    !x y z (z' : num). Q x (z + y + z') ==> P (z + x) (y > x)`,
  REWRITE_TAC[P_def]);

  val imp2 = Q.prove (`
    !(x:num) y z z'. R x y z z' ==> Q (x + y) (z + z')`,
  REWRITE_TAC[Q_def]);

  val t = ``?(a:'a) x (c:num) y. P (5 + (x + 2)) (c > y)``

  conseq_conv_ecc ((match_mp_ecc imp1) then_ecc (match_mp_ecc imp2)) t;
*)

fun (ecc1 orelse_ecc ecc2) g = ecc1 g handle HOL_ERR _ => ecc2 g
fun repeat_ecc ecc g =
  ((ecc then_ecc repeat_ecc ecc) orelse_ecc
   (lift_conseq_conv_ecc REFL_CONSEQ_CONV)) g

fun conj1_ecc (ecc: evars_conseq_conv) {term, evars} =
  let val (tm1, tm2) = dest_conj term
      val tm2_fvs = free_vars tm2
      val ctx = free_varsl [tm1, tm2]
      val ({instantiation, new_evars}, thm) = ecc {term = tm1, evars = evars}
      val (inst_fresh, new_evars) = foldl (fn (ev, (inst, new_evs)) =>
          if tmem ev tm2_fvs then let
            val ev' = variant ctx ev
          in ({redex = ev, residue = ev'} :: inst, ev' :: new_evs) end
          else (inst, ev :: new_evs)
        ) ([], []) new_evars
      val instantiation' = map (fn {redex, residue} =>
          {redex = redex, residue = subst inst_fresh residue}
        ) instantiation
      val thm' = INST inst_fresh thm
      val full_thm =
          cfTacticsBaseLib.CONJ1_CONSEQ_CONV
            (K thm') (subst instantiation' term)
  in ({instantiation = instantiation',
       new_evars = new_evars},
      full_thm)
  end

fun conj2_ecc (ecc: evars_conseq_conv) {term, evars} =
  let val (tm1, tm2) = dest_conj term
      val tm1_fvs = free_vars tm1
      val ctx = free_varsl [tm1, tm2]
      val ({instantiation, new_evars}, thm) = ecc {term = tm2, evars = evars}
      val (inst_fresh, new_evars) = foldl (fn (ev, (inst, new_evs)) =>
          if tmem ev tm1_fvs then let
            val ev' = variant ctx ev
          in ({redex = ev, residue = ev'} :: inst, ev' :: new_evs) end
          else (inst, ev :: new_evs)
        ) ([], []) new_evars
      val instantiation' = map (fn {redex, residue} =>
          {redex = redex, residue = subst inst_fresh residue}
        ) instantiation
      val thm' = INST inst_fresh thm
      val full_thm =
          cfTacticsBaseLib.CONJ2_CONSEQ_CONV
            (K thm') (subst instantiation' term)
  in ({instantiation = instantiation',
       new_evars = new_evars},
      full_thm)
  end

fun conj_ecc ecc1 ecc2 = (conj1_ecc ecc1) then_ecc (conj2_ecc ecc2)

end
