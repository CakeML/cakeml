(**
  Proof of Sturm's theorem, ported from Harrison material
**)
open pred_setTheory listTheory bossLib RealArith realTheory polyTheory;
open renameTheory;
open preambleDandelion;

val _ = new_theory "sturm";

(** HOL-Light compatibility **)
val REAL_MUL_AC = REAL_MUL_ASSOC;
val SPEC = Q.SPEC;
val SPECL = Q.SPECL;
val REAL_ARITH = fn t => REAL_ARITH (Term t);
val SUBGOAL_THEN = fn t => SUBGOAL_THEN (Term t);
val UNDISCH_TAC = fn t => UNDISCH_TAC (Term t);
val EXISTS_TAC = fn t => EXISTS_TAC (Term t);
val GEN_REWRITE_TAC = jrhUtils.GEN_REWR_TAC;

(* ========================================================================= *)
(* Formalization of Sturm sequences and Sturm's theorem.                     *)
(* ========================================================================= *)

(**
do_list override_interface
 ["divides",`poly_divides:real list->real list->bool`;
  "exp",`poly_exp:real list -> num -> real list`;
   "diff",`poly_diff:real list->real list`];; **)

(* ------------------------------------------------------------------------- *)
(* Dreary lemmas about sign alternations.                                    *)
(* ------------------------------------------------------------------------- *)

Theorem SIGN_LEMMA0:
  ! a b c:real.
    &0 < a /\ &0 < b /\ &0 < c ==>
    &0 < a * b /\ &0 < a * c /\ &0 < b * c
Proof
  rpt strip_tac >> irule REAL_LT_MUL >> gs[]
QED

Theorem SIGN_LEMMA1:
  !a b c:real. a * b > &0 ==> (c * a < &0 <=> c * b < &0)
Proof
  REPEAT GEN_TAC >> REWRITE_TAC[real_gt]
  >> REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (SPEC `a:real` REAL_LT_NEGTOTAL)
  >> REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (SPEC `b:real` REAL_LT_NEGTOTAL)
  >> REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (SPEC `c:real` REAL_LT_NEGTOTAL)
  >> ASM_REWRITE_TAC[REAL_MUL_RZERO, REAL_MUL_LZERO, REAL_LT_REFL]
  >> POP_ASSUM_LIST(MP_TAC o MATCH_MP SIGN_LEMMA0 o end_itlist CONJ)
  >> REWRITE_TAC[REAL_MUL_LNEG, REAL_MUL_RNEG, REAL_NEG_NEG]
  >> REWRITE_TAC[REAL_MUL_AC] >> REAL_ARITH_TAC
QED

Theorem SIGN_LEMMA2:
  !a b c:real. a * b > &0 ==> (a * c < &0 <=> b * c < &0)
Proof
  REPEAT GEN_TAC
  >> DISCH_THEN(MP_TAC o SPEC_ALL o MATCH_MP SIGN_LEMMA1)
  >> REAL_ARITH_TAC
QED

Theorem SIGN_LEMMA3:
  !a b:real. a < &0 ==> (a * b > &0 <=> b < &0)
Proof
  REPEAT GEN_TAC
  >> REWRITE_TAC[REAL_ARITH `a:real < &0 <=> -(&1) * a > &0`]
  >> DISCH_THEN(MP_TAC o MATCH_MP SIGN_LEMMA1)
  >> DISCH_THEN(MP_TAC o SPEC `-b`)
  >> REWRITE_TAC[REAL_MUL_AC, real_gt, REAL_MUL_LNEG, REAL_MUL_RNEG,
              REAL_NEG_NEG, REAL_MUL_LID, REAL_MUL_RID] >> REAL_ARITH_TAC
QED

Theorem SIGN_LEMMA5:
   (a:real) * b < &0 <=> a > &0 /\ b < &0 \/ a < &0 /\ b > &0
Proof
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
                (SPEC `a:real` REAL_LT_NEGTOTAL)
  >> REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (SPEC `b:real` REAL_LT_NEGTOTAL)
  >> gs[REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_LT_REFL, real_gt]
  >> POP_ASSUM_LIST(MP_TAC o end_itlist CONJ)
  >> DISCH_THEN(fn th => MP_TAC th >> ASSUME_TAC th)
  >-(
    POP_ASSUM(MP_TAC o MATCH_MP REAL_LT_MUL)
    >> REWRITE_TAC[REAL_MUL_LNEG, REAL_MUL_RNEG, REAL_NEG_NEG]
    >> REAL_ARITH_TAC)
  >- (
    rpt strip_tac >> ‘0 = a * 0’ by REAL_ARITH_TAC
    >> pop_assum $ once_rewrite_tac o single
    >> irule REAL_LT_LMUL_IMP >> gs[])
  >- (
    rpt strip_tac >> ‘0 = 0 * b’ by REAL_ARITH_TAC
    >> pop_assum $ once_rewrite_tac o single
    >> irule REAL_LT_RMUL_IMP >> gs[])
  >> rpt strip_tac >> EQ_TAC >> rpt strip_tac >>  gs[]
  >- (
    ‘0 < -a ∧ 0 < -b’ by (conj_tac >> REAL_ASM_ARITH_TAC)
    >> ‘0 < -a * -b’ by (irule REAL_LT_MUL >> gs[])
    >> gs[REAL_MUL_LNEG, REAL_MUL_RNEG, REAL_NEG_NEG]
    >> ‘0 < 0’ by REAL_ASM_ARITH_TAC
    >> gs[])
  >> REAL_ASM_ARITH_TAC
QED

Theorem SIGN_LEMMA4:
  !a b c:real. a * b < &0 /\ ~(c = &0) ==> (c * a < &0 <=> ~(c * b < &0))
Proof
  REPEAT STRIP_TAC
  >> MP_TAC(SPECL [`a:real`, `-b`, `c:real`] SIGN_LEMMA2)
  >> ASM_REWRITE_TAC[REAL_MUL_RNEG, real_gt]
  >> ASM_REWRITE_TAC[REAL_ARITH `&0 < -a:real <=> a:real < &0`]
  >> REWRITE_TAC[REAL_MUL_AC] >> DISCH_THEN SUBST1_TAC
  >> REWRITE_TAC[REAL_MUL_RNEG, REAL_MUL_AC]
  >> SUBGOAL_THEN `~((b:real) * (c:real) = &0)` MP_TAC
  >- (
    ASM_REWRITE_TAC[REAL_ENTIRE, DE_MORGAN_THM]
    >> DISCH_TAC >> UNDISCH_TAC `(a:real) * (b:real) < &0`
    >> ASM_REWRITE_TAC[REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_LT_REFL]
  )
  >> rpt strip_tac >> EQ_TAC >> strip_tac >> gs[SIGN_LEMMA5]
  >> REAL_ASM_ARITH_TAC
QED

Theorem SIGN_LEMMA6:
  !a b:real. a * b <= &0 <=> a >= &0 /\ b <= &0 \/ a <= &0 /\ b >= &0
Proof
  REWRITE_TAC[real_ge, REAL_LE_LT, REAL_ENTIRE, SIGN_LEMMA5] >> rpt gen_tac
  >> Cases_on `a = &0` >> Cases_on `b = &0`
  >> ASM_REWRITE_TAC[REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_LT_REFL]
  >> REWRITE_TAC[real_gt]
  >> (REAL_ARITH_TAC ORELSE metis_tac[])
QED

(* ------------------------------------------------------------------------- *)
(* The number of variations in sign of a list of reals.                      *)
(* ------------------------------------------------------------------------- *)

Definition varrec_def:
  varrec prev [] = 0 ∧
  varrec prev (CONS h t) =
    if prev * (h:real) < &0 then SUC(varrec h t)
    else if h = &0 then varrec prev t
    else varrec (h:real) (t:real list)
End

Definition variation_def:
  variation (l:real list) = varrec (&0) (l:real list)
End

(* ------------------------------------------------------------------------- *)
(* Show that it depends only on the sign of the "previous element".          *)
(* ------------------------------------------------------------------------- *)

Theorem VARREC_SIGN:
  !(l:real list) (r s:real). r * s > &0 ==> (varrec r l = varrec s l)
Proof
  Induct_on ‘l’ >> REPEAT GEN_TAC >> REWRITE_TAC[varrec_def]
  >> DISCH_TAC
  >> FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP SIGN_LEMMA2 th])
  >> Cases_on `s * h < &0` >> ASM_REWRITE_TAC[]
  >> COND_CASES_TAC >> REWRITE_TAC[]
  >> FIRST_ASSUM MATCH_MP_TAC >> ASM_REWRITE_TAC[]
QED

(* ------------------------------------------------------------------------- *)
(* Middle is irrelevant if surrounding elements have opposite sign.          *)
(* ------------------------------------------------------------------------- *)

Theorem VARREC_STRADDLE:
 !f g h x.
   poly f x * poly h x < &0 ⇒
   (varrec (poly f x) (MAP (\p. poly p x) (CONS g (CONS h l))) =
    SUC (varrec (poly h x) (MAP (\p. poly p x) l)))
Proof
  REPEAT GEN_TAC >> REWRITE_TAC[listTheory.MAP, varrec_def]
  >> Cases_on `poly h x = &0`
  >> Cases_on `poly g x = &0`
  >> ASM_REWRITE_TAC[REAL_MUL_LZERO, REAL_MUL_RZERO, real_gt, REAL_LT_REFL]
  >- (gs[])
  >> DISCH_TAC >> ASM_REWRITE_TAC[]
  >> jrhUtils.GEN_REWR_TAC (LAND_CONV o RATOR_CONV o RATOR_CONV o RAND_CONV o LAND_CONV)
   [REAL_MUL_SYM]
  >> MP_TAC(SPECL [`poly f x`, `poly h x`, `poly g x`] SIGN_LEMMA4)
  >> ASM_REWRITE_TAC[] >> DISCH_THEN SUBST1_TAC >>
  Cases_on `poly g x * poly h x < &0` >> gs[SIGN_LEMMA5]
  >> TRY COND_CASES_TAC >> gs[] >> REAL_ASM_ARITH_TAC
QED

(* ------------------------------------------------------------------------- *)
(* Property of being a (standard) Sturm sequence.                            *)
(* ------------------------------------------------------------------------- *)

Definition STURM_def:
  STURM f f' [] = f' poly_divides f ∧
  STURM f f' (g::gs) = ((∃ k. &0 < k ∧ f' poly_divides (f + k ## g)) ∧
                              degree g < degree f' ∧ STURM f' g gs)
End

(* ------------------------------------------------------------------------- *)
(* If a polynomial doesn't have a root in an interval, sign doesn't change.  *)
(* ------------------------------------------------------------------------- *)

Theorem STURM_NOROOT:
  ∀ a b p.
    a ≤ b ∧
    (∀ x. a <= x /\ x <= b ==> ~(poly p x = &0)) ⇒
    poly p a * poly p b > &0
Proof
  REPEAT GEN_TAC >> REWRITE_TAC[real_gt]
  >> jrhUtils.GEN_REWR_TAC (LAND_CONV o LAND_CONV) [REAL_LE_LT]
  >> DISCH_THEN(CONJUNCTS_THEN2 DISJ_CASES_TAC ASSUME_TAC)
  >- (
    SUBGOAL_THEN `~(poly p a = &0) /\ ~(poly p b = &0)` STRIP_ASSUME_TAC
    >- (
     CONJ_TAC >> FIRST_ASSUM MATCH_MP_TAC
     >> UNDISCH_TAC `a:real < b:real` >> REAL_ARITH_TAC
    )
    >> REPEAT_TCL DISJ_CASES_THEN MP_TAC (SPEC `poly p a` REAL_LT_NEGTOTAL)
    >> REPEAT_TCL DISJ_CASES_THEN MP_TAC (SPEC `poly p b` REAL_LT_NEGTOTAL)
    >> ASM_REWRITE_TAC[]
    >> REWRITE_TAC[PROVE [] “a ==> b ==> c <=> b /\ a ==> c”]
    >> TRY(DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_MUL)
           >> REWRITE_TAC[REAL_MUL_LNEG, REAL_MUL_RNEG, REAL_NEG_NEG]
           >> NO_TAC)
    >> REWRITE_TAC[REAL_ARITH `&0 < -a:real <=> a:real < &0`]
    >> REWRITE_TAC[REAL_ARITH `&0 < x:real <=> x:real > &0`]
    >> UNDISCH_TAC `a:real < b:real`
    >> REWRITE_TAC[GSYM satTheory.AND_IMP] THENL
       [DISCH_THEN(Q.X_CHOOSE_THEN `x:real` MP_TAC o MATCH_MP POLY_IVT_NEG),
        DISCH_THEN(Q.X_CHOOSE_THEN `x:real` MP_TAC o MATCH_MP POLY_IVT_POS)]
    >> REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))
    >> CONV_TAC CONTRAPOS_CONV >> DISCH_TAC
    >> FIRST_ASSUM MATCH_MP_TAC >> CONJ_TAC
    >> MATCH_MP_TAC REAL_LT_IMP_LE >> ASM_REWRITE_TAC[])
  >> gs[]
QED

(* ------------------------------------------------------------------------- *)
(* Now we get the changes in the variation.                                  *)
(* ------------------------------------------------------------------------- *)

Theorem STURM_NOROOT_NOVAR_LEMMA:
  ∀ f a b l.
    a <= b ∧
    (∀ x. a <= x /\ x <= b ==> ~(poly f x = &0)) ⇒
    (varrec r (MAP (\p. poly p a) (CONS f l)) +
     varrec (poly f a) (MAP (\p. poly p b) l) =
     varrec r (MAP (\p. poly p b) (CONS f l)) +
     varrec (poly f a) (MAP (\p. poly p a) l))
Proof
  REPEAT GEN_TAC >> DISCH_TAC
  >> jrhUtils.GEN_REWR_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [listTheory.MAP]
  >> jrhUtils.GEN_REWR_TAC (RAND_CONV o LAND_CONV o RAND_CONV) [listTheory.MAP]
  >> REWRITE_TAC[varrec_def]
  >> FIRST_ASSUM(ASSUME_TAC o MATCH_MP STURM_NOROOT)
  >> FIRST_ASSUM(ASSUME_TAC o MATCH_MP SIGN_LEMMA1)
  >> FIRST_ASSUM(ASSUME_TAC o MATCH_MP VARREC_SIGN)
  >> ASM_REWRITE_TAC[]
  >> SUBGOAL_THEN `~(poly f a = &0) /\ ~(poly f b = &0)` STRIP_ASSUME_TAC
  >- (
    CONJ_TAC >> FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2)
    >> ASM_REWRITE_TAC[REAL_LE_REFL])
  >> ASM_REWRITE_TAC[]
  >> COND_CASES_TAC >> gs[]
QED

Theorem STURM_NOROOT_NOVAR:
  ∀ f a b l.
    a <= b ∧
    (∀ x. a <= x /\ x <= b ==> ~(poly f x = &0)) ∧
    (varrec (poly f a) (MAP (\p. poly p a) l) =
     varrec (poly f a) (MAP (\p. poly p b) l)) ⇒
    (varrec r (MAP (\p. poly p a) (CONS f l)) =
     varrec r (MAP (\p. poly p b) (CONS f l)))
Proof
  REPEAT GEN_TAC >> REWRITE_TAC[CONJ_ASSOC]
  >> DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)
  >> DISCH_THEN(MP_TAC o SPEC_ALL o MATCH_MP STURM_NOROOT_NOVAR_LEMMA)
  >> gs[]
QED

fun check (f:term -> bool) t = if f t then t else raise Feedback.mk_HOL_ERR "" "" ""

Theorem STURM_NOVAR_LEMMA:
  ∀ n l f f' c.
    (LENGTH l = n) ∧
    STURM f f' l ∧
    a <= c ∧ c <= b ∧
    (∀ x.
       a <= x /\ x <= b /\ EXISTS (\p. poly p x = &0) (CONS f (CONS f' l)) ⇒
       (x = c)) ∧
    ~(poly f c = &0) ⇒
    (varrec (poly f a) (MAP (\p. poly p a) (CONS f' l)) =
     varrec (poly f b) (MAP (\p. poly p b) (CONS f' l)))
Proof
  completeInduct_on ‘n’ >> rpt GEN_TAC >> DISCH_TAC
  >> Induct_on ‘l’  >> REWRITE_TAC[STURM_def]
  >- (
    REPEAT STRIP_TAC >>SUBGOAL_THEN `~(poly f' c = &0)` ASSUME_TAC
    >- (
      UNDISCH_TAC `~(poly f c = &0)` >> CONV_TAC CONTRAPOS_CONV
      >> REWRITE_TAC[] >> DISCH_TAC
      >> UNDISCH_TAC `f' poly_divides f` >> REWRITE_TAC[poly_divides]
      >> DISCH_THEN(CHOOSE_THEN SUBST1_TAC)
      >> ASM_REWRITE_TAC[POLY_MUL, REAL_MUL_LZERO]
    )
    >> FIRST_ASSUM(Tactic.UNDISCH_TAC o check is_forall o concl)
    >> REWRITE_TAC[listTheory.EXISTS_DEF] >> DISCH_TAC
    >> SUBGOAL_THEN `(!x. a <= x /\ x <= b ==> ~(poly f x = &0)) /\
                  (!x. a <= x /\ x <= b ==> ~(poly f' x = &0))`
    STRIP_ASSUME_TAC
    >- mesonLib.ASM_MESON_TAC[]
    >> `a:real <= b:real`
      by ( UNDISCH_TAC `c:real <= b:real` >> UNDISCH_TAC `a:real <= c:real` >> REAL_ARITH_TAC)
    >> MATCH_MP_TAC EQ_TRANS
    >> Q.EXISTS_TAC `varrec (poly f b) (MAP (\p. poly p a) [f'])`
    >> CONJ_TAC
    >- (
      MATCH_MP_TAC VARREC_SIGN
      >> MATCH_MP_TAC STURM_NOROOT >> ASM_REWRITE_TAC[]
    )
    >> MATCH_MP_TAC STURM_NOROOT_NOVAR >> ASM_REWRITE_TAC[]
    >> REWRITE_TAC[listTheory.MAP]
  )
  >> REPEAT STRIP_TAC
  >> `!x. a <= x /\ x <= b ==> ~(poly f x = &0)` by
    (
      UNDISCH_TAC `~(poly f c = &0)`
      >> UNDISCH_TAC ‘∀x. a ≤ x ∧ x ≤ b ∧
                       EXISTS (λp. poly p x = 0) (f::f'::h::l) ⇒ x = c’
      >> REWRITE_TAC[listTheory.EXISTS_DEF] >> mesonLib.MESON_TAC[]
    )
  >> `a:real <= b:real` by
    ( UNDISCH_TAC `c:real <= b:real` >> UNDISCH_TAC `a:real <= c:real` >> REAL_ARITH_TAC )
  >> MATCH_MP_TAC EQ_TRANS
  >> EXISTS_TAC
      `varrec (poly f b) (MAP (\p. poly p a) (CONS f' (CONS h l)))`
  >> CONJ_TAC
  >- (
    MATCH_MP_TAC VARREC_SIGN
    >> MATCH_MP_TAC STURM_NOROOT >>ASM_REWRITE_TAC[]
  )
  >> ASM_CASES_TAC “poly f' c = &0” >> ASM_REWRITE_TAC[]
  >- (
    UNDISCH_TAC `f' poly_divides f + k ## h`
    >> REWRITE_TAC[poly_divides]
    >> DISCH_THEN(X_CHOOSE_THEN “q:real list”  MP_TAC)
    >> DISCH_THEN(MP_TAC o C AP_THM “c:real”)
    >> REWRITE_TAC[POLY_MUL,POLY_ADD]
    >> ASM_REWRITE_TAC[REAL_MUL_LZERO]
    >> REWRITE_TAC[REAL_ARITH ‘((x:real) + (y:real) = &0) <=> (x = -y)’]
    >> DISCH_TAC
    >> `(!x. a <= x /\ x <= b ==> ~(poly f x = &0)) /\
                    (!x. a <= x /\ x <= b ==> ~(poly h x = &0))` by
      (
        CONJ_TAC
        >- metis_tac[]
        >> X_GEN_TAC “x:real”
        >> UNDISCH_TAC `!x. a <= x /\ x <= b /\
           EXISTS (\p. poly p x = &0) (CONS f (CONS f' (CONS h l)))
           ==> (x = c)`
        >> DISCH_THEN(MP_TAC o SPEC `x:real`)
        >> REWRITE_TAC[listTheory.EXISTS_DEF]
        >> `(poly h c = &0) <=> (poly f c = &0)` by
          (
            UNDISCH_TAC `poly f c = - (poly (k ## h) c)`
            >> DISCH_THEN SUBST1_TAC >> REWRITE_TAC[POLY_CMUL]
            >> REWRITE_TAC[GSYM REAL_MUL_LNEG]
            >> REWRITE_TAC[REAL_ENTIRE]
            >> ASM_CASES_TAC “poly h c = &0”
            >- ASM_REWRITE_TAC[]
            >> UNDISCH_TAC `&0 < k:real` >> REAL_ARITH_TAC
          )
        >> pop_assum mp_tac
        >> ASM_REWRITE_TAC[ASSUME “~(poly f c = &0)”]
        >> UNDISCH_TAC `~(poly f c = &0)` >> mesonLib.MESON_TAC[]
      )
    >> `poly f a * poly f b > &0 /\
                    poly h a * poly h b > &0`
        by
        (
          CONJ_TAC
          >- (
          MATCH_MP_TAC STURM_NOROOT >> metis_tac[]
          )
          >> MATCH_MP_TAC STURM_NOROOT >> metis_tac[]
        )
    >> SUBGOAL_THEN `(poly f a * poly h a < &0) /\
                    (poly f b * poly h b < &0)`
      MP_TAC
    >- (
      SUBGOAL_THEN `a <= c /\
                      (!x. a <= x /\ x <= c ==> ~(poly (f * h) x = &0))`
          MP_TAC
      >- (
        CONJ_TAC
        >- ASM_REWRITE_TAC[]
        >>  REWRITE_TAC[REAL_ENTIRE, POLY_MUL, DE_MORGAN_THM]
        >> GEN_TAC >> STRIP_TAC >> CONJ_TAC
        >> FIRST_ASSUM MATCH_MP_TAC >> ASM_REWRITE_TAC[]
        >> MATCH_MP_TAC REAL_LE_TRANS >> EXISTS_TAC `c:real`
        >> ASM_REWRITE_TAC[] >> first_assum match_mp_tac
        >> ASM_REWRITE_TAC[]
        >> UNDISCH_TAC ‘x:real≤c:real’ >> UNDISCH_TAC ‘c:real≤b:real’
        >> REAL_ARITH_TAC
      )
      >> DISCH_THEN(MP_TAC o MATCH_MP STURM_NOROOT)
      >> SUBGOAL_THEN `c <= b /\
                      (!x. c <= x /\ x <= b ==> ~(poly (f * h) x = &0))`
          MP_TAC
      >- (
        CONJ_TAC
        >- ASM_REWRITE_TAC[]
        >>  REWRITE_TAC[REAL_ENTIRE, POLY_MUL, DE_MORGAN_THM]
        >> GEN_TAC >> STRIP_TAC >> CONJ_TAC
        >> FIRST_ASSUM MATCH_MP_TAC >> ASM_REWRITE_TAC[]
        >> MATCH_MP_TAC REAL_LE_TRANS >> EXISTS_TAC `c:real`
        >> ASM_REWRITE_TAC[] >> first_assum match_mp_tac
        >> ASM_REWRITE_TAC[] >> UNDISCH_TAC ‘a:real≤c:real’
        >> UNDISCH_TAC ‘c:real ≤x:real’ >> REAL_ARITH_TAC
      )
      >> DISCH_THEN(MP_TAC o MATCH_MP STURM_NOROOT)
      >> SUBGOAL_THEN `poly (f * h) c < &0` MP_TAC
      >- (
        ASM_REWRITE_TAC[POLY_MUL, REAL_MUL_LNEG]
        >> REWRITE_TAC[REAL_ARITH `-x < &0 <=> &0 < x:real`, POLY_CMUL]
        >> REWRITE_TAC[GSYM REAL_MUL_ASSOC]
        >> MATCH_MP_TAC REAL_LT_MUL >> ASM_REWRITE_TAC[]
        >> REWRITE_TAC[REAL_POSSQ]
        >> FIRST_ASSUM MATCH_MP_TAC >> ASM_REWRITE_TAC[]
      )
      >> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV o LAND_CONV)
                         [REAL_MUL_SYM]
      >> DISCH_THEN(fn th => REWRITE_TAC[MATCH_MP SIGN_LEMMA3 th])
      >> REWRITE_TAC[POLY_MUL] >> metis_tac[]
    )
    >> DISCH_THEN(CONJUNCTS_THEN (ASSUME_TAC o MATCH_MP VARREC_STRADDLE))
    >> MATCH_MP_TAC EQ_TRANS
    >> EXISTS_TAC
        `varrec (poly f a) (MAP (\p. poly p a) (CONS f' (CONS h l)))`
    >> CONJ_TAC
    >- (
      MATCH_MP_TAC VARREC_SIGN >> ONCE_REWRITE_TAC[REAL_MUL_SYM]
      >> ASM_REWRITE_TAC[]
    )
    >> ASM_REWRITE_TAC[ arithmeticTheory.LESS_EQ_MONO]
    >> MP_TAC(ISPEC “l:(real list)list” list_CASES)
    >> DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC MP_TAC)
    >- REWRITE_TAC[varrec_def, MAP]
    >> DISCH_THEN(X_CHOOSE_THEN “g:real list”  MP_TAC)
    >> DISCH_THEN(X_CHOOSE_THEN “m:(real list)list” SUBST_ALL_TAC)
    >> FIRST_ASSUM(MP_TAC o SPEC `PRE(PRE n)`)
    >> UNDISCH_TAC `LENGTH (CONS (h:real list) (CONS g m)) = n`
    >> REWRITE_TAC[LENGTH] THEN DISCH_THEN(SUBST_ALL_TAC o SYM)
    >> ‘PRE (PRE (SUC (SUC (LENGTH m)))) = LENGTH m’ by rw[]
    >> pop_assum $ rewrite_tac o single
    >> ‘LENGTH m < SUC (SUC (LENGTH m))’ by rw[]
    >> pop_assum $ rewrite_tac o single
    >> DISCH_THEN(MP_TAC o SPECL [`m:(real list)list`, `h:real list`])
    >> DISCH_THEN(MP_TAC o SPECL [`g:real list`, `c:real`])
    >> ASM_REWRITE_TAC[]
    >> ‘STURM h g m ∧
        (∀x. a ≤ x ∧ x ≤ b ∧ EXISTS (λp. poly p x = 0) (h::g::m) ⇒ x = c)
        ∧  poly h c ≠ 0’
      by (
        CONJ_TAC
        >- metis_tac[STURM_def]
        >> CONJ_TAC
        >- ( rpt strip_tac >> rw[] )
        >> first_assum match_mp_tac >> metis_tac[]
      )
    >> rpt strip_tac >> AP_TERM_TAC
    >> first_assum  MATCH_MP_TAC >> metis_tac[]
  )
  >> SUBGOAL_THEN `~(poly f' a = &0) /\ ~(poly f' b = &0)`
                                      STRIP_ASSUME_TAC
  >- (
    RULE_ASSUM_TAC(REWRITE_RULE[listTheory.EXISTS_DEF])
    >> mesonLib.ASM_MESON_TAC[REAL_LE_REFL, REAL_LT_REFL]
  )
  >> FIRST_ASSUM(MP_TAC o SPEC `PRE n`)
  >> UNDISCH_TAC `LENGTH (CONS (h:real list) l) = n`
  >> REWRITE_TAC[LENGTH] >> DISCH_THEN(SUBST_ALL_TAC o SYM)
  >> ‘PRE (SUC (LENGTH l)) = LENGTH l’ by rw[]
  >> pop_assum $ rewrite_tac o single
  >> ‘LENGTH l < SUC (LENGTH l)’ by rw[]
  >> pop_assum $ rewrite_tac o single
  >> DISCH_THEN(MP_TAC o SPECL [`l:(real list)list`, `f':real list`])
  >> DISCH_THEN(MP_TAC o SPECL [`h:real list`, `c:real`])
  >> RULE_ASSUM_TAC(REWRITE_RULE[STURM_def]) THEN ASM_REWRITE_TAC[]
  >> W(C SUBGOAL_THEN (fn th => REWRITE_TAC[th]) o (fn t => `^t`) o lhand o lhand o snd)
  >- (
    REWRITE_TAC[listTheory.EXISTS_DEF]
    >> REPEAT STRIP_TAC >> FIRST_ASSUM MATCH_MP_TAC
    >> ASM_REWRITE_TAC[listTheory.EXISTS_DEF]
    >> first_assum match_mp_tac
    >> ASM_REWRITE_TAC[listTheory.EXISTS_DEF] >> first_assum match_mp_tac
    >> ASM_REWRITE_TAC[listTheory.EXISTS_DEF]
  )
  >> DISCH_TAC
  >> ONCE_REWRITE_TAC[MAP] >> REWRITE_TAC[varrec_def]
  >> ASM_REWRITE_TAC[]
  >> SUBGOAL_THEN `!x. a <= x /\ x <= b ==> ~(poly f' x = &0)`
                                          ASSUME_TAC
  >- (
    UNDISCH_TAC `~(poly f' c = &0)`
    >> UNDISCH_TAC `!x. a <= x /\ x <= b /\
       EXISTS (\p. poly p x = &0) (CONS f (CONS f' (CONS h l)))
       ==> (x = c)`
    >> REWRITE_TAC[listTheory.EXISTS_DEF] >> mesonLib.MESON_TAC[]
  )
  >> MP_TAC(SPECL [`a:real`, `b:real`, `f':real list`] STURM_NOROOT)
  >> ASM_REWRITE_TAC[] >> rpt strip_tac
  >> ‘(poly f b * poly f' a < &0) ⇔ (poly f b * poly f' b < &0)’ by
    ( irule SIGN_LEMMA1 >> metis_tac[] )
  >> metis_tac[]
QED

Theorem STURM_NOVAR:
 ∀ l f f' c.
        STURM f f' l ∧
        a ≤ c ∧ c ≤ b ∧
        (∀ x.
           a ≤ x ∧ x ≤ b ∧ EXISTS (\p. poly p x = &0) (CONS f (CONS f' l)) ⇒
           (x = c)) ∧
        ~(poly f c = &0) ⇒
        (varrec (poly f a) (MAP (\p. poly p a) (CONS f' l)) =
         varrec (poly f b) (MAP (\p. poly p b) (CONS f' l)))
Proof
  REPEAT STRIP_TAC >> MATCH_MP_TAC STURM_NOVAR_LEMMA >>
  MAP_EVERY EXISTS_TAC [`LENGTH(l:(real list) list)`, `c:real`] >>
  ASM_REWRITE_TAC[]
QED

Theorem STURM_VAR_DLEMMA:
 !p a b.
        a ≤ b ∧
        (!x. a <= x /\ x <= b ==> ~(poly p x = &0))
        ⇒ (!x. a <= x /\ x <= b ==> poly p x > &0) \/
            (!x. a <= x /\ x <= b ==> poly p x < &0)
Proof
  REPEAT GEN_TAC >> STRIP_TAC
  >> REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (SPEC `poly p a` REAL_LT_NEGTOTAL)
  >- (
    FIRST_ASSUM(Tactic.UNDISCH_TAC o check is_forall o concl)
    >> DISCH_THEN(MP_TAC o SPEC `a:real`) >> ASM_REWRITE_TAC[REAL_LE_REFL]
  )
  >-(
    DISJ1_TAC >> REPEAT STRIP_TAC >> REWRITE_TAC[real_gt]
    >> SUBGOAL_THEN `~(poly p x = &0) /\ ~(poly p x < &0)` MP_TAC
    >- (
      CONJ_TAC
      >- ( FIRST_ASSUM MATCH_MP_TAC >> ASM_REWRITE_TAC[REAL_LE_REFL])
      >> DISCH_TAC >> MP_TAC(SPEC `p:real list` POLY_IVT_NEG)
      >> DISCH_THEN(MP_TAC o SPECL [`a:real`, `x:real`])
      >> ASM_REWRITE_TAC[real_gt, NOT_IMP, NOT_EXISTS_THM, REAL_LT_REFL]
      >> jrhUtils.GEN_REWR_TAC LAND_CONV [REAL_LT_LE]
      >> ASM_REWRITE_TAC[]
      >> ASM_CASES_TAC “a:real = x”
      >- mesonLib.ASM_MESON_TAC[REAL_LT_ANTISYM]
      >> ASM_REWRITE_TAC[]
      >>  ‘ (¬∃x'. a < x' ∧ x' < x ∧ poly p x' = 0) ⇔
              ∀x'. ~(a < x' ∧ x' < x ∧ poly p x'=0)’ by
        (gs[NOT_EXISTS_THM])
      >> pop_assum $ rewrite_tac o single
      >> X_GEN_TAC “y:real”
      >> REWRITE_TAC[tautLib.TAUT `~(a /\ b /\ c) <=> a /\ b ==> ~c`]
      >> DISCH_TAC
      >> FIRST_ASSUM MATCH_MP_TAC
      >> UNDISCH_TAC `a:real < y:real /\ y:real < x:real`
      >> UNDISCH_TAC `x:real <= b:real`
      >> REAL_ARITH_TAC
    )
    >> REAL_ARITH_TAC
  )
  >> DISJ2_TAC >> REPEAT STRIP_TAC
  >> SUBGOAL_THEN `~(poly p x = &0) /\ ~(poly p x > &0)` MP_TAC
  >- (
    CONJ_TAC
    >- ( FIRST_ASSUM MATCH_MP_TAC >> ASM_REWRITE_TAC[REAL_LE_REFL] )
    >> DISCH_TAC >> MP_TAC(SPEC `p:real list` POLY_IVT_POS)
    >> DISCH_THEN(MP_TAC o SPECL [`a:real`, `x:real`])
    >> RULE_ASSUM_TAC(Ho_Rewrite.REWRITE_RULE
                        [RealArith.REAL_ARITH “&0 < - x <=> x:real < &0”])
    >> ASM_REWRITE_TAC[real_gt, NOT_IMP, NOT_EXISTS_THM, REAL_LT_REFL]
    >> GEN_REWRITE_TAC LAND_CONV [REAL_LT_LE]
    >> ASM_REWRITE_TAC[]
    >> ASM_CASES_TAC “a:real = x”
    >-  mesonLib.ASM_MESON_TAC[REAL_LT_ANTISYM, real_gt]
    >> ASM_REWRITE_TAC[]
    >> ‘(¬∃x'. a < x' ∧ x' < x ∧ poly p x' = 0) ⇔
          ∀x'. ~(a < x' ∧ x' < x ∧ poly p x'=0)’
      by (gs[NOT_EXISTS_THM])
    >> pop_assum $ rewrite_tac o single
    >> X_GEN_TAC “y:real”
    >> REWRITE_TAC[tautLib.TAUT `~(a /\ b /\ c) <=> a /\ b ==> ~c`]
    >> DISCH_TAC >> FIRST_ASSUM MATCH_MP_TAC
    >> UNDISCH_TAC `a:real < y:real /\ y:real < x:real`
    >> UNDISCH_TAC `x:real <= b:real`
    >> REAL_ARITH_TAC
  )
  >> REAL_ARITH_TAC
QED

Theorem  STURM_VAR_LEMMA:
 !l f f' c.
        rsquarefree f /\
        (f' = diff f) /\
        STURM f f' l /\
        a < c /\ c < b /\
        (!x. a <= x /\ x <= b /\ EXISTS (\p. poly p x = &0) (CONS f (CONS f' l))
             ==> (x = c)) /\
        (poly f c = &0)
        ==> poly f a * poly f' a < &0 /\
            poly f b * poly f' b > &0
Proof
  REPEAT GEN_TAC >> STRIP_TAC
  >> SUBGOAL_THEN `a:real <= b:real` ASSUME_TAC
  >- (
    UNDISCH_TAC `a:real < c:real` >> UNDISCH_TAC `c:real < b:real`
    >> REAL_ARITH_TAC
  )
  >> SUBGOAL_THEN `!x. a <= x /\ x <= b ==> ~(poly (diff f) x = &0)` ASSUME_TAC
  >- (
    X_GEN_TAC “x:real” >> STRIP_TAC
    >> FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I empty_rewrites [RSQUAREFREE_ROOTS])
    >> DISCH_THEN(MP_TAC o SPEC `c:real`) >>  ASM_REWRITE_TAC[]
    >> rpt strip_tac >> ‘x=c’ by (first_x_assum irule >> gs[listTheory.EXISTS_DEF])
    >> rpt BasicProvers.VAR_EQ_TAC
    >> mesonLib.ASM_MESON_TAC[]
  )
  >> MP_TAC(SPECL [`diff f`, `a:real`, `b:real`] STURM_VAR_DLEMMA)
  >> ASM_REWRITE_TAC[] >> DISCH_THEN DISJ_CASES_TAC
  >- (
    CONJ_TAC
    >- (
      rewrite_tac[GSYM realTheory.REAL_NEG_GT0]
      >> MP_TAC(SPECL [`f:real list`, `a:real`, `c:real`] POLY_MVT)
      >> ASM_REWRITE_TAC[REAL_SUB_LZERO]
      >> DISCH_THEN(X_CHOOSE_THEN “x:real” STRIP_ASSUME_TAC)
      >> rewrite_tac[GSYM REAL_MUL_LNEG]
      >> MATCH_MP_TAC REAL_LT_MUL
      >> CONJ_TAC
      >- (
        pop_assum $ rewrite_tac o single
        >> MATCH_MP_TAC REAL_LT_MUL
        >> CONJ_TAC
        >- ( rewrite_tac[ REAL_SUB_LT] >> rw[] )
        >> REWRITE_TAC[REAL_ARITH `&0 < x <=> x:real > &0`]
        >> first_assum irule >> rw[REAL_LT_IMP_LE]
        >> UNDISCH_TAC `x:real < c:real`
        >> UNDISCH_TAC `c:real < b:real` >> REAL_ARITH_TAC
      )
      >> REWRITE_TAC[REAL_ARITH `&0 < x <=> x:real > &0`]
      >> first_assum irule
      >> CONJ_TAC
      >- ASM_REWRITE_TAC[REAL_LE_REFL]
      >> rw[]
    )
    >> MP_TAC(SPECL [`f:real list`, `c:real`, `b:real`] POLY_MVT)
    >> ASM_REWRITE_TAC[REAL_SUB_RZERO]
    >> DISCH_THEN(X_CHOOSE_THEN “x:real” STRIP_ASSUME_TAC)
    >> ‘∀x. &0<x:real ⇒ x > &0’ by rw[real_gt]
    >> first_assum irule >>  MATCH_MP_TAC REAL_LT_MUL
    >> CONJ_TAC
    >- (
      qpat_assum ‘poly f b = (b − c) * poly (diff f) x’$ rewrite_tac o single
      >> MATCH_MP_TAC REAL_LT_MUL
      >> CONJ_TAC
      >- (
        UNDISCH_TAC `c:real < x:real`
        >> UNDISCH_TAC `x:real < b:real` >> REAL_ARITH_TAC
      )
      >> REWRITE_TAC[REAL_ARITH `&0 < x <=> x:real > &0`]
      >> pop_assum $ kall_tac
      >> first_assum irule
      >> CONJ_TAC
      >- (
        UNDISCH_TAC `a:real < c:real` >> UNDISCH_TAC `c:real < x:real`
        >> REAL_ARITH_TAC
      )
      >> rw[REAL_LT_IMP_LE]
    )
    >> REWRITE_TAC[REAL_ARITH `&0 < x:real <=> x > &0`]
    >> pop_assum $ kall_tac
    >> first_assum irule
    >> CONJ_TAC
    >- rw[]
    >> ASM_REWRITE_TAC[REAL_LE_REFL]
  )
  >> CONJ_TAC
  >- (
    rewrite_tac[GSYM realTheory.REAL_NEG_GT0]
    >> MP_TAC(SPECL [`f:real list`, `a:real`, `c:real`] POLY_MVT)
    >> ASM_REWRITE_TAC[REAL_SUB_LZERO]
    >> DISCH_THEN(X_CHOOSE_THEN “x:real” STRIP_ASSUME_TAC)
    >> rewrite_tac[REAL_NEG_RMUL]
    >> MATCH_MP_TAC REAL_LT_MUL
    >> CONJ_TAC
    >- (
      rewrite_tac[GSYM realTheory.REAL_NEG_LT0]
      >> pop_assum $ rewrite_tac o single
      >> rewrite_tac[GSYM realTheory.REAL_NEG_GT0]
      >> rewrite_tac[REAL_NEG_RMUL]
      >> MATCH_MP_TAC REAL_LT_MUL
      >> CONJ_TAC
      >- ( rewrite_tac[REAL_SUB_LT] >> rw[] )
      >> rewrite_tac[realTheory.REAL_NEG_GT0]
      >> first_assum irule
      >> CONJ_TAC
      >-  rw[REAL_LT_IMP_LE]
      >> UNDISCH_TAC `x:real < c:real`
      >> UNDISCH_TAC `c:real < b:real` >> REAL_ARITH_TAC
    )
    >> rewrite_tac[realTheory.REAL_NEG_GT0]
    >> first_assum irule
    >> CONJ_TAC
    >-  ASM_REWRITE_TAC[REAL_LE_REFL]
    >> rw[]
  )
  >> rewrite_tac[real_gt]
  >> ONCE_REWRITE_TAC[REAL_ARITH `&0 < (x:real) * (y:real) <=> &0 < -x * - y` ]
  >> MP_TAC(SPECL [`f:real list`, `c:real`, `b:real`] POLY_MVT)
  >> ASM_REWRITE_TAC[REAL_SUB_RZERO]
  >> DISCH_THEN(X_CHOOSE_THEN “x:real” STRIP_ASSUME_TAC)
  >> MATCH_MP_TAC REAL_LT_MUL
  >> CONJ_TAC
  >- (
    pop_assum $ rewrite_tac o single
    >> rewrite_tac[REAL_NEG_RMUL]
    >> MATCH_MP_TAC REAL_LT_MUL
    >> CONJ_TAC
    >- ( rewrite_tac[REAL_SUB_LT] >> rw[] )
    >> rewrite_tac[realTheory.REAL_NEG_GT0]
    >> first_assum irule
    >> CONJ_TAC
    >- (
      UNDISCH_TAC `a:real < c:real` >> UNDISCH_TAC `c:real < x:real`
      >> REAL_ARITH_TAC
    )
    >> rw[REAL_LT_IMP_LE]
  )
  >> rewrite_tac[realTheory.REAL_NEG_GT0]
  >> first_assum irule
  >> CONJ_TAC
  >- rw[]
  >> ASM_REWRITE_TAC[REAL_LE_REFL]
QED

Theorem  STURM_VAR:
 !l f f' c.
        rsquarefree f /\
        (f' = diff f) /\
        STURM f f' l /\
        a < c /\ c < b /\
        (!x. a <= x /\ x <= b /\ EXISTS (\p. poly p x = &0) (CONS f (CONS f' l))
             ==> (x = c)) /\
        (poly f c = &0)
        ==> (varrec (poly f a) (MAP (\p. poly p a) (CONS f' l)) =
             SUC(varrec (poly f b) (MAP (\p. poly p b) (CONS f' l))))
Proof
  ListConv1.LIST_INDUCT_TAC
  >- (
    REPEAT GEN_TAC
    >> DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP STURM_VAR_LEMMA)
    >> ASM_REWRITE_TAC[listTheory.MAP, varrec_def]
    >> ‘~(poly f b * poly f' b < &0) /\ ~(poly f' b = &0)’ by
      (
        UNDISCH_TAC `poly f b * poly f' b > &0`
        >> ASM_CASES_TAC “poly f' b = &0”
        >- ASM_REWRITE_TAC[real_gt, REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_LT_REFL]
        >> ASM_REWRITE_TAC[] >> REAL_ARITH_TAC
      )
    >> gs[]
  )
  >> REPEAT GEN_TAC >> DISCH_TAC
  >> FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP STURM_VAR_LEMMA)
  >> ONCE_REWRITE_TAC[listTheory.MAP] >> REWRITE_TAC[varrec_def]
  >> ‘poly f a * poly f' a < &0 /\
                  ~(poly f b * poly f' b < &0) /\
                  ~(poly f' a = &0) /\ ~(poly f' b = &0)’ by
    (
      UNDISCH_TAC `poly f b * poly f' b > &0`
      >> UNDISCH_TAC `poly f a * poly f' a < &0`
      >> POP_ASSUM_LIST(K ALL_TAC)
      >> ASM_CASES_TAC “poly f' a = &0”
      >- ASM_REWRITE_TAC
          [real_gt, REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_LT_REFL]
      >> ASM_CASES_TAC “poly f' b = &0”
      >- ASM_REWRITE_TAC
            [real_gt, REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_LT_REFL]
      >> rpt strip_tac
      >- metis_tac[]
      >> assume_tac REAL_LT_ANTISYM
      >> pop_assum $ qspecl_then [‘ poly f b * poly f' b’, ‘&0’] assume_tac
      >> ‘(poly f b * poly f' b < 0 ∧ 0 < poly f b * poly f' b) ⇔ F’
         by metis_tac[]
      >> first_assum match_mp_tac
      >> CONJ_TAC
      >- metis_tac[]
      >> rewrite_tac[GSYM real_gt] >> metis_tac[]
    )
  >> ‘poly f a * (λp. poly p a) f' < 0 ⇔ T’ by metis_tac[]
  >> pop_assum $ rewrite_tac o single
  >> ‘ poly f b * (λp. poly p b) f' < 0 ⇔ F’ by metis_tac[]
  >> pop_assum $ rewrite_tac o single
  >> ‘(λp. poly p b) f' = 0 ⇔ F’ by metis_tac[]
  >> pop_assum $ rewrite_tac o single
  >> AP_TERM_TAC
  >> qpat_x_assum `_ /\ _ /\ _` mp_tac >> rpt strip_tac
  >> `STURM f' h l` by
    (
      qpat_x_assum `STURM _ _ _` $ mp_tac o REWRITE_RULE [STURM_def]
      >> metis_tac[]
    )
  >> pop_assum $ mp_then Any mp_tac STURM_NOVAR >> BETA_TAC
  >> disch_then irule
  >> EXISTS_TAC `c:real`
  >> REPEAT CONJ_TAC
  >- metis_tac[listTheory.EXISTS_DEF]
  >- (
    MP_TAC(SPEC `f:real list` RSQUAREFREE_ROOTS)
    >> ASM_REWRITE_TAC[]
    >> DISCH_THEN(MP_TAC o SPEC `c:real`) >> ASM_REWRITE_TAC[]
  )
  >> MATCH_MP_TAC REAL_LT_IMP_LE >> ASM_REWRITE_TAC[]
QED

(* ------------------------------------------------------------------------- *)
(* The main lemma.                                                           *)
(* ------------------------------------------------------------------------- *)

Theorem STURM_COMPONENT:
 !l f a b c.
        rsquarefree f /\
        STURM f (diff f) l /\
        a <= c /\ c <= b /\
        ~(poly f a = &0) /\
        ~(poly f b = &0) /\
        (!x. a <= x /\ x <= b /\
             EXISTS (\p. poly p x = &0) (CONS f (CONS (diff f) l))
             ==> (x = c))
        ==> (variation (MAP (\p. poly p a) (CONS f (CONS (diff f) l))) =
                if poly f c = &0 then
                    SUC(variation (MAP (\p. poly p b)
                                       (CONS f (CONS (diff f) l))))
                else variation (MAP (\p. poly p b)
                                (CONS f (CONS (diff f) l))))
Proof
  REPEAT STRIP_TAC >> REWRITE_TAC[variation_def]
  >> ONCE_REWRITE_TAC[rich_listTheory.MAP]
  >> REWRITE_TAC[varrec_def, REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_LT_REFL]
  >> ASM_CASES_TAC “poly f c = &0”
  >- (
    ASM_REWRITE_TAC[]
    >> ‘((λp. poly p a) f = 0) ⇔ F’ by metis_tac[]
    >> pop_assum $ rewrite_tac o single
    >> ‘ (λp. poly p b) f = 0 ⇔ F’ by metis_tac[]
    >> pop_assum $ rewrite_tac o single
    >> ‘((λp. poly p a) f) =  poly f a’ by metis_tac[]
    >> ‘((λp. poly p b) f) =  poly f b’ by metis_tac[]
    >> ASM_REWRITE_TAC[] >> irule STURM_VAR
    >> rpt strip_tac
    >- metis_tac[]
    >- metis_tac[]
    >- (
      EXISTS_TAC `c:real`
      >> CONJ_TAC
      >- metis_tac[]
      >> CONJ_TAC
      >- metis_tac[]
      >> CONJ_TAC
      >- ( ASM_REWRITE_TAC[REAL_LT_LE] >> metis_tac[] )
      >> ASM_REWRITE_TAC[REAL_LT_LE] >> metis_tac[]
    )
    >> metis_tac[]
  )
  >> ‘((λp. poly p a) f = 0) ⇔ F’ by metis_tac[]
  >> pop_assum $ rewrite_tac o single
  >> ‘ (λp. poly p b) f = 0 ⇔ F’ by metis_tac[]
  >> pop_assum $ rewrite_tac o single
  >> ‘((λp. poly p a) f) =  poly f a’ by metis_tac[]
  >> ‘((λp. poly p b) f) =  poly f b’ by metis_tac[]
  >> ‘poly f c = 0 ⇔ F’ by metis_tac[]
  >> pop_assum $ rewrite_tac o single
  >> ASM_REWRITE_TAC[] >> MATCH_MP_TAC STURM_NOVAR
  >> EXISTS_TAC ‘c:real’
  >> rpt strip_tac
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >> first_x_assum irule >> metis_tac[]
QED

Theorem FINITE_UNION_IMP:
  FINITE s ∧ FINITE t ⇒ FINITE (s UNION t)
Proof
  gs[pred_setTheory.FINITE_UNION]
QED
(* ------------------------------------------------------------------------- *)
(* Roots of a list of polynomials (maybe in interval) is finite.             *)
(* ------------------------------------------------------------------------- *)

Theorem POLYS_ROOTS_FINITE_SET:
 !l. EVERY (\p. ~(poly p = poly [])) l ==>
     FINITE { x | EXISTS (\p. poly p x = &0) l }
Proof
  ListConv1.LIST_INDUCT_TAC
  >- (
    SUBGOAL_THEN `{ x | EXISTS (\p. poly p x = &0) [] } = {}`
    (fn th => REWRITE_TAC[polyTheory.POLY_ROOTS_FINITE_SET, th])
    >> REWRITE_TAC[pred_setTheory.EXTENSION, pred_setTheory.NOT_IN_EMPTY,
                listTheory.EXISTS_DEF]
    >> gs[]
  )
  >> SUBGOAL_THEN `{ x | EXISTS (\p. poly p x = &0) (CONS h t) } =
                  { x | poly h x = &0 } UNION { x | EXISTS (\p. poly p x = &0) t }`
                                        SUBST1_TAC
  >- (
    REWRITE_TAC[pred_setTheory.EXTENSION, pred_setTheory.IN_UNION,
                 listTheory.EXISTS_DEF]
    >> gs[]
  )
  >> REWRITE_TAC[listTheory.EVERY_DEF] >> STRIP_TAC
  >> STRIP_TAC >> gs[]
  >> ‘FINITE {x | poly h x = 0}’ by metis_tac[polyTheory.POLY_ROOTS_FINITE_SET]
  >> imp_res_tac FINITE_UNION_IMP
  >> rpt $ pop_assum mp_tac
  >> rewrite_tac[pred_setTheory.UNION_DEF, IN_DEF]
  >> simp[]
QED

Theorem  POLYS_INTERVAL_ROOTS_FINITE_SET:
 !l a b. EVERY (\p. ~(poly p = poly [])) l ==>
         FINITE { x | a <= x /\ x <= b /\ EXISTS (\p. poly p x = &0) l }
Proof
  REPEAT GEN_TAC >> DISCH_TAC
  >> MATCH_MP_TAC pred_setTheory.SUBSET_FINITE_I
  >> EXISTS_TAC `{ x | EXISTS (\p. poly p x = &0) l }`
  >> CONJ_TAC
  >- ( MATCH_MP_TAC POLYS_ROOTS_FINITE_SET >> ASM_REWRITE_TAC[] )
  >> REWRITE_TAC[pred_setTheory.SUBSET_DEF] >> gs[]
QED


(* ------------------------------------------------------------------------- *)
(* Proof that we can lay out a finite set in a linear sequence.              *)
(* ------------------------------------------------------------------------- *)

Theorem FINITE_LEAST:
  !(s:real -> bool). FINITE s ==> (s = {}) \/ ?a. a IN s /\ !x. x IN s ==> a <= x
Proof
  qspec_then ‘\s:real->bool. s = ∅ ∨ ∃a. a ∈ s ∧ ∀x. x ∈ s ⇒ a ≤ x’
             mp_tac pred_setTheory.FINITE_INDUCT
  >> reverse impl_tac
  >- gs[]
  >> rpt conj_tac
  >> simp[]
  >> rpt strip_tac
  >- (
    EXISTS_TAC ‘e:real’ >> CONJ_TAC
    >- ( DISJ1_TAC >> gs[] )
    >> strip_tac >> gs[]
  )
  >> DISJ_CASES_TAC(SPECL [`a:real`, `e:real`] REAL_LE_TOTAL)
  >- ( qexists_tac ‘a’ >> gs[] >> rpt strip_tac >> gs[] )
  >> qexists_tac ‘e’ >> gs[] >> rpt strip_tac >> gs[]
  >> mesonLib.ASM_MESON_TAC[REAL_LE_TRANS, REAL_LE_REFL]
QED


Theorem FINITE_LEAST_DELETE :
 !(s:real -> bool). s HAS_SIZE (SUC n)
       ==> ?a. a IN s /\ (s DELETE a) HAS_SIZE n /\
               !x. x IN (s DELETE a) ==> a < x
Proof
  GEN_TAC >> DISCH_THEN(fn th => MP_TAC th >> MP_TAC th)
  >> DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[pred_setTheory.HAS_SIZE_SUC])
  >> REWRITE_TAC[pred_setTheory.HAS_SIZE]
  >> DISCH_THEN(MP_TAC o MATCH_MP FINITE_LEAST o CONJUNCT1)
  >> ASM_REWRITE_TAC[]
  >> DISCH_THEN(X_CHOOSE_THEN “a:real” STRIP_ASSUME_TAC)
  >> EXISTS_TAC `a:real` >> ASM_REWRITE_TAC[]
  >> REWRITE_TAC[GSYM pred_setTheory.HAS_SIZE, pred_setTheory.IN_DELETE]
  >> REWRITE_TAC[REAL_LT_LE] >> mesonLib.ASM_MESON_TAC[]
QED

Theorem HAS_SIZE_ORDER:
 !n (s: real->bool). s HAS_SIZE n ==>
         ?i. (!x. x IN s <=> ?k. k < n /\ (x = i k)) /\
             (!k. i k < i (SUC k))
Proof
  Induct_on ‘n’
  >- (
    GEN_TAC >> REWRITE_TAC[pred_setTheory.HAS_SIZE_0]
    >> DISCH_THEN SUBST1_TAC
    >> REWRITE_TAC[pred_setTheory.NOT_IN_EMPTY] >> gs[]
    >> EXISTS_TAC `real_of_num` >> strip_tac >> gs[REAL_LT]
  )
  >> GEN_TAC >> DISCH_THEN(MP_TAC o MATCH_MP FINITE_LEAST_DELETE)
  >> DISCH_THEN(X_CHOOSE_THEN “a:real” (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))
  >> DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)
  >> DISCH_THEN(fn th => ASSUME_TAC th >> MP_TAC th)
  >> DISCH_THEN(ANTE_RES_THEN MP_TAC)
  >> DISCH_THEN(X_CHOOSE_THEN “i:num->real”  STRIP_ASSUME_TAC)
  >> ASM_CASES_TAC “(n:num)=0”
  >- (
    EXISTS_TAC `\(k:num). a + (&k:real)` >> gs[] >> rpt strip_tac >> eq_tac
    >- (
      strip_tac >> EXISTS_TAC ‘(n:num)’ >> CONJ_TAC
      >- gs[]
      >> gs[] >> metis_tac[]
    )
    >> strip_tac >> gs[]
    >> ‘(k:num)=0’ by gs[] >> pop_assum $ rewrite_tac o single >> gs[]
  )
  >> EXISTS_TAC `\k. if k = 0 then a:real else i(PRE k)`
  >> REWRITE_TAC[] >> CONJ_TAC
  >- (
    X_GEN_TAC “x:real” >> ASM_CASES_TAC “x:real = a”
    >- (
      UNDISCH_TAC `x:real = a` >> DISCH_THEN SUBST_ALL_TAC
      >> ASM_REWRITE_TAC[] >> EXISTS_TAC `0:num`
      >> CONJ_TAC
      >- gs[]
      >> gs[]
    )
    >> SUBGOAL_THEN `x IN s <=> x IN (s DELETE a:real)` SUBST1_TAC
    >- ( REWRITE_TAC[IN_DELETE] >> ASM_REWRITE_TAC[] )
    >> ASM_REWRITE_TAC[] >> EQ_TAC
    >- (
      DISCH_THEN(X_CHOOSE_THEN “k:num” STRIP_ASSUME_TAC)
      >> EXISTS_TAC `SUC k`
      >> CONJ_TAC
      >- gs[arithmeticTheory.LT_SUC]
      >> gs[]
    )
    >> rpt strip_tac
    >> EXISTS_TAC `PRE k`
    >> `x = (if k = 0 then a:real else i (PRE k))` by gs[]
    >> UNDISCH_TAC `x = (if k = 0 then a:real else i (PRE k))`
    >> UNDISCH_TAC `k < SUC n`
    >> SPEC_TAC(“k:num”,“k:num”)
    >> rpt strip_tac
    >- (
      Induct_on ‘k'’
      >- gs[]
      >> rpt strip_tac >> gs[]
    )
    >> Induct_on ‘k'’
    >- gs[]
    >> rpt strip_tac >> gs[]
  )
  >> rpt strip_tac >> gs[]
  >> ASM_CASES_TAC “(k:num)=0”
  >- (
    gs[] >> first_assum match_mp_tac
    >> EXISTS_TAC `0:num` >> ASM_REWRITE_TAC[]
    >> gs[]
  )
  >> gs[]
  >> qpat_assum ‘ ∀k. i k < i (SUC k)’ $ qspec_then ‘PRE k’ assume_tac
  >> ‘SUC(PRE k) = k’ by gs[]
  >> ‘i k = i (SUC (PRE k))’ by
    ( pop_assum $ rewrite_tac o single)
  >> pop_assum $ rewrite_tac o single >> metis_tac[]
QED

Theorem FINITE_ORDER :
 !(s:real -> bool). FINITE s ==>
         ?i N. (!x. x IN s <=> ?k. k < N /\ (x = i k)) /\
               (!k. i k < i (SUC k))
Proof
  REPEAT STRIP_TAC
  >> GEN_EXISTS_TAC "N" `CARD(s:real->bool)`
  >> MATCH_MP_TAC HAS_SIZE_ORDER
  >> ASM_REWRITE_TAC[HAS_SIZE]
QED

(* ------------------------------------------------------------------------- *)
(* We can enumerate the roots in order.                                      *)
(* ------------------------------------------------------------------------- *)

Theorem POLYS_ENUM_ROOTS :
 !l. EVERY (\p. ~(poly p = poly [])) l
       ==> ?i N. (!k. i k < i (SUC k)) /\
                 (!x. a <= x /\ x <= b /\ EXISTS (\p. poly p x = &0) l <=>
                      ?n:num. n < N /\ (x = i n))
Proof
  GEN_TAC
  >> DISCH_THEN (MP_TAC o MATCH_MP POLYS_INTERVAL_ROOTS_FINITE_SET)
  >> DISCH_THEN(MP_TAC o SPECL [`a:real`, `b:real`])
  >> DISCH_THEN(MP_TAC o MATCH_MP FINITE_ORDER) >> strip_tac
  >> qexists_tac ‘i’ >> qexists_tac ‘N’ >> gs[]
QED


(* ------------------------------------------------------------------------- *)
(* Hence we can get separating intervals for the various roots.              *)
(* ------------------------------------------------------------------------- *)

Theorem lemma0[local]:
  (!x y. x * inv(&2) <= y <=> x <= &2 * y) ∧
  (!x y. x <= y * inv(&2) <=> &2 * x <= y)
Proof
  rpt strip_tac
  >- (
    ‘&2*y = y* &2’ by metis_tac[REAL_MUL_COMM]
    >> pop_assum $ rewrite_tac o single
    >> ‘x* inv(&2) = x / &2’ by gs[GSYM real_div]
    >> pop_assum $ rewrite_tac o single
    >> irule REAL_LE_LDIV_EQ >> gs[]
  )
  >> ‘&2 * x = x * &2’ by metis_tac[REAL_MUL_COMM]
  >> pop_assum $ rewrite_tac o single
  >> ‘y * inv(&2) = y / &2’ by  gs[GSYM real_div]
  >> pop_assum $ rewrite_tac o single
  >> irule REAL_LE_RDIV_EQ >> gs[]
QED


Theorem lemma1[local]:
 ∀x1 x2:real. a <= x1 /\ x1 < x2 ==> a <= (x1 + x2) / &2
Proof
  REWRITE_TAC[real_div, lemma0] >> REAL_ARITH_TAC
QED

Theorem lemma2[local]:
  ∀ x0 x1:real. x0 < x1 /\ x1 < x2 ==> (x0 + x1) / &2 <= (x1 + x2) / &2
Proof
  REWRITE_TAC[real_div, lemma0, REAL_MUL_ASSOC]
  >> REAL_ARITH_TAC
QED

Theorem lemma3[local]:
 ∀x1 x2:real.  x1 < x2 /\ x2 <= b ==> (x1 + x2) / &2 <= b
Proof
  REWRITE_TAC[real_div, lemma0] >> REAL_ARITH_TAC
QED

Theorem lemma8a[local]:
  (!k. (i: num -> real) k < i(SUC k)) ==> !m n. m < n ==> i m < i n
Proof
  STRIP_TAC >> GEN_TAC
  >> rpt strip_tac
  >> SUBGOAL_THEN ‘∃ (p:num). n = m + (p+1)’ MP_TAC
  >- ( irule arithmeticTheory.LESS_ADD_1 >> gs[] )
  >> gs[boolTheory.PULL_EXISTS]
  >> REWRITE_TAC[GSYM arithmeticTheory.ADD1]
  >> Q.SPEC_TAC (`n`, `n`) >> Q.SPEC_TAC (`m`, `m`)
  >> Induct_on ‘p’
  >- ( REWRITE_TAC[arithmeticTheory.ADD_CLAUSES] >> gs[] )
  >> REWRITE_TAC[arithmeticTheory.ADD_CLAUSES]
  >> rpt STRIP_TAC
  >> MATCH_MP_TAC REAL_LT_TRANS
  >> EXISTS_TAC `i(SUC(m' + p)):real` >> gs[]
  >> ‘SUC (m' + p) = m' + SUC p’ by REWRITE_TAC[arithmeticTheory.ADD_CLAUSES]
  >> pop_assum $ once_rewrite_tac o single >> first_x_assum irule
QED

Theorem lemma8b[local]:
  (!k. (i: num->real) k < i(SUC k)) ==> !m n. i m < i n <=> m < n
Proof
  DISCH_THEN(MP_TAC o MATCH_MP lemma8a)
  >> mesonLib.MESON_TAC[REAL_LT_REFL, REAL_LT_ANTISYM,
                        arithmeticTheory.LESS_LESS_CASES]
QED

Theorem lemma8[local]:
  (!k. (i: num->real) k < i(SUC k)) ==> !m n. (i m <= i n) <=> m <= n
Proof
  DISCH_THEN(MP_TAC o MATCH_MP lemma8b)
  >> REWRITE_TAC[GSYM arithmeticTheory.NOT_LESS_EQUAL, GSYM REAL_NOT_LE]
  >> mesonLib.MESON_TAC[]
QED

Theorem lemma5[local]:
  (!k. (i: num->real) k < i(SUC k)) ==> !k n. i k <= (i n + i(SUC n)) / &2
                                 ==> k <= n
Proof
  DISCH_TAC
  >> REWRITE_TAC[arithmeticTheory.LESS_EQ_IFF_LESS_SUC]
  >> FIRST_ASSUM(fn th => REWRITE_TAC[GSYM(MATCH_MP lemma8b th)])
  >> REPEAT GEN_TAC >> REWRITE_TAC[real_div, lemma0]
  >> POP_ASSUM(MP_TAC o SPEC `n:num`) >> REAL_ARITH_TAC
QED

Theorem lemma6[local]:
  (!k. (i:num->real) k < i(SUC k)) ==> !k n. (i k + i (SUC k)) / &2 <= i n
                                 ==> SUC k <= n
Proof
  DISCH_TAC >> REWRITE_TAC[GSYM arithmeticTheory.LESS_EQ]
  >> FIRST_ASSUM(fn th => REWRITE_TAC[GSYM(MATCH_MP lemma8b th)])
  >> REPEAT GEN_TAC >> REWRITE_TAC[real_div, lemma0]
  >> POP_ASSUM(MP_TAC o SPEC `k:num`) >> REAL_ARITH_TAC
QED

Theorem lemma7[local]:
  (!k. (i: num->real) k < i(SUC k)) ==> !k n. (i n + i(SUC n)) / &2 <= i k /\
                                 i k <= (i(SUC n) + i(SUC(SUC n))) / &2
                                 ==> (k = SUC n)
Proof
  REPEAT STRIP_TAC
  >> irule arithmeticTheory.LESS_EQUAL_ANTISYM
  >> CONJ_TAC
  >- ( FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP lemma6) >> gs[] )
  >> FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP lemma5) >> gs[]
QED

Theorem lemma4[local]:
  (!k. (i:num->real) k < i(SUC k)) ==> !k n. ~((i k + i (SUC k)) = 2 * i n)
Proof
  DISCH_TAC >> REPEAT GEN_TAC
  >> ONCE_REWRITE_TAC[GSYM REAL_LE_ANTISYM] >> STRIP_TAC
  >> SUBGOAL_THEN `~(SUC k <= k)` MP_TAC
  >-  gs[]
  >> REWRITE_TAC[]
  >> MATCH_MP_TAC arithmeticTheory.LESS_EQ_TRANS
  >> EXISTS_TAC `n:num`
  >> CONJ_TAC
  >- ( FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP lemma6) >> gs[] )
  >> FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP lemma5) >> gs[]
QED

Theorem POLYS_INTERVAL_SEPARATION:
 !f l a b.
       a <= b /\
       EVERY (\p. ~(poly p = poly [])) l /\
       ~(poly f a = &0) /\
       ~(poly f b = &0)
       ==> ?i N. (i 0 = a) /\ (i N = b) /\
                 (!k. i(k) <= i(SUC k)) /\
                 (!k. k <= N ==> ~(poly f (i k) = &0)) /\
                 (!k. ?c. i(k) <= c /\ c <= i(SUC k) /\
                          !x. i(k) <= x /\ x <= i(SUC k) /\
                              EXISTS (\p. poly p x = &0) (CONS f l)
                              ==> (x = c))
Proof
  REPEAT STRIP_TAC
  >> SUBGOAL_THEN `EVERY (\p. ~(poly p = poly [])) (CONS f l)` MP_TAC
  >- (
    ASM_REWRITE_TAC[EVERY_DEF] >> UNDISCH_TAC `~(poly f a = &0)`
    >> CONV_TAC CONTRAPOS_CONV >> REWRITE_TAC[] >> gs[]
    >> REWRITE_TAC[poly_def]
  )
  >> DISCH_THEN(MP_TAC o MATCH_MP POLYS_ENUM_ROOTS)
  >> DISCH_THEN(X_CHOOSE_THEN “i:num->real” MP_TAC)
  >> DISCH_THEN(X_CHOOSE_THEN “N:num” STRIP_ASSUME_TAC)
  >> EXISTS_TAC `\n. if n = 0 then a:real else if n < N then
                       (i(PRE n) + i(n)) / &2 else b`
  >> EXISTS_TAC `SUC N` >> gs[]
  >> REPEAT CONJ_TAC
  >- (
    GEN_TAC >> gs[]
    >> ASM_CASES_TAC “k:num=0”
    >- (
      ASM_CASES_TAC  “k<N:num”
      >- (
        ASM_CASES_TAC “SUC k < N”
        >> ASM_REWRITE_TAC[REAL_LE_REFL]
        >- (
          MATCH_MP_TAC lemma1 >> ASM_REWRITE_TAC[]
          >> FIRST_ASSUM(MP_TAC o SPEC `(i:num->real) 0`)
          >> CONV_TAC CONTRAPOS_CONV
          >> DISCH_THEN(fn th => REWRITE_TAC[th])
          >> EXISTS_TAC `k:num` >> ASM_REWRITE_TAC[]
        )
      )
      >> gs[]
    )
    >> gs[] >> ASM_CASES_TAC “k<N:num”
    >- (
      ASM_CASES_TAC “SUC k < N”
      >- (
        gs[] >> ‘k = (SUC (PRE k))’ by gs[]
        >> ‘i k = i (SUC (PRE k))’ by metis_tac[]
        >> ‘i (PRE k) + i k = i k + i (PRE k)’ by real_tac
        >> ntac 2 $ pop_assum $ once_rewrite_tac o single
        >> gs[]
        >> last_assum $ qspec_then ‘PRE k’ assume_tac >> gs[]
        >> ‘i (PRE k) < i (SUC k)’ suffices_by real_tac
        >> irule REAL_LT_TRANS
        >> qexists_tac ‘i (SUC (PRE k))’ >> gs[]
        >> ‘(SUC (PRE k)) = k’ by gs[]
        >> pop_assum $ once_rewrite_tac o single
        >> gs[])
      >> asm_rewrite_tac[]
      >> MATCH_MP_TAC lemma3
      >> CONJ_TAC
      >- ( ‘k = (SUC (PRE k))’ by gs[] >> metis_tac[] )
      >> FIRST_ASSUM(MP_TAC o SPEC `(i:num->real) k`)
      >> CONV_TAC CONTRAPOS_CONV
      >> DISCH_THEN(fn th => REWRITE_TAC[th])
      >> EXISTS_TAC `k:num` >> ASM_REWRITE_TAC[]
    )
    >> gs[]
  )
  >- (
    GEN_TAC >> ASM_CASES_TAC “k:num =0”
    >- (
      ASM_REWRITE_TAC[]
      >> DISCH_TAC >> gs[]
    )
    >> gs[]
    >> COND_CASES_TAC >> ASM_REWRITE_TAC[]
    >> DISCH_TAC
    >> FIRST_ASSUM(MP_TAC o SPEC `(i (PRE k) + i k) / &2`)
    >> SUBGOAL_THEN `a:real <= ((i:num->real) (PRE k) + i k) / &2 /\
                  (i (PRE k) + i k) / &2 <= b:real`
        (fn th => REWRITE_TAC[th])
    >- (
      CONJ_TAC
      >- (
        MATCH_MP_TAC lemma1
        >> CONJ_TAC
        >- (
          FIRST_ASSUM(MP_TAC o SPEC `(i:num->real) (PRE k)`)
          >> CONV_TAC CONTRAPOS_CONV
          >> DISCH_THEN(fn th => REWRITE_TAC[th])
          >> EXISTS_TAC `(PRE k):num`
          >> gs[]
        )
        >> ‘k = (SUC (PRE k))’ by gs[]
        >> ‘i k = i (SUC (PRE k))’ by metis_tac[] >> gs[]
      )
      >> MATCH_MP_TAC lemma3
      >> CONJ_TAC
      >- ( ‘k = (SUC (PRE k))’ by gs[] >> metis_tac[] )
      >> FIRST_ASSUM(MP_TAC o SPEC `(i:num->real) k`)
      >> CONV_TAC CONTRAPOS_CONV
      >> DISCH_THEN(fn th => REWRITE_TAC[th])
      >> EXISTS_TAC `k:num` >> ASM_REWRITE_TAC[]
    )
    >> CONV_TAC CONTRAPOS_CONV >> gs[] >> strip_tac
    >> gen_tac >> rewrite_tac[IMP_DISJ_THM]
    >> DISJ1_TAC
    >> ‘k= SUC(PRE k)’ by gs[]
    >> ‘i k = i (SUC (PRE k))’ by metis_tac[]
    >> pop_assum $ rewrite_tac o single
    >> irule (SIMP_RULE (simpLib.mk_simpset [realSimps.RMULRELNORM_ss]) [] lemma4) >> metis_tac[]
  )
  >> GEN_TAC >> gs[]
  >> ASM_CASES_TAC “k:num =0” >> ASM_REWRITE_TAC[]
  >- (
    ASM_CASES_TAC “N:num=0”
    >- (
      EXISTS_TAC `a:real` >> ASM_REWRITE_TAC[REAL_LE_REFL]
      >> rw[]
    )
    >> ASM_CASES_TAC “N= SUC 0” >> rw[]
    >- (
      EXISTS_TAC `(i:num->real) 0` >> gs[]
      >> REPEAT CONJ_TAC
      >- (
        FIRST_ASSUM(MP_TAC o SPEC `(i:num->real) 0`)
        >> CONV_TAC CONTRAPOS_CONV
        >> DISCH_THEN(fn th => REWRITE_TAC[th])
        >> EXISTS_TAC `0:num` >> gs[]
      )
      >-(
        FIRST_ASSUM(MP_TAC o SPEC `(i:num->real) 0`)
        >> CONV_TAC CONTRAPOS_CONV
        >> DISCH_THEN(fn th => REWRITE_TAC[th])
        >> EXISTS_TAC `0:num` >> gs[]
      )
      >> gen_tac >> strip_tac >> gs[]
      >> ‘n=0’ by gs[] >> metis_tac[]
    )
    >> SUBGOAL_THEN `SUC 0 < N` ASSUME_TAC
    >- (
      REWRITE_TAC[GSYM arithmeticTheory.NOT_LESS_EQUAL]
      >> gs[]
    )
    >> ASM_REWRITE_TAC[] >> EXISTS_TAC `(i:num->real) 0`
    >> SUBGOAL_THEN `a:real <= i 0 /\
                    (i:num ->real) 0 <= (i 0 + i (SUC 0)) / &2 /\
                    (i 0 + i (SUC 0)) / &2 <= b:real`
                                               STRIP_ASSUME_TAC
    >- (
      REPEAT CONJ_TAC
      >- (
        FIRST_ASSUM(MP_TAC o SPEC `(i:num->real) 0`)
        >> CONV_TAC CONTRAPOS_CONV
        >> DISCH_THEN(fn th => REWRITE_TAC[th])
        >> EXISTS_TAC `0:num` >> rw[]
      )
      >- (
        MATCH_MP_TAC lemma1
        >> ASM_REWRITE_TAC[REAL_LE_REFL]
      )
      >> MATCH_MP_TAC lemma3 >> ASM_REWRITE_TAC[]
      >> FIRST_ASSUM(MP_TAC o SPEC `(i:num->real) (SUC 0)`)
      >> CONV_TAC CONTRAPOS_CONV
      >> DISCH_THEN(fn th => REWRITE_TAC[th])
      >> EXISTS_TAC `SUC 0` >> ASM_REWRITE_TAC[]
    )
    >> ‘1 = SUC 0’ by gs[] >> pop_assum $ rewrite_tac o single
    >> ASM_REWRITE_TAC[] >> conj_tac >- gs[]
    >> X_GEN_TAC “x:real”
    >> ‘ (poly f x = 0 ∨ EXISTS (λp. poly p x = 0) l) =
         EXISTS (\p. poly p x = &0) (CONS f l) ’ by gs[]
    >> pop_assum $ rewrite_tac o single
    >> STRIP_TAC
    >> SUBGOAL_THEN `a <= x /\ x <= b /\
                    EXISTS (\p. poly p x = &0) (CONS f l)`
                                                MP_TAC
    >- (
      REPEAT CONJ_TAC
      >- ASM_REWRITE_TAC[]
      >- (
        MATCH_MP_TAC REAL_LE_TRANS
        >> EXISTS_TAC `((i:num->real) 0 + i (SUC 0)) / &2`
        >> gs[]
      )
      >> rw[]
    )
    >> first_assum $ qspec_then ‘x’ (fn th => let val (th1, th2) =
               EQ_IMP_RULE th in assume_tac th1 end)
    >> rpt strip_tac >> qpat_x_assum ‘_ ⇒ ∃ n. n < N ∧ x = i n’ mp_tac
    >> impl_tac
    >- (rpt conj_tac >> gs[])
    >> DISCH_THEN(X_CHOOSE_THEN “n:num” STRIP_ASSUME_TAC)
    >> ASM_REWRITE_TAC[] >> AP_TERM_TAC
    >> UNDISCH_TAC `2 * x:real <= (i 0 + i (SUC 0))`
    >> ASM_REWRITE_TAC[]
    >> FIRST_ASSUM(ASSUME_TAC o MATCH_MP lemma5)
    >> gs[]
    >> ‘1 = SUC 0’ by gs[]
    >> pop_assum $ rewrite_tac o single
    >> DISCH_THEN(ANTE_RES_THEN MP_TAC) >> gs[]
  )
  >> ASM_CASES_TAC “SUC k < N”
  >- (
    SUBGOAL_THEN `k < N:num` ASSUME_TAC
    >- gs[]
    >> ASM_REWRITE_TAC[]
    >> EXISTS_TAC `(i:num->real) k` >> REPEAT CONJ_TAC
    >- (
      MATCH_MP_TAC lemma3
      >> CONJ_TAC
      >- (
        ‘k = SUC (PRE k)’ by gs[]
        >> metis_tac[]
      )
      >> gs[]
    )
    >- ( MATCH_MP_TAC lemma1 >> gs[] )
    >>  X_GEN_TAC “x:real”
    >> ‘ (poly f x = 0 ∨ EXISTS (λp. poly p x = 0) l) =
         EXISTS (\p. poly p x = &0) (CONS f l) ’ by gs[]
    >> pop_assum $ rewrite_tac o single
    >> STRIP_TAC
    >> SUBGOAL_THEN `a <= x /\ x <= b /\
                       EXISTS (\p. poly p x = &0) (CONS f l)`
                              MP_TAC
    >- (
      REPEAT CONJ_TAC
      >- (
        MATCH_MP_TAC REAL_LE_TRANS
        >> EXISTS_TAC `((i:num->real) (PRE k) + i k) / &2`
        >> ASM_REWRITE_TAC[]
        >> MATCH_MP_TAC lemma1 >> CONJ_TAC
        >- (
          FIRST_ASSUM(MP_TAC o SPEC `(i:num->real) (PRE k)`)
          >> CONV_TAC CONTRAPOS_CONV
          >> DISCH_THEN(fn th => REWRITE_TAC[th])
          >> EXISTS_TAC `PRE k` >> ASM_REWRITE_TAC[]
          >> UNDISCH_TAC `k < N:num` >> gs[]
        )
        >> ‘k= SUC (PRE k)’ by gs[]
        >> metis_tac[]
      )
      >- (
        MATCH_MP_TAC REAL_LE_TRANS
        >> EXISTS_TAC `((i:num->real) k + i(SUC k)) / &2`
        >> ASM_REWRITE_TAC[]
        >> MATCH_MP_TAC lemma3 >> ASM_REWRITE_TAC[]
        >> FIRST_ASSUM(MP_TAC o SPEC `(i:num->real) (SUC k)`)
        >> CONV_TAC CONTRAPOS_CONV
        >> DISCH_THEN(fn th => REWRITE_TAC[th])
        >> EXISTS_TAC `SUC k` >> ASM_REWRITE_TAC[]
      )
      >> gs[]
    )
    >> first_assum $ qspec_then ‘x’ (fn th => let val (th1, th2) =
                 EQ_IMP_RULE th in assume_tac th1 end)
    >> rpt strip_tac >> qpat_x_assum ‘_ ⇒ ∃ n. n < N ∧ x = i n’ mp_tac
    >> impl_tac
    >- (rpt conj_tac >> gs[])
    >> DISCH_THEN(X_CHOOSE_THEN “n:num” STRIP_ASSUME_TAC)
    >> ASM_REWRITE_TAC[] >> AP_TERM_TAC
    >> SUBGOAL_THEN `((i:num->real) (PRE k) + i k) / &2 <= i n /\
                    i n <= (i k + i (SUC k)) / &2`
                                             MP_TAC
    >- (
      FIRST_ASSUM(UNDISCH_TAC o (fn t => `^t`) o check is_eq o concl)
      >> DISCH_THEN SUBST_ALL_TAC >> ASM_REWRITE_TAC[]
    )
    >> UNDISCH_TAC `~(k:num = 0)`
    >> SPEC_TAC(“k:num”,“m:num”)
    >> Induct_on ‘m’
    >- gs[]
    >> strip_tac >> ‘PRE (SUC m) = m’ by gs[]
    >> pop_assum $ rewrite_tac o single
    >> FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP lemma7)
  )
  >> ASM_CASES_TAC “k< N:num” >> ASM_REWRITE_TAC[]
  >- (
    EXISTS_TAC `(i:num->real) k`
    >> ASM_REWRITE_TAC[CONJ_ASSOC]
    >> ‘ ((i (PRE k) + i k) / 2 ≤ i k ∧ i k ≤ b)’ by
      (
        CONJ_TAC
        >- (
          irule REAL_MIDDLE2
          >> ‘k= SUC (PRE k)’ by gs[]
          >> irule REAL_LT_IMP_LE >> metis_tac[]
        )
        >> FIRST_ASSUM(MP_TAC o SPEC `(i:num->real) k`)
        >> CONV_TAC CONTRAPOS_CONV
        >> DISCH_THEN(fn th => REWRITE_TAC[th])
        >> EXISTS_TAC ‘k:num’ >> ASM_REWRITE_TAC[]
      )
    >> ASM_REWRITE_TAC[]
    >> X_GEN_TAC “x:real”
    >> ‘ (poly f x = 0 ∨ EXISTS (λp. poly p x = 0) l) =
         EXISTS (\p. poly p x = &0) (CONS f l) ’ by gs[]
    >> pop_assum $ rewrite_tac o single
    >> STRIP_TAC
    >> SUBGOAL_THEN `a <= x /\ x <= b /\
        EXISTS (\p. poly p x = &0) (CONS f l)`
              MP_TAC
    >- (
      REPEAT CONJ_TAC
      >- (
        MATCH_MP_TAC REAL_LE_TRANS
        >> EXISTS_TAC `((i:num->real) (PRE k) + i k) / &2`
        >> ASM_REWRITE_TAC[] >> MATCH_MP_TAC lemma1
        >> CONJ_TAC
        >- (
          FIRST_ASSUM(MP_TAC o SPEC `(i:num->real) (PRE k)`)
          >> CONV_TAC CONTRAPOS_CONV
          >> DISCH_THEN(fn th => REWRITE_TAC[th])
          >> EXISTS_TAC `PRE k` >> ASM_REWRITE_TAC[]
          >> UNDISCH_TAC `k < N:num` >> gs[]
        )
        >> ‘k= SUC (PRE k)’ by gs[] >> metis_tac[]
      )
      >- ASM_REWRITE_TAC[]
      >> metis_tac[]
    )
    >> first_assum $ qspec_then ‘x’ (fn th => let val (th1, th2) =
                       EQ_IMP_RULE th in assume_tac th1 end)
    >> rpt strip_tac >> qpat_x_assum ‘_ ⇒ ∃ n. n < N ∧ x = i n’ mp_tac
    >> impl_tac
    >- (rpt conj_tac >> gs[])
    >> DISCH_THEN(X_CHOOSE_THEN “n:num” STRIP_ASSUME_TAC)
    >> ASM_REWRITE_TAC[] >> AP_TERM_TAC
    >> FIRST_ASSUM(MP_TAC o SPECL [`n:num`, `PRE k`] o MATCH_MP lemma7)
    >> FIRST_ASSUM(UNDISCH_TAC o (fn t => `^t`) o check is_eq o concl)
    >> DISCH_THEN SUBST_ALL_TAC
    >> UNDISCH_TAC `((i:num->real) (PRE k) + i k) / &2 <= i n`
    >> SUBGOAL_THEN `(i:num->real) n <= (i k + i(SUC k)) / &2` MP_TAC
    >- (
      MATCH_MP_TAC lemma1 >> ASM_REWRITE_TAC[]
      >> FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP lemma8 th])
      >> UNDISCH_TAC `n < N:num`
      >> UNDISCH_TAC `~(SUC k < N)` >> gs[]
    )
    >> UNDISCH_TAC `~(k:num = 0)` >>  SPEC_TAC(“k:num”, “m:num”)
    >> Induct_on ‘m’
    >- gs[]
    >> gs[] >> mesonLib.MESON_TAC[]
  )
  >> gs[] >> EXISTS_TAC ‘b:real’
  >> ASM_REWRITE_TAC[REAL_LE_REFL]
  >> REWRITE_TAC[CONJ_ASSOC, REAL_LE_ANTISYM]
  >> gs[]
QED


(* ------------------------------------------------------------------------- *)
(* Basic lemma.                                                              *)
(* ------------------------------------------------------------------------- *)

Theorem  STURM_LEMMA_lemma[local] :
 ∀ s: real->bool. (s INTER t = EMPTY) ==> FINITE s /\ FINITE t ==>
 (CARD (s UNION t) = CARD s + CARD t)
Proof
  rpt strip_tac
  >> ‘CARD (s ∩ t) = 0’ by gs[CARD_DEF]
  >> ‘CARD (s ∪ t) = CARD (s ∪ t) + CARD (s ∩ t)’ by gs[]
  >> metis_tac[CARD_UNION]
QED

Theorem STURM_LEMMA:
 !i n.
        rsquarefree f /\
        STURM f (diff f) l /\
        (!k. i k <= i (SUC k)) /\
        (!k. k <= n ==> ~(poly f (i k) = &0)) /\
        (!k. ?c. i k <= c /\
                 c <= i (SUC k) /\
                 (!x. i k <= x /\
                      x <= i (SUC k) /\
                      EXISTS (\p. poly p x = &0) (CONS f (CONS (diff f) l))
                      ==> (x = c)))
        ==> FINITE { x | i 0 <= x /\ x <= i n /\ (poly f x = &0) } /\
            (variation (MAP (\p. poly p (i n))
                            (CONS f (CONS (diff f) l))) +
             CARD { x | i 0 <= x /\ x <= i n /\ (poly f x = &0) } =
             variation (MAP (\p. poly p (i 0))
                        (CONS f (CONS (diff f) l))))
Proof
  GEN_TAC >> Induct_on ‘n’
  >- (
    STRIP_TAC
    >> SUBGOAL_THEN `{x | (i:num->real) 0 <= x /\ x <= (i:num->real) 0 /\ (poly f x = &0)} = {}`
       SUBST1_TAC
    >- (
      REWRITE_TAC[EXTENSION, NOT_IN_EMPTY]
      >> REWRITE_TAC[CONJ_ASSOC, REAL_LE_ANTISYM]
      >> UNDISCH_TAC `!(k:num). k <= 0 ==> ~(poly f (i k) = &0)`
      >> DISCH_THEN(MP_TAC o SPEC `0`)
      >> REWRITE_TAC[arithmeticTheory.LESS_EQ_REFL] >> gs[]
    )
    >> CONJ_TAC
    >- metis_tac[FINITE_EMPTY]
    >> gs[CARD_DEF]
  )
(** second subgoal begins **)
  >> STRIP_TAC
  >> SUBGOAL_THEN `({x | i 0 <= x /\ x <= i (SUC n) /\ (poly f x = &0)} =
                   {x | i 0 <= x /\ x <= i n /\ (poly f x = &0)} UNION
                   {x | i n <= x /\ x <= i (SUC n) /\ (poly f x = &0)}) /\
                  ({x | i 0 <= x /\ x <= i n /\ (poly f x = &0)} INTER
                   {x | i n <= x /\ x <= i (SUC n) /\ (poly f x = &0)} =
                   EMPTY)`
    STRIP_ASSUME_TAC
  >- (
    REWRITE_TAC[EXTENSION, IN_INTER, IN_UNION]
    >> CONJ_TAC
    >- (
      GEN_TAC >> gs[] >> REWRITE_TAC[CONJ_ASSOC]
      >> REWRITE_TAC[tautLib.TAUT `a /\ c \/ b /\ c <=> (a \/ b) /\ c`]
      >> MATCH_MP_TAC(tautLib.TAUT `(c ==> (a <=> b)) ==> (a /\ c <=> b /\ c)`)
      >> DISCH_TAC >> eq_tac
      >- (
        strip_tac
        >> Cases_on `x <= i n` >> gs[REAL_NOT_LE, REAL_LT_LE]
      )
      >> strip_tac THEN gs[]
      >- (
        MATCH_MP_TAC REAL_LE_TRANS
        >> EXISTS_TAC `(i:num->real) n` >> gs[]
      )
      >> MATCH_MP_TAC REAL_LE_TRANS >> EXISTS_TAC `(i:num->real) n`
      >> gs[] >> SPEC_TAC(“n:num”, “m:num”)
      >> Induct_on ‘m’
      >- gs[]
      >> MATCH_MP_TAC REAL_LE_TRANS
      >> EXISTS_TAC `(i:num->real) m` >> gs[]
    )
    >> GEN_TAC >> REWRITE_TAC[NOT_IN_EMPTY] >> STRIP_TAC
    >> UNDISCH_TAC `!k. k <= SUC n ==> ~(poly f (i k) = &0)` >> gs[]
    >> EXISTS_TAC ‘n:num’ >> gs[arithmeticTheory.LESS_EQ_SUC_REFL]
    >> SUBGOAL_THEN `(i:num->real) n = x`
          (fn th => ASM_REWRITE_TAC[th])
    >> ONCE_REWRITE_TAC[GSYM REAL_LE_ANTISYM]
    >> ASM_REWRITE_TAC[]
  )
  >> FIRST_ASSUM(UNDISCH_TAC o (fn t => `^t`) o check is_imp o concl)
  >> ASM_REWRITE_TAC[]
  >> SUBGOAL_THEN `!k:num. k <= n ==> ~(poly f (i k) = &0)` ASSUME_TAC
  >- (
    GEN_TAC >> DISCH_TAC >> FIRST_ASSUM MATCH_MP_TAC
    >> UNDISCH_TAC `k <= n:num` >> gs[]
  )
  >> ASM_REWRITE_TAC[]
  >> DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)
  >> FIRST_ASSUM(X_CHOOSE_THEN “c:real” STRIP_ASSUME_TAC o SPEC `n:num`)
  >> MP_TAC(SPECL [`l:(real list)list`, `f:real list`] STURM_COMPONENT)
  >> DISCH_THEN(MP_TAC o SPECL [`(i:num->real) n`, `(i:num->real)(SUC n)`])
  >> DISCH_THEN(MP_TAC o SPEC `c:real`) >> ASM_REWRITE_TAC[]
  >> SUBGOAL_THEN `~(poly f (i n) = &0) /\ ~(poly f (i (SUC n)) = &0)`
                                           ASSUME_TAC
  >- (
    UNDISCH_TAC `!k:num. k <= n ==> ~(poly f (i k) = &0)`
    >> DISCH_THEN(K ALL_TAC) >> CONJ_TAC
    >> FIRST_ASSUM MATCH_MP_TAC >> rw[]
  )
  >> ASM_REWRITE_TAC[]
  >> ASM_CASES_TAC “poly f c = &0” >> ASM_REWRITE_TAC[]
  >- (
    SUBGOAL_THEN
    `FINITE {x | i n <= x /\ x <= i (SUC n) /\ (poly f x = &0)} /\
    (CARD {x | i n <= x /\ x <= i (SUC n) /\ (poly f x = &0)} = 1)`
          STRIP_ASSUME_TAC
    >- (
      SUBGOAL_THEN `{x | i n <= x /\ x <= i (SUC n) /\ (poly f x = &0)} =
                      {c}`
                         SUBST_ALL_TAC
      >- (
        REWRITE_TAC[EXTENSION, IN_INSERT, NOT_IN_EMPTY]
        >> X_GEN_TAC “x:real” >> EQ_TAC
        >- (
          STRIP_TAC
          >> ASM_REWRITE_TAC[] >> FIRST_ASSUM MATCH_MP_TAC
          >> ASM_REWRITE_TAC[listTheory.EXISTS_DEF]
          >> ‘i n ≤ x ∧ x ≤ i (SUC n) ∧ poly f x = 0’ by
            (
              pop_assum mp_tac
              >> disch_then $ MATCH_ACCEPT_TAC o
                                    SIMP_RULE std_ss [IN_GSPEC_IFF]
            )
          >> metis_tac[]
        )
        >> strip_tac >> rw[]
      )
      >> REWRITE_TAC[FINITE_INSERT] >> rw[CARD_SING, FINITE_EMPTY]
    )
    >> rpt strip_tac
    >- ( REWRITE_TAC[FINITE_UNION] >> rw[] )
    >> FIRST_ASSUM(MP_TAC o MATCH_MP STURM_LEMMA_lemma)
    >> ASM_REWRITE_TAC[]
    >> DISCH_THEN SUBST_ALL_TAC
    >> REWRITE_TAC[GSYM arithmeticTheory.ADD1, arithmeticTheory.ADD_CLAUSES,
              arithmeticTheory.LESS_EQ_MONO]
    >> ‘variation (MAP (λp. poly p (i (SUC n))) (f::diff f::l)) +
        CARD {x | i 0 ≤ x ∧ x ≤ i n ∧ poly f x = 0} =
        CARD {x | i 0 ≤ x ∧ x ≤ i n ∧ poly f x = 0} +
        variation (MAP (λp. poly p (i (SUC n))) (f::diff f::l))
       ’ by metis_tac[arithmeticTheory.ADD_COMM]
    >> pop_assum $ rewrite_tac o single
    >> rewrite_tac[arithmeticTheory.SUC_ADD_SYM] >> metis_tac[]
    >> ‘SUC (variation (MAP (λp. poly p (i (SUC n))) (f::diff f::l))) =
        variation (MAP (λp. poly p (i n)) (f::diff f::l)) ’ by metis_tac[]
  )
  >> SUBGOAL_THEN
       `FINITE {x | i n <= x /\ x <= i (SUC n) /\ (poly f x = &0)} /\
        (CARD {x | i n <= x /\ x <= i (SUC n) /\ (poly f x = &0)} = 0)`
         STRIP_ASSUME_TAC
  >- (
    SUBGOAL_THEN `{x | i n <= x /\ x <= i (SUC n) /\ (poly f x = &0)} =
                      EMPTY`
                           SUBST_ALL_TAC
    >- (
      REWRITE_TAC[EXTENSION, IN_INSERT, NOT_IN_EMPTY]
      >> X_GEN_TAC “x:real” >> STRIP_TAC
      >> UNDISCH_TAC `~(poly f c = &0)`
      >> SUBGOAL_THEN `x:real = c` (fn th => ASM_REWRITE_TAC[SYM th])
      >- (
        FIRST_ASSUM MATCH_MP_TAC >> ASM_REWRITE_TAC[listTheory.EXISTS_DEF]
        >> ‘i n ≤ x ∧ x ≤ i (SUC n) ∧ poly f x = 0’ by
          (
            pop_assum mp_tac
            >> disch_then $ MATCH_ACCEPT_TAC o SIMP_RULE std_ss [IN_GSPEC_IFF]
          )
        >> metis_tac[]
      )
      >> ‘i n ≤ x ∧ x ≤ i (SUC n) ∧ poly f x = 0’ by
        (
          pop_assum mp_tac
          >> disch_then $ MATCH_ACCEPT_TAC o SIMP_RULE std_ss [IN_GSPEC_IFF]
        )
    )
    >> rw[]
  )
  >> FIRST_ASSUM(MP_TAC o MATCH_MP STURM_LEMMA_lemma)
  >> ASM_REWRITE_TAC[]
  >> DISCH_THEN SUBST_ALL_TAC >> DISCH_THEN SUBST1_TAC
  >> DISCH_THEN(SUBST1_TAC o SYM)
  >> REWRITE_TAC[GSYM arithmeticTheory.ADD1, arithmeticTheory.ADD_CLAUSES,
              arithmeticTheory.LESS_EQ_MONO]
  >> MATCH_MP_TAC FINITE_UNION_IMP >> ASM_REWRITE_TAC[]
QED

(* ------------------------------------------------------------------------- *)
(* We just need to show that things in Sturm sequence are nontrivial.        *)
(* ------------------------------------------------------------------------- *)

Theorem STURM_NONZERO_LEMMA:
 !l f f'. ~(poly f = poly []) /\ STURM f f' l
          ==> ~(poly f' = poly [])
Proof
  ListConv1.LIST_INDUCT_TAC >> REWRITE_TAC[STURM_def]
  >- (
    REPEAT GEN_TAC >> CONV_TAC CONTRAPOS_CONV
    >> REWRITE_TAC[DE_MORGAN_THM]
    >> DISCH_TAC >> ASM_CASES_TAC “f' poly_divides f”
    >> ASM_REWRITE_TAC[]
    >> UNDISCH_TAC `f' poly_divides f` >> REWRITE_TAC[poly_divides]
    >> DISCH_THEN(CHOOSE_THEN SUBST1_TAC)
    >> ASM_REWRITE_TAC[FUN_EQ_THM, POLY_MUL, REAL_MUL_LZERO, poly_def]
    >> gs[]
  )
  >> REPEAT GEN_TAC >> CONV_TAC CONTRAPOS_CONV
  >> REWRITE_TAC[] >> DISCH_TAC >> ASM_REWRITE_TAC[]
  >> DISCH_THEN(MP_TAC o el 3 o CONJUNCTS)
  >> REWRITE_TAC[arithmeticTheory.NOT_LESS]
  >> FIRST_ASSUM(SUBST1_TAC o  MATCH_MP DEGREE_ZERO)
  >> gs[degree]
QED

Theorem STURM_NONZERO :
 !l f f'. ~(poly f = poly []) /\ STURM f f' l
          ==> EVERY (\p. ~(poly p = poly [])) (CONS f' l)
Proof
  ListConv1.LIST_INDUCT_TAC >> REWRITE_TAC[STURM_def]
  >- (
    REWRITE_TAC[listTheory.EVERY_DEF] >> REPEAT GEN_TAC >> STRIP_TAC
    >> gs[] >>  MATCH_MP_TAC STURM_NONZERO_LEMMA
    >> EXISTS_TAC `[]:(real list)list`
    >> EXISTS_TAC `f:real list` >> ASM_REWRITE_TAC[STURM_def]
  )
  >> REPEAT STRIP_TAC >> ONCE_REWRITE_TAC[listTheory.EVERY_DEF]
  >> ASM_REWRITE_TAC[]
  >> SUBGOAL_THEN `~(poly f' = poly [])` ASSUME_TAC
  >- (
    DISCH_THEN(SUBST_ALL_TAC o MATCH_MP DEGREE_ZERO)
    >> UNDISCH_TAC `degree h < 0` >> gs[]
  )
  >> CONJ_TAC
  >- metis_tac[]
  >> FIRST_ASSUM MATCH_MP_TAC
  >> EXISTS_TAC `f':real list` >> metis_tac[]
QED


(* ------------------------------------------------------------------------- *)
(* And finally...                                                            *)
(* ------------------------------------------------------------------------- *)

Theorem STURM_STRONG:
 !f a b l.
    a <= b /\
    ~(poly f a = &0) /\
    ~(poly f b = &0) /\
    rsquarefree f /\
    STURM f (diff f) l
    ==> FINITE {x | a <= x /\ x <= b /\ (poly f x = &0)} /\
        (variation
           (MAP (\p. poly p b) (CONS f (CONS (diff f) l))) +
         CARD {x | a <= x /\ x <= b /\ (poly f x = &0)} =
         variation
         (MAP (\p. poly p a) (CONS f (CONS (diff f) l))))
Proof
  REPEAT GEN_TAC >> STRIP_TAC
  >> SUBGOAL_THEN `EVERY (\p. ~(poly p = poly [])) (CONS (diff f) l)`
               ASSUME_TAC
  >- (
    MATCH_MP_TAC STURM_NONZERO
    >> EXISTS_TAC `f:real list` >> ASM_REWRITE_TAC[]
    >> DISCH_THEN SUBST_ALL_TAC
    >> UNDISCH_TAC `~(poly [] a = &0)` >> REWRITE_TAC[poly_def]
  )
  >> MP_TAC(SPECL [`f:real list`, `CONS (diff f) l`, `a:real`, `b:real`]
             POLYS_INTERVAL_SEPARATION)
  >> ASM_REWRITE_TAC[]
  >> DISCH_THEN(X_CHOOSE_THEN “i:num->real” MP_TAC)
  >> DISCH_THEN(X_CHOOSE_THEN “N:num” MP_TAC)
  >> DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) MP_TAC)
  >> DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) MP_TAC)
  >> STRIP_TAC >> MATCH_MP_TAC STURM_LEMMA
  >> ASM_REWRITE_TAC[]
QED


Theorem STURM_THM:
!f a b l.
    a <= b /\
    ~(poly f a = &0) /\
    ~(poly f b = &0) /\
    rsquarefree f /\
    STURM f (diff f) l
    ==> {x | a <= x /\ x <= b /\ (poly f x = &0)}
        HAS_SIZE
        (variation
           (MAP (\p. poly p a) (CONS f (CONS (diff f) l))) -
         variation
         (MAP (\p. poly p b) (CONS f (CONS (diff f) l))))
Proof
  REPEAT GEN_TAC
  >> DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP STURM_STRONG)
  >> ASM_REWRITE_TAC[pred_setTheory.HAS_SIZE]
  >> UNDISCH_TAC
    `variation (MAP (\p. poly p b) (CONS f (CONS (diff f) l))) +
       CARD {x | a <= x /\ x <= b /\ (poly f x = &0)} =
  variation (MAP (\p. poly p a) (CONS f (CONS (diff f) l)))`
  >> gs[]
QED

(* ------------------------------------------------------------------------- *)
(* Show that what we get at the end of the Sturm sequence is a GCD.          *)
(* ------------------------------------------------------------------------- *)

Theorem STURM_GCD :
!l k f f'.
        STURM f f' (CONS k l)
        ==> ?q e r s. (poly f = poly (q * LAST (CONS k l))) /\
                      (poly f' = poly (e * LAST (CONS k l))) /\
                      (poly (LAST (CONS k l)) =
                       poly (r * f + s * f'))
Proof
  ListConv1.LIST_INDUCT_TAC
  >- (
    REPEAT GEN_TAC >> REWRITE_TAC[STURM_def, LAST_DEF]
    >> DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)
    >> DISCH_THEN(X_CHOOSE_THEN “c:real” STRIP_ASSUME_TAC)
    >> UNDISCH_TAC `k poly_divides f'` >> REWRITE_TAC[poly_divides]
    >> DISCH_THEN(X_CHOOSE_TAC “e:real list”)
    >> UNDISCH_TAC `f' poly_divides f + c ## k`
    >> REWRITE_TAC[poly_divides]
    >> DISCH_THEN(X_CHOOSE_TAC “g:real list”)
    >> EXISTS_TAC `e * g + [-c]`
    >> EXISTS_TAC `e:real list`
    >> EXISTS_TAC `[-(inv(c))]`
    >> EXISTS_TAC `inv(c) ## g`
    >> SUBGOAL_THEN `poly f = poly ((e * g + [- c]) * k)` ASSUME_TAC
    >- (
      REWRITE_TAC[FUN_EQ_THM] >> X_GEN_TAC “x:real”
      >> UNDISCH_TAC `poly (f + c ## k) = poly (f' * g)`
      >> DISCH_THEN(MP_TAC o SPEC `x:real` o ONCE_REWRITE_RULE[FUN_EQ_THM])
      >> REWRITE_TAC[POLY_ADD, POLY_MUL, POLY_CMUL]
      >> ASM_REWRITE_TAC[poly_def, REAL_MUL_RZERO, REAL_ADD_RID, POLY_MUL]
      >> REAL_ARITH_TAC
    )
    >> ASM_REWRITE_TAC[]
    >> ASM_REWRITE_TAC[FUN_EQ_THM, POLY_MUL, REAL_MUL_AC]
    >> CONJ_TAC
    >- ( X_GEN_TAC “x:real” >> rw[REAL_MUL_SYM] )
    >> X_GEN_TAC “x:real”
    >> ASM_REWRITE_TAC[POLY_MUL, POLY_ADD, POLY_CMUL]
    >> ASM_REWRITE_TAC[poly_def, REAL_MUL_RZERO, REAL_ADD_RID, POLY_MUL]
    >> REWRITE_TAC[REAL_MUL_RNEG, REAL_ADD_LDISTRIB, REAL_ADD_RDISTRIB,REAL_MUL_AC]
    >> rewrite_tac[REAL_MUL_LNEG] >> rewrite_tac[REAL_NEGNEG]
    >> ‘c⁻¹ * poly e x * poly g x * poly k x =
        c⁻¹ * poly g x * poly k x * poly e x’
      by
      (
        ‘poly e x * poly g x * poly k x =
         poly g x * poly k x * poly e x’
         by
         (
           ‘poly e x * poly g x * poly k x =
            poly e x * (poly g x * poly k x)’ by
            rewrite_tac[GSYM REAL_MUL_ASSOC]
           >> pop_assum $ rewrite_tac o single
           >> rw [REAL_MUL_SYM]
         )
        >> REAL_ARITH_TAC
      )
    >> pop_assum $ rewrite_tac o single
    >> REWRITE_TAC[REAL_ARITH `(-a + b) + (a:real) = (b:real)`]
    >> ONCE_REWRITE_TAC[REAL_MUL_SYM]
    >> `inv(c) * (c:real) = &1` by
      (
        MATCH_MP_TAC REAL_MUL_LINV
        >> UNDISCH_TAC `&0 < c:real` >> REAL_ARITH_TAC
      )
    >> gs[]
  )
  (* second goal starts here *)
  >> REPEAT GEN_TAC >> ONCE_REWRITE_TAC[LAST_DEF]
  >> ONCE_REWRITE_TAC[STURM_def] >> REWRITE_TAC[NOT_CONS_NIL]
  >> DISCH_THEN(CONJUNCTS_THEN MP_TAC)
  >> DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)
  >> DISCH_THEN(ANTE_RES_THEN MP_TAC) >> STRIP_TAC
  >> DISCH_THEN(X_CHOOSE_THEN “c:real” MP_TAC)
  >> DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)
  >> REWRITE_TAC[poly_divides]
  >> DISCH_THEN(X_CHOOSE_THEN “u:real list” ASSUME_TAC)
  >> EXISTS_TAC `q * u + (-c) ## e`
  >> EXISTS_TAC `q:real list`
  >> EXISTS_TAC `-(inv c) ## s`
  >> EXISTS_TAC `r + inv c ## s * u`
  >> ASM_REWRITE_TAC[]
  >> SUBGOAL_THEN `poly f = poly ((q * u + - c ## e) * LAST (CONS h l))`
                                ASSUME_TAC
  >- (
    UNDISCH_TAC `poly (LAST (CONS h l)) = poly (r * f' + s * k)`
    >> DISCH_THEN(K ALL_TAC)
    >> REWRITE_TAC[FUN_EQ_THM] >> X_GEN_TAC “x:real”
    >> UNDISCH_TAC `poly (f + c ## k) = poly (f' * u)`
    >> DISCH_THEN(MP_TAC o SPEC `x:real` o ONCE_REWRITE_RULE[FUN_EQ_THM])
    >> REWRITE_TAC[POLY_ADD, POLY_MUL, POLY_CMUL]
    >> ASM_REWRITE_TAC[poly_def, REAL_MUL_RZERO, REAL_ADD_RID, POLY_MUL]
    >> REAL_ARITH_TAC
  )
  >> ASM_REWRITE_TAC[]
  >> UNDISCH_TAC `poly (LAST (CONS h l)) = poly (r * f' + s * k)`
  >> DISCH_THEN(K ALL_TAC)
  >> REWRITE_TAC[FUN_EQ_THM] >> X_GEN_TAC “x:real”
  >> ASM_REWRITE_TAC[POLY_ADD, POLY_MUL, POLY_CMUL, POLY_NEG]
  >> REWRITE_TAC[REAL_ADD_LDISTRIB, REAL_ADD_RDISTRIB]
  >> REWRITE_TAC[REAL_MUL_LNEG, REAL_MUL_RNEG, REAL_MUL_AC]
  >> REWRITE_TAC[REAL_NEG_NEG]
  >> ‘c⁻¹ * poly s x * poly q x * poly u x * poly (LAST (h::l)) x =
      c⁻¹ * poly s x * poly u x * poly q x * poly (LAST (h::l)) x ’
    by REAL_ARITH_TAC >> pop_assum $ rewrite_tac o single
  >> REWRITE_TAC[REAL_ARITH `-a + b + ((c:real) + (a:real)) = (b:real) + c`]
  >> ‘ c⁻¹ * poly s x * c * poly e x * poly (LAST (h::l)) x =
       poly s x * poly e x * poly (LAST (h::l)) x’ by
    (
      ‘c⁻¹ * poly s x * c * poly e x * poly (LAST (h::l)) x=
       (inv(c) * c) * poly s x * poly e x * poly (LAST (h::l)) x’
       by REAL_ARITH_TAC >> pop_assum $ rewrite_tac o single
      >> `inv(c) * (c:real) = &1` by
        (
          MATCH_MP_TAC REAL_MUL_LINV
          >> UNDISCH_TAC `&0 < c:real` >> REAL_ARITH_TAC
        )
      >> pop_assum $ rewrite_tac o single
      >> REAL_ARITH_TAC
    )
  >> pop_assum $ rewrite_tac o single
  >> REAL_ARITH_TAC
QED


(* ------------------------------------------------------------------------- *)
(* Hence avoid a separate check for squarefreeness.                          *)
(* ------------------------------------------------------------------------- *)

Theorem STURM_THEOREM :
 !f a b l d.
        a <= b /\
        ~(poly f a = &0) /\
        ~(poly f b = &0) /\
        ~(poly (diff f) = poly []) /\
        STURM f (diff f) l /\
        ~(l = []) /\
        (LAST l = [d]) /\
        ~(d = &0)
        ==> {x | a <= x /\ x <= b /\ (poly f x = &0)} HAS_SIZE
            (variation (MAP (\p. poly p a) (CONS f (CONS (diff f) l))) -
             variation (MAP (\p. poly p b) (CONS f (CONS (diff f) l))))
Proof
  REPEAT STRIP_TAC >> MATCH_MP_TAC STURM_THM
  >> ASM_REWRITE_TAC[]
  >> UNDISCH_TAC `LAST l = [d:real]`
  >> UNDISCH_TAC `STURM f (diff f) l`
  >> UNDISCH_TAC `~(l:(real list)list = [])`
  >> SPEC_TAC(“l:(real list)list”, “l:(real list)list”)
  >> ListConv1.LIST_INDUCT_TAC
  >- REWRITE_TAC[NOT_CONS_NIL]
  >> gen_tac >> strip_tac
  >> DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP STURM_GCD)
  >> DISCH_THEN SUBST_ALL_TAC
  >> MP_TAC(SPECL [`f:real list`, `q:real list`] POLY_SQUAREFREE_DECOMP)
  >> DISCH_THEN(MP_TAC o SPECL [`[d:real]`, `e:real list`])
  >> DISCH_THEN(MP_TAC o SPECL [`r:real list`, `s:real list`])
  >> UNDISCH_TAC `~(poly (diff f) = poly [])`
  >> DISCH_THEN(fn th => REWRITE_TAC[th])
  >> ASM_REWRITE_TAC[] >> DISCH_THEN(MP_TAC o CONJUNCT1)
  >> REWRITE_TAC[rsquarefree]
  >> SUBGOAL_THEN `(poly q = poly []) <=> (poly (q * [d]) = poly [])`
                                                                 ASSUME_TAC
  >- (
    ASM_REWRITE_TAC[poly_def, REAL_ENTIRE, FUN_EQ_THM, POLY_MUL]
    >> ASM_REWRITE_TAC[REAL_MUL_RZERO, REAL_ADD_RID]
  )
  >> ASM_REWRITE_TAC[]
  >> MATCH_MP_TAC(tautLib.TAUT `(p ==> (q <=> r)) ==> (p /\ q ==> p /\ r)`)
  >> STRIP_TAC
  >> SUBGOAL_THEN `!a:real. poly_order a (f:real list) = poly_order a (q:real list)`
  (fn th => REWRITE_TAC[th])
  >> X_GEN_TAC “c:real” >> MATCH_MP_TAC EQ_TRANS
  >> EXISTS_TAC `poly_order (c:real) ((q:real list) * [d:real])`
  >> CONJ_TAC
  >- ( MATCH_MP_TAC ORDER_POLY >> ASM_REWRITE_TAC[] )
  >> FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP ORDER_MUL th])
  >> SUBGOAL_THEN `poly_order c [d] = 0` (fn th => REWRITE_TAC[th, POLY_ADD_CLAUSES])
  >> MP_TAC(SPECL [`[d:real]`, `c:real`] ORDER_ROOT)
  >> ASM_REWRITE_TAC[poly_def, REAL_MUL_RZERO, REAL_ADD_RID]
  >> gs[] >> gs[]
QED


(* ------------------------------------------------------------------------- *)
(* A conversion for calculating variations.                                  *)
(* ------------------------------------------------------------------------- *)
(*
val VARIATION_CONV =
  let
    val HO_GEN_REWRITE_CONV = Ho_Rewrite.GEN_REWRITE_CONV
    val variation_conv = HO_GEN_REWRITE_CONV I [variation_def]
    val cond_conv = HO_GEN_REWRITE_CONV I [COND_CLAUSES]
    val sig_conv = HO_GEN_REWRITE_CONV I [SIGN_LEMMA5]
    val varrec0_conv = HO_GEN_REWRITE_CONV I [CONJUNCT1 varrec_def]
    val varrec1_conv = HO_GEN_REWRITE_CONV I [CONJUNCT2 varrec_def]
  in
    let
      fun VARREC_CONV tm =
        varrec0_conv tm
        handle HOL_ERR _ =>
        let
         val th1 = (varrec1_conv THENC
                    RATOR_CONV(LAND_CONV(sig_conv THENC REAL_RAT_REDUCE_CONV)) THENC
                    cond_conv) tm
         val tm1 = rand(concl th1)
        in
          if is_cond tm1 then
            let val th2 = (RATOR_CONV(LAND_CONV REAL_RAT_REDUCE_CONV) THENC
                           cond_conv THENC
                           VARREC_CONV) tm1
            in
              TRANS th1 th2
            end
          else
            TRANS th1 (RAND_CONV VARREC_CONV tm1)
        end
    in
  variation_conv THENC VARREC_CONV THENC
                 DEPTH_CONV NUM_SUC_CONV
                 end
                 end; *)

val _ = export_theory();
