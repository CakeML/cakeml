(**
  Proofs ported about extrema of real-valued, univariate functions,
  ported from the work by Harrison
**)
open bossLib RealArith realTheory polyTheory limTheory;
open renameTheory;
open preambleDandelion;

val _ = new_theory "drang";

(* ------------------------------------------------------------------------- *)
(* General theorem about bounding functions.                                 *)
(* ------------------------------------------------------------------------- *)

(** HOL-Light compatibility **)
val REAL_MUL_AC = REAL_MUL_ASSOC;
val SPEC = Q.SPEC;
val SPECL = Q.SPECL;
val REAL_ARITH = fn t => REAL_ARITH (Term t);
val SUBGOAL_THEN = fn t => SUBGOAL_THEN (Term t);
val UNDISCH_TAC = fn t => UNDISCH_TAC (Term t);
val EXISTS_TAC = fn t => EXISTS_TAC (Term t);
val GEN_REWRITE_TAC = jrhUtils.GEN_REWR_TAC;
val ASM_CASES_TAC = fn t => ASM_CASES_TAC (Term t);

Theorem BOUND_THEOREM_POS:
  ∀ (f:real->real) f' a b ub.
    (∀ x. a ≤ x ∧ x ≤ b ⇒ (f diffl (f' x)) x) ∧
    f a ≤ ub ∧
    f b ≤ ub ∧
    (∀ x. a ≤ x ∧ x ≤ b ∧ (f' x = 0) ⇒ f x ≤ ub) ⇒
    (∀ x. a ≤ x ∧ x ≤ b ⇒ f x ≤ ub)
Proof
  rpt gen_tac >> strip_tac >> reverse $ Cases_on `a <= b`
  >- (
    rpt gen_tac >> pop_assum mp_tac
    >> REAL_ARITH_TAC)
  >> ‘∀ x. a ≤ x ∧ x ≤ b ⇒ f contl x’
    by (
      rpt strip_tac >> match_mp_tac DIFF_CONT >>
      qexists_tac ‘f' x’ >> gs[])
  >> qspecl_then [‘f’, ‘a’, ‘b’] mp_tac CONT_ATTAINS
  >> gs[] >> strip_tac >> VAR_EQ_TAC
  >> rename1 ‘a ≤ c’
  >> `f(c:real) <= ub`
    by (
      Cases_on ‘a:real = c’ >- gs[]
      >> Cases_on `c:real = b` >- gs[]
      >> qpat_x_assum ‘a <= c’ mp_tac
      >> disch_then $ mp_tac o REWRITE_RULE[REAL_LE_LT]
      >> qpat_x_assum ‘c <= b’ mp_tac
      >> disch_then $ mp_tac o REWRITE_RULE[REAL_LE_LT]
      >> gs[] >> rpt strip_tac
      >> qspecl_then [`a`, `b`, `c`] mp_tac INTERVAL_LEMMA
      >> gs[]
      >> disch_then $ X_CHOOSE_THEN (Term `d:real`) strip_assume_tac
      >> ‘f' c = 0’
        by (
        irule DIFF_LMAX
        >> EXISTS_TAC ‘f:real->real’
        >> EXISTS_TAC ‘c:real’ >> CONJ_TAC
        >- (qexists_tac ‘d’ >> gs[])
        >> first_assum irule >> gs[REAL_LE_LT])
      >> first_x_assum irule >> gs[])
  >> rpt strip_tac >> irule REAL_LE_TRANS >> qexists_tac ‘f c’
  >> conj_tac >> gs[]
QED

Theorem BOUND_THEOREM_NEG:
 ∀ f f' a b ub.
   (∀ x. a ≤ x ∧ x ≤ b ⇒ (f diffl (f' x)) x) ∧
   ub ≤ f(a) ∧
   ub ≤ f(b) ∧
   (∀ x. a ≤ x ∧ x ≤ b ∧ (f'(x) = 0) ⇒ ub ≤ f(x)) ⇒
   (∀ x. a ≤ x ∧ x ≤ b ⇒ ub ≤ f(x))
Proof
  rpt strip_tac
  >> qspecl_then [‘λ x. - (f x)’, ‘λ x. - (f' x)’] mp_tac BOUND_THEOREM_POS
  >> disch_then $ qspecl_then [‘a’, ‘b’, ‘-ub’] mp_tac
  >> REWRITE_TAC[REAL_LE_NEG2]
  >> gs[] >> impl_tac >> gs[]
  >> rpt strip_tac >> irule DIFF_NEG >> gs[]
QED

Theorem BOUND_THEOREM_EXACT:
 ∀ f f' a b ub.
   (∀ x. a ≤ x ∧ x ≤ b ⇒ (f diffl (f' x)) x) ∧
   abs(f a) ≤ ub ∧
   abs(f b) ≤ ub ∧
   (∀ x. a ≤ x ∧ x ≤ b ∧ (f'(x) = 0) ⇒ abs(f x) ≤ ub) ⇒
   (∀ x. a ≤ x ∧ x ≤ b ⇒ abs(f x) ≤ ub)
Proof
  rpt gen_tac
  >> REWRITE_TAC[REAL_ARITH `abs(a) <= b <=> -b <= a /\ a <= b`]
  >> REWRITE_TAC[PROVE [] (Term `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`)]
  >> REWRITE_TAC[FORALL_AND_THM] >> STRIP_TAC >> GEN_TAC >> CONJ_TAC
  >- (
    MATCH_MP_TAC BOUND_THEOREM_NEG >> ASM_REWRITE_TAC[] >>
    EXISTS_TAC `f':real->real` >> ASM_REWRITE_TAC[])
  >> MATCH_MP_TAC BOUND_THEOREM_POS >> ASM_REWRITE_TAC[]
  >> EXISTS_TAC `f':real->real` >> ASM_REWRITE_TAC[]
QED

Theorem BOUND_THEOREM_EXACT_ALT:
 ∀ f f' a b ub.
   (∀ x. a ≤ x ∧ x ≤ b ⇒ (f diffl (f' x)) x) ∧
   (∀ x. (x = a) ∨ (x = b) ∨
         a < x ∧ x < b ∧ (f'(x) = &0) ⇒ abs(f x) ≤ ub) ⇒
   (∀ x. a ≤ x ∧ x ≤ b ⇒ abs(f x) ≤ ub)
Proof
  REPEAT GEN_TAC >> STRIP_TAC
  >> MATCH_MP_TAC BOUND_THEOREM_EXACT
  >> EXISTS_TAC `f':real->real`
  >> ASM_REWRITE_TAC[] >> REPEAT STRIP_TAC
  >> FIRST_ASSUM MATCH_MP_TAC >> ASM_REWRITE_TAC[]
  >> qpat_x_assum `x <= b` mp_tac >> qpat_x_assum `a <= x` mp_tac
  >> REAL_ARITH_TAC
QED

Theorem lemma[local]:
  ∀ l. EVERY P l ∧ EXISTS Q l ⇒ EXISTS (λ x. P x ∧ Q x) l
Proof
  Induct_on ‘l’ >> gs[EVERY_DEF, EXISTS_DEF]
  >> rpt strip_tac >> gs[EXISTS_DEF]
QED

Theorem BOUND_THEOREM_INEXACT:
 ∀ f f' l a b.
   (∀ x. a ≤ x ∧ x ≤ b ⇒ (f diffl f'(x)) x) ∧
   (∀ x. a ≤ x ∧ x ≤ b ⇒ abs(f'(x)) <= B) ∧
   (∀ x. a ≤ x ∧ x ≤ b ∧ (f'(x) = &0) ⇒
         EXISTS (λ (u,v). u ≤ x ∧ x ≤ v) l) ∧
    EVERY (λ (u,v). a ≤ u ∧ v ≤ b ∧ abs(u - v) ≤ e ∧ abs(f u) ≤ ub) l ⇒
   ∀ x. a ≤ x ∧ x ≤ b ⇒ abs(f x) ≤ max (abs (f a)) (max (abs (f b)) (ub + B * e))
Proof
  rpt gen_tac >> strip_tac
  >> reverse $ Cases_on ‘a ≤ b’
  >- (
    CCONTR_TAC >> gs[]
    >> qpat_x_assum ‘~ (a ≤ b)’ mp_tac
    >> gs[] >> irule REAL_LE_TRANS >> qexists_tac ‘x’ >> gs[])
  >> match_mp_tac BOUND_THEOREM_EXACT
  >> qexists_tac ‘f'’ >> gs[]
  >> simp[SimpL “$==>”, REAL_LE_MAX]
  >> X_GEN_TAC “x:real”
  >> DISCH_THEN (fn th => ASSUME_TAC th >> MP_TAC th)
  >> DISCH_THEN (ANTE_RES_THEN MP_TAC)
  >> qpat_x_assum ‘EVERY _ l’ mp_tac
  >> rewrite_tac[AND_IMP_INTRO]
  >> DISCH_THEN (MP_TAC o MATCH_MP lemma)
  >> SPEC_TAC(“l:(real#real)list”,“l:(real#real)list”)
  >> Induct >> rewrite_tac[EXISTS_DEF]
  >> REWRITE_TAC[PROVE [] “a ∨ b ⇒ c ⇔ (a ⇒ c) ∧ (b ⇒ c)”]
  >> gs[FORALL_PROD]
  >> MAP_EVERY X_GEN_TAC [“u:real”, “v:real”] >> STRIP_TAC
  >> qpat_x_assum ‘abs (f u) ≤ ub’ mp_tac
  >> gs[REAL_LE_MAX]
  >> ‘abs (f x - f u) ≤ B * e’ suffices_by REAL_ARITH_TAC
  >> Cases_on ‘x = u’
  >- (
    ASM_REWRITE_TAC[REAL_SUB_REFL, REAL_ABS_0]
    >> MATCH_MP_TAC REAL_LE_MUL >> conj_tac
    >- (
      irule REAL_LE_TRANS >> qexists_tac ‘abs (f' x)’ >> conj_tac
      >- REAL_ARITH_TAC
      >> first_x_assum match_mp_tac >> asm_rewrite_tac[])
    >> irule REAL_LE_TRANS >> qexists_tac ‘abs (u - v)’
    >> gs[])
  >> ‘∃ l z. u < z ∧ z < x ∧
             (f diffl l) z ∧
             (f x - f u = (x - u) * l)’
    by (
      MATCH_MP_TAC MVT >> rpt conj_tac
      >- gs[REAL_LT_LE]
      >- (
        X_GEN_TAC “y:real” >> strip_tac
        >> irule DIFF_CONT
        >> qexists_tac ‘f' y’ >> first_x_assum irule
        >> MAP_EVERY (fn t => qpat_x_assum t mp_tac)
                     [‘a ≤ u’, ‘u ≤ y’, ‘y ≤ x’, ‘x ≤ v’, ‘v ≤ b’]
        >> REAL_ARITH_TAC)
      >> X_GEN_TAC “y:real” >> strip_tac >> REWRITE_TAC[differentiable]
      >> qexists_tac `f' y` >> first_x_assum irule
      >> MAP_EVERY (fn t => qpat_x_assum t mp_tac)
                   [‘a ≤ u’, ‘u < y’, ‘y < x’, ‘x ≤ v’, ‘v ≤ b’]
      >> REAL_ARITH_TAC)
  >> rename [‘(f diffl l1) z’]
  >> pop_assum $ rewrite_tac o single
  >> rewrite_tac [ABS_MUL]
  >> GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM]
  >> irule REAL_LE_MUL2 >> rewrite_tac[REAL_ABS_POS] >> conj_tac
  >- (
    MAP_EVERY (fn t => qpat_x_assum t mp_tac)
      [‘u ≤ x’, ‘x ≤ v’, ‘abs (u - v) ≤ e’]
    >> REAL_ARITH_TAC)
  >> ‘l1 = f' z’
    by (
      irule DIFF_UNIQ
      >> qexists_tac `f` >> qexists_tac `z:real`
      >> gs[] >> first_x_assum irule
      >> MAP_EVERY (fn t => qpat_x_assum t mp_tac)
                   [‘a ≤ u’, ‘u < z’, ‘z < x’, ‘x ≤ b’]
      >> REAL_ARITH_TAC)
  >> VAR_EQ_TAC >> first_x_assum irule
  >> MAP_EVERY (fn t => qpat_x_assum t mp_tac)
               [‘a ≤ u’, ‘u < z’, ‘z < x’, ‘x ≤ b’]
  >> REAL_ARITH_TAC
QED

Definition recordered_def:
  recordered (a:real) [] b = (a ≤ b) ∧
  recordered a (h::t) b =
    (a < FST h ∧ FST h ≤ SND h ∧ recordered (SND h) t b)
End

Theorem RECORDERED_CLAUSES =
        map (SIMP_CONV std_ss [recordered_def])
            [“recordered a [] b”, “recordered a ((u,v)::t) b”]
          |> LIST_CONJ

Theorem RECORDERED_MONO:
  ∀ l a a' b.
    a ≤ a' ∧
    recordered a' l b ⇒
    recordered a l b
Proof
  Induct_on ‘l’ >> gs[recordered_def]
  >- (rpt strip_tac >> real_tac)
  >> rpt strip_tac >> irule REAL_LET_TRANS
  >> qexists_tac ‘a'’ >> gs[]
QED

Theorem FINITE_AD_HOC_LEMMA:
 ∀ a b n.
   (a INTER b = EMPTY) ∧
   (∃ x. x IN a) ∧
   (a UNION b) HAS_SIZE n ⇒
   ∃ m. m < n ∧ b HAS_SIZE m
Proof
  rpt strip_tac >> gs[HAS_SIZE]
  >> ‘CARD(a UNION b) + CARD (a INTER b) = CARD a + CARD(b)’
    by gs[CARD_UNION]
  >> ‘CARD (a INTER b) = 0’ by gs[]
  >> pop_assum $ gs o single
  >> ‘~ (a HAS_SIZE 0)’
     by (CCONTR_TAC >> gs[HAS_SIZE_0])
  >> Cases_on ‘CARD a’ >> gs[EXTENSION, HAS_SIZE]
QED

Theorem RECORDERED_CONTAINED_LEMMA:
  ∀ l p a b n.
    recordered a l b ∧
    EVERY (λ(u,v). poly p(u) * poly p(v) ≤ 0) l ∧
    {x | a ≤ x ∧ x ≤ b ∧ (poly p x = 0) ∧
         EXISTS (λ (u,v). u ≤ x ∧ x ≤ v) l} HAS_SIZE n ⇒
    LENGTH l ≤ n
Proof
  Induct >> gs[LENGTH] >> rpt gen_tac
  >> Cases_on ‘h’ >> gs[]
  >> rename1 ‘recordered a ((u,v)::l) b’
  >> gs[recordered_def]
  >> qmatch_goalsub_abbrev_tac ‘_ ∧ _  ∧ set_zeroes HAS_SIZE _’
  >> `set_zeroes =
     {x | a ≤ x ∧ x ≤ b ∧ (poly p x = 0) ∧ u ≤ x ∧ x ≤ v} UNION
     {x | a ≤ x ∧ x ≤ b ∧ (poly p x = 0) ∧
         EXISTS (λ (u,v). u ≤ x ∧ x ≤ v) l}`
    by (
       unabbrev_all_tac >> gs[EXTENSION, IN_UNION] >> metis_tac[])
  >> pop_assum $ rewrite_tac o single >> unabbrev_all_tac
  >> rpt strip_tac
  >> Q.ISPECL_THEN [
      `{x | a <= x /\ x <= b /\ (poly p x = &0) /\ u <= x /\ x <= v}`,
     `{x | a <= x /\ x <= b /\ (poly p x = &0) /\ EXISTS (λ (u,v). u <= x /\ x <= v) l}`,
      `n:num`] mp_tac FINITE_AD_HOC_LEMMA
  >> gs[]
  >> W((fn t => SUBGOAL_THEN ‘^t’ (fn th => REWRITE_TAC[th])) o funpow 2 lhand o snd)
  >- (
    reverse conj_tac
    >- (
      MP_TAC(Q.SPECL [`u:real`, `v:real`, `p:real list`] sturmTheory.STURM_NOROOT)
      >> gs[real_gt, GSYM REAL_NOT_LE]
      >> strip_tac >> qexists_tac ‘x’ >> gs[] >> conj_tac
      >> last_x_assum kall_tac
      >- real_tac
      >> irule REAL_LE_TRANS >> qexists_tac ‘v’ >> gs[]
      >> UNDISCH_TAC ‘recordered v l b’
      >> rpt $ pop_assum kall_tac
      >> SPEC_TAC (“v:real”, “v:real”)
      >> Induct_on ‘l’ >> gs[recordered_def]
      >> rpt strip_tac >> gs[]
      >> irule REAL_LE_TRANS >> qexists_tac ‘SND h’ >> gs[]
      >> last_x_assum kall_tac >> real_tac)
    >> rewrite_tac[IN_INTER, EXTENSION] >> strip_tac >> reverse EQ_TAC >- gs[]
    >> rpt strip_tac
    >> gs[IN_GSPEC_IFF]
    >> qpat_x_assum ‘EXISTS _ _’ mp_tac
    >> qpat_x_assum `recordered _ _ _` mp_tac
    >> qpat_x_assum `x ≤ v` mp_tac
    >> rpt $ pop_assum kall_tac
    >> SPEC_TAC (“v:real”, “v:real”)
    >> SPEC_TAC (“x:real”, “x:real”)
    >> Induct_on ‘l’ >> rpt strip_tac >> gs[recordered_def]
    >- (
      Cases_on ‘h’ >> gs[] >> ‘x < x’ suffices_by gs[]
      >> irule REAL_LET_TRANS >> qexists_tac ‘v’ >> gs[]
      >> irule REAL_LTE_TRANS >> qexists_tac ‘q’ >> gs[])
    >> last_x_assum $ qspecl_then [‘x’, ‘SND h’] mp_tac
    >> ‘x ≤ SND h’ by real_tac
    >> rpt $ disch_then drule
    >> gs[combinTheory.o_DEF]
    >> irule LIST_EXISTS_MONO
    >> qexists_tac ‘λ (u,v). u ≤ x ∧ x ≤ v’ >> gs[])
  >>  disch_then $ X_CHOOSE_THEN “m:num” strip_assume_tac
  >> irule LESS_OR
  >> irule LESS_EQ_LESS_TRANS
  >> qexists_tac ‘m’ >> gs[]
  >> first_assum irule
  >> qexists_tac ‘a’ >> qexists_tac ‘b’ >> qexists_tac ‘p’ >> gs[]
  >> irule RECORDERED_MONO
  >> qexists_tac ‘v’ >> gs[]
  >> last_x_assum kall_tac >> real_tac
QED

Theorem CARD_SUBSET_LE:
  ∀ a b.
    FINITE b /\ a SUBSET b /\ (CARD b <= CARD a) ==> (a = b)
Proof
  rpt strip_tac
  >> ‘CARD a ≤ CARD b’ by metis_tac[CARD_SUBSET]
  >> ‘CARD b = CARD a’ by gs[]
  >> irule SUBSET_EQ_CARD >> gs[]
  >> irule SUBSET_FINITE >> qexists_tac ‘b’ >> gs[]
QED

Theorem RECORDERED_ROOTCOUNT:
  ∀ l a b.
    {x | a ≤ x ∧ x ≤ b ∧ (poly p x = &0)} HAS_SIZE (LENGTH l) ∧
    recordered a l b ∧
    EVERY (λ (u,v). poly p(u) * poly p(v) ≤ 0) l ⇒
    ∀ x. a ≤ x ∧ x ≤ b ∧ (poly p(x) = &0) ⇒
         EXISTS (λ (u,v). u ≤ x ∧ x ≤ v) l
Proof
  rpt gen_tac >> disch_tac
  >> gs[PROVE[] “(a ==> b) <=> (a /\ b <=> a)”]
  >> ‘{x | a <= x /\ x <= b /\ (poly p x = &0) /\
           EXISTS (λ (u,v). u <= x /\ x <= v) l} =
                {x | a <= x /\ x <= b /\ (poly p x = &0)}’
    by (
      last_x_assum $ strip_assume_tac o REWRITE_RULE[HAS_SIZE]
      >> irule CARD_SUBSET_LE >> rpt $ reverse conj_tac >> gs[]
      >- gs[SUBSET_DEF]
      >> irule RECORDERED_CONTAINED_LEMMA
      >> qexists_tac ‘a’ >> qexists_tac ‘b’ >> qexists_tac ‘p’ >> gs[HAS_SIZE]
      >> irule SUBSET_FINITE
      >> qexists_tac `{x | a <= x /\ x <= b /\ (poly p x = &0)}`
      >> gs[SUBSET_DEF])
  >> gs[EXTENSION] >> metis_tac[]
QED

val _ = export_theory();
