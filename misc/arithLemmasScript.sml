(*
   General-purpose arithmetic lemmas (DIV, MOD, EXP, LOG, FUNPOW, etc.)
   used throughout the CakeML development.
*)
Theory arithLemmas
Ancestors
  arithmetic combin relation bit pred_set
Libs
  boolSimps mp_then dep_rewrite BasicProvers

val _ = numLib.temp_prefer_num();

(* theorem behind impl_tac *)
Theorem IMP_IMP =
  METIS_PROVE[]``(P /\ (Q ==> R)) ==> ((P ==> Q) ==> R)``

Definition least_from_def:
  least_from P n = if (∃x. P x ∧ n ≤ x) then $LEAST (λx. P x ∧ n ≤ x) else $LEAST P
End

Theorem LEAST_thm:
   $LEAST P = least_from P 0
Proof
  srw_tac[][least_from_def,ETA_AX]
QED

Theorem least_from_thm:
   least_from P n = if P n then n else least_from P (n+1)
Proof
  srw_tac[][least_from_def] >>
  numLib.LEAST_ELIM_TAC >> srw_tac[][] >> full_simp_tac(srw_ss())[] >> res_tac >>
  TRY(metis_tac[arithmeticTheory.LESS_OR_EQ]) >- (
    numLib.LEAST_ELIM_TAC >> srw_tac[][] >> full_simp_tac(srw_ss())[] >- metis_tac[] >>
    qmatch_rename_tac`a = b` >>
    `n ≤ b` by DECIDE_TAC >>
    Cases_on`b < a` >-metis_tac[] >>
    spose_not_then strip_assume_tac >>
    `a < b` by DECIDE_TAC >>
    `¬(n + 1 ≤ a)` by metis_tac[] >>
    `a = n` by DECIDE_TAC >>
    full_simp_tac(srw_ss())[] )
  >- (
    Cases_on`n+1≤x`>-metis_tac[]>>
    `x = n` by DECIDE_TAC >>
    full_simp_tac(srw_ss())[] )
  >- (
    `¬(n ≤ x)` by metis_tac[] >>
    `x = n` by DECIDE_TAC >>
    full_simp_tac(srw_ss())[] )
QED

Theorem FUNPOW_mono:
   (∀x y. R1 x y ⇒ R2 x y) ∧
    (∀R1 R2. (∀x y. R1 x y ⇒ R2 x y) ⇒ ∀x y. f R1 x y ⇒ f R2 x y) ⇒
    ∀n x y. FUNPOW f n R1 x y ⇒ FUNPOW f n R2 x y
Proof
  strip_tac >> Induct >> simp[] >>
  simp[arithmeticTheory.FUNPOW_SUC] >>
  first_x_assum match_mp_tac >> srw_tac[][]
QED

Theorem FUNPOW_SUC_PLUS:
   ∀n a. FUNPOW SUC n = (+) n
Proof
Induct \\ simp[FUNPOW,FUN_EQ_THM]
QED

Definition between_def:
  between x y z ⇔ x:num ≤ z ∧ z < y
End

Theorem IN_between:
   x ∈ between y z ⇔ y ≤ x ∧ x < z
Proof
  rw[IN_DEF] \\ EVAL_TAC
QED

(* never used *)
Theorem SUC_LEAST:
   !x. P x ==> (SUC ($LEAST P) = LEAST x. 0 < x /\ P (PRE x))
Proof
  GEN_TAC THEN STRIP_TAC THEN
  numLib.LEAST_ELIM_TAC THEN
  STRIP_TAC THEN1 PROVE_TAC[] THEN
  numLib.LEAST_ELIM_TAC THEN
  STRIP_TAC THEN1 (
    Q.EXISTS_TAC `SUC x` THEN
    SRW_TAC[][] ) THEN
  Q.X_GEN_TAC`nn` THEN
  STRIP_TAC THEN
  Q.X_GEN_TAC`m` THEN
  `?n. nn = SUC n` by ( Cases_on `nn` THEN SRW_TAC[][] THEN DECIDE_TAC ) THEN
  SRW_TAC[][] THEN
  FULL_SIMP_TAC(srw_ss())[] THEN
  `~(n < m)` by PROVE_TAC[] THEN
  `~(SUC m < SUC n)` by (
    SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
    RES_TAC THEN
    FULL_SIMP_TAC(srw_ss())[] ) THEN
  DECIDE_TAC
QED

(* never used *)
Theorem RTC_invariant:
   !R P. (!x y. P x /\ R x y ==> P y) ==> !x y. RTC R x y ==> P x ==> RTC (R RINTER (\x y. P x /\ P y)) x y
Proof
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac RTC_INDUCT >>
  srw_tac[][] >> res_tac >> full_simp_tac(srw_ss())[] >>
  simp[Once RTC_CASES1] >>
  disj2_tac >>
  HINT_EXISTS_TAC >>
  simp[RINTER]
QED

(* never used *)
Theorem RTC_RSUBSET:
   !R1 R2. R1 RSUBSET R2 ==> (RTC R1) RSUBSET (RTC R2)
Proof
  simp[RSUBSET] >> rpt gen_tac >> strip_tac >>
  ho_match_mp_tac RTC_INDUCT >>
  simp[] >>
  metis_tac[RTC_CASES1]
QED

(* TODO - candidate for move to HOL *)
Theorem plus_compose:
   !n:num m. $+ n o $+ m = $+ (n + m)
Proof
  SRW_TAC[ARITH_ss][FUN_EQ_THM]
QED

Theorem LESS_1[simp]:
 x < 1 ⇔ (x = 0:num)
Proof
DECIDE_TAC
QED

Theorem MOD_SUB_LEMMA:
   n MOD k = 0 /\ m MOD k = 0 /\ 0 < k ==> (n - m) MOD k = 0
Proof
  Cases_on `m <= n` \\ fs []
  \\ imp_res_tac LESS_EQ_EXISTS \\ rw []
  \\ qpat_x_assum `(m + _) MOD k = 0` mp_tac
  \\ once_rewrite_tac[GSYM MOD_PLUS]
  \\ fs[]
QED

Theorem MULT_LE_EXP:
   ∀a:num b. a ≠ 1 ⇒ a * b ≤ a ** b
Proof
  Induct_on`b` >> simp[arithmeticTheory.MULT,arithmeticTheory.EXP] >>
  Cases >> simp[] >> strip_tac >>
  first_x_assum(qspec_then`SUC n`mp_tac) >>
  simp[arithmeticTheory.MULT] >>
  Cases_on`b=0` >- (
    simp[arithmeticTheory.EXP] ) >>
  `SUC b ≤ b + b * n` suffices_by simp[] >>
  simp[arithmeticTheory.ADD1] >>
  Cases_on`b * n` >> simp[] >>
  fs[arithmeticTheory.MULT_EQ_0] >> fs[]
QED

Theorem OLEAST_SOME_IMP:
   $OLEAST P = SOME i ⇒ P i ∧ (∀n. n < i ⇒ ¬P n)
Proof
  simp[WhileTheory.OLEAST_def]
  \\ metis_tac[WhileTheory.LEAST_EXISTS_IMP]
QED

Theorem EXP2_EVEN:
   ∀n. EVEN (2 ** n) ⇔ n ≠ 0
Proof
  Induct >> simp[EXP,EVEN_DOUBLE]
QED

Theorem irreflexive_inv_image:
   !R f. irreflexive R ==> irreflexive (inv_image R f)
Proof
  SIMP_TAC std_ss [irreflexive_def,inv_image_def]
QED

Theorem trichotomous_inv_image:
   !R f. trichotomous R /\ (INJ f UNIV UNIV) ==> trichotomous (inv_image R f)
Proof
  SIMP_TAC std_ss [trichotomous,inv_image_def,INJ_DEF,IN_UNIV] THEN
  METIS_TAC[]
QED

Theorem plus_0_I[simp]:
   $+ 0n = I
Proof
rw[FUN_EQ_THM]
QED

Theorem MOD_2EXP_0_EVEN:
   ∀x y. 0 < x ∧ MOD_2EXP x y = 0 ⇒ EVEN y
Proof
  rw[EVEN_MOD2,bitTheory.MOD_2EXP_def,MOD_EQ_0_DIVISOR]
  \\ Cases_on`x` \\ fs[EXP]
QED

Theorem ADD_MOD_EQ_LEMMA:
   k MOD d = 0 /\ n < d ==> (k + n) MOD d = n
Proof
  rw [] \\ `0 < d` by decide_tac
  \\ fs [MOD_EQ_0_DIVISOR]
  \\ pop_assum kall_tac
  \\ first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] MOD_MULT))
  \\ fs []
QED

Theorem IN_EVEN =
  SIMP_CONV std_ss [IN_DEF] ``x ∈ EVEN``

Theorem FUNPOW_refl_trans_chain:
   transitive P ∧ reflexive P ⇒
   ∀n x.  (∀j. j < n ⇒ P (FUNPOW f j x) (f (FUNPOW f j x))) ⇒
     P x (FUNPOW f n x)
Proof
  strip_tac
  \\ Induct
  \\ rw[]
  >- fs[reflexive_def]
  \\ rw[]
  \\ fs[transitive_def]
  \\ last_x_assum irule
  \\ simp[FUNPOW_SUC]
  \\ qexists_tac`FUNPOW f n x`
  \\ simp[]
QED
