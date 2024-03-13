(*
  Prove theorems cv_transLib uses for its operation
*)
open HolKernel Parse boolLib bossLib dep_rewrite;
open cv_typeTheory cvTheory cv_typeLib cv_repLib;
open arithmeticTheory wordsTheory cv_repTheory integerTheory ratTheory
     listTheory rich_listTheory bitstringTheory integer_wordTheory;

val _ = new_theory "cv_prim";

Overload c2n[local] = “cv$c2n”
Overload c2b[local] = “cv$c2b”
Overload Num[local] = “cv$Num”
Overload Pair[local] = “cv$Pair”

(*----------------------------------------------------------*
   bool
 *----------------------------------------------------------*)

Theorem cv_rep_T[cv_rep]:
  b2c T = Num 1
Proof
  fs []
QED

Theorem cv_rep_F[cv_rep]:
  b2c F = Num 0
Proof
  fs []
QED

Theorem cv_rep_not[cv_rep]:
  b2c (~b1) = cv_sub (Num 1) (b2c b1)
Proof
  Cases_on ‘b1’ \\ fs []
QED

Theorem cv_rep_and[cv_rep]:
  b2c (b1 ∧ b2) = cv_if (b2c b1) (b2c b2) (Num 0)
Proof
  Cases_on ‘b1’ \\ Cases_on ‘b2’ \\ fs []
QED

Theorem cv_rep_or[cv_rep]:
  b2c (b1 ∨ b2) = cv_if (b2c b1) (Num 1) (b2c b2)
Proof
  Cases_on ‘b1’ \\ Cases_on ‘b2’ \\ fs [cv_rep_def]
QED

Theorem cv_inline_imp[cv_rep]:
  b2c (a ⇒ b) = cv_if (b2c a) (b2c b) (Num 1)
Proof
  Cases_on `a` >> Cases_on `b` >> gvs[cvTheory.b2c_def]
QED

(*----------------------------------------------------------*
   num
 *----------------------------------------------------------*)

Theorem cv_rep_suc[cv_rep]:
  Num (SUC n) = cv_add (Num n) (Num 1)
Proof
  fs []
QED

Theorem cv_rep_sub1[cv_rep]:
  Num (PRE n) = cv_sub (Num n) (Num 1)
Proof
  fs []
QED

Theorem cv_rep_add[cv_rep]:
  Num (n + m) = cv_add (Num n) (Num m)
Proof
  fs []
QED

Theorem cv_rep_sub[cv_rep]:
  Num (n - m) = cv_sub (Num n) (Num m)
Proof
  fs []
QED

Theorem cv_rep_mul[cv_rep]:
  Num (n * m) = cv_mul (Num n) (Num m)
Proof
  fs [cv_rep_def]
QED

Theorem cv_rep_div[cv_rep]:
  Num (n DIV m) = cv_div (Num n) (Num m)
Proof
  fs [cv_rep_def]
QED

Theorem cv_rep_mod[cv_rep]:
  Num (n MOD m) = cv_mod (Num n) (Num m)
Proof
  fs [cv_rep_def]
QED

Theorem cv_rep_exp[cv_rep]:
  Num (n ** m) = cv_exp (Num n) (Num m)
Proof
  fs [cv_rep_def,cvTheory.cv_exp_def]
QED

Theorem cv_rep_odd[cv_rep]:
  b2c (ODD n) = cv_mod (Num n) (Num 2)
Proof
  fs [cv_rep_def] \\ rw [] \\ gvs [bitTheory.ODD_MOD2_LEM]
  \\ ‘n MOD 2 < 2’ by fs []
  \\ Cases_on ‘n MOD 2’ \\ fs []
QED

Theorem cv_rep_even[cv_rep]:
  b2c (EVEN n) = cv_sub (Num 1) (cv_mod (Num n) (Num 2))
Proof
  simp [cv_rep_odd,cv_rep_not,arithmeticTheory.EVEN_ODD]
QED

Theorem cv_rep_lt[cv_rep]:
  b2c (n < m) = cv_lt (Num n) (Num m)
Proof
  fs [cv_rep_def] \\ rw []
QED

Theorem cv_rep_le[cv_rep]:
  b2c (n ≤ m) = cv_sub (Num 1) (cv_lt (Num m) (Num n))
Proof
  fs [cv_rep_def] \\ rw []
QED

Theorem cv_rep_num_case[cv_rep]:
  cv_rep p1 c1 Num x ∧
  cv_rep p2 c2 (a:'a->cv) y ∧
  (∀v:num. cv_rep (p3 v) (c3 (Num v)) (a:'a->cv) (z v)) ⇒
  cv_rep (p1 ∧ (x = 0 ⇒ p2) ∧ ∀n. x = SUC n ⇒ p3 n)
         (cv_if (cv_lt (Num 0) c1) (let y = cv_sub c1 (Num 1) in c3 y) c2)
         a (num_CASE x y z)
Proof
  rw [] \\ gvs [cv_rep_def] \\ rw [] \\ gvs []
  \\ Cases_on ‘x’ \\ gvs []
QED

Definition cv_min_def:
  cv_min x y = cv_if (cv_lt x y) x y
End

Definition cv_max_def:
  cv_max x y = cv_if (cv_lt x y) y x
End

Theorem cv_min_thm[cv_rep]:
  Num (MIN m n) = cv_min (Num m) (Num n)
Proof
  fs [cv_min_def] \\ rw []
  \\ BasicProvers.every_case_tac \\ fs []
  \\ gvs [arithmeticTheory.MIN_DEF]
QED

Theorem cv_max_thm[cv_rep]:
  Num (MAX m n) = cv_max (Num m) (Num n)
Proof
  fs [cv_max_def] \\ rw []
  \\ BasicProvers.every_case_tac \\ fs []
  \\ gvs [arithmeticTheory.MAX_DEF]
QED

Definition cv_gcd_def:
  cv_gcd a b = cv_if a (cv_gcd (cv_mod b a) a) b
Termination
  WF_REL_TAC `measure $ λ(a,b). c2n a + c2n b + (c2n a - c2n b)` >>
  rpt gen_tac >> strip_tac >>
  simp[] >> gvs[c2b_def] >>
  Cases_on `b` >> gvs[cv_mod_def] >>
  `m MOD SUC k - SUC k = 0` by (
    simp[] >> irule LESS_IMP_LESS_OR_EQ >> simp[]) >>
  `m MOD SUC k < SUC k` by simp[] >>
  simp[] >> DECIDE_TAC
End

Theorem cv_gcd_thm[cv_rep]:
  Num (gcd a b) = cv_gcd (Num a) (Num b)
Proof
  qsuff_tac `∀c d a b. c = Num a ∧ d = Num b ⇒ Num (gcd a b) = cv_gcd c d`
  >- rw[] >>
  ho_match_mp_tac cv_gcd_ind >> rw[] >>
  rw[Once gcdTheory.GCD_EFFICIENTLY, Once cv_gcd_def] >> gvs[] >>
  gvs[c2b_def] >> Cases_on `a` >> gvs[]
QED

Definition cv_log2_def:
  cv_log2 acc n =
    cv_if (cv_lt (Num 1) n)
      (cv_log2 (cv_add acc (Num 1)) (cv_div n (Num 2)))
      acc
Termination
  WF_REL_TAC `measure $ λ(_,n). cv$c2n n` >> Cases >> rw[]
End

Theorem cv_rep_LOG2[cv_rep]:
  n ≠ 0 ⇒ Num (LOG2 n) = cv_log2 (Num 0) (Num n)
Proof
  qsuff_tac `∀acc. n ≠ 0 ⇒ cv_log2 (Num acc) (Num n) = Num (LOG2 n + acc)`
  >- rw[] >>
  simp[bitTheory.LOG2_def] >>
  completeInduct_on `n` >> rw[] >>
  once_rewrite_tac[numeral_bitTheory.LOG_compute] >> simp[] >>
  once_rewrite_tac[cv_log2_def] >>
  simp[cvTheory.cv_lt_def] >>
  IF_CASES_TAC >> gvs[cvTheory.c2b_def, AllCaseEqs()] >>
  first_x_assum $ qspec_then `n DIV 2` mp_tac >>
  simp[DIV_LT_X, DIV_EQ_X]
QED

(*----------------------------------------------------------*
   int
 *----------------------------------------------------------*)

Theorem cv_int_of_num[cv_rep]:
  from_int (&n) = Num n
Proof
  gvs[from_int_def]
QED

Definition cv_abs_def:
  cv_abs i = cv_if (cv_ispair i) (cv_fst i) i
End

Theorem cv_Num[cv_rep]:
  Num (integer$Num i) = cv_abs (from_int i)
Proof
  gvs[from_int_def, cv_abs_def] >>
  rw[] >> gvs[cv_ispair_def]
QED

Definition cv_int_neg_def:
  cv_int_neg x =
    cv_if (cv_eq x (Num 0)) x $
          cv_if (cv_ispair x) (cv_fst x) (Pair x (Num 0))
End

Theorem cv_neg_int[cv_rep]:
  from_int (- x) = cv_int_neg (from_int x)
Proof
  gvs[from_int_def]
  \\ Cases_on ‘x = 0’ \\ gvs [cv_int_neg_def]
  \\ Cases_on ‘x’ \\ gvs []
QED

Definition cv_int_lt_def:
  cv_int_lt i j =
    cv_if (cv_ispair i) (* if i < 0 *)
      (cv_if (cv_ispair j) (* if j < 0 *)
        (cv_lt (cv_abs j) (cv_abs i))
        (Num 1))
      (cv_if (cv_ispair j) (* if j < 0 *)
        (Num 0)
        (cv_lt i j))
End

Theorem cv_int_lt[cv_rep]:
  b2c (int_lt i j) = cv_int_lt (from_int i) (from_int j)
Proof
  simp[cv_int_lt_def, from_int_def, cv_abs_def] >>
  IF_CASES_TAC >>
  gvs[COND_RAND] >> rw[] >> gvs[c2b_def] >>
  Cases_on `i` >> gvs[] >> Cases_on `j` >> gvs[]
QED

Theorem cv_int_le[cv_rep]:
  b2c (int_le i j) = cv_if (cv_int_lt (from_int j) (from_int i))
                      (Num 0) (Num 1)
Proof
  simp[int_le, GSYM cv_int_lt] >> Cases_on `j < i` >> simp[]
QED

Theorem cv_int_gt[cv_rep]:
  b2c (int_gt i j) = cv_int_lt (from_int j) (from_int i)
Proof
  simp[int_gt, GSYM cv_int_lt]
QED

Theorem cv_int_ge[cv_rep]:
  b2c (int_ge i j) = cv_if (cv_int_lt (from_int i) (from_int j))
                      (Num 0) (Num 1)
Proof
  simp[int_ge, int_le, GSYM cv_int_lt] >> Cases_on `i < j` >> gvs[]
QED

Definition cv_int_add_def:
  cv_int_add i j =
    cv_if (cv_ispair i) (* if i < 0 *)
      (cv_if (cv_ispair j) (* if j < 0 *)
        (Pair (cv_add (cv_fst i) (cv_fst j)) (Num 0))
        (cv_if (cv_int_lt j (cv_fst i)) (* i < 0 ∧ ¬(j < 0); if j < |i| *)
          (Pair (cv_sub (cv_fst i) j) (Num 0))
          (cv_sub j (cv_fst i))))
      (cv_if (cv_ispair j) (* if j < 0 *)
        (cv_if (cv_int_lt i (cv_fst j)) (* ¬(i < 0) ∧ j < 0; if i < |j| *)
          (Pair (cv_sub (cv_fst j) i) (Num 0))
          (cv_sub i (cv_fst j)))
        (cv_add i j))
End

Theorem cv_int_add[cv_rep]:
  from_int (i + j) = cv_int_add (from_int i) (from_int j)
Proof
  simp[from_int_def, cv_int_add_def, cv_int_lt_def, cv_sub_def] >>
  Cases_on `i < 0` >> Cases_on `j < 0` >> gvs[] >>
  namedCases_on `i` ["ni","ni",""] >> namedCases_on `j` ["nj","nj",""] >>
  gvs[INT_ADD_CALCULATE]
  >- (Cases_on `ni ≤ nj` >> gvs[])
  >- (Cases_on `nj ≤ ni` >> gvs[])
QED

Theorem cv_int_sub[cv_rep]:
  from_int (i - j) = cv_int_add (from_int i) (cv_int_neg (from_int j))
Proof
  simp[int_sub, GSYM cv_neg_int, GSYM cv_int_add]
QED

Definition total_int_div_def:
  total_int_div i j = if j = 0 then 0 else int_div i j
End

Theorem total_int_div:
  total_int_div i j =
    if j = 0 then 0
    else if j < 0 then
            if i < 0 then &(Num i DIV Num j)
            else -&(Num i DIV Num j) + if Num i MOD Num j = 0 then 0 else -1
    else if i < 0 then -&(Num i DIV Num j) + if Num i MOD Num j = 0 then 0 else -1
         else &(Num i DIV Num j)
Proof
  simp[total_int_div_def, int_div] >>
  Cases_on `j = 0` >> gvs[] >>
  Cases_on `j < 0` >> Cases_on `i < 0` >> gvs[] >>
  namedCases_on `i` ["ni","ni",""] >> gvs[] >>
  namedCases_on `j` ["nj","nj",""] >> gvs[]
QED

Definition cv_int_div_def:
  cv_int_div i j =
    cv_if (cv_eq j (Num 0)) (Num 0) $
      cv_if (cv_ispair j) (* if j < 0 *)
        (cv_if (cv_ispair i) (* if i < 0 *)
          (cv_div (cv_fst i) (cv_fst j))
          (cv_int_add
            (Pair (cv_div i (cv_fst j)) (Num 0))
            (cv_if (cv_mod i (cv_fst j))
              (Pair (Num 1) (Num 0)) (Num 0))))
        (cv_if (cv_ispair i) (* if i < 0 *)
          (cv_int_add
            (Pair (cv_div (cv_fst i) j) (Num 0))
            (cv_if (cv_mod (cv_fst i) j)
              (Pair (Num 1) (Num 0)) (Num 0)))
          (cv_div i j))
End

Theorem cv_int_div[cv_rep]:
  from_int (total_int_div i j) = cv_int_div (from_int i) (from_int j)
Proof
  simp[total_int_div, cv_int_div_def, from_int_def] >>
  Cases_on `j = 0` >> gvs[] >>
  Cases_on `j < 0` >> Cases_on `i < 0` >> gvs[] >>
  Cases_on `i = 0` >> gvs[] >>
  reverse $ Cases_on `Num i MOD Num j` >> gvs[] >>
  simp[INT_ADD_CALCULATE, cv_int_add_def, cv_int_lt_def] >>
  Cases_on `Num i DIV Num j` >> gvs[]
QED

Definition cv_int_mul_def:
  cv_int_mul i j =
    cv_if (cv_eq i (Num 0)) (Num 0) $
    cv_if (cv_eq j (Num 0)) (Num 0) $
    cv_if (cv_ispair i)
      (cv_if (cv_ispair j)
        (cv_mul (cv_fst i) (cv_fst j))
        (Pair (cv_mul (cv_fst i) j) (Num 0)))
      (cv_if (cv_ispair j)
        (Pair (cv_mul i (cv_fst j)) (Num 0))
        (cv_mul i j))
End

Theorem cv_int_mul[cv_rep]:
  from_int (i * j) = cv_int_mul (from_int i) (from_int j)
Proof
  simp[cv_int_mul_def, from_int_def, cv_eq_def] >>
  namedCases_on `i` ["ni","ni",""] >> gvs[] >>
  namedCases_on `j` ["nj","nj",""] >> gvs[] >>
  gvs[INT_MUL_CALCULATE]
QED

(*----------------------------------------------------------*
   rat
 *----------------------------------------------------------*)

(*---------- Helper lemmas - TODO move these? ----------*)

Theorem Num_neg:
  Num (-a) = Num a
Proof
  Cases_on `a` >> gvs[]
QED

Theorem gcd_LESS_EQ:
  ∀m n. n ≠ 0 ⇒ gcd m n ≤ n
Proof
  recInduct gcdTheory.gcd_ind >> rw[Once gcdTheory.gcd_def]
QED

Theorem ABS_SGN:
  ABS (SGN i) = if i = 0 then 0 else 1
Proof
  Cases_on `i` >> gvs[intExtensionTheory.SGN_def]
QED

Theorem divides_coprime_mul:
  ∀n m k. gcd n m = 1 ⇒ (divides n (m * k) ⇔ divides n k)
Proof
  rw[] >> eq_tac >> rw[]
  >- (gvs[Once gcdTheory.GCD_SYM] >> drule gcdTheory.L_EUCLIDES >> simp[])
  >- (drule dividesTheory.DIVIDES_MULT >> disch_then irule)
QED

Theorem nmr_dnm_unique:
  gcd n1 d1 = 1 ∧ gcd n2 d2 = 1 ∧
  n1 * d2 = n2 * d1
  ⇒ n1 = n2 ∧ d1 = d2
Proof
  strip_tac >> imp_res_tac divides_coprime_mul >> gvs[] >>
  first_x_assum $ qspec_then `n2` $ mp_tac o iffLR >> gvs[] >>
  impl_tac >- (gvs[dividesTheory.divides_def] >> qexists `d2` >> gvs[]) >>
  strip_tac >> first_x_assum $ qspec_then `n1` assume_tac >> gvs[] >>
  dxrule_all dividesTheory.DIVIDES_ANTISYM >> strip_tac >> gvs[]
QED

Theorem SGN_MUL_Num[simp]:
  SGN i * &Num i = i
Proof
  Cases_on `i` >> gvs[intExtensionTheory.SGN_def] >>
  simp[INT_MUL_CALCULATE]
QED

Theorem gcd_RATND[simp]:
  gcd (Num $ RATN r) (RATD r) = 1
Proof
  CCONTR_TAC >> gvs[] >>
  qmatch_asmsub_abbrev_tac `gcd n d` >>
  `d ≠ 0` by (unabbrev_all_tac >> gvs[]) >>
  qspecl_then [`n`,`d`] assume_tac gcdTheory.FACTOR_OUT_GCD >> gvs[] >>
  Cases_on `n = 0` >> gvs[] >>
  qspecl_then [`rat_sgn r * &p`,`q`] mp_tac RATN_LEAST >> simp[] >>
  Cases_on `q = 0` >> gvs[] >> reverse $ rw[]
  >- (
    simp[RAT_SGN_ALT, GSYM INT_ABS_MUL, ABS_SGN] >>
    Cases_on `r = 0` >> gvs[] >>
    `ABS (RATN r) = &n` by (unabbrev_all_tac >> Cases_on `RATN r` >> gvs[]) >>
    simp[] >> qpat_assum `n = _` SUBST1_TAC >> simp[] >>
    Cases_on `p = 0` >> gvs[] >> simp[NOT_LESS_EQUAL] >>
    Cases_on `gcd n d = 0` >- gvs[] >- simp[]
    ) >>
  rewrite_tac[Once RATN_RATD_EQ_THM] >> DEP_REWRITE_TAC[RAT_LDIV_EQ] >> simp[] >>
  simp[RDIV_MUL_OUT] >> DEP_REWRITE_TAC[RAT_RDIV_EQ] >> simp[] >>
  `RATN r = rat_sgn r * &n` by (simp[RAT_SGN_ALT] >> unabbrev_all_tac >> gvs[]) >>
  simp[GSYM rat_of_int_MUL, AC RAT_MUL_ASSOC RAT_MUL_COMM] >>
  simp[RAT_MUL_ASSOC] >> rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
  simp[RAT_MUL_NUM_CALCULATE] >>
  qsuff_tac `(p * gcd n d) * q = (q * gcd n d) * p`
  >- metis_tac[]
  >- simp[]
QED

Theorem RATND_suff_eq:
  gcd (Num n) d = 1 ∧ d ≠ 0
  ⇒ RATN (rat_of_int n / &d) = n ∧ RATD (rat_of_int n / &d) = d
Proof
  strip_tac >>
  qpat_abbrev_tac `r = _ / _` >>
  qsuff_tac `rat_sgn r = SGN n ∧ Num (RATN r) = Num n ∧ RATD r = d`
  >- (rw[RAT_SGN_ALT] >> once_rewrite_tac[GSYM SGN_MUL_Num] >> metis_tac[]) >>
  conj_asm1_tac
  >- (
    unabbrev_all_tac >> simp[RAT_SGN_ALT, intExtensionTheory.SGN_def] >>
    Cases_on `n` >> gvs[] >> simp[rat_of_int_ainv]
    ) >>
  `rat_of_int n * &RATD r = rat_of_int (RATN r) * &d` by (
    DEP_REWRITE_TAC[GSYM RAT_RDIV_EQ] >> simp[] >>
    simp[GSYM LDIV_MUL_OUT] >> rewrite_tac[Once RAT_MUL_COMM] >>
    DEP_REWRITE_TAC[GSYM RAT_LDIV_EQ] >> unabbrev_all_tac >> gvs[]) >>
  pop_assum mp_tac >> simp[rat_of_int_def] >>
  `n < 0 ⇔ r < 0` by (
    unabbrev_all_tac >> gvs[RAT_LDIV_LES_POS] >>
    Cases_on `n` >> gvs[] >> simp[rat_of_int_ainv]) >>
  IF_CASES_TAC >> gvs[Num_neg] >>
  simp[RAT_MUL_NUM_CALCULATE] >> strip_tac >> irule nmr_dnm_unique >> simp[]
QED

Definition div_gcd_def:
  div_gcd a b =
    let d = gcd (Num a) b in
      if d = 0 ∨ d = 1 then (a, b) else (a / &d, b DIV d)
End

Theorem div_gcd_reduces:
  div_gcd a b = (n,d) ∧ b ≠ 0 ⇒ d ≠ 0 ∧ gcd (Num n) d = 1 ∧ a * &d = n * &b
Proof
  rw[div_gcd_def] >> gvs[]
  >- (
    Cases_on `b = 1` >> gvs[] >>
    DEP_REWRITE_TAC[DIV_EQ_0] >> simp[NOT_LESS] >>
    Cases_on `gcd (Num a) b` >> gvs[] >>
    qspecl_then [`Num a`,`b`] assume_tac gcd_LESS_EQ >> gvs[]
    )
  >- (
    Cases_on `Num a = 0` >> simp[] >>
    qspecl_then [`Num a`,`b`] assume_tac gcdTheory.FACTOR_OUT_GCD >> gvs[] >>
    qsuff_tac `b DIV gcd (Num a) b = q ∧ Num (a / &gcd (Num a) b) = p` >> rw[]
    >- (
      qpat_x_assum `b = _` $ simp o single o Once >>
      irule MULT_DIV >> Cases_on `gcd (Num a) b` >> gvs[]
      ) >>
    simp[int_div] >> rw[] >> gvs[Num_neg]
    >- (
      qpat_x_assum `Num a = _` $ simp o single o Once >>
      irule MULT_DIV >> Cases_on `gcd (Num a) b` >> gvs[]
      )
    >- (
      qpat_x_assum `Num a = _` $ simp o single o Once >>
      irule MULT_DIV >> Cases_on `gcd (Num a) b` >> gvs[]
      )
    >- (
      irule FALSITY >> pop_assum mp_tac >> simp[] >>
      qpat_x_assum `Num a = _` $ rewrite_tac o single o Once >>
      irule MOD_EQ_0 >> simp[]
      )
    )
  >- (
    qspecl_then [`Num a`,`b`] assume_tac gcdTheory.FACTOR_OUT_GCD >>
    Cases_on `a = 0` >> gvs[] >>
    qabbrev_tac `g = gcd (Num a) b` >>
    `b DIV g = q` by  (irule DIV_UNIQUE >> qexists `0` >> gvs[]) >>
    `a / &g = SGN a * &p` by (
      qspec_then `a` mp_tac $ GEN_ALL (GSYM SGN_MUL_Num) >>
      disch_then $ rewrite_tac o single o Once >>
      DEP_REWRITE_TAC[INT_MUL_DIV] >> conj_tac >- gvs[] >>
      AP_TERM_TAC >> gvs[INT_DIV_CALCULATE] >>
      rewrite_tac[Once MULT_COMM] >> irule MULT_DIV >> gvs[]) >>
    simp[] >>
    qspec_then `a` mp_tac $ GEN_ALL (GSYM SGN_MUL_Num) >>
    disch_then $ rewrite_tac o single o Once >>
    once_rewrite_tac[GSYM INT_MUL_ASSOC] >>
    AP_TERM_TAC >> simp[INT_MUL_CALCULATE]
    )
QED

Theorem div_gcd_correct:
  div_gcd a b = (n,d) ∧ b ≠ 0 ⇒
  rat_of_int a / &b = rat_of_int n / &d ∧
  RATN (rat_of_int a / &b) = n ∧
  RATD (rat_of_int a / &b) = d
Proof
  strip_tac >> reverse conj_asm1_tac
  >- (
    pop_assum SUBST_ALL_TAC >> match_mp_tac RATND_suff_eq >>
    imp_res_tac div_gcd_reduces >> simp[]
    ) >>
  simp[RAT_LDIV_EQ, RDIV_MUL_OUT] >> DEP_REWRITE_TAC[RAT_RDIV_EQ] >> simp[] >>
  once_rewrite_tac[GSYM rat_of_int_of_num] >> simp[rat_of_int_MUL] >>
  imp_res_tac div_gcd_reduces >> gvs[] >>
  gvs[AC INT_MUL_ASSOC INT_MUL_COMM]
QED

(*----------*)

Theorem cv_rat_of_int[cv_rep]:
  from_rat (rat_of_int i) = Pair (from_int i) (Num 1)
Proof
  rw[from_rat_def]
QED

Definition cv_rat_neg_def:
  cv_rat_neg r = Pair (cv_int_neg (cv_fst r)) (cv_snd r)
End

Theorem cv_rat_neg[cv_rep]:
  from_rat (-r) = cv_rat_neg (from_rat r)
Proof
  simp[from_rat_def, cv_rat_neg_def, cv_neg_int]
QED

Definition cv_rat_reciprocal_def:
  cv_rat_reciprocal r =
    cv_if (cv_int_lt (cv_fst r) (Num 0))
      (Pair (Pair (cv_snd r) (Num 0)) (cv_fst (cv_fst r)))
      (Pair (cv_snd r) (cv_fst r))
End

Theorem cv_rat_reciprocal[cv_rep]:
  r ≠ 0 ⇒ from_rat (rat_minv r) = cv_rat_reciprocal (from_rat r)
Proof
  rw[] >> simp[RAT_MINV_RATND] >> simp[cv_rat_reciprocal_def] >>
  `Num 0 = from_int 0` by gvs[from_int_def] >> simp[] >> pop_assum kall_tac >>
  reverse $ rw[] >> gvs[c2b_def] >> pop_assum mp_tac >>
  simp[Once from_rat_def, GSYM cv_int_lt] >>
  strip_tac >> gvs[] >> Cases_on `r < 0` >> gvs[]
  >- (
    `rat_sgn r = 1` by (CCONTR_TAC >> gvs[RAT_LEQ_LES, RAT_LEQ_ANTISYM]) >>
    `rat_of_int (ABS (RATN r)) = &Num (RATN r)` by (Cases_on `RATN r` >> gvs[]) >>
    simp[from_rat_def] >>
    qspecl_then [`int_of_num $ RATD r`,`Num (RATN r)`]
      mp_tac $ GEN_ALL RATND_suff_eq >>
    simp[Once gcdTheory.GCD_SYM] >> strip_tac >> simp[from_int_def]
    )
  >- (
    `rat_sgn r = -1` by gvs[] >> simp[] >>
    simp[rat_of_int_ainv, from_rat_def, from_int_def] >>
    DEP_REWRITE_TAC[RAT_LDIV_LES_POS] >> simp[] >> conj_tac
    >- (
      `0 = rat_of_int 0` by gvs[] >> pop_assum SUBST1_TAC >>
      rewrite_tac[rat_of_int_LT] >> simp[]
      ) >>
    simp[RAT_MUL_NUM_CALCULATE] >>
    simp[GSYM RAT_DIV_AINV, Num_neg] >>
    `rat_of_int (ABS (RATN r)) = &Num (RATN r)` by (Cases_on `RATN r` >> gvs[]) >>
    qspecl_then [`int_of_num $ RATD r`,`Num (RATN r)`]
      mp_tac $ GEN_ALL RATND_suff_eq >>
    simp[Once gcdTheory.GCD_SYM]
    )
QED

Definition cv_rat_norm_def:
  cv_rat_norm r =
    let d = cv_gcd (cv_abs (cv_fst r)) (cv_snd r) in
    cv_if (cv_lt d (Num 2))
      r
      (Pair (cv_int_div (cv_fst r) d) (cv_div (cv_snd r) d))
End

Theorem cv_rat_norm_div_gcd:
  (λ(x,y). Pair (from_int x) (Num y)) (div_gcd a b) =
  cv_rat_norm (Pair (from_int a) (Num b))
Proof
  simp[div_gcd_def, cv_rat_norm_def] >>
  simp[GSYM cv_Num, GSYM cv_gcd_thm, c2b_def] >>
  ntac 3 $ simp[Once COND_RAND] >> simp[COND_RATOR] >>
  `Num (gcd (Num a) b) = from_int (&(gcd (Num a) b))` by simp[from_int_def] >>
  simp[GSYM cv_int_div] >>
  simp[wordsTheory.NUMERAL_LESS_THM] >>
  Cases_on `a = 0 ∧ b = 0 ∨ gcd (Num a) b = 1` >> gvs[] >>
  IF_CASES_TAC >> gvs[] >> simp[total_int_div_def] >> IF_CASES_TAC >> gvs[]
QED

Theorem from_rat_eq_cv_rat_norm_suff[local]:
  r = rat_of_int n / &d ∧ d ≠ 0 ∧
  from_int n = x ∧
  Num d = y
  ⇒ from_rat r = cv_rat_norm (Pair x y)
Proof
  rw[] >> simp[GSYM cv_rat_norm_div_gcd] >>
  pairarg_tac >> gvs[from_rat_def] >>
  drule_all div_gcd_correct >> rw[]
QED

Definition cv_rat_add_def:
  cv_rat_add r1 r2 =
    cv_rat_norm $ Pair
      (cv_int_add (cv_int_mul (cv_fst r1) (cv_snd r2)) (cv_int_mul (cv_fst r2) (cv_snd r1)))
      (cv_mul (cv_snd r1) (cv_snd r2))
End

Theorem cv_rat_add[cv_rep]:
  from_rat (r1 + r2) = cv_rat_add (from_rat r1) (from_rat r2)
Proof
  simp[cv_rat_add_def] >> irule from_rat_eq_cv_rat_norm_suff >>
  qexistsl [`RATD r1 * RATD r2`,`(RATN r1 * &RATD r2) + (RATN r2 * &RATD r1)`] >>
  simp[from_rat_def] >> rw[]
  >- (
    simp[cv_int_add] >> rpt MK_COMB_TAC >> simp[] >>
    simp[cv_int_mul] >> rpt MK_COMB_TAC >> simp[from_int_def]
    ) >>
  qspecl_then [`&RATD r1`,`rat_of_int $ RATN r1`,`&RATD r2`,`rat_of_int $ RATN r2`]
    mp_tac $ GEN_ALL $ GSYM RAT_DIVDIV_ADD >> simp[] >>
  once_rewrite_tac[GSYM rat_of_int_of_num] >>
  rewrite_tac[rat_of_int_MUL, rat_of_int_ADD, INT_MUL_CALCULATE] >> simp[]
QED

Theorem cv_rat_sub[cv_rep]:
  from_rat (r1 - r2) = cv_rat_add (from_rat r1) (cv_rat_neg (from_rat r2))
Proof
  simp[RAT_SUB_ADDAINV, GSYM cv_rat_neg, GSYM cv_rat_add]
QED

Definition cv_rat_mul_def:
  cv_rat_mul r1 r2 =
    cv_rat_norm $ Pair
      (cv_int_mul (cv_fst r1) (cv_fst r2))
      (cv_mul (cv_snd r1) (cv_snd r2))
End

Theorem cv_rat_mul[cv_rep]:
  from_rat (r1 * r2) = cv_rat_mul (from_rat r1) (from_rat r2)
Proof
  simp[cv_rat_mul_def] >> irule from_rat_eq_cv_rat_norm_suff >>
  qexistsl [`RATD r1 * RATD r2`,`RATN r1 * RATN r2`] >>
  simp[from_rat_def, cv_int_mul] >>
  qspecl_then [`&RATD r2`,`rat_of_int $ RATN r2`,`&RATD r1`,`rat_of_int $ RATN r1`]
    mp_tac $ GEN_ALL $ GSYM RAT_DIVDIV_MUL >>
  simp[rat_of_int_MUL, RAT_MUL_NUM_CALCULATE]
QED

Theorem cv_rat_div[cv_rep]:
  r2 ≠ 0 ⇒ from_rat (r1 / r2) =
            cv_rat_mul (from_rat r1) (cv_rat_reciprocal (from_rat r2))
Proof
  simp[RAT_DIV_MULMINV, GSYM cv_rat_reciprocal, GSYM cv_rat_mul]
QED

Definition cv_rat_lt_def:
  cv_rat_lt r1 r2 =
    cv_int_lt (cv_int_mul (cv_fst r1) (cv_snd r2))
              (cv_int_mul (cv_fst r2) (cv_snd r1))
End

Theorem cv_rat_lt[cv_rep]:
  b2c (r1 < r2) = cv_rat_lt (from_rat r1) (from_rat r2)
Proof
  rw[cv_rat_lt_def, from_rat_def] >>
  `∀n. Num n = from_int (&n)` by simp[from_int_def] >>
  simp[] >> pop_assum kall_tac >>
  simp[GSYM cv_int_mul, GSYM cv_int_lt] >> AP_TERM_TAC >>
  qspec_then `r1` mp_tac $ GEN_ALL RATN_RATD_EQ_THM >>
  disch_then $ rewrite_tac o single o Once >>
  qspec_then `r2` mp_tac $ GEN_ALL RATN_RATD_EQ_THM >>
  disch_then $ rewrite_tac o single o Once >>
  `0 < RATD r1` by gvs[] >> `0 < RATD r2` by gvs[] >>
  rename1 `rat_of_int n1 / &d1 < rat_of_int n2 / &d2` >>
  simp[RAT_LDIV_LES_POS, RDIV_MUL_OUT, RAT_RDIV_LES_POS] >>
  once_rewrite_tac[GSYM rat_of_int_of_num] >> rewrite_tac[rat_of_int_MUL] >>
  simp[AC INT_MUL_ASSOC INT_MUL_COMM]
QED

Theorem cv_rat_le[cv_rep]:
  b2c (r1 ≤ r2) = cv_if (cv_rat_lt (from_rat r2) (from_rat r1))
                        (Num 0) (Num 1)
Proof
  simp[GSYM RAT_LEQ_LES, GSYM cv_rat_lt] >> Cases_on `r2 < r1` >> gvs[]
QED

Theorem cv_rat_gt[cv_rep]:
  b2c (r1 > r2) = cv_rat_lt (from_rat r2) (from_rat r1)
Proof
  simp[rat_gre_def, GSYM cv_rat_lt]
QED

Theorem cv_rat_ge[cv_rep]:
  b2c (r1 ≥ r2) = cv_if (cv_rat_lt (from_rat r1) (from_rat r2))
                        (Num 0) (Num 1)
Proof
  simp[rat_geq_def, GSYM RAT_LEQ_LES, GSYM cv_rat_lt] >>
  Cases_on `r1 < r2` >> gvs[]
QED

(*----------------------------------------------------------*
   char
 *----------------------------------------------------------*)

Theorem cv_chr_thm[cv_rep]:
  n < 256 ⇒ from_char (CHR n) = Num n
Proof
  gvs [from_char_def]
QED

Theorem cv_ord_thm[cv_rep]:
  Num (ORD c) = from_char c
Proof
  gvs [from_char_def]
QED

(*----------------------------------------------------------*
   if, let, arb, =
 *----------------------------------------------------------*)

Theorem cv_rep_if[cv_rep]:
  cv_rep p1 c1 b2c b ∧
  cv_rep p2 c2 f t ∧
  cv_rep p3 c3 f e ⇒
  cv_rep (p1 ∧ (b ⇒ p2) ∧ (~b ⇒ p3))
         (cv_if c1 c2 c3) f (if b then t else e)
Proof
  fs [cv_rep_def] \\ rw [] \\ gvs []
QED

Theorem cv_rep_let[cv_rep]:
  cv_rep p1 c1 (a:'a->cv) x ∧
  (∀v. cv_rep (p2 v) (c2 (a v)) (b:'b->cv) (y v)) ⇒
  cv_rep (p1 ∧ ∀v. v = x ⇒ p2 v) (LET c2 c1) b (LET y x)
Proof
  fs [cv_rep_def]
QED

Theorem cv_rep_arb[cv_rep]:
  F ⇒ f ARB = Num 0
Proof
  fs []
QED

Theorem cv_rep_eq[cv_rep]:
  cv_rep p1 c1 f x ∧
  cv_rep p2 c2 f y ∧
  from_to f t ⇒
  cv_rep (p1 ∧ p2) (cv_eq c1 c2) b2c (x = y)
Proof
  fs [cv_rep_def,cv_eq_def]
  \\ Cases_on ‘x = y’ \\ fs []
  \\ rw [] \\ gvs []
  \\ fs [from_to_def]
  \\ metis_tac []
QED

(*----------------------------------------------------------*
   word lemmas, ported from:
   HOL/examples/l3-machine-code/arm8/asl-equiv/l3_equivalence_miscScript.sml
   TODO: move these?
 *----------------------------------------------------------*)

Theorem bitify_APPEND[local]:
  ∀l1 l2 a. bitify a (l1 ++ l2) = bitify (bitify a l1) l2
Proof
  rw[bitify_reverse_map]
QED

Theorem v2n_APPEND[local]:
  ∀a b. v2n (a ++ b) = v2n b + (2 ** LENGTH b * v2n a)
Proof
  rw[v2n_def, bitify_APPEND] >>
  rw[bitify_reverse_map] >>
  gvs[numposrepTheory.num_from_bin_list_def, numposrepTheory.l2n_APPEND]
QED

Theorem v2n[local]:
  v2n [] = 0 ∧
  v2n (b::bs) = if b then 2 ** LENGTH bs + v2n bs else v2n bs
Proof
  rw[] >> once_rewrite_tac[CONS_APPEND]
  >- EVAL_TAC >>
  once_rewrite_tac[v2n_APPEND] >> simp[] >> EVAL_TAC
QED

Theorem fixwidth_REPLICATE[local]:
  ∀len l. fixwidth len l =
    if LENGTH l ≤ len then REPLICATE (len - LENGTH l) F ++ l
    else DROP (LENGTH l - len) l
Proof
  rw[fixwidth, GSYM pad_left_extend, PAD_LEFT] >> gvs[GSYM REPLICATE_GENLIST] >>
  `len = LENGTH l` by gvs[] >> pop_assum SUBST_ALL_TAC >> gvs[]
QED

Theorem cv_inline_word_ror[cv_inline]:
  ∀r a. (a : α word) ⇄ r =
    let d = dimindex (:α);
        r = r MOD d
    in a ≪ (d − r) ‖ a ⋙ r
Proof
  rw[] >> qspec_then `a` assume_tac ranged_bitstring_nchotomy >> gvs[] >>
  simp[word_ror_v2w, rotate_def] >> IF_CASES_TAC >> gvs[] >>
  qabbrev_tac `r' = r MOD dimindex (:'a)` >>
  `r' < dimindex (:'a)` by (unabbrev_all_tac >> gvs[]) >>
  qpat_x_assum `Abbrev _` kall_tac >>
  simp[word_lsl_v2w, word_lsr_v2w, rotate_def, word_or_v2w] >>
  simp[Once v2w_11] >> simp[field_def, ADD1] >>
  `shiftr v 0 = v` by simp[shiftr_def] >> simp[fixwidth] >>
  simp[bor_def, bitwise_def, shiftl_def, shiftr_def, PAD_LEFT, PAD_RIGHT, MAX_DEF] >>
  simp[fixwidth_REPLICATE, GSYM MAP_DROP, GSYM ZIP_DROP, DROP_APPEND] >>
  `dimindex (:α) − r' − dimindex (:α) = 0` by simp[] >> simp[] >>
  rw[LIST_EQ_REWRITE, EL_DROP, EL_MAP, EL_ZIP, EL_APPEND_EQN, EL_REPLICATE] >> rw[]
QED

(*----------------------------------------------------------*
   word conversions
 *----------------------------------------------------------*)

Theorem cv_rep_word_w2n[cv_rep]:
  Num (w2n w) = from_word (w :'a word)
Proof
  fs [cv_rep_def] \\ rw [] \\ gvs [from_word_def]
QED

Theorem cv_rep_word_n2w[cv_rep]:
  from_word (n2w n : 'a word) = (cv_mod (Num n) (Num (2 ** dimindex (:'a))))
Proof
  fs [cv_rep_def] \\ rw [] \\ gvs [from_word_def,dimword_def]
QED

Theorem cv_rep_word_w2w[cv_rep]:
  from_word ((w2w (w:'a word)) : 'b word)
  =
  if dimindex (:'a) ≤ dimindex (:'b) then from_word w else
    cv_mod (from_word w) (Num (2 ** dimindex (:'b)))
Proof
  fs [cv_rep_def] \\ rw []
  \\ gvs [from_word_def,GSYM dimword_def,w2w_def]
  \\ irule LESS_LESS_EQ_TRANS
  \\ irule_at Any w2n_lt
  \\ gvs [dimword_def]
QED

Theorem cv_inline_word_sw2sw[cv_inline]:
 sw2sw (w : 'a word) =
  let v = w in (if word_msb v then -1w ≪ dimindex (:'a) else 0w) + w2w v : 'b word
Proof
  rw[sw2sw_w2w_add]
QED

Theorem cv_rep_dimindex[cv_rep]:
  Num (dimindex (:'a)) =  Num (dimindex (:'a))
Proof
  simp[]
QED

Theorem cv_inline_w2i[cv_inline]:
  w2i w = let v = w in if word_msb v then -&w2n (-v) else &w2n v
Proof
  simp[w2i_def]
QED

Definition v2n_custom_def:
  v2n_custom acc [] = acc ∧
  v2n_custom acc (T::rest) = v2n_custom (2 * acc + 1n) rest ∧
  v2n_custom acc (F::rest) = v2n_custom (2 * acc) rest
End

Theorem v2n_custom_thm:
  v2n_custom 0 = v2n
Proof
  qsuff_tac `∀acc l. v2n_custom acc l = v2n l + acc * (2 ** LENGTH l)`
  >- rw[FUN_EQ_THM] >>
  recInduct v2n_custom_ind >> rw[v2n_custom_def, v2n] >>
  simp[RIGHT_ADD_DISTRIB, EXP]
QED

Theorem cv_inline_v2n[cv_inline] = GSYM v2n_custom_thm;

Theorem cv_inline_v2w[cv_inline] =
  REWRITE_RULE [GSYM v2n_custom_thm] $ GSYM n2w_v2n;

Theorem cv_inline_w2v[cv_inline]:
  w2v (w:'a word) = let d = dimindex (:'a) in
                      GENLIST (λi. word_bit (d - 1 - i) w) d
Proof
  simp[w2v_def, GENLIST_FUN_EQ, word_bit_def]
QED

(*----------------------------------------------------------*
   word arithmetic
 *----------------------------------------------------------*)

Theorem cv_rep_word_add[cv_rep]:
  from_word (w1 + w2)
  =
  cv_mod (cv_add (from_word (w1 :'a word)) (from_word w2)) (Num (dimword (:'a)))
Proof
  fs [cv_rep_def] \\ rw [] \\ gvs [from_word_def]
  \\ Cases_on ‘w1’ \\ Cases_on ‘w2’ \\ gvs [wordsTheory.word_add_n2w]
QED

Definition cv_word_sub_def:
  cv_word_sub x y d =
    cv_if (cv_lt x y)
      (cv_sub (cv_add x d) y)
      (cv_sub x y)
End

Theorem cv_rep_word_sub[cv_rep]:
  from_word (w1 - w2 :'a word)
  =
  cv_word_sub (from_word w1) (from_word w2) (Num (dimword (:'a)))
Proof
  fs [cv_rep_def] \\ rw [] \\ gvs [from_word_def,cv_word_sub_def]
  \\ Cases_on ‘w1’ \\ Cases_on ‘w2’ \\ gvs []
  \\ reverse $ Cases_on ‘n < n'’ \\ gvs []
  >- gvs [arithmeticTheory.NOT_LESS,GSYM wordsTheory.n2w_sub]
  \\ gvs [wordsTheory.word_sub_def,wordsTheory.word_2comp_n2w]
  \\ gvs [wordsTheory.word_add_n2w]
QED

Theorem cv_rep_word_neg[cv_rep]:
  from_word (- w1 :'a word)
  =
  cv_word_sub (Num 0) (from_word w1) (Num (dimword (:'a)))
Proof
  rewrite_tac [GSYM wordsTheory.WORD_SUB_LZERO,cv_rep_word_sub]
  \\ fs [from_word_def]
QED

Theorem cv_rep_word_mul[cv_rep]:
  from_word (w1 * w2 :'a word)
  =
  cv_mod (cv_mul (from_word w1) (from_word w2)) (Num (dimword (:'a)))
Proof
  fs [cv_rep_def] \\ rw [] \\ gvs [from_word_def]
  \\ Cases_on ‘w1’ \\ Cases_on ‘w2’ \\ gvs [wordsTheory.word_mul_n2w]
QED

Theorem cv_rep_word_div[cv_rep]:
  from_word (word_div w1 w2)
  =
  cv_div (from_word w1) (from_word w2)
Proof
  fs [cv_rep_def] \\ rw [] \\ gvs [from_word_def]
  \\ Cases_on ‘w1’ \\ Cases_on ‘w2’ \\ gvs [word_div_def]
  \\ rename [‘n DIV m’] \\ Cases_on ‘m’ \\ fs []
  \\ gvs [DIV_LT_X] \\ gvs [MULT_CLAUSES]
QED

Theorem cv_rep_word_mod[cv_rep]:
  from_word (word_mod w1 w2)
  =
  cv_mod (from_word w1) (from_word w2)
Proof
  fs [cv_rep_def] \\ rw [] \\ gvs [from_word_def]
  \\ Cases_on ‘w1’ \\ Cases_on ‘w2’ \\ gvs [word_mod_def]
  \\ rename [‘n MOD m’] \\ Cases_on ‘m’ \\ fs []
  \\ irule LESS_EQ_LESS_TRANS
  \\ last_x_assum $ irule_at Any
  \\ irule arithmeticTheory.MOD_LESS_EQ \\ fs []
QED

Theorem cv_inline_word_log2[cv_inline] = word_log2_def;

(*----------------------------------------------------------*
   word_msb, unit_max, word shifts
 *----------------------------------------------------------*)

Theorem cv_rep_word_msb[cv_rep]:
  b2c (word_msb w)
  =
  cv_div (from_word (w :'a word)) (Num (2 ** (dimindex (:'a) - 1)))
Proof
  rw [Once EQ_SYM_EQ] \\ gvs [from_word_def]
  \\ Cases_on ‘w’ \\ gvs [wordsTheory.word_msb_def]
  \\ gvs [wordsTheory.n2w_def,fcpTheory.FCP_BETA,bitTheory.BIT_def,
          bitTheory.BITS_THM,wordsTheory.dimword_def]
  \\ ‘0 < dimindex (:'a)’ by fs [fcpTheory.DIMINDEX_GT_0]
  \\ Cases_on ‘dimindex (:'a)’ \\ gvs []
  \\ rename [‘SUC l’]
  \\ ‘0 < 2:num’ by fs []
  \\ drule arithmeticTheory.DIVISION
  \\ disch_then $ qspec_then ‘n DIV (2 ** l)’
       (strip_assume_tac o ONCE_REWRITE_RULE [CONJ_COMM])
  \\ pop_assum (fn th => simp [Once th])
  \\ simp [arithmeticTheory.DIV_DIV_DIV_MULT]
  \\ ‘n DIV (2 * 2 ** l) = 0’ by gvs [DIV_EQ_X,GSYM EXP]
  \\ asm_rewrite_tac [] \\ simp []
  \\ drule (DECIDE “n < 2 ⇒ n = 0 ∨ n = 1:num”)
  \\ strip_tac \\ gvs []
QED

Theorem cv_rep_word_uint_max[cv_rep]:
  from_word (UINT_MAXw:'a word)
  =
  Num (2 ** dimindex (:'a) - 1)
Proof
  rw [cv_rep_def,from_word_def] \\ EVAL_TAC
  \\ gvs [w2n_n2w,dimword_def]
QED

Theorem cv_rep_word_lsl[cv_rep]:
  from_word (word_lsl (w:'a word) n)
  =
  cv_mod (cv_mul (from_word w) (cv_exp (Num 2) (Num n)))
         (Num (2 ** dimindex (:'a)))
Proof
  gvs [cv_rep_def] \\ rw [] \\ gvs []
  \\ gvs [from_word_def,cv_exp_def]
  \\ Cases_on ‘w’ \\ gvs [word_lsl_n2w]
  \\ rw [] \\ gvs [dimword_def]
  \\ ‘0n < 2 ** dimindex (:'a)’ by gvs []
  \\ drule MOD_TIMES2
  \\ disch_then (fn th => once_rewrite_tac [GSYM th])
  \\ qsuff_tac ‘2 ** n MOD 2 ** dimindex (:α) = 0’ \\ gvs []
  \\ ‘dimindex (:'a) ≤ n’ by fs []
  \\ gvs [LESS_EQ_EXISTS,EXP_ADD]
QED

Theorem cv_rep_word_lsr[cv_rep]:
  from_word (word_lsr (w:'a word) n)
  =
  cv_div (from_word w) (cv_exp (Num 2) (Num n))
Proof
  gvs [cv_rep_def] \\ rw [] \\ gvs []
  \\ gvs [from_word_def,cv_exp_def,w2n_lsr]
QED

Theorem word_asr_add[cv_inline]:
  w ≫ n =
  let x = w in
  if word_msb (x :'a word) then
    (dimindex (:'a) − 1 '' dimindex (:α) − n) UINT_MAXw + (x ⋙ n)
  else x ⋙ n
Proof
  simp []
  \\ dep_rewrite.DEP_REWRITE_TAC [WORD_ADD_OR]
  \\ conj_tac >-
   (gvs [fcpTheory.CART_EQ,word_and_def,word_bits_def,
          wordsTheory.word_0,fcpTheory.FCP_BETA,word_slice_def]
    \\ rpt strip_tac \\ CCONTR_TAC \\ gvs [word_T,word_lsr_def]
    \\ gvs [fcpTheory.FCP_BETA])
  \\ rw [word_asr]
QED

(*----------------------------------------------------------*
   word comparisons (unsigned and signed)
 *----------------------------------------------------------*)

Theorem cv_word_lo_thm[cv_rep]:
  b2c (word_lo w1 w2) = cv_lt (from_word w1) (from_word w2)
Proof
  fs [from_word_def] \\ rw [WORD_LO]
QED

Theorem cv_word_hi_thm[cv_rep]:
  b2c (word_hi w2 w1) = cv_lt (from_word w1) (from_word w2)
Proof
  fs [from_word_def] \\ rw [WORD_HI]
QED

Theorem cv_word_hs_thm[cv_rep]:
  b2c (word_hs w1 w2) = cv_sub (Num 1) (cv_lt (from_word w1) (from_word w2))
Proof
  simp [GSYM cv_word_hi_thm,GSYM cv_rep_not,WORD_HS,WORD_HI,
        GREATER_EQ,GREATER_DEF,NOT_LESS]
QED

Theorem cv_word_ls_thm[cv_rep]:
  b2c (word_ls w1 w2) = cv_sub (Num 1) (cv_lt (from_word w2) (from_word w1))
Proof
  simp [GSYM cv_word_hi_thm,GSYM cv_rep_not]
  \\ rw [WORD_HI,WORD_LS,NOT_LESS,arithmeticTheory.GREATER_DEF]
QED

Definition cv_word_lt_def:
  cv_word_lt w1 w2 msb1 msb2 =
    cv_if (cv_eq msb1 msb2)
          (cv_lt w1 w2)
          (cv_if msb1 (Num 1) (cv_sub (Num 1) msb2))
End

Theorem cv_word_lt_thm[cv_rep]:
  b2c (word_lt w1 w2)
  =
  cv_word_lt (from_word w1) (from_word (w2:'a word))
             (cv_div (from_word w1) (Num (2 ** (dimindex (:'a) - 1))))
             (cv_div (from_word w2) (Num (2 ** (dimindex (:'a) - 1))))
Proof
  rewrite_tac [GSYM cv_rep_word_msb] \\ simp [Once EQ_SYM_EQ]
  \\ gvs [cv_word_lt_def]
  \\ ‘∀b1 b2. (c2b (cv_eq (b2c b1) (b2c b2)) = (b1 = b2)) ∧ (c2b (b2c b1) = b1)’ by
    (Cases \\ Cases \\ gvs [])
  \\ simp [GSYM cv_word_lo_thm,GSYM cv_rep_not,wordsTheory.WORD_LT,WORD_LO]
  \\ rw [] \\ gvs []
QED

Theorem cv_word_gt_thm[cv_rep]:
  b2c (word_gt w2 w1)
  =
  cv_word_lt (from_word w1) (from_word (w2:'a word))
             (cv_div (from_word w1) (Num (2 ** (dimindex (:'a) - 1))))
             (cv_div (from_word w2) (Num (2 ** (dimindex (:'a) - 1))))
Proof
  rewrite_tac [wordsTheory.WORD_GREATER,cv_word_lt_thm]
QED

Theorem cv_word_le_thm[cv_rep]:
  b2c (word_le w2 w1)
  =
  cv_sub (Num 1)
         (cv_word_lt (from_word w1) (from_word (w2:'a word))
                     (cv_div (from_word w1) (Num (2 ** (dimindex (:'a) - 1))))
                     (cv_div (from_word w2) (Num (2 ** (dimindex (:'a) - 1)))))
Proof
  rewrite_tac [GSYM cv_word_lt_thm,GSYM cv_rep_not,WORD_NOT_LESS]
QED

Theorem cv_word_ge_thm[cv_rep]:
  b2c (word_ge w1 w2)
  =
  cv_sub (Num 1)
         (cv_word_lt (from_word w1) (from_word (w2:'a word))
                     (cv_div (from_word w1) (Num (2 ** (dimindex (:'a) - 1))))
                     (cv_div (from_word w2) (Num (2 ** (dimindex (:'a) - 1)))))
Proof
  rewrite_tac [cv_word_le_thm,wordsTheory.WORD_GREATER_EQ]
QED

(*----------------------------------------------------------*
   word bits, slice, extract, concat
 *----------------------------------------------------------*)

Theorem cv_word_bit_thm[cv_rep]:
  b2c (word_bit b w) =
    cv_mod (cv_div (from_word w) (cv_exp (Num 2) (Num b))) (Num 2)
Proof
  Cases_on `w` >> simp[word_bit_n2w] >>
  simp[GSYM cv_rep_exp, from_word_def] >>
  simp[bitTheory.BIT_DEF] >>
  simp[LE_LT1] >> `dimindex (:'a) ≠ 0` by gvs[] >> simp[] >>
  Cases_on `b < dimindex (:'a)` >> gvs[]
  >- (
    simp[oneline b2c_def] >> rw[] >> gvs[] >>
    qspecl_then [`n DIV 2 ** b`,`2`] assume_tac MOD_LESS >> simp[]
    ) >>
  gvs[dimword_def] >>
  qsuff_tac `n DIV 2 ** b = 0` >> gvs[] >>
  irule LESS_DIV_EQ_ZERO >> gvs[NOT_LESS] >>
  irule LESS_LESS_EQ_TRANS >> goal_assum drule >> simp[]
QED

Triviality MIN_lemma:
  l ≠ 0 ⇒ MIN k (l - 1) + 1 = MIN (k+1) l
Proof
  rw [MIN_DEF] \\ gvs []
QED

Theorem cv_word_bits_thm[cv_rep]:
  from_word (word_bits h l (w:'a word))
  =
  cv_div (cv_mod (from_word w)
                 (cv_exp (Num 2) (cv_min (cv_add (Num h) (Num 1)) (Num (dimindex (:'a))))))
         (cv_exp (Num 2) (Num l))
Proof
  simp [Once EQ_SYM_EQ]
  \\ ‘w = n2w (w2n w)’ by fs []
  \\ pop_assum (fn th => once_rewrite_tac [th])
  \\ rewrite_tac [word_bits_n2w,bitTheory.BITS_THM2,cv_add_def,GSYM cv_min_thm,
                  cv_exp_def,c2n_def]
  \\ gvs [from_word_def,ADD1,MIN_lemma,w2n_lt]
  \\ gvs [DIV_LT_X]
  \\ match_mp_tac LESS_EQ_LESS_TRANS
  \\ irule_at (Pos hd) arithmeticTheory.MOD_LESS_EQ
  \\ gvs []
  \\ match_mp_tac LESS_LESS_EQ_TRANS
  \\ irule_at (Pos hd) w2n_lt
  \\ gvs []
QED

Theorem cv_word_slice_thm[cv_rep]:
  from_word (word_slice h l (w:'a word))
  =
  cv_mod (cv_mul
    (cv_div (cv_mod (from_word w)
                   (cv_exp (Num 2) (cv_min (cv_add (Num h) (Num 1)) (Num (dimindex (:'a))))))
            (cv_exp (Num 2) (Num l)))
     (Num (2 ** l))) (Num (dimword (:α)))
Proof
  rewrite_tac [GSYM cv_word_bits_thm,wordsTheory.WORD_SLICE_THM]
  \\ rewrite_tac [cv_rep_word_lsl,cv_exp_def] \\ fs []
  \\ simp [from_word_def,dimword_def]
QED

Theorem cv_word_extract[cv_rep] =
  “from_word (word_extract h l (w:'a word) : 'b word)”
  |> SIMP_CONV std_ss [word_extract_def,cv_rep_word_w2w,cv_word_bits_thm];

Triviality word_join_add:
  FINITE 𝕌(:'a) ∧ FINITE 𝕌(:'b) ⇒
  word_join (v:'a word) (w:'b word) =
  (w2w v ≪ dimindex (:β)) + w2w w
Proof
  simp [word_join_def]
  \\ once_rewrite_tac [EQ_SYM_EQ] \\ rw []
  \\ irule WORD_ADD_OR
  \\ gvs [fcpTheory.CART_EQ,word_and_def,fcpTheory.FCP_BETA,word_lsl_def,w2w]
  \\ gvs [fcpTheory.index_sum,wordsTheory.word_0,NOT_LESS]
  \\ metis_tac []
QED

Theorem cv_word_join_thm[cv_rep]:
  FINITE 𝕌(:'a) ∧ FINITE 𝕌(:'b) ⇒
  from_word (word_join (w1:'a word) (w2:'b word))
  =
  cv_add (cv_mul (from_word w1) (cv_exp (Num 2) (Num (dimindex (:'b)))))
         (from_word w2)
Proof
  simp [word_join_add, cv_rep_word_add, cv_rep_word_lsl, cv_rep_word_w2w]
  \\ gvs [fcpTheory.index_sum]
  \\ gvs [from_word_def,cv_add_def,cv_mod_def,cv_mul_def,cv_exp_def]
  \\ gvs [GSYM dimword_def]
  \\ ‘(dimword (:β) * w2n w1) < 2 ** (dimindex (:α) + dimindex (:β))’ by
   (once_rewrite_tac [ADD_COMM]
    \\ rewrite_tac [EXP_ADD,dimword_def,LT_MULT_LCANCEL]
    \\ simp [GSYM dimword_def,w2n_lt])
  \\ rpt strip_tac \\ gvs []
  \\ qsuff_tac ‘(w2n w2 + dimword (:'b) * w2n w1) < dimword (:α + β)’ >- fs []
  \\ simp [dimword_def] \\ gvs [fcpTheory.index_sum,EXP_ADD]
  \\ irule LESS_LESS_EQ_TRANS
  \\ rewrite_tac [GSYM dimword_def]
  \\ qexists_tac ‘SUC (w2n w1) * dimword (:β)’
  \\ gvs [LE_MULT_RCANCEL] \\ gvs [DECIDE “SUC n ≤ k ⇔ n < k”, w2n_lt]
  \\ gvs [MULT_CLAUSES,w2n_lt]
QED

Theorem cv_word_concat_thm[cv_rep] =
  “from_word (((w1:'a word) @@ (w2:'b word)) :'c word)”
    |> REWRITE_CONV [word_concat_def,cv_rep_word_w2w,
                     UNDISCH cv_word_join_thm]
    |> DISCH_ALL
    |> SIMP_RULE std_ss [fcpTheory.index_sum];

(*----------------------------------------------------------*
   word or, and, xor
 *----------------------------------------------------------*)

Definition cv_word_or_loop_def:
  cv_word_or_loop x y =
    if c2b (cv_lt (Num 0) x) then
      cv_add (cv_mul (Num 2) (cv_word_or_loop (cv_div x (Num 2)) (cv_div y (Num 2))))
             (cv_max (cv_mod x (Num 2)) (cv_mod y (Num 2)))
    else y
Termination
  WF_REL_TAC ‘measure (c2n o FST)’ \\ Cases \\ fs [] \\ rw []
End

Theorem cv_word_or_loop_def[allow_rebind] = cv_word_or_loop_def
  |> REWRITE_RULE [GSYM cvTheory.cv_if]

Definition cv_word_or_def:
  cv_word_or x y =
    cv_if (cv_lt x y)
      (cv_word_or_loop x y)
      (cv_word_or_loop y x)
End

Definition cv_word_and_loop_def:
  cv_word_and_loop x y =
    if c2b (cv_lt (Num 0) x) then
      cv_add (cv_mul (Num 2) (cv_word_and_loop (cv_div x (Num 2)) (cv_div y (Num 2))))
             (cv_div (cv_add (cv_mod x (Num 2)) (cv_mod y (Num 2))) (Num 2))
    else (Num 0)
Termination
  WF_REL_TAC ‘measure (c2n o FST)’ \\ Cases \\ fs [] \\ rw []
End

Theorem cv_word_and_loop_def[allow_rebind] = cv_word_and_loop_def
  |> REWRITE_RULE [GSYM cvTheory.cv_if]

Definition cv_word_and_def:
  cv_word_and x y =
    cv_if (cv_lt x y)
      (cv_word_and_loop x y)
      (cv_word_and_loop y x)
End

Definition cv_word_xor_loop_def:
  cv_word_xor_loop x y =
    if c2b (cv_lt (Num 0) x) then
      cv_add (cv_mul (Num 2) (cv_word_xor_loop (cv_div x (Num 2)) (cv_div y (Num 2))))
             (cv_mod (cv_add (cv_mod x (Num 2)) (cv_mod y (Num 2))) (Num 2))
    else y
Termination
  WF_REL_TAC ‘measure (c2n o FST)’ \\ Cases \\ fs [] \\ rw []
End

Theorem cv_word_xor_loop_def[allow_rebind] = cv_word_xor_loop_def
  |> REWRITE_RULE [GSYM cvTheory.cv_if]

Definition cv_word_xor_def:
  cv_word_xor x y =
    cv_if (cv_lt x y)
      (cv_word_xor_loop x y)
      (cv_word_xor_loop y x)
End

Theorem BITWISE_ADD:
  ∀l k m n b.
    BITWISE (l + k) b m n =
    BITWISE l b m n +
    BITWISE k b (m DIV 2 ** l) (n DIV 2 ** l) * 2 ** l
Proof
  Induct_on ‘k’
  \\ fs [bitTheory.BITWISE_def,arithmeticTheory.ADD_CLAUSES]
  \\ rw [] \\ rewrite_tac [arithmeticTheory.ADD_ASSOC,arithmeticTheory.EQ_ADD_RCANCEL]
  \\ simp_tac std_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
  \\ simp_tac std_ss [AC arithmeticTheory.MULT_ASSOC arithmeticTheory.MULT_COMM]
  \\ simp_tac std_ss [arithmeticTheory.LEFT_ADD_DISTRIB]
  \\ simp_tac std_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
  \\ simp_tac std_ss [AC arithmeticTheory.MULT_ASSOC arithmeticTheory.MULT_COMM]
  \\ simp [DECIDE “m + n = n + k ⇔ m = k:num”]
  \\ simp_tac std_ss [Once arithmeticTheory.MULT_COMM]
  \\ rewrite_tac [GSYM bitTheory.SBIT_MULT]
  \\ rewrite_tac [GSYM bitTheory.BIT_SHIFT_THM4]
QED

Theorem BITWISE:
  BITWISE 0 b m n = 0 ∧
  BITWISE (SUC k) b m n =
  (if b (ODD m) (ODD n) then 1 else 0) + 2 * BITWISE k b (m DIV 2) (n DIV 2)
Proof
  rewrite_tac [DECIDE “SUC n = 1 + n”,BITWISE_ADD] \\ gvs []
  \\ rewrite_tac [DECIDE “1 = SUC 0”,bitTheory.BITWISE_def] \\ gvs []
  \\ gvs [bitTheory.SBIT_def,bitTheory.BIT0_ODD]
QED

Theorem cv_word_and_loop_thm:
  ∀m n.
    m ≤ n ∧ n < dimword (:'a) ⇒
    cv_word_and_loop (Num m) (Num n) = Num (w2n (n2w m && n2w n :'a word))
Proof
  simp [wordsTheory.word_and_n2w,wordsTheory.dimword_def,bitTheory.BITWISE_LT_2EXP]
  \\ Q.SPEC_TAC (‘dimindex (:'a)’,‘l’)
  \\ completeInduct_on ‘m’
  \\ simp [Once cv_word_and_loop_def]
  \\ Cases_on ‘m = 0’ \\ fs [wordsTheory.WORD_AND_CLAUSES]
  >-
   (qsuff_tac ‘∀l n. BITWISE l $/\ 0 n = 0’ >- fs []
    \\ Induct \\ fs [BITWISE])
  \\ gvs [PULL_FORALL,AND_IMP_INTRO] \\ rw []
  \\ Cases_on ‘l’ \\ gvs []
  \\ rename [‘n < 2 ** SUC l’]
  \\ gvs [BITWISE]
  \\ first_x_assum $ qspecl_then [‘m DIV 2’,‘l’,‘n DIV 2’] mp_tac
  \\ impl_tac
  >- (gvs [] \\ irule_at Any arithmeticTheory.DIV_LE_MONOTONE \\ gvs [])
  \\ strip_tac \\ gvs [bitTheory.BITWISE_LT_2EXP,wordsTheory.dimword_def]
  \\ Cases_on ‘ODD m’
  \\ Cases_on ‘ODD n’
  \\ imp_res_tac bitTheory.ODD_MOD2_LEM
  \\ gvs [arithmeticTheory.ODD_EVEN]
  \\ imp_res_tac arithmeticTheory.EVEN_MOD2 \\ gvs []
QED

Theorem cv_word_or_loop_thm:
  ∀m n.
    m ≤ n ∧ n < dimword (:'a) ⇒
    cv_word_or_loop (Num m) (Num n) = Num (w2n (n2w m || n2w n :'a word))
Proof
  simp [wordsTheory.word_or_n2w,wordsTheory.dimword_def,bitTheory.BITWISE_LT_2EXP]
  \\ Q.SPEC_TAC (‘dimindex (:'a)’,‘l’)
  \\ completeInduct_on ‘m’
  \\ simp [Once cv_word_or_loop_def]
  \\ Cases_on ‘m = 0’ \\ fs [wordsTheory.WORD_OR_CLAUSES]
  >-
   (Induct \\ fs [BITWISE]
    \\ rpt strip_tac
    \\ ‘0 < 2:num’ by fs []
    \\ drule_then strip_assume_tac arithmeticTheory.DIVISION
    \\ pop_assum $ qspec_then ‘n’ mp_tac \\ strip_tac
    \\ pop_assum kall_tac
    \\ pop_assum (fn th => simp [Once th])
    \\ first_x_assum $ qspec_then ‘n DIV 2’ mp_tac
    \\ impl_tac >- gvs []
    \\ disch_then (fn th => simp [Once th])
    \\ Cases_on ‘ODD n’
    \\ imp_res_tac bitTheory.ODD_MOD2_LEM \\ gvs []
    \\ gvs [arithmeticTheory.ODD_EVEN]
    \\ imp_res_tac arithmeticTheory.EVEN_MOD2 \\ gvs [])
  \\ gvs [PULL_FORALL,AND_IMP_INTRO,GSYM cv_max_thm] \\ rw []
  \\ Cases_on ‘l’ \\ gvs []
  \\ rename [‘n < 2 ** SUC l’]
  \\ gvs [BITWISE]
  \\ first_x_assum $ qspecl_then [‘m DIV 2’,‘l’,‘n DIV 2’] mp_tac
  \\ impl_tac
  >- (gvs [] \\ irule_at Any arithmeticTheory.DIV_LE_MONOTONE \\ gvs [])
  \\ strip_tac \\ gvs [bitTheory.BITWISE_LT_2EXP,wordsTheory.dimword_def]
  \\ Cases_on ‘ODD m’
  \\ Cases_on ‘ODD n’
  \\ imp_res_tac bitTheory.ODD_MOD2_LEM
  \\ gvs []
  \\ gvs [arithmeticTheory.ODD_EVEN]
  \\ imp_res_tac arithmeticTheory.EVEN_MOD2 \\ gvs []
QED

Theorem cv_word_xor_loop_thm:
  ∀m n.
    m ≤ n ∧ n < dimword (:'a) ⇒
    cv_word_xor_loop (Num m) (Num n) = Num (w2n (word_xor (n2w m) (n2w n) :'a word))
Proof
  simp [wordsTheory.word_xor_n2w,wordsTheory.dimword_def,bitTheory.BITWISE_LT_2EXP]
  \\ Q.SPEC_TAC (‘dimindex (:'a)’,‘l’)
  \\ completeInduct_on ‘m’
  \\ simp [Once cv_word_xor_loop_def]
  \\ Cases_on ‘m = 0’ \\ fs [wordsTheory.WORD_XOR_CLAUSES]
  >-
   (Induct \\ fs [BITWISE]
    \\ rpt strip_tac
    \\ ‘0 < 2:num’ by fs []
    \\ drule_then strip_assume_tac arithmeticTheory.DIVISION
    \\ pop_assum $ qspec_then ‘n’ mp_tac \\ strip_tac
    \\ pop_assum kall_tac
    \\ pop_assum (fn th => simp [Once th])
    \\ first_x_assum $ qspec_then ‘n DIV 2’ mp_tac
    \\ impl_tac >- gvs []
    \\ disch_then (fn th => simp [Once th])
    \\ Cases_on ‘ODD n’
    \\ imp_res_tac bitTheory.ODD_MOD2_LEM \\ gvs []
    \\ gvs [arithmeticTheory.ODD_EVEN]
    \\ imp_res_tac arithmeticTheory.EVEN_MOD2 \\ gvs [])
  \\ gvs [PULL_FORALL,AND_IMP_INTRO] \\ rw []
  \\ Cases_on ‘l’ \\ gvs []
  \\ rename [‘n < 2 ** SUC l’]
  \\ gvs [BITWISE]
  \\ first_x_assum $ qspecl_then [‘m DIV 2’,‘l’,‘n DIV 2’] mp_tac
  \\ impl_tac
  >- (gvs [] \\ irule_at Any arithmeticTheory.DIV_LE_MONOTONE \\ gvs [])
  \\ strip_tac \\ gvs [bitTheory.BITWISE_LT_2EXP,wordsTheory.dimword_def]
  \\ ‘0 < 2:num’ by fs []
  \\ drule arithmeticTheory.MOD_PLUS
  \\ disch_then (fn th => simp_tac std_ss [Once (GSYM th)])
  \\ Cases_on ‘ODD m’
  \\ Cases_on ‘ODD n’
  \\ imp_res_tac bitTheory.ODD_MOD2_LEM
  \\ full_simp_tac std_ss [arithmeticTheory.ODD_EVEN]
  \\ imp_res_tac arithmeticTheory.EVEN_MOD2
  \\ full_simp_tac std_ss [arithmeticTheory.ODD_EVEN]
QED

Theorem cv_rep_word_and[cv_rep]:
  from_word (w1 && w2)
  =
  cv_word_and (from_word w1) (from_word w2)
Proof
  fs [cv_rep_def] \\ rw [] \\ gvs [from_word_def]
  \\ rw [cv_word_and_def]
  \\ Cases_on ‘w1’ \\ Cases_on ‘w2’ \\ gvs []
  \\ Cases_on ‘n < n'’ \\ gvs []
  >-
   (‘n ≤ n'’ by fs [] \\ pop_assum mp_tac \\ pop_assum kall_tac \\ rw []
    \\ drule_all cv_word_and_loop_thm
    \\ strip_tac \\ gvs [])
  \\ gvs [arithmeticTheory.NOT_LESS]
  \\ drule_all cv_word_and_loop_thm
  \\ strip_tac \\ gvs []
  \\ simp [Once wordsTheory.WORD_AND_COMM]
QED

Theorem cv_rep_word_or[cv_rep]:
  from_word (w1 || w2)
  =
  cv_word_or (from_word w1) (from_word w2)
Proof
  fs [cv_rep_def] \\ rw [] \\ gvs [from_word_def]
  \\ rw [cv_word_or_def]
  \\ Cases_on ‘w1’ \\ Cases_on ‘w2’ \\ gvs []
  \\ Cases_on ‘n < n'’ \\ gvs []
  >-
   (‘n ≤ n'’ by fs [] \\ pop_assum mp_tac \\ pop_assum kall_tac \\ rw []
    \\ drule_all cv_word_or_loop_thm
    \\ strip_tac \\ gvs [])
  \\ gvs [arithmeticTheory.NOT_LESS]
  \\ drule_all cv_word_or_loop_thm
  \\ strip_tac \\ gvs []
  \\ simp [Once wordsTheory.WORD_OR_COMM]
QED

Theorem cv_rep_word_xor[cv_rep]:
  from_word (word_xor w1 w2)
  =
  cv_word_xor (from_word w1) (from_word w2)
Proof
  fs [cv_rep_def] \\ rw [] \\ gvs [from_word_def]
  \\ rw [cv_word_xor_def]
  \\ Cases_on ‘w1’ \\ Cases_on ‘w2’ \\ gvs []
  \\ Cases_on ‘n < n'’ \\ gvs []
  >-
   (‘n ≤ n'’ by fs [] \\ pop_assum mp_tac \\ pop_assum kall_tac \\ rw []
    \\ drule_all cv_word_xor_loop_thm
    \\ strip_tac \\ gvs [])
  \\ gvs [arithmeticTheory.NOT_LESS]
  \\ drule_all cv_word_xor_loop_thm
  \\ strip_tac \\ gvs []
  \\ simp [Once wordsTheory.WORD_XOR_COMM]
QED

Theorem cv_rep_word_not[cv_rep]:
  from_word (¬ w :'a word)
  =
  cv_word_xor (from_word w) (Num (2 ** dimindex (:'a) - 1))
Proof
  ‘¬w = w ⊕ UINT_MAXw’ by fs [WORD_XOR_CLAUSES]
  \\ asm_rewrite_tac [cv_rep_word_xor, cv_rep_word_uint_max]
QED

val _ = export_theory();
