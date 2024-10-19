(*
  Pure functions for the Rat module.
*)
open preamble mlstringTheory mlintTheory;
open ratLib gcdTheory ratTheory;

val _ = new_theory "mlrat";

(* representation type *)

Datatype:
  rational = RatPair int num
End

Definition rational_of_num_def:
  rational_of_num (n:num) = RatPair (&n) 1
End

Definition rational_of_int_def:
  rational_of_int (n:int) = RatPair n 1
End

(* connection between real and rat *)

Definition real_of_rat_def:
  real_of_rat (r:rat) : real =
    intreal$real_of_int (RATN r) /  real_of_num (RATD r)
End

Theorem real_of_rat_int:
   real_of_rat (&x) = &x
Proof
  simp[real_of_rat_def, intrealTheory.real_of_int]
QED

Theorem real_of_rat_le[simp]:
   ∀r1 r2. real_of_rat r1 ≤ real_of_rat r2 ⇔ r1 ≤ r2
Proof
  simp[real_of_rat_def] >> rpt gen_tac >>
  assume_tac (RATN_DIV_RATD |> Q.INST [‘r’ |-> ‘r1’] |> SYM) >>
  assume_tac (RATN_DIV_RATD |> Q.INST [‘r’ |-> ‘r2’] |> SYM) >>
  map_every qabbrev_tac
    [‘n1 = RATN r1’, ‘n2 = RATN r2’, ‘d1 = RATD r1’, ‘d2 = RATD r2’] >>
  ‘0 < d1 ∧ 0 < d2’ by simp[Abbr‘d1’, Abbr‘d2’] >>
  simp[realTheory.REAL_LE_LDIV_EQ, realTheory.mult_ratl,
       realTheory.REAL_LE_RDIV_EQ] >>
  simp[RAT_LDIV_LEQ_POS, RDIV_MUL_OUT, RAT_RDIV_LEQ_POS] >>
  simp_tac bool_ss [GSYM intrealTheory.real_of_int_num,
                    GSYM intrealTheory.real_of_int_mul,
                    intrealTheory.real_of_int_le, GSYM rat_of_int_of_num,
                    rat_of_int_MUL, rat_of_int_LE, integerTheory.INT_MUL_COMM]
QED

Theorem real_of_rat_eq[simp]:
   ∀r1 r2. real_of_rat r1 = real_of_rat r2 ⇔ r1 = r2
Proof
  simp[real_of_rat_def] >> rpt gen_tac >>
  assume_tac (RATN_DIV_RATD |> Q.INST [‘r’ |-> ‘r1’] |> SYM) >>
  assume_tac (RATN_DIV_RATD |> Q.INST [‘r’ |-> ‘r2’] |> SYM) >>
  map_every qabbrev_tac
    [‘n1 = RATN r1’, ‘n2 = RATN r2’, ‘d1 = RATD r1’, ‘d2 = RATD r2’] >>
  ‘0 < d1 ∧ 0 < d2’ by simp[Abbr‘d1’, Abbr‘d2’] >>
  simp[realTheory.REAL_EQ_RDIV_EQ, realTheory.REAL_EQ_LDIV_EQ,
       RAT_RDIV_EQ, RAT_LDIV_EQ, realTheory.mult_ratl, RDIV_MUL_OUT] >>
  simp_tac bool_ss [GSYM intrealTheory.real_of_int_num,
                    GSYM intrealTheory.real_of_int_mul,
                    intrealTheory.real_of_int_11, GSYM rat_of_int_of_num,
                    rat_of_int_MUL, rat_of_int_11, integerTheory.INT_MUL_COMM]
QED

Theorem real_of_rat_lt:
   ∀r1 r2. real_of_rat r1 < real_of_rat r2 ⇔ r1 < r2
Proof
  rpt gen_tac >>
  ‘∀s1:real s2. s1 < s2 <=> s1 <= s2 /\ s1 <> s2’
    by metis_tac[realTheory.REAL_LE_LT, realTheory.REAL_LT_REFL] >>
  ‘∀r1 r2:rat. r1 < r2 <=> r1 <= r2 /\ r1 <> r2’
    by metis_tac[rat_leq_def, RAT_LES_REF] >>
  simp[]
QED

Theorem real_of_rat_add:
   ∀r1 r2. real_of_rat (r1 + r2) = real_of_rat r1 + real_of_rat r2
Proof
  simp[real_of_rat_def] >> rpt gen_tac >>
  map_every (fn q =>
                assume_tac (RATN_DIV_RATD |> Q.INST [‘r’ |-> q] |> SYM))
            [‘r1’, ‘r2’, ‘r1 + r2’] >>
  map_every qabbrev_tac
    [‘n1 = RATN r1’, ‘n2 = RATN r2’, ‘d1 = RATD r1’, ‘d2 = RATD r2’,
     ‘sn = RATN (r1 + r2)’, ‘sd = RATD (r1 + r2)’] >>
  ‘0 < d1 ∧ 0 < d2 ∧ 0 < sd’ by simp[Abbr‘d1’, Abbr‘d2’, Abbr‘sd’] >>
  simp[realTheory.REAL_ADD_RAT, realTheory.eq_ratr, realTheory.mult_ratr] >>
  simp_tac bool_ss [GSYM intrealTheory.real_of_int_num,
                    GSYM intrealTheory.real_of_int_mul,
                    GSYM intrealTheory.real_of_int_add,
                    intrealTheory.real_of_int_11] >>
  ‘r1 + r2 = (rat_of_int n1 * &d2 + rat_of_int n2 * &d1) / (&d1 * &d2)’
    by (ntac 2 (last_x_assum SUBST1_TAC) >> simp[RAT_DIVDIV_ADD]) >>
  pop_assum mp_tac >>
  simp[RAT_LDIV_EQ, RAT_RDIV_EQ, RDIV_MUL_OUT, LDIV_MUL_OUT] >>
  simp_tac bool_ss [GSYM rat_of_int_of_num, rat_of_int_MUL, rat_of_int_ADD,
                    rat_of_int_11] >>
  simp[integerTheory.INT_MUL_COMM]
QED

Theorem real_of_rat_mul:
  ∀r1 r2. real_of_rat (r1 * r2) = real_of_rat r1 * real_of_rat r2
Proof
  simp[real_of_rat_def] >> rpt gen_tac >>
  map_every (fn q =>
                assume_tac (RATN_DIV_RATD |> Q.INST [‘r’ |-> q] |> SYM))
            [‘r1’, ‘r2’, ‘r1 * r2’] >>
  map_every qabbrev_tac
    [‘n1 = RATN r1’, ‘n2 = RATN r2’, ‘d1 = RATD r1’, ‘d2 = RATD r2’,
     ‘pn = RATN (r1 * r2)’, ‘pd = RATD (r1 * r2)’] >>
  ‘0 < d1 ∧ 0 < d2 ∧ 0 < pd’ by simp[Abbr‘d1’, Abbr‘d2’, Abbr‘pd’] >>
  markerLib.RM_ALL_ABBREVS_TAC >>
  simp[realTheory.eq_ratr, realTheory.mult_rat, realTheory.mult_ratr] >>
  simp_tac bool_ss [GSYM intrealTheory.real_of_int_num,
                    GSYM intrealTheory.real_of_int_mul,
                    GSYM intrealTheory.real_of_int_add,
                    intrealTheory.real_of_int_11] >>
  ‘r1 * r2 = (rat_of_int n1 * rat_of_int n2) / (&d1 * &d2)’
    by (ntac 2 (last_x_assum SUBST1_TAC) >> simp[RAT_DIVDIV_MUL]) >>
  pop_assum mp_tac >>
  simp[RAT_LDIV_EQ, RDIV_MUL_OUT, RAT_RDIV_EQ, LDIV_MUL_OUT] >>
  simp_tac bool_ss [GSYM rat_of_int_of_num, rat_of_int_MUL, rat_of_int_11] >>
  simp[integerTheory.INT_MUL_COMM]
QED

Theorem real_of_rat_ainv:
  ∀r. real_of_rat (-r) = -real_of_rat r
Proof
  gen_tac >> simp[real_of_rat_def, realTheory.neg_rat]
QED

Theorem real_of_rat_sub:
   ∀r1 r2. real_of_rat (r1 - r2) = real_of_rat r1 - real_of_rat r2
Proof
  rpt gen_tac >>
  simp[RAT_SUB_ADDAINV, real_of_rat_ainv, real_of_rat_add,
       realTheory.real_sub]
QED

Triviality inv_div:
  x ≠ 0r ∧ y ≠ 0 ⇒ (inv (x / y) = y / x)
Proof
  simp[realTheory.real_div, realTheory.REAL_INV_MUL, realTheory.REAL_INV_EQ_0,
       realTheory.REAL_INV_INV, realTheory.REAL_MUL_COMM]
QED

Theorem real_of_int_eq_num[simp]:
   ((real_of_int i = &n) <=> (i = &n)) /\
   ((&n = real_of_int i) <=> (i = &n))
Proof
  simp[EQ_IMP_THM] >> simp[intrealTheory.real_of_int_def] >>
  Cases_on ‘i’ >> simp[realTheory.eq_ints]
QED

Theorem rat_of_int_eq_num[simp]:
   ((rat_of_int i = &n) <=> (i = &n)) /\
   ((&n = rat_of_int i) <=> (i = &n))
Proof
  Cases_on ‘i’ >> simp[rat_of_int_def]
QED

Theorem real_of_rat_inv:
  !r. r ≠ 0 ==> real_of_rat (rat_minv r) = inv (real_of_rat r)
Proof
  gen_tac >> simp[real_of_rat_def] >>
  assume_tac (RATN_DIV_RATD |> SYM) >>
  assume_tac (RATN_DIV_RATD |> Q.INST [‘r’ |-> ‘rat_minv r’] |> SYM) >>
  map_every qabbrev_tac [‘n = RATN r’, ‘d = RATD r’, ‘n' = RATN (rat_minv r)’,
                         ‘d' = RATD (rat_minv r)’] >>
  ‘0 < d ∧ 0 < d'’ by simp[Abbr‘d’, Abbr‘d'’] >>
  markerLib.RM_ALL_ABBREVS_TAC >>
  simp[RAT_LDIV_EQ, inv_div, realTheory.eq_ratr, realTheory.mult_rat,
       realTheory.mult_ratr] >>
  simp_tac bool_ss [GSYM intrealTheory.real_of_int_num,
                    GSYM intrealTheory.real_of_int_mul,
                    intrealTheory.real_of_int_11] >>
  last_x_assum SUBST_ALL_TAC >> strip_tac >> fs[RAT_DIV_MINV] >>
  fs[RAT_RDIV_EQ, RAT_LDIV_EQ, RDIV_MUL_OUT, LDIV_MUL_OUT] >>
  last_x_assum mp_tac >>
  simp[RAT_MUL_NUM_CALCULATE, rat_of_int_MUL]
QED

Theorem real_of_rat_div:
  x ≠ 0 ⇒ real_of_rat (x' / x) = real_of_rat x' / real_of_rat x
Proof
  simp [RAT_DIV_MULMINV,real_of_rat_mul,real_of_rat_inv,realTheory.real_div]
QED

Theorem real_of_int_of_rat:
  real_of_int i = real_of_rat (rat_of_int i)
Proof
  simp[real_of_rat_def]
QED

Theorem rat_of_int_eq:
  gcd (Num (ABS n1)) d1 = 1 ∧ d1 ≠ 0 ∧
  gcd (Num (ABS n2)) d2 = 1 ∧ d2 ≠ 0 ∧
  rat_of_int n1 / &d1 = rat_of_int n2 / &d2 ⇒
  n1 = n2 ∧ d1 = d2
Proof
  rpt strip_tac >>
  Cases_on `d1 = d2` >> rveq
  >- rfs[RAT_MINV_EQ_0, RAT_DIV_MULMINV, RAT_EQ_RMUL] >>
  fs[] >>
  `(rat_of_int n1 / &d1) * (&d1 * &d2) = (rat_of_int n2 / &d2) * (&d1 * &d2)`
    by fs [RAT_EQ_RMUL] >>
  `rat_of_int n1 / &d1 * &d1 = rat_of_int n1`
     by (simp_tac bool_ss [RAT_DIV_MULMINV] >>
         metis_tac[RAT_MUL_LINV, RAT_MUL_ASSOC, RAT_MUL_RID,
                   RAT_EQ_NUM_CALCULATE]) >>
  `rat_of_int n2 / &d2 * &d2 = rat_of_int n2`
     by (simp_tac bool_ss [RAT_DIV_MULMINV] >>
         metis_tac[RAT_MUL_LINV, RAT_MUL_ASSOC, RAT_MUL_RID,
                   RAT_EQ_NUM_CALCULATE]) >>
  `rat_of_int n1 * & d2 = rat_of_int n2 * & d1`
     by metis_tac [RAT_MUL_ASSOC,RAT_MUL_COMM] >>
  pop_assum mp_tac >>
  ntac 3 (pop_assum kall_tac) >> fs [] >>
  Cases_on `n1` >> Cases_on `n2` >>
  fs [integerTheory.INT_ABS_NUM, integerTheory.INT_ABS_NEG,
      rat_of_int_ainv, RAT_MUL_NUM_CALCULATE] >>
  rfs [RAT_DIV_EQ0] >> strip_tac >>
  rename [`d1 * n1 = d2 * n2:num`]
  \\ `divides d2 (d1 * n1) /\
      divides n2 (d1 * n1) /\
      divides d1 (d2 * n2) /\
      divides n1 (d2 * n2)` by
     (fs [dividesTheory.divides_def] \\ metis_tac [MULT_COMM])
  \\ `gcd d1 n2 = 1 /\ gcd d2 n1 = 1` by metis_tac [GCD_SYM]
  \\ fs []
  \\ imp_res_tac L_EUCLIDES
  \\ imp_res_tac dividesTheory.DIVIDES_ANTISYM
  \\ rveq \\ rfs [arithmeticTheory.EQ_MULT_RCANCEL]
QED

Definition toString_def:
  toString (RatPair i n) =
    if n = 1 then mlint$toString i else
      concat [mlint$toString i ; implode"/" ; mlint$toString (&n)]
End

Definition real_to_rational_def[nocompute]:
  real_to_rational (r:real) =
    let (n,d) = (@x. ∃n d. x = (n,d) ∧
                           r = real_of_int n / & d ∧
                           gcd (Num (ABS n)) d = 1 ∧
                           d ≠ 0) in
      RatPair n d
End

Definition real_to_str_def:
  real_to_str r = toString (real_to_rational r)
End

Theorem real_of_int_div_eq:
  ∀n d n' d'.
    gcd (Num (ABS n')) d' = 1 ∧ d' ≠ 0 ∧
    gcd (Num (ABS n)) d = 1 ∧ d ≠ 0 ⇒
    (real_of_int n / &d = real_of_int n' / &d' ⇔ n = n' ∧ d = d')
Proof
  rw [] \\ eq_tac \\ gvs [] \\ strip_tac
  \\ irule rat_of_int_eq \\ fs []
  \\ fs [real_of_int_of_rat]
  \\ gvs [GSYM real_of_rat_int]
  \\ ‘&d ≠ 0:rat ∧ &d' ≠ 0:rat’ by gvs []
  \\ dxrule $ real_of_rat_div
  \\ dxrule $ real_of_rat_div
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ rpt strip_tac \\ fs []
QED

Theorem real_to_str_num[compute]:
  real_to_str (& n) = toString (RatPair (&n) 1)
Proof
  fs [real_to_str_def] \\ AP_TERM_TAC
  \\ fs [real_to_rational_def]
  \\ pairarg_tac \\ fs []
  \\ qspecl_then [‘&n’,‘1’] mp_tac real_of_int_div_eq
  \\ fs [gcdTheory.GCD_1]
  \\ strip_tac \\ gvs [SF CONJ_ss]
QED

Theorem real_to_str_neg_num[compute]:
  real_to_str (-& n) = toString (RatPair (-&n) 1)
Proof
  fs [real_to_str_def] \\ AP_TERM_TAC
  \\ fs [real_to_rational_def]
  \\ pairarg_tac \\ fs []
  \\ qspecl_then [‘-&n’,‘1’] mp_tac real_of_int_div_eq
  \\ fs [gcdTheory.GCD_1]
  \\ strip_tac \\ gvs [SF CONJ_ss]
QED

Theorem real_to_str_rat[compute]:
  real_to_str (& n / & d) =
  toString (if d = 0 then real_to_rational (& n / & d)
            else let k = gcd n d in RatPair (& (n DIV k)) (d DIV k))
Proof
  fs [real_to_str_def] \\ AP_TERM_TAC
  \\ IF_CASES_TAC \\ fs []
  \\ fs [real_to_rational_def]
  \\ pairarg_tac \\ fs []
  \\ Cases_on ‘n = 0’
  >-
   (gvs [realTheory.REAL_DIV_LZERO,realTheory.REAL_DIV_ZERO,SF CONJ_ss]
    \\ fs [DIV_EQ_X])
  \\ qspecl_then [‘n’,‘d’] mp_tac gcdTheory.FACTOR_OUT_GCD
  \\ impl_tac >- fs []
  \\ strip_tac
  \\ qabbrev_tac ‘k = gcd n d’ \\ gvs []
  \\ full_simp_tac std_ss [GSYM realTheory.REAL_MUL]
  \\ ‘& k ≠ 0:real’ by gvs []
  \\ full_simp_tac std_ss [realTheory.REAL_DIV_LMUL_CANCEL]
  \\ once_rewrite_tac [MULT_COMM]
  \\ fs [MULT_DIV]
  \\ qspecl_then [‘&p’,‘q’] mp_tac real_of_int_div_eq \\ fs []
  \\ strip_tac \\ gvs [SF CONJ_ss]
QED

Theorem real_to_str_neg_rat[compute]:
  real_to_str (-& n / & d) =
  toString (if d = 0 then real_to_rational (-& n / & d)
            else let k = gcd n d in RatPair (-& (n DIV k)) (d DIV k))
Proof
  fs [real_to_str_def] \\ AP_TERM_TAC
  \\ IF_CASES_TAC \\ fs []
  \\ fs [real_to_rational_def]
  \\ pairarg_tac \\ fs []
  \\ Cases_on ‘n = 0’
  >-
   (gvs [realTheory.REAL_DIV_LZERO,realTheory.REAL_DIV_ZERO,SF CONJ_ss]
    \\ fs [DIV_EQ_X])
  \\ qspecl_then [‘n’,‘d’] mp_tac gcdTheory.FACTOR_OUT_GCD
  \\ impl_tac >- fs []
  \\ strip_tac
  \\ qabbrev_tac ‘k = gcd n d’ \\ gvs []
  \\ full_simp_tac std_ss [GSYM realTheory.REAL_MUL]
  \\ ‘& k ≠ 0:real’ by gvs []
  \\ full_simp_tac std_ss [realTheory.REAL_DIV_LMUL_CANCEL,
                           GSYM (CONJUNCT1 realTheory.neg_rat)]
  \\ full_simp_tac std_ss [realTheory.neg_rat]
  \\ once_rewrite_tac [MULT_COMM]
  \\ fs [MULT_DIV]
  \\ qspecl_then [‘-&p’,‘q’] mp_tac real_of_int_div_eq \\ fs []
  \\ strip_tac \\ gvs [SF CONJ_ss]
QED

Theorem INT_FLOOR_real_of_int:
  INT_FLOOR (real_of_int i) = i
Proof
  simp[intrealTheory.INT_FLOOR]
QED

val _ = export_theory ();
